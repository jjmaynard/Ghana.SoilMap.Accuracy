# Title: Functional profile comparison
# Description: This python code implements a functional comparision of soil profiles using the GAEZ soil quality property ratings related to soil texture, rock fragments, and depth
# Author: Jonathan Maynard
# Date: November 3, 2020

import os, random, collections, operator
import csv, math, struct, sys
import scipy.stats
import colour
import math
from math import radians, cos, sin, asin, sqrt
import json

import numpy as np
import pandas as pd
import skimage
import re
import urllib.request, urllib.error, urllib.parse
from scipy.spatial import distance
from scipy.interpolate import CubicSpline
from sklearn.utils import validation
from sklearn.metrics import pairwise
from sklearn.metrics.pairwise import euclidean_distances
from scipy.sparse import issparse

from pandas.io.json import json_normalize
#from skimage import color
from collections import OrderedDict
from collections import Counter
import MySQLdb
import io

from osgeo import gdal, ogr
from osgeo.gdalconst import *
import geopandas as gpd
import shapely
from shapely.geometry import Point, Polygon, shape, LinearRing

#####################################################################################################
#                                       back-end functions                                            #
#####################################################################################################
def getDataStore_Connection():
    try:
        HOST = '127.0.0.1'
        USER = 'root'
        PASSWORD = 'root'
        DATABASE = 'apex'
        conn = MySQLdb.connect(host=HOST, user=USER, passwd=PASSWORD, db=DATABASE)
        return conn
    except Exception as err:
        print(err)
        sys.exit(str(err))

def getWISE30sec_data(MUGLB_NEW_Select):
    try:
        conn = getDataStore_Connection()
        cur = conn.cursor()
        sql = 'SELECT MUGLB_NEW, COMPID, id, MU_GLOBAL, NEWSUID, SCID, PROP, CLAF,  PRID, Layer, TopDep, BotDep,  CFRAG,  SDTO,  STPC,  CLPC, CECS, PHAQ, ELCO, SU_name, FAO_SYS FROM  wise_soil_data WHERE MUGLB_NEW IN (' + ','.join(map(str, MUGLB_NEW_Select)) + ')'  
        cur.execute(sql)
        results = cur.fetchall()
        data = pd.DataFrame(list(results))
        data.columns = ['MUGLB_NEW',  'COMPID', 'id', 'MU_GLOBAL', 'NEWSUID', 'SCID', 'PROP', 'CLAF',  'PRID', 'Layer', 'TopDep', 'BotDep',  'CFRAG',  'SDTO',  'STPC',  'CLPC', 'CECS', 'PHAQ', 'ELCO', 'SU_name', 'FAO_SYS']
        return data
        conn.close()
    except Exception as err:
        print(err)
        return None

def getWISE30sec_comp_data(COMPID):
    try:
        conn = getDataStore_Connection()
        cur = conn.cursor()
        COMPID_List = [COMPID]
        sql = 'SELECT MUGLB_NEW, COMPID, id, MU_GLOBAL, NEWSUID, SU_name, SCID, PROP, CLAF,  PRID, Layer, TopDep, BotDep, Drain, DrainNum, CFRAG, SDTO, STPC, CLPC, PSCL, BULK, TAWC, ORGC, TOTN, CECS, CECc, ECEC, TEB, BSAT, ALSA, ESP, PHAQ, TCEQ, GYPS, ELCO, PHASE1, PHASE2, ROOTS, IL, SWR, ADD_PROP, T_DC, S_DC, T_BULK_DEN, T_REF_BULK, S_BULK_DEN, S_REF_BULK, text_class, text_class_id, REF_DEPTH FROM  wise_soil_data WHERE COMPID IN (' + ','.join(map(str, COMPID_List)) + ')'
        cur.execute(sql)
        results = cur.fetchall()
        data = pd.DataFrame(list(results))
        data.columns = ['MUGLB_NEW', 'COMPID', 'id', 'MU_GLOBAL', 'NEWSUID', 'SU_name', 'SCID', 'PROP', 'CLAF',  'PRID', 'Layer', 'TopDep', 'BotDep', 'Drain', 'DrainNum', 'CFRAG', 'SDTO', 'STPC', 'CLPC', 'PSCL', 'BULK', 'TAWC', 'ORGC', 'TOTN', 'CECS', 'CECc', 'ECEC', 'TEB', 'BSAT', 'ALSA', 'ESP', 'PHAQ', 'TCEQ', 'GYPS', 'ELCO', 'PHASE1', 'PHASE2', 'ROOTS', 'IL', 'SWR', 'ADD_PROP', 'T_DC', 'S_DC', 'T_BULK_DEN', 'T_REF_BULK', 'S_BULK_DEN', 'S_REF_BULK','text_class', 'text_class_id', 'REF_DEPTH']
        return data
        conn.close()
    except Exception as err:
        print(err)
        return None
    finally:
        conn.close()

### Land Qualities:
  # 1. Climate regime (temperature, moisture, radiation) -- [Climatic suitability classification]
  # 2. Flooding regime -- [Moisture regime analysis of water collecting sites]
  # 3. Soil erosion -- [Assessment of sustainable use of sloping terrain]
  # 4. Soil nutrient maintenance -- [Fallow period requirement assessment]
  # 5. Soil physical and chemical properties -- [Soil suitability classification]
  
# Module IV (Agro-edaphic suitability)
### Calculations are crop/LUT specific and are performed for rainfed systems only
# In the GAEZ approach, land qualities are assessed in several steps involving specific procedures. The land qualities related to climate and climate‐soil interactions (flooding regimes, soil erosion and soil nutrient maintenance) are treated separate from those land qualities specifically related to soil properties and conditions as reflected in the Harmonized World Soil Database and the GAEZ terrain-slope database.

## Soil Qualities
# Soil quality will be calculated at each soil depth and averaged using appropriate depth weights.
# Standard GAEZ depth weights: 
# Depth  |  # of layers  | Weighting Factors
# 120    |      6        | 2, 1.5 , 1, .75, .5, .25
# 100    |      5        | 1.75, 1.5 , 1, .5, .25
# 80     |      4        | 1.75, 1.25 , .75, .25
# 60     |      3        | 1.5, 1, .5
# 40     |      2        | 1.25, .75
# 20     |      1        | 1

# Profile
def getGAEZ_profile_req(CROP_ID, Input_Level_List):
    try:
        conn = getDataStore_Connection()
        cur = conn.cursor()
        sql = 'SELECT CROP_ID, CROP, input_level, SQI_code, score, property_value, property, unit, property_id, property_text FROM  GAEZ_profile_req_rf WHERE CROP_ID=\'' + CROP_ID + '\' AND input_level IN ('  + ','.join(map(str, Input_Level_List)) + ')'
        cur.execute(sql)
        results = cur.fetchall()
        data = pd.DataFrame(list(results))
        data.columns = ['CROP_ID', 'CROP', 'input_level', 'SQI_code', 'score', 'property_value', 'property', 'unit', 'property_id', 'property_text']
        return data
        conn.close()
    except Exception as err:
        print(err)
        return None
    finally:
        conn.close()

# Texture
def getGAEZ_texture_req(CROP_ID, Input_Level_List):
    try:
        conn = getDataStore_Connection()
        cur = conn.cursor()
        sql = 'SELECT CROP_ID, CROP, input_level, SQI_code, score, text_class_id, text_class FROM  GAEZ_text_req_rf WHERE CROP_ID=\'' + CROP_ID + '\' AND input_level IN ('  + ','.join(map(str, Input_Level_List)) + ')'
        cur.execute(sql)
        results = cur.fetchall()
        data = pd.DataFrame(list(results))
        data.columns = ['CROP_ID', 'CROP', 'input_level', 'SQI_code', 'score', 'text_class_id', 'text_class']
        return data
        conn.close()
    except Exception as err:
        print(err)
        return None
    finally:
        conn.close()

# Phase
def getGAEZ_phase_req(CROP_ID, Input_Level_List):
    try:
        conn = getDataStore_Connection()
        cur = conn.cursor()
        sql = 'SELECT CROP_ID, CROP, input_level, SQI_code, property, phase_id, phase, score FROM  GAEZ_phase_req_rf WHERE CROP_ID=\'' + CROP_ID + '\' AND input_level IN ('  + ','.join(map(str, Input_Level_List)) + ')'
        cur.execute(sql)
        results = cur.fetchall()
        data = pd.DataFrame(list(results))
        data.columns = ['CROP_ID', 'CROP', 'input_level', 'SQI_code', 'property', 'phase_id', 'phase', 'score']
        return data
        conn.close()
    except Exception as err:
        print(err)
        return None
    finally:
        conn.close()
        
# Drainage
def getGAEZ_drainage_req(CROP_ID, Input_Level_List):
    try:
        conn = getDataStore_Connection()
        cur = conn.cursor()
        sql = 'SELECT CROP_ID, CROP, input_level, SQI_code, PSCL, DrainNum, Drain, score FROM  GAEZ_drainage_req_rf WHERE CROP_ID=\'' + CROP_ID + '\' AND input_level IN ('  + ','.join(map(str, Input_Level_List)) + ')'
        cur.execute(sql)
        results = cur.fetchall()
        data = pd.DataFrame(list(results))
        data.columns = ['CROP_ID', 'CROP', 'input_level', 'SQI_code', 'PSCL', 'DrainNum', 'Drain', 'score']
        return data
        conn.close()
    except Exception as err:
        print(err)
        return None
    finally:
        conn.close()
        
# # Terrain (Not currently implemented)
# def getGAEZ_terrain_req(CROP_ID, Input_Level_List):
#     try:
#         conn = getDataStore_Connection()
#         cur = conn.cursor()
#         sql = 'SELECT CROP_ID, CROP, crop_group, input_level, FM_class, slope_class, slope_class_id, rating, rating_text FROM  GAEZ_terrain_req_rf WHERE CROP_ID=\'' + CROP_ID + '\' AND input_level IN ('  + ','.join(map(str, Input_Level_List)) + ')'
#         cur.execute(sql)
#         results = cur.fetchall()
#         data = pd.DataFrame(list(results))
#         data.columns = ['CROP_ID', 'CROP', 'crop_group', 'input_level', 'FM_class', 'slope_class', 'slope_class_id', 'rating', 'rating_text']
#         return data
#         conn.close()
#     except Exception as err:
#         print(err)
#         return None
#     finally:
#         conn.close()  
  
# -----------------------------------------------------------------------------------------------------
#Function to GAEZ Soil Quality Indides
def func_prof_comp_GAEZ_SQI(data, CROP_ID, inputLevel, depthWt_type=1):
#     data = getWISE30sec_comp_data(COMPID)
# 
# ## ---------------------------------------------------------------------------------------------------------------------
#     def agg_data_layer_SQI(data, bottom, sd=2, depth=False):
#         if np.isnan(bottom) or bottom == 0:
#             data_d = pd.Series([np.nan])
#             
#             d_lyrs = pd.Series([np.nan])
#             if depth is True:
#                 return data_d, d_lyrs
#             else:
#                 return data_d
#         elif bottom >= 0 and bottom < 21:
#             data_d = pd.Series([round(pd.Series.mean(data[0:21]), sd)])
#             data_d = data_d.rename(index={0:'sl1'})
#             d_lyrs = pd.Series([21]).rename(index={0:'sl1'})
#             if depth is True:
#                 return data_d, d_lyrs
#             else:
#                 return data_d
#         elif bottom >=21 and bottom < 41:
#             data_d = pd.Series([round(pd.Series.mean(data[0:20]), sd), round(pd.Series.mean(data[20:bottom]), sd)])
#             data_d = data_d.rename(index={0:'sl1', 1:'sl2'})
#             d_lyrs = pd.Series([20, bottom]).rename(index={0:'sl1', 1:'sl2'})
#             if depth is True:
#                 return data_d, d_lyrs
#             else:
#                 return data_d
#         elif bottom >= 41 and bottom < 61:
#             data_d = pd.Series([round(pd.Series.mean(data[0:20]), sd), round(pd.Series.mean(data[20:40]), sd), round(pd.Series.mean(data[40:bottom]), sd)])
#             data_d = data_d.rename(index={0:'sl1', 1:'sl2', 2:'sl3'})
#             d_lyrs = pd.Series([20, 40, bottom]).rename(index={0:'sl1', 1:'sl2', 2:'sl3'})
#             if depth is True:
#                 return data_d, d_lyrs
#             else:
#                 return data_d
#         elif bottom >= 61 and bottom < 81:
#             data_d = pd.Series([round(pd.Series.mean(data[0:20]), sd), round(pd.Series.mean(data[20:40]), sd), round(pd.Series.mean(data[40:60]), sd), round(pd.Series.mean(data[60:bottom]), sd)])
#             data_d = data_d.rename(index={0:'sl1', 1:'sl2', 2:'sl3',3:'sl4'})
#             d_lyrs = pd.Series([20, 40, 60, bottom]).rename(index={0:'sl1', 1:'sl2', 2:'sl3',3:'sl4'})
#             if depth is True:
#                 return data_d, d_lyrs
#             else:
#                 return data_d
#         elif bottom >= 81 and bottom < 101:
#             data_d = pd.Series([round(pd.Series.mean(data[0:20]), sd), round(pd.Series.mean(data[20:40]), sd), round(pd.Series.mean(data[40:60]), sd), round(pd.Series.mean(data[60:80]), sd), round(pd.Series.mean(data[80:bottom]), sd)])
#             data_d = data_d.rename(index={0:'sl1', 1:'sl2', 2:'sl3',3:'sl4', 4:'sl5'})
#             d_lyrs = pd.Series([20, 40, 60, 80, bottom]).rename(index={0:'sl1', 1:'sl2', 2:'sl3',3:'sl4', 4:'sl5'})
#             if depth is True:
#                 return data_d, d_lyrs
#             else:
#                 return data_d
#         elif bottom >= 101 and bottom < 120:
#             data_d = pd.Series([round(pd.Series.mean(data[0:20]), sd), round(pd.Series.mean(data[20:40]), sd), round(pd.Series.mean(data[40:60]), sd), round(pd.Series.mean(data[60:80]), sd), round(pd.Series.mean(data[80:100]), sd), round(pd.Series.mean(data[100:bottom]), sd)])
#             data_d = data_d.rename(index={0:'sl1', 1:'sl2', 2:'sl3',3:'sl4', 4:'sl5', 5:'sl6'})
#             d_lyrs = pd.Series([20, 40, 60, 80, 100, bottom]).rename(index={0:'sl1', 1:'sl2', 2:'sl3',3:'sl4', 4:'sl5', 5:'sl6'})
#             if depth is True:
#                 return data_d, d_lyrs
#             else:
#                 return data_d
#         elif bottom >= 120:
#             data_d = pd.Series([round(pd.Series.mean(data[0:20]), sd), round(pd.Series.mean(data[20:40]), sd), round(pd.Series.mean(data[40:60]), sd), round(pd.Series.mean(data[60:80]), sd), round(pd.Series.mean(data[80:100]), sd), round(pd.Series.mean(data[100:120]), sd)])
#             data_d = data_d.rename(index={0:'sl1', 1:'sl2', 2:'sl3',3:'sl4', 4:'sl5', 5:'sl6'})
#             d_lyrs = pd.Series([20, 40, 60, 80, 100, 120]).rename(index={0:'sl1', 1:'sl2', 2:'sl3',3:'sl4', 4:'sl5', 5:'sl6'})
#             if depth is True:
#                 return data_d, d_lyrs
#             else:
#                 return data_d
#                 
#     def agg_data_layer(data, bottom, sd=2, depth=False):
#         if np.isnan(bottom) or bottom == 0:
#             data_d = pd.Series([np.nan])
#             
#             d_lyrs = pd.Series([np.nan])
#             if depth is True:
#                 return data_d, d_lyrs
#             else:
#                 return data_d
#         elif bottom >= 0 and bottom < 1:
#             data_d = pd.Series([round(pd.Series.mean(data[0:1]), sd)])
#             data_d = data_d.rename(index={0:'sl1'})
#             d_lyrs = pd.Series([1]).rename(index={0:'sl1'})
#             if depth is True:
#                 return data_d, d_lyrs
#             else:
#                 return data_d
#         elif bottom >=1 and bottom < 11:
#             data_d = pd.Series([round(pd.Series.mean(data[0:1]), sd), round(pd.Series.mean(data[1:bottom]), sd)])
#             data_d = data_d.rename(index={0:'sl1', 1:'sl2'})
#             d_lyrs = pd.Series([1, bottom]).rename(index={0:'sl1', 1:'sl2'})
#             if depth is True:
#                 return data_d, d_lyrs
#             else:
#                 return data_d
#         elif bottom >= 11 and bottom < 21:
#             data_d = pd.Series([round(pd.Series.mean(data[0:1]), sd), round(pd.Series.mean(data[1:10]), sd), round(pd.Series.mean(data[10:bottom]), sd)])
#             data_d = data_d.rename(index={0:'sl1', 1:'sl2', 2:'sl3'})
#             d_lyrs = pd.Series([1, 10, bottom]).rename(index={0:'sl1', 1:'sl2', 2:'sl3'})
#             if depth is True:
#                 return data_d, d_lyrs
#             else:
#                 return data_d
#         elif bottom >= 21 and bottom < 51:
#             data_d = pd.Series([round(pd.Series.mean(data[0:1]), sd), round(pd.Series.mean(data[1:10]), sd), round(pd.Series.mean(data[10:20]), sd), round(pd.Series.mean(data[20:bottom]), sd)])
#             data_d = data_d.rename(index={0:'sl1', 1:'sl2', 2:'sl3',3:'sl4'})
#             d_lyrs = pd.Series([1, 10, 20, bottom]).rename(index={0:'sl1', 1:'sl2', 2:'sl3',3:'sl4'})
#             if depth is True:
#                 return data_d, d_lyrs
#             else:
#                 return data_d
#         elif bottom >= 51 and bottom < 71:
#             data_d = pd.Series([round(pd.Series.mean(data[0:1]), sd), round(pd.Series.mean(data[1:10]), sd), round(pd.Series.mean(data[10:20]), sd), round(pd.Series.mean(data[20:50]), sd), round(pd.Series.mean(data[50:bottom]), sd)])
#             data_d = data_d.rename(index={0:'sl1', 1:'sl2', 2:'sl3',3:'sl4', 4:'sl5'})
#             d_lyrs = pd.Series([1, 10, 20, 50, bottom]).rename(index={0:'sl1', 1:'sl2', 2:'sl3',3:'sl4', 4:'sl5'})
#             if depth is True:
#                 return data_d, d_lyrs
#             else:
#                 return data_d
#         elif bottom >= 71 and bottom < 101:
#             data_d = pd.Series([round(pd.Series.mean(data[0:1]), sd), round(pd.Series.mean(data[1:10]), sd), round(pd.Series.mean(data[10:20]), sd), round(pd.Series.mean(data[20:50]), sd), round(pd.Series.mean(data[50:70]), sd), round(pd.Series.mean(data[70:bottom]), sd)])
#             data_d = data_d.rename(index={0:'sl1', 1:'sl2', 2:'sl3',3:'sl4', 4:'sl5', 5:'sl6'})
#             d_lyrs = pd.Series([1, 10, 20, 50, 70, bottom]).rename(index={0:'sl1', 1:'sl2', 2:'sl3',3:'sl4', 4:'sl5', 5:'sl6'})
#             if depth is True:
#                 return data_d, d_lyrs
#             else:
#                 return data_d
#         elif bottom >= 101:
#             data_d = pd.Series([round(pd.Series.mean(data[0:1]), sd), round(pd.Series.mean(data[1:10]), sd), round(pd.Series.mean(data[10:20]), sd), round(pd.Series.mean(data[20:50]), sd), round(pd.Series.mean(data[50:70]), sd), round(pd.Series.mean(data[70:100]), sd)])
#             data_d = data_d.rename(index={0:'sl1', 1:'sl2', 2:'sl3',3:'sl4', 4:'sl5', 5:'sl6'})
#             d_lyrs = pd.Series([1, 10, 20, 50, 70, 100]).rename(index={0:'sl1', 1:'sl2', 2:'sl3',3:'sl4', 4:'sl5', 5:'sl6'})
#             if depth is True:
#                 return data_d, d_lyrs
#             else:
#                 return data_d
# 
#     def gettt(row, sand=None, silt=None, clay=None):
#         if sand is not None and silt is not None and clay is not None:
#             sand = sand
#             silt = silt
#             clay = clay
#         else:
#             sand = row['sandtotal_r']
#             silt = row['silttotal_r']
#             clay = row['claytotal_r']
# 
#         if (silt + 1.5 * clay) < 15:
#             return "Sand"
#         elif (silt + 1.5 * clay) >= 15 and (silt + 2.0 * clay) < 30:
#             return "Loamy sand"
#         elif (clay >= 7) and (clay <= 20) and (sand > 52) and ((silt + 2.0 * clay) >= 30):
#             return "Sandy loam"
#         elif (clay < 7) and (silt < 50) and ((silt + 2.0 * clay) >= 30):
#             return "Sandy loam"
#         elif (clay >= 7) and (clay <= 27) and (silt >= 28) and (silt < 50) and (sand <= 52):
#             return "Loam"
#         elif ((silt >= 50) and (clay >= 12) and (clay < 27)) or ((silt >= 50) and (silt < 80) and (clay < 12)):
#             return "Silt loam"
#         elif (silt >= 80) and (clay < 12):
#             return "Silt"
#         elif (clay >= 20) and (clay < 35) and (silt < 28) and (sand > 45):
#             return "Sandy clay loam"
#         elif (clay >= 27) and (clay < 40) and (sand > 20) and (sand <= 45):
#             return "Clay loam"
#         elif (clay >= 27) and (clay < 40) and (sand <= 20):
#             return "Silty clay loam"
#         elif (clay >= 35) and (sand >= 45):
#             return "Sandy clay"
#         elif (clay >= 40) and (silt >= 40):
#             return "Silty clay"
#         elif (clay >= 40) and (sand <= 45) and (silt < 40):
#             return "Clay"
#     def getSand(field):
#         if field is None:
#             return(np.nan)
#         else:
#             lfield = field.lower()
#             if lfield == "sand":
#                 return 92.0
#             elif lfield == "loamy sand":
#                 return 80.0
#             elif lfield == "sandy loam":
#                 return 61.5
#             elif lfield == "sandy clay loam":
#                 return 62.5
#             elif lfield == "loam":
#                 return 37.5
#             elif lfield == "silt":
#                 return 10.0
#             elif lfield == "silt loam":
#                 return 25.0
#             elif lfield == "silty clay loam":
#                 return 10.0
#             elif lfield == "clay loam":
#                 return 32.5
#             elif lfield == "sandy clay":
#                 return 55.0
#             elif lfield == "silty clay":
#                 return 10.0
#             elif lfield == "clay":
#                 return 22.5
# 
#     def getClay(field):
#         if field is None:
#             return(np.nan)
#         else:
#             lfield = field.lower()
#             if lfield == "sand":
#                 return 5.0
#             elif lfield == "loamy sand":
#                 return 7.5
#             elif lfield == "sandy loam":
#                 return 10.0
#             elif lfield == "sandy clay loam":
#                 return 27.5
#             elif lfield == "loam":
#                 return 17.0
#             elif lfield == "silt":
#                 return 6.0
#             elif lfield == "silt loam":
#                 return 13.5
#             elif lfield == "silty clay loam":
#                 return 33.5
#             elif lfield == "clay loam":
#                 return 33.5
#             elif lfield == "sandy clay":
#                 return 45.0
#             elif lfield == "silty clay":
#                 return 50.0
#             elif lfield == "clay":
#                 return 70.0
#     def getCF_fromClass(cf):
#         if cf == "0-1%":
#             return 0
#         elif cf == "0-15%":
#             return 0
#         elif cf == "1-15%":
#             return 8
#         elif cf == "15-35%":
#             return 25
#         elif cf == "35-60%":
#             return 48
#         elif cf == ">60%":
#             return 80
#         else:
#             return np.nan
            
    def getTXT_id(texture):
            lfield = texture.lower()
            if lfield == "sand":
                return 12
            elif lfield == "loamy sand":
                return 11
            elif lfield == "sandy loam":
                return 10
            elif lfield == "sandy clay loam":
                return 9
            elif lfield == "loam":
                return 8
            elif lfield == "silt":
                return 5
            elif lfield == "silt loam":
                return 6
            elif lfield == "silty clay loam":
                return 3
            elif lfield == "clay loam":
                return 4
            elif lfield == "sandy clay":
                return 7
            elif lfield == "silty clay":
                return 2
            elif lfield == "clay":
                return 1

    # if plot_data is not None:
    #     #------------------------------------------------------------------------------------------------
    #     #------ Load in user data --------#
    #     # cleanup the arrays
    #     soil_df = plot_data[['texture', 'bottom', 'rfv_class']]
    #     soil_df.columns = ["soilHorizon", "horizonDepth", "rfvDepth"]
    #     soil_df = soil_df.dropna(how='all')
    #     soil_df['bottom'] = soil_df.horizonDepth
    #     soil_df = soil_df.where((pd.notnull(soil_df)), None)
    #     top = []
    #     hzIdx = len(soil_df.horizonDepth) - 1
    #     top.append(0)
    #     for i in range(0, hzIdx + 1):
    #         if i < hzIdx:
    #             top.append(int(soil_df.horizonDepth[i]))
    #     soil_df['top'] = top
    #     soil_df = soil_df.set_index('horizonDepth')
    #     bedrock = plot_data['bedrock_depth'][0]
    #     if np.isnan(bedrock):
    #         bedrock = 120
    #     else:
    #         bedrock = bedrock
    # 
    #     #Drop rows where all horizon variables are missing
    #     soil_df_slice = soil_df.dropna(how='all', subset=['soilHorizon', 'rfvDepth'])
    #     if soil_df_slice.empty:
    #         soil_df_slice = None
    #     else:
    #         soil_df_slice['index'] = soil_df_slice.index
    #         soil_df_slice = soil_df_slice.reset_index(drop=True)
    #         soil_df_slice = soil_df_slice.set_index('index')
    # 
    #     if soil_df_slice is not None:
    #         #If bedrock has been recorded and the lowest soil depth associated with data is greater than bedrock, then change lowest soil depth to bedrock depth
    #         if bedrock is not None and soil_df_slice.bottom.iloc[-1] > bedrock:
    #             soil_df_slice.bottom.iloc[-1] = bedrock
    #             soil_df.bottom[soil_df_slice.index[-1]] = bedrock
    #             soil_df = soil_df.reset_index(drop=True)
    #             #This will create a depth gap that needs to be infilled with NaN or None
    #             #Infill missing horizons
    #             for j in range(len(soil_df)):
    #                 if j == len(soil_df) - 1:
    #                     break
    #                 if (soil_df.top[j + 1] > soil_df.bottom[j]):
    #                     layer_add = pd.DataFrame([None, None, None, soil_df.top[j + 1], soil_df.bottom[j]]).T
    #                     layer_add.columns = ['soilHorizon', 'rfvDepth', 'lab_Color', 'bottom', 'top']
    #                     soil_df = pd.concat([soil_df, layer_add], axis=0)
    #                     soil_df = soil_df.sort_values(['top'], ascending = True)
    #                     soil_df = soil_df.reset_index(drop=True)
    #             soil_df = soil_df.where((pd.notnull(soil_df)), None)
    # 
    #         #Create index list of soil slices where user data exists
    #         soil_df_slice = soil_df_slice.reset_index(drop=True)
    #         pedon_slice_index = []
    #         for i in range(len(soil_df_slice)):
    #             for j in range(int(soil_df_slice.top[i]), int(soil_df_slice.bottom[i])):
    #                 pedon_slice_index.append(j)
    #         pedon_slice_index = [x for x in pedon_slice_index if x < 120]
    # 
    #         #Soil properties to lists
    #         soilHorizon = soil_df.soilHorizon.tolist()
    #         rfvDepth = soil_df.rfvDepth.tolist()
    #         horizonDepthB = soil_df.bottom.tolist()
    #         horizonDepthT = soil_df.top.tolist()
    #         horizonDepthB = [int(x) for x in horizonDepthB]
    #         horizonDepthT = [int(x) for x in horizonDepthT]
    # 
    #         #Format and generate user data
    #         #Generate user specified percent clay, sand, and rfv distributions
    #         spt = []
    #         cpt = []
    #         p_cfg = []
    #         p_sandpct_intpl =[]
    #         p_claypct_intpl = []
    #         p_cfg_intpl =[]
    # 
    #         for i in range(len(soilHorizon)):
    #             spt.append(getSand(soilHorizon[i]))
    #             cpt.append(getClay(soilHorizon[i]))
    #             p_cfg.append(getCF_fromClass(rfvDepth[i]))
    # 
    #         for i in range(len(soilHorizon)):
    #             for j in range(horizonDepthT[i], horizonDepthB[i]):
    #                 p_sandpct_intpl.append(spt[i])
    #                 p_claypct_intpl.append(cpt[i])
    #                 p_cfg_intpl.append(p_cfg[i])
    # 
    #         #Length of interpolated texture and RF depth
    #         p_bottom_depth = pd.DataFrame([-999, "sample_pedon", soil_df_slice.bottom.iloc[-1]]).T
    #         p_bottom_depth.columns = ["cokey", "compname", "bottom_depth"]
    #         p_sandpct_intpl = pd.Series(p_sandpct_intpl)
    #         p_claypct_intpl = pd.Series(p_claypct_intpl)
    #         p_cfg_intpl = pd.Series(p_cfg_intpl)
    # 
    #         #Adjust depth interval of user data
    #         if len(p_sandpct_intpl) > 120:
    #             p_sandpct_intpl = p_sandpct_intpl[0:120]
    #             p_sandpct_intpl = p_sandpct_intpl.reset_index(drop=True)
    #         else:
    #             Na_add = 120 - len(p_sandpct_intpl)
    #             pd_add = pd.Series(np.nan, index = np.arange(Na_add))
    #             p_sandpct_intpl = pd.concat([p_sandpct_intpl, pd_add])
    #             p_sandpct_intpl = p_sandpct_intpl.reset_index(drop=True)
    # 
    #         if len(p_claypct_intpl) > 120:
    #             p_claypct_intpl = p_claypct_intpl[0:120]
    #             p_claypct_intpl = p_claypct_intpl.reset_index(drop=True)
    #         else:
    #             Na_add = 120 - len(p_claypct_intpl)
    #             pd_add = pd.Series(np.nan, index = np.arange(Na_add))
    #             p_claypct_intpl = pd.concat([p_claypct_intpl, pd_add])
    #             p_claypct_intpl = p_claypct_intpl.reset_index(drop=True)
    # 
    #         if len(p_cfg_intpl) > 120:
    #             p_cfg_intpl = p_cfg_intpl[0:120]
    #             p_cfg_intpl = p_cfg_intpl.reset_index(drop=True)
    #         elif (len(p_cfg_intpl) < 120) and (len(p_cfg_intpl) > 0):
    #             Na_add = 120 - len(p_cfg_intpl)
    #             pd_add = pd.Series(np.nan, index = np.arange(Na_add))
    #             p_cfg_intpl = pd.concat([p_cfg_intpl, pd_add])
    #             p_cfg_intpl = p_cfg_intpl.reset_index(drop=True)
    # 
    #         p_compname = pd.Series("sample_pedon", index = np.arange(len(p_sandpct_intpl)))
    #         p_hz_data = pd.concat([p_compname, p_sandpct_intpl, p_claypct_intpl, p_cfg_intpl], axis=1)
    #         p_hz_data.columns = ["compname", "sandpct_intpl", "claypct_intpl", "rfv_intpl"]
    # 
    #         #Drop empty data columns
    #         p_hz_data = p_hz_data.loc[:, ~p_hz_data.isnull().all()]
    #         #Drop empty depth slices
    #         p_hz_data = p_hz_data[p_hz_data.index.isin(pedon_slice_index)]
    #         #list of user entered variables to match against
    #         p_hz_data_names = p_hz_data.columns.tolist()
    #         p_bottom = p_bottom_depth["bottom_depth"].astype(int).iloc[0]
    #         snd_d, hz_depb = agg_data_layer_SQI(data=p_hz_data["sandpct_intpl"], bottom = p_bottom, depth=True)
    #         cly_d = agg_data_layer_SQI(data=p_hz_data["claypct_intpl"], bottom = p_bottom)
    #         txt_d = []
    # 
    #         for l in range(len(snd_d)):
    #             text_T = gettt(row=None, sand = snd_d[l],silt = (100-(snd_d[l]+cly_d[l])), clay = cly_d[l])
    #             txt_d.append(text_T.lower())
    #         txt_d = pd.Series(txt_d)
    #         txt_d.index = snd_d.index
    #         
    #         txt_id = []
    #         for l in range(len(txt_d)):
    #             txd_id_T = getTXT_id(txt_d[l])
    #             txt_id.append(txd_id_T)
    #         txt_id = pd.Series(txt_id)
    #         txt_id.index = snd_d.index
    # 
    #         rf_d = agg_data_layer_SQI(data=p_hz_data["rfv_intpl"], bottom = p_bottom)
    #         p_hz_data = pd.concat([hz_depb, txt_d, txt_id, rf_d], axis=1)
    #         p_hz_data.columns = ["BotDep", "text_class", "text_class_id", "CFRAG"]
    #         
    #         # This assumes that all depths start from the top and are consecutive
    #         depths = len(p_hz_data.index)
    #         data = data.iloc[0:depths, :]
    #         data = data.assign(text_class=p_hz_data['text_class'].values)
    #         data = data.assign(text_class_id=p_hz_data['text_class_id'].values)
    #         data = data.assign(CFRAG=p_hz_data['CFRAG'].values)
    #         data = data.assign(REF_DEPTH=bedrock)
    #     else:
    #         data = data
    text_class = data['texture'].values
    txt_id = []
    for l in range(len(text_class)):
        txd_id_T = getTXT_id(text_class[l])
        txt_id.append(txd_id_T)
    txt_id = pd.Series(txt_id)
    data = data.assign(text_class_id=txt_id)
    
    bedrock = data['bedrock_depth'][0]
    if np.isnan(bedrock):
        bedrock = 120
    else:
        bedrock = bedrock
    data = data.assign(REF_DEPTH=bedrock)
    depths = len(data.index)

  # S0 No constraint (100%)
  # S1 Slight constraint (90%)
  # S2 Moderate constraint (70%)
  # S3 Severe constraint (50%)
  # S4 Very severe constraint (30%)
  # N  Not suitable (<10%)
  
  # determine possible input_level codes
    if inputLevel == 'L':
        Input_Level_List = ['1','3', '4']
    elif inputLevel == 'I':
        Input_Level_List = ['2','3', '4']
    elif inputLevel == 'H':
        Input_Level_List = ['4','5']
    else:
        return 'Please enter `inputLevel`'
        
  # Standard GAEZ depth weights:
  # Depth  |  # of layers  | Weighting Factors
  # 120    |      6        | 2, 1.5 , 1, .75, .5, .25
  # 100    |      5        | 1.75, 1.5 , 1, .5, .25
  # 80     |      4        | 1.75, 1.25 , .75, .25
  # 60     |      3        | 1.5, 1, .5
  # 40     |      2        | 1.25, .75
  # 20     |      1        | 1

# depth weights adjusted to reflect LPKS depths. Assume max depth of 70 cm and depths 0-1,1-10,10-20,20-50,50-70, gives equal weight to 0-20 cm depths
    if depthWt_type == 1:
        if depths == 5:
            wts = [0.125, 1.125, 1.25, 1.66, 0.84]
        elif depths ==4:
            wts = [0.15, 1.10, 1.25, 1.5]
        elif depths ==3:
            wts = [.15, 1.35, 1.5]
        elif depths ==2:
            wts = [.02, 1.8]
        elif depths ==1:
            wts = [1]
        else:
            return 'Input data missing'
    elif depthWt_type == 2:   
        if depths == 5:
            wts = [0.2, 1.8, 2, 0.67, 0.33]
        elif depths ==4:
            wts = [0.16, 1.44, 1.6, 0.8]
        elif depths ==3:
            wts = [.15, 1.35, 1.5]
        elif depths ==2:
            wts = [.02, 1.8]
        elif depths ==1:
            wts = [1]
        else:
            return 'Input data missing'          
          
          
  # Load in crop and input specific property requirements
    #Texture requirements based on crop and input level
    texture_req = getGAEZ_texture_req(CROP_ID, Input_Level_List)
    #Property requirements based on crop and input level
    property_req = getGAEZ_profile_req(CROP_ID, Input_Level_List)
    #Phase requirements based on crop and input level
    phase_req = getGAEZ_phase_req(CROP_ID, Input_Level_List)    
    #Drainage requirements based on crop and input level
    drainage_req = getGAEZ_drainage_req(CROP_ID, Input_Level_List)    

  # SQI 1: Soil fertility
    if inputLevel == 'H':
        SQ1_score = 'NA'
    else:
        SQ1_scores = []
        for s in range(len(data.index)):
            layer = data.loc[s]
          
          #texture score
            text_class_id = str(layer.text_class_id)
            sq1_text_req = texture_req.query('SQI_code == 1 & text_class_id ==' + text_class_id).reset_index(drop=True)
            txt_score = sq1_text_req.score[0]
            SQ1_scores.append(txt_score)
        SQ1_score = np.mean([a * b for a, b in zip(SQ1_scores, wts)])

  # SQI 2  
    SQ2_scores = []

      #texture score: texture score is only included in the 'High Input' class.
    if inputLevel == 'H':
        for s in range(len(data.index)):
            layer = data.loc[s]
            text_class_id = str(layer.text_class_id)
            sq2_text_req = texture_req.query('SQI_code == 2 & text_class_id ==' + text_class_id).reset_index(drop=True)
            SQ2_scores.append(sq2_text_req.score[0])
        SQ2_score = np.mean([a * b for a, b in zip(SQ2_scores, wts)])
    else:
        SQ2_score = None
    
  # SQI 3  
    SQ3_scores = []
    
  #profile properties
    # soil depth
    sq3_rd_req = property_req.query('SQI_code == 3 & property == \'rd\'').sort_values(by='property_value', ascending=False).reset_index(drop=True)
    rd = data.REF_DEPTH[0]
    sq3_rd_score = None
    j = 0
    n = len(sq3_rd_req.property_value)-1
    while sq3_rd_score == None:
        if rd >= sq3_rd_req.property_value[j] or j == n:
            sq3_rd_score = sq3_rd_req.score[j]
        else:
            sq3_rd_score = None
            j = j + 1

  #soil layer properties        
    for s in range(len(data.index)):
        layer = data.loc[s]
     #texture score
        text_class_id = str(layer.text_class_id)
        sq3_text_req = texture_req.query('SQI_code == 3 & text_class_id ==' + text_class_id).reset_index(drop=True)
        sq3_txt_score = sq3_text_req.score[0]   

     #cf score
        sq3_cf_req = property_req.query('SQI_code == 3 & property == \'cf\'').sort_values(by='property_value', ascending=False).reset_index(drop=True)
        cf = layer.rfv
        sq3_cf_score = None
        t=0
        n = len(sq3_cf_req.property_value)-1
        while sq3_cf_score == None:
            if cf >= sq3_cf_req.property_value[t] or t == n:
                sq3_cf_score = sq3_cf_req.score[t]
            else:
                sq3_cf_score = None
                t = t + 1  
                
        sq3_scores_pd = pd.DataFrame(data={'txt': [sq3_txt_score], 'cf': [sq3_cf_score]}).T
        min = np.argmin(sq3_scores_pd)
        sq3_scores_lowProp = sq3_scores_pd.index[min]
        sq3_scores_lowVal = sq3_scores_pd.iloc[min, 0]
        SQ3_scores.append(sq3_rd_score*(sq3_scores_lowVal/100)) 
    SQ3_score = np.mean([a * b for a, b in zip(SQ3_scores, wts)])

  # SQI 7  
    SQ7_scores = []
  #profile properties
    # soil depth
    sq7_rd_req = property_req.query('SQI_code == 7 & property == \'rd\'').sort_values(by='property_value', ascending=False).reset_index(drop=True)
    rd = data.REF_DEPTH[0]
    sq7_rd_score = None
    j = 0
    n = len(sq7_rd_req.property_value)-1
    while sq7_rd_score == None:
        if rd >= sq7_rd_req.property_value[j] or j == n:
            sq7_rd_score = sq7_rd_req.score[j]
        else:
            sq7_rd_score = None
            j = j + 1
    
  #soil layer properties        
    for s in range(len(data.index)):
        layer = data.loc[s]
     #texture score
        text_class_id = str(layer.text_class_id)
        sq7_text_req = texture_req.query('SQI_code == 3 & text_class_id ==' + text_class_id).reset_index(drop=True)
        sq7_txt_score = sq7_text_req.score[0]   

    #cf score
        sq7_cf_req = property_req.query('SQI_code == 7 & property == \'cf\'').sort_values(by='property_value', ascending=False).reset_index(drop=True)
        cf = layer.rfv
        sq7_cf_score = None
        t=0
        n = len(sq7_cf_req.property_value)-1
        while sq7_cf_score == None:
            if cf >= sq7_cf_req.property_value[t] or t == n:
                sq7_cf_score = sq7_cf_req.score[t]
            else:
                sq7_cf_score = None
                t = t + 1  

        sq7_scores_pd = pd.DataFrame(data={'rd': [sq7_rd_score], 'txt': [sq7_txt_score], 'cf': [sq7_cf_score]}).T
        sq7_min = np.argmin(sq7_scores_pd)
        sq7_scores_lowVal = sq7_scores_pd.iloc[sq7_min, 0]
        sq7_scores_lowProp = sq7_scores_pd.index[sq7_min]
        sq7_scores_high_mean = sq7_scores_pd.loc[sq7_scores_pd.index != sq7_scores_lowProp, :].mean()
        SQ7_scores.append(np.mean([sq7_scores_lowVal,sq7_scores_high_mean]))
    SQ7_score = np.mean([a * b for a, b in zip(SQ7_scores, wts)])
    #Soil Rating

    #Low input farming:
    if inputLevel == 'L':
        SR = SQ1_score * (SQ3_score/100) * (SQ7_score/100)
    elif inputLevel == 'I':
        SR = SQ1_score * (SQ3_score/100) * (SQ7_score/100)
    elif inputLevel == 'H':
        SR = SQ2_score * (SQ3_score/100) * (SQ7_score/100)
    SQI_scores = pd.DataFrame(data={'SQ1': [SQ1_score],'SQ2': [SQ2_score],'SQ3': [SQ3_score], 'SQ7': [SQ7_score], 'SR': [SR], 'Input Level': inputLevel, 'id': data.id[0]})
    return(SQI_scores)    

