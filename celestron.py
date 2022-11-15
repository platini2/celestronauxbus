#!/usr/bin/env python

"""Celestron.py: Celestron AUXBUS Scanner"""
__author__ = "Patricio Latini"
__copyright__ = "Copyright 2021, Patricio Latini"
__credits__ = "Patricio Latini"
__license__ = "GPLv3"
__version__ = "0.9.30"
__maintainer__ = "Patricio Latini"
__email__ = "p_latini@hotmail.com"
__status__ = "Production"

import sys, getopt
import socket
import time
import threading
import binascii
import serial
import keyboard
import argparse
import os
from datetime import datetime,timezone
from PIL import Image, ImageDraw

global triggerscan
triggerscan = ' '
global endthread
endthread = False
global msgqueue
msgqueue = ''
global emulategps
emulategps = False
global mount
mount = ''
global verbose
verbose = False
global starsensesave
starsensesave = True
global filecsvoutput
filecsvoutput = False
global rawfileoutput
rawfileoutput = False
global oof
oof = 0

scannerid = 0x22
preamble = 0x3b
preamble2 = 0x3c

mounts = {
            0x01 : 'Nexstar GPS Legacy',
            0x0001 : 'Nexstar GPS',
            ### 0x05xx : 'CGE',
            ### 0x06xx : 'Advanced GT',
            0x0783 : 'Nexstar SLT',
            ### 0x09xx : 'CPC',
            ### 0x0axx : 'GT',
            0x0b83 : '4/5SE',
            0x0c82 : '6/8SE',
            ### 0x0dxx : 'CGE Pro',
            ### 0x0exx : 'CGEM DX',
            ### 0x0fxx : 'LCM',
            ### 0x10xx : 'Skyprodigy',                
            0x1189 : 'CPC Deluxe',
            0x1283 : 'GT Series',
            ### 0x13xx : 'Starseeker',    
            0x1485 : 'AVX',
            ### 0x15xx : 'Cosmos',              
            0x1687 : 'Nexstar Evolution',
            0x1788 : 'CGX'}
            ### 0x18xx : 'CGXL',
            ### 0x19xx : 'Astrofi',
            ### 0x1axx : 'SkyWatcher'}


devices = {
            0x01 : 'Main Board',
            0x04 : 'Nexstar HC',
            0x0d : 'Nexstar+ HC',
            0x0e : 'Starsense HC',
            0x10 : 'AZM MC',
            0x11 : 'ALT MC', 
            0x12 : 'Focuser',
            0x17 : 'Dew Heater Controller', 
            0x20 : 'CPWI',
            0x21 : 'CFM',
            0x22 : 'AUXBUS Scanner',
            0x30 : 'CGX RA Switch',
            0x31 : 'CGX DEC Switch',
            0x32 : 'CGX DEC Autoguide Pt',
            0xb0 : 'GPS',
            0xb2 : 'RTC',
            0xb3 : 'Skyportal Accessory',
            0xb4 : 'Starsense Camera',
            0xb5 : 'Nexstar EVO WiFi',
            0xb6 : 'Battery Power Cont',
            0xb7 : 'Charge Port',
            0xb8 : 'Starsense Camera SW',
            0xbb : 'Dew Heater Controller',
            0xbf : 'Mount Lights'}

controllers = [ 0x04 , 0x0d , 0x0e , 0x20, 0x21, 0x22 ]
activedevices = {}

commands = {  
            (0x01, 0xfe) : 'MB_GET_FW_VER', 
            (0x04, 0xfe) : 'NXS_GET_FW_VER',
            (0x0d, 0xfe) : 'NXS_GET_FW_VER',
            (0x0e, 0xfe) : 'NXS_GET_FW_VER',
            (0x10, 0x01) : 'MTR_GET_POSITION',		# Returns 16/24 bit BAM position
            (0x10, 0x02) : 'MTR_GOTO',			# Coarse, 16/24 bit BAM position
            (0x10, 0x04) : 'MTR_SET_POSITION',		# Resets to new 16/24 bit BAM position
            (0x10, 0x05) : 'MTR_GET_MODEL',		# Return the model number of the telescope
            (0x10, 0x06) : 'MTR_PTRACK',		# 16/24 bit speed [arcseconds/1024] + track rate
            (0x10, 0x07) : 'MTR_NTRACK',		# 16/24 bit speed [arcseconds/1024] - track rate
            (0x10, 0x08) : 'MTR_REMOTE_SWITCH_ALIVE',
            (0x10, 0x09) : 'MTR_SWITCH_STATE_CHANGE',
            (0x10, 0x0a) : 'MTR_AG_STATE_CHANGE 0x0A',
            (0x10, 0x0b) : 'MTR_MVSWITCH',		# ALT only, finds downstop switch
            (0x10, 0x0c) : 'MTR_PECTRAIN',		# AZM only, EQNorth/South must be on before sending this command
            (0x10, 0x0d) : 'MTR_PECPLAY',		# AZM only, EQNorth/South must be on before sending this command
            (0x10, 0x0e) : 'MTR_GET_PEC_BIN',		# Gets PEC bin
            (0x10, 0x10) : 'MTR_SET_POS_BACKLASH',	# Positive backlash, followed by 1 byte (0-99) 0=Off, 99=Max
            (0x10, 0x11) : 'MTR_SET_NEG_BACKLASH',	# Negative backlash, followed by 1 byte (0-99) 0=Off, 99=Max
            (0x10, 0x12) : 'MTR_IS_MVSWITCH_OVER',
            (0x10, 0x13) : 'MTR_IS_GOTO_OVER',
            (0x10, 0x14) : 'MTR_PEC_STATE_CHANGE',
            (0x10, 0x15) : 'MTR_IS_PECTRAIN_OVER',
            (0x10, 0x16) : 'MTR_CANCEL_PECTRAIN',
            (0x10, 0x17) : 'MTR_GOTO2',
            (0x10, 0x18) : 'MTR_IS_INDEX_FOUND',
            (0x10, 0x19) : 'MTR_FIND_INDEX',
            (0x10, 0x1a) : 'MTR_SET_USER_LIMIT_MIN',
            (0x10, 0x1b) : 'MTR_SET_USER_LIMIT_MAX',
            (0x10, 0x1c) : 'MTR_GET_USER_LIMIT_MIN',
            (0x10, 0x1d) : 'MTR_GET_USER_LIMIT_MAX',
            (0x10, 0x1e) : 'MTR_IS_USER_LIMIT_ENABLED',
            (0x10, 0x1f) : 'MTR_SET_USER_LIMIT_ENABLED',
            (0x10, 0x20) : 'MTR_SET_CUSTOM_RATE9',
            (0x10, 0x21) : 'MTR_GET_CUSTOM_RATE9',
            (0x10, 0x22) : 'MTR_SET_CUSTOM_RATE9_ENA',
            (0x10, 0x23) : 'MTR_GET_CUSTOM_RATE9_ENA',
            (0x10, 0x24) : 'MTR_PMSLEW_RATE',
            (0x10, 0x25) : 'MTR_NMSLEW_RATE',
            (0x10, 0x26) : 'MTR_AUX_GUIDE',
            (0x10, 0x27) : 'MTR_IS_AUX_GUIDE_ACTIVE',
            (0x10, 0x2a) : 'MTR_HS_CALIBRATION_ENABLE',
            (0x10, 0x2b) : 'MTR_IS_HS_CALIBRATED',
            (0x10, 0x2c) : 'MTR_GET_HS_POSITIONS',
            (0x10, 0x30) : 'MTR_EEPROM_READ',
            (0x10, 0x31) : 'MTR_EEPROM_WRITE',
            (0x10, 0x32) : 'MTR_PROGRAM_READ',
            (0x10, 0x38) : 'MTR_CORDWRAP_ON',
            (0x10, 0x39) : 'MTR_CORDWRAP_OFF',
            (0x10, 0x3a) : 'MTR_SET_CORDWRAP_POSITION',
            (0x10, 0x3b) : 'MTR_IS_CORDWRAP_ON',
            (0x10, 0x3c) : 'MTR_GET_CORDWRAP_POSITION',
            (0x10, 0x3d) : 'MTR_SET_SHUTTER',
            (0x10, 0x40) : 'MTR_GET_POS_BACKLASH',
            (0x10, 0x41) : 'MTR_GET_NEG_BACKLASH',
            (0x10, 0x46) : 'MTR_SET_AUTOGUIDE_RATE',
            (0x10, 0x47) : 'MTR_GET_AUTOGUIDE_RATE',
            (0x10, 0x48) : 'MTR_SET_SWITCH_CALIBRATION',
            (0x10, 0x49) : 'MTR_SET_SWITCH_CALIBRATION',
            (0x10, 0x4a) : 'MTR_SET_PRN_VALUE',
            (0x10, 0x4b) : 'MTR_GET_PRN_VALUE',
            (0x10, 0x50) : 'MTR_SEND_WARNING',
            (0x10, 0x51) : 'MTR_SEND_ERROR',
            (0x10, 0x5b) : 'MTR_SET_PID_KP',
            (0x10, 0x5c) : 'MTR_SET_PID_KI',
            (0x10, 0x5d) : 'MTR_SET_PID_KD',
            (0x10, 0x5f) : 'MTR_ENABLE_PID_ANALYSIS',
            (0x10, 0x8a) : 'MTR_PROGRAMMER_ENABLE',
            (0x10, 0xee) : 'MTR_GET_HARDSWITCH_ENABLE',
            (0x10, 0xef) : 'MTR_SET_HARDSWITCH_ENABLE',
            (0x10, 0xfa) : 'MTR_GET_CHIPVERSION',
            (0x10, 0xfb) : 'MTR_GET_BOOTVERSION',
            (0x10, 0xfc) : 'MTR_IS_APPROACH_DIR_NEG',
            (0x10, 0xfd) : 'MTR_SET_APPROACH_DIR_NEG',
            (0x10, 0xfe) : 'MTR_GET_VERSION',         
            (0x11, 0x01) : 'MTR_GET_POSITION', 
            (0x11, 0x02) : 'MTR_GOTO', 
            (0x11, 0x04) : 'MTR_SET_POSITION', 
            (0x11, 0x05) : 'MTR_GET_MODEL',
            (0x11, 0x06) : 'MTR_PTRACK',
            (0x11, 0x07) : 'MTR_NTRACK',
            (0x11, 0x08) : 'MTR_REMOTE_SWITCH_ALIVE',
            (0x11, 0x09) : 'MTR_SWITCH_STATE_CHANGE',
            (0x11, 0x0a) : 'MTR_AG_STATE_CHANGE 0x0A',
            (0x11, 0x0b) : 'MTR_MVSWITCH',
            (0x11, 0x0c) : 'MTR_PECTRAIN',
            (0x11, 0x0d) : 'MTR_PECPLAY',
            (0x11, 0x0e) : 'MTR_GET_PEC_BIN',
            (0x11, 0x10) : 'MTR_SET_POS_BACKLASH',
            (0x11, 0x11) : 'MTR_SET_NEG_BACKLASH',
            (0x11, 0x12) : 'MTR_IS_MVSWITCH_OVER',
            (0x11, 0x13) : 'MTR_IS_GOTO_OVER',
            (0x11, 0x14) : 'MTR_PEC_STATE_CHANGE',
            (0x11, 0x15) : 'MTR_IS_PECTRAIN_OVER',
            (0x11, 0x16) : 'MTR_CANCEL_PECTRAIN',
            (0x11, 0x17) : 'MTR_GOTO2',
            (0x11, 0x18) : 'MTR_IS_INDEX_FOUND',
            (0x11, 0x19) : 'MTR_FIND_INDEX',
            (0x11, 0x1a) : 'MTR_SET_USER_LIMIT_MIN',
            (0x11, 0x1b) : 'MTR_SET_USER_LIMIT_MAX',
            (0x11, 0x1c) : 'MTR_GET_USER_LIMIT_MIN',
            (0x11, 0x1d) : 'MTR_GET_USER_LIMIT_MAX',
            (0x11, 0x1e) : 'MTR_IS_USER_LIMIT_ENABLED',
            (0x11, 0x1f) : 'MTR_SET_USER_LIMIT_ENABLED',
            (0x11, 0x20) : 'MTR_SET_CUSTOM_RATE9',
            (0x11, 0x21) : 'MTR_GET_CUSTOM_RATE9',
            (0x11, 0x22) : 'MTR_SET_CUSTOM_RATE9_ENA',
            (0x11, 0x23) : 'MTR_GET_CUSTOM_RATE9_ENA',
            (0x11, 0x24) : 'MTR_PMSLEW_RATE',
            (0x11, 0x25) : 'MTR_NMSLEW_RATE',
            (0x11, 0x26) : 'MTR_AUX_GUIDE',
            (0x11, 0x27) : 'MTR_IS_AUX_GUIDE_ACTIVE',
            (0x11, 0x2a) : 'MTR_HS_CALIBRATION_ENABLE',
            (0x11, 0x2b) : 'MTR_IS_HS_CALIBRATED',
            (0x11, 0x2c) : 'MTR_GET_HS_POSITIONS',
            (0x11, 0x30) : 'MTR_EEPROM_READ',
            (0x11, 0x31) : 'MTR_EEPROM_WRITE',
            (0x11, 0x32) : 'MTR_PROGRAM_READ',
            (0x11, 0x38) : 'MTR_CORDWRAP_ON',
            (0x11, 0x39) : 'MTR_CORDWRAP_OFF',
            (0x11, 0x3a) : 'MTR_SET_CORDWRAP_POSITION',
            (0x11, 0x3b) : 'MTR_IS_CORDWRAP_ON',
            (0x11, 0x3c) : 'MTR_GET_CORDWRAP_POSITION',
            (0x11, 0x3d) : 'MTR_SET_SHUTTER',
            (0x11, 0x40) : 'MTR_GET_POS_BACKLASH',
            (0x11, 0x41) : 'MTR_GET_NEG_BACKLASH',
            (0x11, 0x46) : 'MTR_SET_AUTOGUIDE_RATE',
            (0x11, 0x47) : 'MTR_GET_AUTOGUIDE_RATE',
            (0x11, 0x48) : 'MTR_SET_SWITCH_CALIBRATION',
            (0x11, 0x49) : 'MTR_SET_SWITCH_CALIBRATION',
            (0x11, 0x4a) : 'MTR_SET_PRN_VALUE',
            (0x11, 0x4b) : 'MTR_GET_PRN_VALUE',
            (0x11, 0x50) : 'MTR_SEND_WARNING',
            (0x11, 0x51) : 'MTR_SEND_ERROR',
            (0x11, 0x5b) : 'MTR_SET_PID_KP',
            (0x11, 0x5c) : 'MTR_SET_PID_KI',
            (0x11, 0x5d) : 'MTR_SET_PID_KD',
            (0x11, 0x5f) : 'MTR_ENABLE_PID_ANALYSIS',
            (0x11, 0x8a) : 'MTR_PROGRAMMER_ENABLE',
            (0x11, 0xee) : 'MTR_GET_HARDSWITCH_ENABLE',
            (0x11, 0xef) : 'MTR_SET_HARDSWITCH_ENABLE',
            (0x11, 0xfa) : 'MTR_GET_CHIPVERSION',
            (0x11, 0xfb) : 'MTR_GET_BOOTVERSION',
            (0x11, 0xfc) : 'MTR_IS_APPROACH_DIR_NEG',
            (0x11, 0xfd) : 'MTR_SET_APPROACH_DIR_NEG',
            (0x11, 0xfe) : 'MTR_GET_VERSION',
            (0x12, 0x01) : 'FOCUS_GET_POSITION',   
            (0x12, 0x02) : 'FOCUS_GOTO_FAST', 
            (0x12, 0x13) : 'FOCUS_SLEW_DONE',
            (0x12, 0x24) : 'FOCUS_MOVE_POS',
            (0x12, 0x25) : 'FOCUS_MOVE_NEG',
            (0x12, 0x2c) : 'FOCUS_XXX',
            (0x12, 0x3b) : 'FOCUS_XXX',
            (0x12, 0xfe) : 'FUCUS_GET_FW_VER',
            (0x17, 0x00) : 'DEWHEATER_GET_CURRENT_POWER',
            (0x17, 0x04) : 'DEWHEATER_GET_LIMIT_POWER',
            (0x17, 0x10) : 'DEWHEATER_GET_POWER_PORTS',
            (0x17, 0x11) : 'DEWHEATER_GET_PORTS',
            (0x17, 0x12) : 'DEWHEATER_GET_STATUS',
            (0x17, 0x18) : 'DEWHEATER_GET_AMBIENT', 
            (0x20, 0xfe) : 'NXS_GET_FW_VER',
            (0xb0, 0x01) : 'GPS_GET_LAT',    
            (0xb0, 0x02) : 'GPS_GET_LONG',
            (0xb0, 0x03) : 'GPS_GET_DATE',
            (0xb0, 0x04) : 'GPS_GET_YEAR',
            (0xb0, 0x07) : 'GPS_GET_SAT_INFO',
            (0xb0, 0x08) : 'GPS_GET_RCVR_STATUS',
            (0xb0, 0x33) : 'GPS_GET_TIME',
            (0xb0, 0x36) : 'GPS_TIME_VALID',
            (0xb0, 0x37) : 'GPS_LINKED',
            (0xb0, 0xa0) : 'GPS_GET_COMPASS',
            (0xb0, 0xfe) : 'GPS_GET_FW_VER',
            (0xb3, 0xfe) : 'WIFI_GET_FW_VER',
            (0xb4, 0x3e) : 'SS_SET_ALIGN_CENTER',
            (0xb4, 0x3f) : 'SS_GET_ALIGN_CENTER',
            (0xb4, 0x90) : 'SS_RESET_CAPTURE',
            (0xb4, 0x91) : 'SS_GET_STATUS',
            (0xb4, 0x92) : 'SS_GET_CAPTURE_DATA',
            (0xb4, 0x94) : 'SS_START_CAPTURE',
            (0xb4, 0x9f) : 'SS_GET_IMAGE3',
            (0xb4, 0xfe) : 'SS_GET_FW_VER',
            (0xb5, 0xfe) : 'WIFI_GET_FW_VER',
            (0xb6, 0x10) : 'BAT_GET_VOLTAGE',
            (0xb6, 0x18) : 'BAT_GET_CURRENT',
            (0xb6, 0xfe) : 'BAT_GET_FW_VER',
            (0xb7, 0x10) : 'CHG_GET_MODE',
            (0xb7, 0xfe) : 'CHG_GET_FW_VER',
            (0xbb, 0xfe) : 'DEWHEATER_GET_FW_VER',
            (0xbf, 0x10) : 'LIGHT_GET_LEVEL',
            (0xbf, 0xfe) : 'LIGHT_GET_FW_VER'}

SERVER_IP = '1.2.3.4'
SERVER_PORT = 2000
BUFFER_SIZE = 100
KEEP_ALIVE_INTERVAL = 10

def twos_comp(val, bits):
    """compute the 2's complement of int value val"""
    if (val & (1 << (bits - 1))) != 0: 
        val = val - (1 << bits)        
    return val

def tosigned24(hexnum):
    n = int(hexnum,16)
    n = n & 0xffffff
    return n | (-(n & 0x800000))

def hextoposition(hexnum):
    position = tosigned24(hexnum)/pow(2,24)*360
    return position

def decdeg2dms(dd):
    d = int(dd)
    m = int((abs(dd) - abs(d)) * 60)
    s = round((abs(dd) - abs(d) - m/60) * 3600.00,2)
    return d,m,s

def xprint(*args):
    print(" ".join(map(str,args)))

def decodecommandvalue(sender,device,command,commandvalue):
    if hex(command) == '0xfe':
        if len(commandvalue)<4:
            commandvalue = '.'.join([format(int(c, 16)) for c in commandvalue])
        else:
            commandvalue = format(int(commandvalue[0], 16)) + '.' + format(int(commandvalue[1], 16))+ '.' + str(int(format(int(commandvalue[2],16), '02x')+format(int(commandvalue[3],16), '02x'),16))
    elif hex(device) == '0x10' or hex(device) == '0x11':
        if hex(command) == '0x1' or hex(command) == '0x2' or hex(command) == '0x3a' or hex(command) == '0x3c':
            commandvaluehex = ''.join([format(int(c, 16), '02x') for c in commandvalue])   
            latitude=twos_comp(int(commandvaluehex,16),24)
            latitude=latitude*360/pow(2,24)
            d,m,s = decdeg2dms(latitude)
            commandvalue = format(d) + '°' + format(m) + '\'' + format(s) + '"'
        elif hex(command) == '0x17' or hex(command) == '0x6' or hex(command) == '0x7':
            if sender == device:
                if hex(int(commandvalue[0],16)) == '0x1': commandvalue = '1 - ACK'
            else:
                commandvaluehex = ''.join([format(int(c, 16), '02x') for c in commandvalue])   
                latitude=twos_comp(int(commandvaluehex,16),24)
                latitude=latitude*360/pow(2,24)
                d,m,s = decdeg2dms(latitude)
                commandvalue = format(d) + '°' + format(m) + '\'' + format(s) + '"'
        elif hex(command) == '0x5':
            commandvalue = format(''.join([format(int(c, 16), '02x') for c in commandvalue]))
        elif hex(command) == '0x12':
            if hex(int(commandvalue[0],16)) == '0x0': commandvalue = '0 - False'
            elif hex(int(commandvalue[0],16)) == '0x1': commandvalue = '1 - True'
        elif hex(command) == '0x13':
            if hex(int(commandvalue[0],16)) == '0x0': commandvalue = '0 - Not Done'
            elif hex(int(commandvalue[0],16)) == '0x1': commandvalue = '1 - Check'
            elif hex(int(commandvalue[0],16)) == '0xff': commandvalue = '255 - Done'
        elif hex(command) == '0x23':
            if hex(int(commandvalue[0],16)) == '0x0': commandvalue = '0 - Disabled'
            elif hex(int(commandvalue[0],16)) == '0x1': commandvalue = '1 - Enabled'
        elif hex(command) == '0x24' or hex(command) == '0x25' or hex(command) == '0x40' or hex(command) == '0x41':
            commandvalue = format(int(commandvalue[0],16))
        elif hex(command) == '0x3b':
            if hex(int(commandvalue[0],16)) == '0x0': commandvalue = '0 - Disabled'
            elif hex(int(commandvalue[0],16)) == '0xff': commandvalue = '255 - Enabled'
        elif hex(command) == '0x46' or hex(command) == '0x47':
            commandvalue = format(100*int(commandvalue[0],16)/256)
        elif hex(command) == '0xfc' or hex(command) == '0xfd':
            if hex(int(commandvalue[0],16)) == '0x0': commandvalue = '0 - Positive'
            elif hex(int(commandvalue[0],16)) == '0x1': commandvalue = '1 - Negative'
    elif hex(device) == '0xb0':
        if hex(command) == '0x1' or hex(command) == '0x2':
            commandvaluehex = ''.join([format(int(c, 16), '02x') for c in commandvalue])   
            latitude=twos_comp(int(commandvaluehex,16),24)
            latitude=latitude*360/pow(2,24)
            d,m,s = decdeg2dms(latitude)
            commandvalue = format(d) + '°' + format(m) + '\'' + format(s) + '"'
        elif hex(command) == '0x3':
            commandvalue = format(int(commandvalue[0], 16)) + '/' + format(int(commandvalue[1], 16))
        elif hex(command) == '0x4':
            commandvalue = format(int(''.join([format(int(c, 16), '02x') for c in commandvalue]), 16))
        elif hex(command) == '0x7':
            commandvalue = format(int(commandvalue[0], 16)) + ' - ' + format(int(commandvalue[1], 16))
        elif hex(command) == '0x33':
            commandvalue = format(int(commandvalue[0], 16)) + ':' + format(int(commandvalue[1], 16))+ ':' + format(int(commandvalue[2], 16))
        elif hex(command) == '0x36' or hex(command) == '0x37':
            if hex(int(commandvalue[0],16)) == '0x0': commandvalue = '0 - No'
            elif hex(int(commandvalue[0],16)) == '0x1': commandvalue = '1 - Yes'
    elif hex(device) == '0xb4':
        if hex(command) == '0x3f':
            if len(commandvalue)== 8:
                centerx = ''.join([format(int(c, 16), '02x') for c in reversed(commandvalue[0:4])])
                centery = ''.join([format(int(c, 16), '02x') for c in reversed(commandvalue[4:8])])
                commandvalue = format(int(centerx, 16)) + ' - ' + format(int(centery, 16))
            else:
                commandvalue = format(int(commandvalue[0],16))
        if hex(command) == '0x91' or hex(command) == '0x92' or hex(command) == '0x94' or hex(command) == '0x9f':
            if hex(int(commandvalue[0],16)) == '0x1': commandvalue = '1 (Error)' + ' - Stars: ' + format(int(commandvalue[1], 16))
            elif hex(int(commandvalue[0],16)) == '0x3': commandvalue = '3 (Ready)' + ' - Stars: ' + format(int(commandvalue[1], 16))
            elif hex(int(commandvalue[0],16)) == '0x9': commandvalue = '9 (Finished)' + ' - Stars: ' + format(int(commandvalue[1], 16))
    elif hex(device) == '0x17':
        if hex(command) == '0x0':
            commandvalue = format(int(''.join([format(int(c, 16), '02x') for c in commandvalue[0:2]]), 16)/1000) + ' V - ' + format(int(''.join([format(int(c, 16), '02x') for c in commandvalue[2:4]]), 16)/1000) + ' A '
        if hex(command) == '0x4':
            commandvalue = format(int(''.join([format(int(c, 16), '02x') for c in commandvalue[0:2]]), 16)/1000) + ' A - ' + format(int(''.join([format(int(c, 16), '02x') for c in commandvalue[2:4]]), 16)/1000) + ' A '
        if hex(command) == '0x10':
            commandvalue = format(int(commandvalue[0], 16))
        elif hex(command) == '0x11':
            if hex(sender) != '0x17':
                if hex(int(commandvalue[0],16)) == '0x0': commandvalue = '0 - Get 12V Ports'
                elif hex(int(commandvalue[0],16)) == '0x1': commandvalue = '1 - Get Dew Heater Ports'
            else:                
               commandvalue = format(int(commandvalue[0], 16))
        elif hex(command) == '0x12':
            if hex(sender) != '0x17':
                if hex(int(commandvalue[0],16)) == '0x0': commandvalue = '0 - Port 1'
                elif hex(int(commandvalue[0],16)) == '0x1': commandvalue = '1 - Port 2'
            else:
                if hex(int(commandvalue[1],16)) == '0x0': mode = 'Manual'
                elif hex(int(commandvalue[1],16)) == '0x1': mode = 'Auto'
                if hex(int(commandvalue[2],16)) == '0x0':
                    commandvalue = 'Port ' + format(int(commandvalue[0], 16)) + ' - ' + mode + ' - Power: Off ' + format(int(commandvalue[2], 16)) + ' - Agression ' + format(int(commandvalue[5], 16))
                else:
                    commandvaluehex = ''.join([format(int(c, 16), '02x') for c in commandvalue[6:10]])
                    temp=int(commandvaluehex,16)/1000
                    commandvalue = 'Port ' + format(int(commandvalue[0], 16)) + ' - ' + mode + ' - Power: On ' + format(int(commandvalue[2], 16)) + ' - Agression ' + format(int(commandvalue[5], 16)) + ' - Temp ' + format(temp)
        elif hex(command) == '0x18':
            commandvaluehex = ''.join([format(int(c, 16), '02x') for c in commandvalue[0:4]])   
            temp=int(commandvaluehex,16)/1000
            commandvaluehex = ''.join([format(int(c, 16), '02x') for c in commandvalue[4:8]])   
            dew=int(commandvaluehex,16)/1000
            commandvalue= 'Temp: ' + format(temp) + '°C Dew: ' + format(dew) + '°C Hum: ' + format(int(commandvalue[8], 16)) + '%'

    else:
        commandvaluehex = ''.join([format(int(c, 16), '02x') for c in commandvalue])         
        commandvalue = commandvaluehex
    return commandvalue

def decodemsg(msg):
    global mount
    byte=0
    sum=0
    checksumok = 0
    commandvalue = []
    for c in range(0,len(msg),2):
      byte = int(c/2+1)
      value = int(msg[c:c+2],16)
      if (byte>1 and byte <len(msg)/2):
        sum=sum+value
      if (byte == 2):
        length = value
      if (byte == 3):
        sender = value
      if (byte == 4):
        receiver = value   
      if (byte == 5):
        command = value   
      if (byte > 5 and byte < 3+length):
        commandvalue.append(hex(value))
      if (byte == len(msg)/2):
        checksum = value
        sum=65536-sum
        sum=sum&255
        if checksum == sum:
          checksumok = 1
    if checksumok:
      if (sender == scannerid or receiver == scannerid):
        if sender == scannerid:
          device = receiver
        else:
          device = sender
      else:
        if sender not in controllers:
          device = sender
        else:
          device = receiver
      if len(commandvalue)>0:
        if hex(command) == '0xfe':
          commandvalue = decodecommandvalue(sender,device,command,commandvalue)
          if len(commandvalue)>0:
            activedevices.update({hex(sender):commandvalue}) if hex(sender) not in activedevices else activedevices
        else:
          commandvalue = decodecommandvalue(sender,device,command,commandvalue)
          if hex(command) == '0x5' and hex(sender) == '0x10':
            mount = int(commandvalue,16)
      if (device,command) in commands:
          commandtext = commands[(device,command)]
      else:
          commandtext = 'UNKNOWN'
      if sender in devices:
          sendertext = devices[sender]
      else: 
          sendertext = 'UNKNOWN'
      if receiver in devices:
          receivertext = devices[receiver]
      else: 
          receivertext = 'UNKNOWN'
      if verbose:
          dumptext = ' --- ' + str(msg)
      else:
          dumptext = ''
      output = str(format(round(time.time()-starttime,6),'14.6f')) + " - " + "{:<21}".format(sendertext) + " (0x" + str(format(sender,'02x')) + ") " + "-> " + "{:<21}".format(receivertext) + " (0x" + str(format(receiver,'02x')) + ") " + "--- " + "{:<21}".format(commandtext) + " (0x" + str(format(command,'02x')) + ") " + "--- " + str(commandvalue) + dumptext
      xprint (output)
      if filecsvoutput:
          fileoutput = str(format(round(time.time()-starttime,6),'14.6f')) + "," + sendertext + "," + str(hex(sender)) + ","  + receivertext + "," + str(hex(receiver)) + ","  + commandtext + "," + str(hex(command)) + "," + str(commandvalue) + "," + str(msg)
          print(fileoutput,  file=open('auxbuslog.csv', 'a'))
      if emulategps:
        global gpslat,gpslon    
        if str(hex(receiver)) == '0xb0':
          if str(hex(command)) == '0x36':
            transmitmsg('3b',receiver,sender,command,'01')
          if str(hex(command)) == '0xfe':
            transmitmsg('3b',receiver,sender,command,'0b01')
          if str(hex(command)) == '0x33':
            transmitmsg('3b',receiver,sender,command,format(datetime.now(timezone.utc).hour, '02x')+format(datetime.now(timezone.utc).minute, '02x')+format(datetime.now(timezone.utc).second, '02x'))
          if str(hex(command)) == '0x3':
            transmitmsg('3b',receiver,sender,command,format(datetime.now(timezone.utc).month, '02x')+format(datetime.now(timezone.utc).day, '02x'))
          if str(hex(command)) == '0x4':
            transmitmsg('3b',receiver,sender,command,format(datetime.now(timezone.utc).year, '04x'))
          if str(hex(command)) == '0x37':
            transmitmsg('3b',receiver,sender,command,'01')
          if str(hex(command)) == '0x2':
            if gpslon>=0:
                gpslonhex=format(int(gpslon/360*pow(2,24)),'06x')
            else: 
                gpslonhex=format(int((gpslon+360)/360*pow(2,24)),'06x')
            transmitmsg('3b',receiver,sender,command,gpslonhex)
          if str(hex(command)) == '0x1':
            if gpslat>=0:
                gpslathex=format(int(gpslat/360*pow(2,24)),'06x')
            else: 
                gpslathex=format(int((gpslat+360)/360*pow(2,24)),'06x')
            transmitmsg('3b',receiver,sender,command,gpslathex)
    else:
      output = str(hex(sender)+ " -> " + hex(receiver) + " --- " + hex(command) + " --- " + ' '.join(map(str, commandvalue)) + " CRC FAIL!")
      xprint (output)

def decodestarsensestar(msg):
    ssxfov=5.16
    ssyfov=5.16
    msg="".join(reversed([msg[i:i+2] for i in range(0, len(msg), 2)]))
    bx,px,by,py=int(msg[0:2],16)-64,int(msg[2:8],16),int(msg[8:10],16)-64,int(msg[10:16],16)
    dx,mx,sx = decdeg2dms(twos_comp(int(msg[2:8],16),24)*ssxfov/pow(2,24))
    dy,my,sy = decdeg2dms(twos_comp(int(msg[10:16],16),24)*ssyfov/pow(2,24))
    px = format(dx) + '°' + format(mx) + '\'' + format(sx) + '"'
    py = format(dy) + '°' + format(my) + '\'' + format(sy) + '"'
    msg=str(bx) + " - " + "{:<11}".format(px) + " - " + str(by) + " - " + "{:<11}".format(py)
    return msg

def starsensepixel(msg,ssxres,ssyres):
    msg="".join(reversed([msg[i:i+2] for i in range(0, len(msg), 2)]))
    bx,px,by,py=int(msg[0:2],16)-64,int(msg[2:8],16),int(msg[8:10],16)-64,int(msg[10:16],16)
    pixelx = int(ssxres/2+(twos_comp(int(msg[2:8],16),24)*ssxres/pow(2,24)))
    pixely = int(ssyres/2-(twos_comp(int(msg[10:16],16),24)*ssyres/pow(2,24)))
    return pixelx,pixely,bx,by

def decodemsg3c(msg):
    global starsensesave
    starlen=2*8
    pixellist = []
    ssxres=960
    ssyres=960
    byte=0
    sum=0
    checksumok = 0
    commandvalue = []
    for c in range(2,len(msg),2):
      byte = int(c/2+1)
      value = int(msg[c:c+2],16)
      if (byte>1 and byte <len(msg)/2):
        sum=sum+value
      if (byte == 4):
        lengthH = value
      if (byte == 5):
        lengthL = value
        length = lengthH*256+lengthL 
      if (byte == len(msg)/2):
        checksum = value
        sum=65536-sum
        sum=sum&255
        if checksum == sum:
          checksumok = 1
    if checksumok:
        if verbose:
          dumptext = ' --- ' + str(msg)
        else:
          dumptext = ''
        output = str(format(round(time.time()-starttime,6),'14.6f')) + " - " + "Starsense HC Data - " + str(int(length)/8) + " Stars " + msg[5*2:-2] + dumptext
        xprint (output)       
        data=msg[5*2:-2]
        stars=[data[i:i+starlen] for i in range(0, len(data), starlen)]
        for star in stars:
            if star!="0000000000000000":
                xprint("                 Star",stars.index(star)+1," - ",decodestarsensestar(star))
                pixellist.append(starsensepixel(star,ssxres,ssyres))
        if starsensesave:
            img = Image.new('L', (ssxres, ssyres))
            for pixel in pixellist:
                shape = [pixel[0],pixel[1],pixel[0]+pixel[2]-1,pixel[1]+pixel[3]]
                img1 = ImageDraw.Draw(img)
                img1.rectangle(shape, fill ="white", outline ="white")
            imgfilename = 'starsense-image-' + datetime.now().strftime("%Y%m%d-%H%M%S") + '.png'
            img.save(imgfilename)
        if filecsvoutput:
            fileoutput = str(format(round(time.time()-starttime,6),'14.6f')) + "," + "Starsense Camera" + "," + "0xb4" + ","  + "All" + "," + "0x00" + ","  + "Data" + "," + "0x00" + "," + "[]" + "," + str(msg)
            print(fileoutput,  file=open('auxbuslog.csv', 'a'))
    else:
        xprint ("Starsense HC Data - CRC FAIL!")

def processmsgqueue():
  global msgqueue
  global oof
  if len(msgqueue)>1:
    while len(msgqueue)>1 and msgqueue[0:2] != str(hex(preamble))[2:] and msgqueue[0:2] != str(hex(preamble2))[2:]:
      #oofd = oofd + msgqueue[0:2]
      oof = oof+1
      msgqueue=msgqueue[2:]
  emptyqueue=0
  while len(msgqueue)>=(2*6) and (msgqueue[0:2] == str(hex(preamble))[2:] or msgqueue[0:2] == str(hex(preamble2))[2:]) and emptyqueue==0:
    if msgqueue[0:2] == str(hex(preamble))[2:]:
        length = int(msgqueue[2:4],16)
        if len(msgqueue)>=(2*(length+3)):
          decodemsg(msgqueue[0:2*(length+3)])
          msgqueue=msgqueue[2*(length+3):]
        else:
          emptyqueue=1
    if msgqueue[0:2] == str(hex(preamble2))[2:]:
        msgqueue = msgqueue.replace('3b0202','3b')
        length = int(msgqueue[6:10],16)
        if len(msgqueue)>=(2*(length+6)):
          decodemsg3c(msgqueue[0:2*(length+6)])
          msgqueue=msgqueue[2*(length+6):]
        else:
          emptyqueue=1
        
def encodemsg(sender,receiver,command,value):
  global preamble
  global msgqueue
  global connmode
  commandvalue=[]
  byte=0
  if sender=='':
    if connmode=='wifi' or connmode=='hc' :
        sender = scannerid
    if connmode=='serial':
        sender = scannerid      
  for c in range(0,len(value),2):
      byte = int(c/2+1)
      value2 = int(value[c:c+2],16)
      commandvalue.append(hex(value2))
  length = 3 + int(len(value)/2)
  valuesum = sum(int(i,16) for i in commandvalue)
  summa = length + sender + receiver + command + valuesum
  summa=65536-summa
  summa=summa&255
  output1 = "{:02x}{:02x}{:02x}{:02x}{:02x}".format(preamble,length,sender,receiver,command)
  output2 = value
  output3 = "{:02x}".format(summa)
  output = output1 + output2 + output3
  if (connmode == "hc" or connmode == "wifi") and not emulategps :
    msgqueue = msgqueue + output
    processmsgqueue()
#  decodemsg(output)
  hexoutput = binascii.unhexlify(output)
  return hexoutput

def encodemsg3c():
  global preamble2
  global msgqueue
#  data = "8c832644e88592436d0a6244b57d5b449d941a434e5626426638ad43402d054438af88443780214454c0274447334f446e1f8b44742330443f52b3438287864333dbed43114a1c444e3143444622f143eac52f441ae35844ecc527449db62744dd9a5a44413624448af01144fab93843bba9ea4366991244ded72844f5a11244a219f143c84437446df098424538944398386e44deb27e430b8e8a44448a1a445f973e44dd0f0a4475784844a7f43c44ee4b4e4441f7334430ae814428670c44140aa5434d3e29448ebdb442af5a5043b8084742ce225543af866044542bda437dd300447a1d53440cb492442466fd43fc84f14350206344f1286b44735a6344c58a48444d2303443c719244b902ef43c553304496648443e98a0d436aebc64382cf094497401d44c97d984419f01944e7b33f44b9ac1944f9e68b4326a43b43aadb1344e49f3044a4577b440d719c43cc797644bc180f44e8bd1d441dd80b447c977944673a4844fea5534311c8b5431df19044b105ed43b9a769444225f343d29b1c44836b03444bc5184487604a44d493c243a7cd5c44bf43624428e81c44c74f40447c0f9c43b28b12440b7ec043f1f7a5432addf9432fce7943e46a1a447feb69445451d9436fea8044d31fa043e69b7a43e9f410446df48d440e49ce4317edff43e83629448d60cc436c5bfa43b83c754433f120434442aa430543e0432b6a3444c1c04243fb0a1144afde404308395a43c96530443f8529449ebf7d434a787344df662b44b35add432f6e434457d5674434d854448f49014468a5d543ff472b448c528e4355c1e143eff24a448eb33c4457391044a38b0e44840caa4365a85a442f887d433ffc06448a27be43389419442b8801441cbd45445edde6435ef62743c0e7ef43d5ea5444d0d0fb4203727943fb38224452ab34447b39b543c5188a4446995c44a941e5428240ed43638663442672bc4322083c44609e63442453f143383156445539574465dcd14356704a43161302442baf2344c5ab3f441be97d4394ed7642f54a6e4439b60343b71f7e44ebc21343f2f2fe433e8ee9428da37944090d4a4471335244aa774c438b6f8e43c5ca80430000000000000000"
  data = "01922744b63b96436e90cb4307c13c44136e8a4305c58943ef2721448c572f4442988b44b392904319110944a3b563445f38424412e29543726fbd430666d5426032354403490343ea882b44b2ce30444b68c043a1352a44fcad11442194e443f6e040441bd6fa43b36f8f4492ecdc416698ac438ab3dc43d4010b42e8fe1a44abc09c43ee6cd1433c981644019a4944c316a843a0e70943c58493425ea70844534ba64306071442f804c24390011244d4fd5744d0ab0b427679cd431286c4437beaba4348d7c14356d93a4488a17543a7b20144400e1e442f4024446a430e441e99b442693820447fe55c4480865644ecc00744524de44395599a44317aaf4390b9454413bd454496239444b84a51448bfe9a44b6e8c2434c41d94298546444200d19444af003442b8a3e4431469c4321b4d6439bbb1744003721445c2d6244d1798844967fd7439904ca422ecd2b448944d5436df46044ef158b4380c46244f25e4b4462c2dc43c7d84344b78f1e442b8ba4437e49f2435a7a664472ff0b4342834544b53b85435d1fca4302475042cfb56b445916604370345a4406825944a8cb9a44bd83f8439c2447446ebc1344363b7444a253e243f08951433ec184430e44114341ab82430b7378441160de42ec5d5e44163c5643367a7e448da2a443c62e8944c82b3c44e7b33543a8bd3d44fe1d3a440fc6a2434e6a39448ebded436a6c4544aaf9634486d41844302b2144a30e4044abb14c44d31d2644850ef7413026fd434d08b0438d6203445e2cf343b15c994425432844fb011644cae9df4288b5f143c77c2c442b7fd343bc4e0044d28e5c44433c3344d12cb843d4119143ee06ec43f053df429870b443d8edec437ad47242f2b51b444d306543ae4ac843debb5444d3434943d3596e44eb751b443a200b44435d3a432721364430f2ad4207d0854359bad14350e8a8431c2a3544d6fb88449261604410cc7d440a57b743583c7d44b315c74340155c44c8da5c44a86b5f441db19c4353e88d445b4f2044b0a0e0437e85fc43c7028d43172e5c44a0a84f448c9baf43b7976f44b5d75f440e0f654447c22444d923024427bc5644717edf43a3ce24440000000000000000"
#  data = "908086434f114844b3707144fb581c44b3e02a4472103644c014fe43b3b4c443372e934458245044232e5143fed1f04377709b445b440e4419355944d59ebb4274dbf6415fb65a443eff2e439b9d5d44a8a57244433f384458fb3944f5085b4444cb3f4306152e4466ca8a440c844d44928939449a141b4451a1e943afa54842ad8f2f440cbc2d4458e98f4492de4f43bd318c44f017e242913f3343eebf5444538883442cbb0b443581594376c34f44ce359944a1816b430e2ff843bf26b743b31c1c43f164c043f96c1644a155b343b5fb2e44d0756c44894b79441b956b44203a3d44e0744d4404d8744467ed5243c1b24444e745bf43e2d17344ee63e243c88ba6438d432f44959be643ab3c3344f1fabc436a03e7430e148344fd245f44e8698344e74c05433ecb93444941b9437f6a8d4469d6c942e6ae6e444f32d943b66d1a44e9600144575a4c449b591f431d41a0432a0cfb436ced664356ddc941a1f25e447fec674343d6d44285ea9e43cfa69044e72536448de978449c424f44071193447b408a42a9000044166f63443188dd43672d48433b020250c24324ccc543d5140c44c75d324308de51444fe63c449809a44327415f4498078143d7e58043057a6b44fb018543c0ed064471fb8a431a6c1e447b8d2c43cc6b6d4463c7bc43b3113144535a6c44b7094b4419432144e2a410441ada25444a76e343a4b46644e74d7144a3de2e44d808974446521e44f0545344d0c39a42c7d05a4453143644389690429188db4398a38d438da25d44b7d4d442f8b4e643ad787a425d1aa7436c072e443c9e4944ecdc7b43d32827447b21e84223633a442efab2439d159443a4e865446d70bb438d073144d8856444456f6a42bcfaa54342a71644a5ca4a438f6f6c43d501d1432ca47544d6f46c440987ca4201c0024446a2c443ebd78a43552a4d44a9983a44f03ee3431c591744d6a2b2437a38c94371938d43054d404476241d446cda3944d1964f445ed2414369f604449c446a449998664340012c443f346a42aa329a428f6e6a42314a3f44978246445aaf3244b302e2430040334454132944d2911b44dc6a7d4344a2314401006a42306629440000000000000000"
#  data = "908086434f114844b3707144fb581c44b3e02a4472103644c014fe43b3b4c443372e934458245044232e5143fed1f04377709b445b440e4419355944d59ebb4274dbf6415fb65a443eff2e439b9d5d44a8a57244433f384458fb3944f5085b4444cb3f4306152e4466ca8a440c844d44928939449a141b4451a1e943afa54842ad8f2f440cbc2d4458e98f4492de4f43bd318c44f017e242913f3343eebf5444538883442cbb0b443581594376c34f44ce359944a1816b430e2ff843bf26b743b31c1c43f164c043f96c1644a155b343b5fb2e44d0756c44894b79441b956b44203a3d44e0744d4404d8744467ed5243c1b24444e745bf43e2d17344ee63e243c88ba6438d432f44959be643ab3c3344f1fabc436a03e7430e148344fd245f44e8698344e74c05433ecb93444941b9437f6a8d4469d6c942e6ae6e444f32d943b66d1a44e9600144575a4c449b591f431d41a0432a0cfb436ced664356ddc941a1f25e447fec674343d6d44285ea9e43cfa69044e72536448de978449c424f44071193447b408a42a9000044166f63443188dd43672d48433b50c24324ccc543d5140c44c75d324308de51444fe63c449809a44327415f4498078143d7e58043057a6b44fb018543c0ed064471fb8a431a6c1e447b8d2c43cc6b6d4463c7bc43b3113144535a6c44b7094b4419432144e2a410441ada25444a76e343a4b46644e74d7144a3de2e44d808974446521e44f0545344d0c39a42c7d05a4453143644389690429188db4398a38d438da25d44b7d4d442f8b4e643ad787a425d1aa7436c072e443c9e4944ecdc7b43d32827447b21e84223633a442efab2439d159443a4e865446d70bb438d073144d8856444456f6a42bcfaa54342a71644a5ca4a438f6f6c43d501d1432ca47544d6f46c440987ca4201c0024446a2c443ebd78a43552a4d44a9983a44f03ee3431c591744d6a2b2437a38c94371938d43054d404476241d446cda3944d1964f445ed2414369f604449c446a449998664340012c443f346a42aa329a428f6e6a42314a3f44978246445aaf3244b302e2430040334454132944d2911b44dc6a7d4344a2314401006a42306629440000000000000000"
#  data = "ae286544861549444a0283446305bf432eba75449bb32b4465095a4373bc6b443ba977443039cf42947b2344694e454466c94444f46f0e4375547d44198f36441b41a3438b959f437bb78344dec8f54353b0f541e517ec4379281f446ce41043d7b0084302c60944d27a1044ae864644012e824415d39f43a36e85441332f64125a48643124b64448ef52f4423d388423fdc46443e7b0f4443ce95426ced0d444eb04c448afba04343d52344b961fc4395eb3c448582e9434b5b514487e0424491828e447ece03426deb0c447fec664319e58c42e5462a44f7ba94441ae5394446681d4345a2c9433e0f73443fad0a44fdd3a04266fa994393216a43f7a1d142febacf4343950b44284c8244123888433d024744f169c243ab793a44d6de6243ca126844e0760d44ea0e3544d62ac643356d5944cd815744ad71354437c05144d91873432b9f0143bbbaa94370529043d0c040441f5d0542b7125144a11a5e44e086ee43c8bdbc435999d8434cdb52443df72f4453cdfa4309028d4394eab043c882bc43c234e443431f34443cd455446e0a4944d51b2644ccfdb243d48bbf4380f74444103d0a44d8509f43f22d2d441aef93438eb142440a7a30444a4b4f44274e9a4479f7b84323827244215e6944a9606d4421f167431a30474457d015433707af430d43134454df5f448e423643edb10c44259c604453111e4402f969442518a44354ed0643ccd28a44cd001644bfcbcb433cac2a44d840e743a0295d44b16a03442957d84396dd9a44cd8cc74394bf9044974d4044f66bf643a8a51c444fc146445f1a21443ea2bb4335dfff43bbe0a6434f08c84339a1bb437c2a20449ae8664479375744dcd45c4487a2574313c6014239bd61449e99d7431b341f434f13834457ec5043649e1b4417f8444492ad3044f3be544406308b43375b2144c414934401aafe4306de4b44759b9343b92feb430a46fc433362fa437230ec437765fe431f875e4341149543e5d236441d128744ce20db43d1054844697443444b1b2b44a648dc41cce48e437c791143b75a46437eaf3344c0374f447dcd6b43bc80484481c70844786595444b07374440949b44c23d47440000000000000000"
#  data = "19fb6c44e0c35d434c1e0943fda04744f44f6044aca99043fbae674484a06244baa7dc43eff9ba43d22b1e44728c96436f3e7b437d6d3444cd65e643583526441dd06e434aba3844b04b2643f168a643e3946b4427565c44fb3c59443072774344798f4459bcec43e1d8ad43d1af494419522643d8b1ca430cbcbe433d410c4486800b444748cb4318509a4334c8c6437d883543d14b2443d9f36143d8114e44645c3d441b15c343c72121438acf5144c7fd9a44e8689f4267da9444cb43eb4164eb95441063fe4363ee8d442b5f274443c84044a7b58b43b5325d4493d71244b49cb543bac8074449e69744c9b65f440e6c9443ad83d7427f8fcf4222dd3044ff9f9d43d3c43d4368645c44abbb5e4481667f4434244e424a474d44ac835e44963fa5433cf41342dab0104498890e440eb2fb43108ed0439ea57644d50cb042cd9fb743e715ed43cb806b44d1859543336ed5435e24144426e6c14361c03843eff03544b13b68444c718a44380d95420f2fb84381b24543186fbb427e4d8343e3b1b043ba0fe0432f587044f7d91a4466778c44c4a73544c3ec9b44796a7e433b3307439eaadd4369e501441ccc5a43c8ecd943037101443ea391441453ac43014483445f77c643dceb824464e70e4414d89444b99a3244c8678b44e7be1f43e3c5bf4305082d44a6d224443a921143abb21d447e790c44dcbe0d420dbfb44305ac82441d26194400c365439da80944684186433db4e943f8c83643e2113344ca5d8144e1a74c44deb69842cda33b4455432f43cf14f543180a544482ea784319907b44f35f2d44c5a18444fe62ce43621f3144022218424dea2a440f735843c69609446868c043b94064445664594418c24d444f81ef43b7838d43de5c4b439ed4f6435a141e43d27d4d4375baad434b28f64285974543b4e61444f14c8843cfaa8f43a7026e44021c6942cd40b24361d791443f1623446fa94b44e9b2574419d2c44349de4d4449cb91445df23a444cb28c439098f6424f4ad943c5c4b5430bdd95446cc2aa429d485544844ef64258a436440ed44b447bc79744a225be4264daff43b0c082439a3f92441c7c6e44ffeb4d447eb15e430000000000000000"
  length = "{:08x}".format(int(len(data)/2))
  data = length + data
  valuesum = sum(int(data[c:c+2],16) for c in range(0,len(data),2)) 
  summa = 0 + valuesum
  summa=65536-summa
  summa=summa&255
  c=0
  while c<len(data):
    if (int(data[c:c+2],16)==0x3b):
      data=data[:c+2]+'0202'+data[c+2:]
    c=c+2
  output1 = "{:02x}".format(preamble2)
  output2 = data
  output3 = "{:02x}".format(summa)
  output = output1 + output2 + output3
  #output = "3c00000320908086434f114844b3707144fb581c44b3e02a4472103644c014fe43b3b4c443372e934458245044232e5143fed1f04377709b445b440e4419355944d59ebb4274dbf6415fb65a443eff2e439b9d5d44a8a57244433f384458fb3944f5085b4444cb3f4306152e4466ca8a440c844d44928939449a141b4451a1e943afa54842ad8f2f440cbc2d4458e98f4492de4f43bd318c44f017e242913f3343eebf5444538883442cbb0b443581594376c34f44ce359944a1816b430e2ff843bf26b743b31c1c43f164c043f96c1644a155b343b5fb2e44d0756c44894b79441b956b44203a3d44e0744d4404d8744467ed5243c1b24444e745bf43e2d17344ee63e243c88ba6438d432f44959be643ab3c3344f1fabc436a03e7430e148344fd245f44e8698344e74c05433ecb93444941b9437f6a8d4469d6c942e6ae6e444f32d943b66d1a44e9600144575a4c449b591f431d41a0432a0cfb436ced664356ddc941a1f25e447fec674343d6d44285ea9e43cfa69044e72536448de978449c424f44071193447b408a42a9000044166f63443188dd43672d48433b020250c24324ccc543d5140c44c75d324308de51444fe63c449809a44327415f4498078143d7e58043057a6b44fb018543c0ed064471fb8a431a6c1e447b8d2c43cc6b6d4463c7bc43b3113144535a6c44b7094b4419432144e2a410441ada25444a76e343a4b46644e74d7144a3de2e44d808974446521e44f0545344d0c39a42c7d05a4453143644389690429188db4398a38d438da25d44b7d4d442f8b4e643ad787a425d1aa7436c072e443c9e4944ecdc7b43d32827447b21e84223633a442efab2439d159443a4e865446d70bb438d073144d8856444456f6a42bcfaa54342a71644a5ca4a438f6f6c43d501d1432ca47544d6f46c440987ca4201c0024446a2c443ebd78a43552a4d44a9983a44f03ee3431c591744d6a2b2437a38c94371938d43054d404476241d446cda3944d1964f445ed2414369f604449c446a449998664340012c443f346a42aa329a428f6e6a42314a3f44978246445aaf3244b302e2430040334454132944d2911b44dc6a7d4344a2314401006a42306629440000000000000000f5"
  if connmode == "hc":
    msgqueue = msgqueue + output
    processmsgqueue()
#  decodemsg3c(output)
  hexoutput = binascii.unhexlify(output)
  return hexoutput



def scanauxbus(target):
  xprint ("-----------------------")
  xprint ("Initiating AUXBUS SCAN ")
  xprint ("-----------------------")
  xprint ("     Timestamp - Sender                  Hex   -> Receiver                Hex   --- Command      Hex   --- Value")
  if target=='known':
    for device in devices:
      transmitmsg('3b','',device,0xfe,'')
  if target=='all':
    for device in range(0x01,0xff):
      transmitmsg('3b','',device,0xfe,'')
  time.sleep(0.5) 
  identifymount()
  time.sleep(1)  
  xprint ("-----------------------")
  xprint (" Finished AUXBUS SCAN  ")
  xprint ("-----------------------")
  printactivedevices()

def identifymount():
  device = 0x10
  if str(hex(device)) in activedevices:
    transmitmsg('3b','',device,0x05,'')

def printactivedevices():
  if mount in mounts:
    mounttext = mounts[mount]
  else: 
    mounttext = 'UNKNOWN' + " (" + str(hex(mount))+ ")" if len(str(mount))>0 else 'NOT DETECTED'  
  xprint ("-----------------------")
  xprint (" Mount :", mounttext )
  xprint ("-----------------------")
  xprint ("-----------------------")
  xprint ("   Detected Devices    ")
  xprint ("-----------------------")
  listactivedevices=list(activedevices)
  for device in activedevices:
    output = str(listactivedevices.index(device))+ ") " + "{:<21}".format(devices[int(device,16)]) + " (0x" + format(int(device,16),'02x') + ") - " + activedevices[device]
    xprint (output)
  
def resettime():
    global starttime
    starttime=time.time()

def printhelpmenu():
  xprint ("-----------------------")
  xprint ("      Commands         ")
  xprint ("-----------------------")
  xprint ("d) show Device list    ")
  xprint ("c) send Command to device")
  xprint ("k) toggle Keepalive send")
  xprint ("s) reScan AUXBUS       ")
  xprint ("a) rescan AUXBUS for All")
  xprint ("v) toggle Verbose output")
  xprint ("f) toggle csv File output")
  xprint ("g) toggle GPS simulator")
  xprint ("ss) toggle Starsense Image Save")
  xprint ("4) trigger Starsense Image captura")
  xprint ("8) Read raw capture from file rawinput.txt")
  xprint ("9) Write raw capture to file rawoutput.txt")
  xprint ("r) Reset Packet Timer  ")
  xprint ("o) Out of frame counter") 
  xprint ("h) print this Help menu")
  xprint ("q) Quit                ")
  xprint ("-----------------------")

def transmitmsg(msgtype,sender,receiver,command,value):
    if msgtype=='3b':
        data = encodemsg(sender,receiver,command,value)
    if msgtype=='3c':
        data = encodemsg3c()
    if rawfileoutput:
        fileoutput = str(round(time.time()-starttime,6)) + " " + str(binascii.hexlify(data),'utf-8')
        print(fileoutput, file=open('rawoutput.txt', 'a'))
    if connmode == 'wifi':
        sock.send(data)
    if connmode == 'serial':
        ser.rtscts = True
        ser.rts=True
        ser.write(data)
        ser.rts=False
        ser.rts=True
        ser.rts=False
        time.sleep(.1)
        ser.read(ser.inWaiting())
        ser.rtscts = False
    if connmode == 'hc':
        ser.write(data)
    time.sleep(0.15)

def keep_alive(interval):
    global endthread
    while not endthread:
        if keepalive:
            transmitmsg('3b','',0x10,0xfe,'')
        time.sleep(interval)
    xprint ("Finished Keep Alive")

def receivedata():
  global msgqueue
  global endthread
  global rawfileoutput
  data=''
  while not endthread:
      time.sleep(.05)
      if connmode=='wifi':
        data = sock.recv(BUFFER_SIZE)
      if connmode=='serial' or connmode=='hc':
        if (ser.inWaiting()>0):
            data = ser.read(ser.inWaiting())
      if len(data)>0:
          stringdata = binascii.hexlify(data)
          msgqueue = msgqueue + str(stringdata,'utf-8')
          if rawfileoutput:
              fileoutput = str(round(time.time()-starttime,6)) + " " + str(stringdata,'utf-8')
              print(fileoutput,  file=open('rawoutput.txt', 'a'))
          processmsgqueue()
          data=''
  xprint ("Finished Receive Data")

def sendingdata(interval):
  global triggerscan
  while not endthread:
      time.sleep(.05)
      if triggerscan == 'known' or triggerscan == 'all':
          scanauxbus (triggerscan)
          triggerscan = ''
          lasttx = time.time()
      if keepalive:
          if time.time()-lasttx > interval:
             transmitmsg('3b','',0x10,0xfe,'')
             lasttx = time.time()
      

def fileplayback(filename):
    global msgqueue
    resettime()
    f = open(filename, "r")
    f.seek(0)
    file =''
    linenum=0
    for line in f.read().splitlines():
      linenum=linenum+1
      line2=line.split()
      if len(line2) == 2: 
         if linenum != 1:
            time.sleep(float(line2[0])-lasttime)
         lasttime = float(line2[0])
         data = line2[1]
      else:
         data = line2[0]
      msgqueue = msgqueue + data
      processmsgqueue()
    f.close()
    xprint ("Finished File Processing")

def initializeconn(connmodearg,port):
    global connmode
    global keepalive
    connmode = connmodearg
    if connmode=='wifi':
        keepalive=True
        SERVER_IP = port
        global sock
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.connect((SERVER_IP, SERVER_PORT))
    if connmode=='serial' or connmode=='hc':
        keepalive=False
        COM_PORT = port
        global ser
        ser = serial.Serial()
        ser.port = COM_PORT
        if connmode=='serial':
            ser.baudrate = 19200
        if connmode=='hc':
            ser.baudrate = 9600
        ser.bytesize = serial.EIGHTBITS
        ser.parity = serial.PARITY_NONE
        ser.stopbits = serial.STOPBITS_ONE
        ser.timeout = 0
        ser.xonxoff = False
        ser.open()
        if ser.isOpen():
            ser.flushInput()
            ser.flushOutput()
        if connmode=='hc':
            data = b'\x56'
            ser.write(data)
            time.sleep(.5)
            #Should return 0x05 0x1f 0x23
            ser.read(ser.inWaiting())
            data = b'\x8a'
            ser.write(data)
            time.sleep(.5)
            #Should return 0xf8
            ser.read(ser.inWaiting())
            #print(data)
            ser.close
            ser.baudrate = 115200
            ser.open
            time.sleep(1)
            data = b'\x0a\x00\x02\x08\x00\x4b\x00\x00\xd0\xc0'
            ser.write(data)
            time.sleep(.5)
            #Should return 0x05 0x00 0x06 0x38 0xc0
            data = ser.read(ser.inWaiting())

def appstartup():
  global starttime
  global triggerscan
  xprint ("-------------------------------")
  xprint (" AUXBUS SCANNER VERSION",__version__)
  xprint ("-------------------------------") 
  starttime=time.time()
  launchthreads()
  xprint ("-----------------------")
  xprint ("Starting AUXBUS Monitor")
  xprint ("-----------------------")
  triggerscan='known'

def closeconn():
  xprint ("-----------------------")
  xprint ("      Closing          ")
  xprint ("-----------------------")
  if connmode=='wifi': 
    sock.close()
  if connmode=='serial' or connmode=='hc':
    ser.close()

def launchthreads():
    global t0,t1,t2
    global keepalive
    
    t0 = threading.Thread(target=receivedata)
    t0.daemon = True
    t0.start()

    t2 = threading.Thread(target=sendingdata, args = (KEEP_ALIVE_INTERVAL,))
    t2.daemon = True
    t2.start()
    
def mainloop():
  global emulategps
  global keepalive
  global gpslat,gpslon
  global activedevices
  global mount
  global starttime
  global endthread
  global verbose
  global filecsvoutput
  global rawfileoutput
  global oof
  global triggerscan
  global starsensesave

  while True:
    inputkey = input("Enter Command:")
    if inputkey == "d":
        printactivedevices()

    if inputkey == "c":
        printactivedevices()
        time.sleep(0.2)
        print ("-----------------------")
        print ("Choose device")
        key1 = input("Enter Device:")
        listactivedevices=list(activedevices)
        filtercommands=[(k[1], v) for k, v in commands.items() if k[0]==int(listactivedevices[int(key1)],16)]
        for command in filtercommands:
            output = chr(97+filtercommands.index(command)) + ") " + str(hex(command[0])) + " (" + str(command[1]) + ") "
            print (output)
        time.sleep(0.2)
        print ("-----------------------")
        print ("Choose command")
        key2 = input("Enter Command:")
        transmitmsg('3b','',int(listactivedevices[int(key1)],16),filtercommands[ord(key2)-97][0],'')

    if inputkey == "k":
        print ("-----------------------")
        print ("   Toggle Keepalive    ")
        print ("-----------------------")
        if keepalive:
            keepalive=False
            print ("   Keepalive Disabled    ")
        else:
            keepalive=True
            print ("   Keepalive Enabled    ")
    if inputkey == "g":
        print ("-----------------------")
        print (" Toggle GPS Emulation  ")
        print ("-----------------------")
        if emulategps:
            emulategps=False
            print ("  GPS Emulation Disabled    ")
        else:
            activedevices.update({hex(176):'11.1'}) if hex(176) not in activedevices else activedevices
            gpslat=float(input("Enter GPS Latitude in Decimal Format: "))
            gpslon=float(input("Enter GPS Longitude in Decimal Format: "))
            emulategps=True
            print ("  GPS Emulation Enabled    ")
    if inputkey == "s":
        activedevices = {}
        mount = ''
        triggerscan = 'known'
    if inputkey == "a":
        activedevices = {}
        mount = ''
        triggerscan = 'all'
    if inputkey == "i":
        identifymount()
    if inputkey == "v":
        verbose = not verbose
    if inputkey == "f":
        filecsvoutput = not filecsvoutput
        if filecsvoutput:
            fileoutput = 'timestamp,'+'sender,'+'sender_id,'+'receiver,'+'receiver_id,'+'command,'+'command_id,'+'command_data,'+'raw_packet'
            print(fileoutput, file=open('auxbuslog.csv','w'))
    if inputkey == "ss":
        starsensesave = not starsensesave
    if inputkey == "r":
        resettime()
    if inputkey == "h":
        printhelpmenu()
    if inputkey == "o":
        print("Out of Frame bytes : ", oof)
    if inputkey == "3":
        transmitmsg('3c','','','','')
    if inputkey == "4":
        transmitmsg('3b','',0xb4,0x90,'03e800')
        time.sleep(4)
        transmitmsg('3b','',0xb4,0x94,'00')
        time.sleep(4)
        transmitmsg('3b','',0xb4,0x92,'')
    if inputkey == "8":
        if os.path.isfile("rawinput.txt"):
          fileplayback("rawinput.txt")
        else:
          print ("rawinput.txt is not present")
    if inputkey == "9":
        rawfileoutput = not rawfileoutput
        if rawfileoutput:
          open('rawoutput.txt','w')
    if inputkey == "q":
        endthread = True
        transmitmsg('3b','',0x10,0xfe,'')
        t0.join()
        t2.join()
        closeconn()
        break
    time.sleep(.1)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('connmode', help='connection mode (wifi / serial / hc)')
    parser.add_argument('port', help='connection port (ip address / COM Port')
    args = parser.parse_args()
    initializeconn(args.connmode, args.port)
    appstartup()
    mainloop()

if __name__ == '__main__':
    main()
