#!/usr/bin/env python

"""Celestron.py: Celestron AUXBUS Scanner"""
__author__ = "Patricio Latini"
__copyright__ = "Copyright 2021, Patricio Latini"
__credits__ = "Patricio Latini"
__license__ = "GPLv3"
__version__ = "0.12.26"
__maintainer__ = "Patricio Latini"
__email__ = "p_latini@hotmail.com"
__status__ = "Production"
__mode__ = "text"

##### TKINTER CODE
import tkinter as tk
from tkinter import ttk
from tkinter import scrolledtext
from tkinter import messagebox
import serial.tools.list_ports
import re
import queue
##### TKINTER CODE

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
starsensesave = False
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
            0x0783 : 'Nexstar SLT',
            0x1189 : 'CPC Deluxe',
            0x1283 : 'GT Series',
            0x1485 : 'AVX',
            0x1687 : 'Nexstar Evolution',
            0x1788 : 'CGX',
            0x0c82 : '6/8SE'}

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
            (0x10, 0x11) : 'MTR_SET_NEG_BACKLASH',	# Negative	 backlash, followed by 1 byte (0-99) 0=Off, 99=Max
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
            (0x17, 0x10) : '?????_????',
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
            (0xb4, 0x90) : 'SS_GET_ALIGN_CAPTUR',
            (0xb4, 0x91) : 'SS_GET_STAR_COUNT',
            (0xb4, 0x92) : 'SS_GET_IMAGE2',
            (0xb4, 0x94) : 'SS_GET_IMAGE1',
            (0xb4, 0x9f) : 'SS_GET_IMAGE3',
            (0xb4, 0x3f) : 'SS_ALIGN_CENTER',
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
    if (val & (1 << (bits - 1))) != 0: # if sign bit is set e.g., 8bit: 128-255
        val = val - (1 << bits)        # compute negative value
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
    if __mode__ == 'text':
      print(" ".join(map(str,args)))
    if __mode__ == 'UI':
      q.put(" ".join(map(str,args))) 
      app.event_generate('<<AppendLine>>', when='tail')

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
        elif hex(command) == '0x13' or hex(command) == '0x15':
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
      output = str(format(round(time.time()-starttime,6),'14.6f')) + " - " + "{:<20}".format(sendertext) + " (0x" + str(format(sender,'02x')) + ") " + "-> " + "{:<20}".format(receivertext) + " (0x" + str(format(receiver,'02x')) + ") " + "--- " + "{:<20}".format(commandtext) + " (0x" + str(format(command,'02x')) + ") " + "--- " + str(commandvalue) + dumptext
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
    ssxfov=6.88
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
    pixely = int(ssyres/2+(twos_comp(int(msg[10:16],16),24)*ssyres/pow(2,24)))
    return pixelx,pixely,bx,by

def decodemsg3c(msg):
    global starsensesave
    starlen=2*8
    pixellist = []
    ssxres=1280
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
        output = str(format(round(time.time()-starttime,6),'14.6f')) + " - " + "Starsense HC Data - " + str(int(length)/8) + " Stars" + msg[5*2:-2] + dumptext
        xprint (output)       
        data=msg[5*2:-2]
        stars=[data[i:i+starlen] for i in range(0, len(data), starlen)]
        for star in stars:
            if star!="0000000000000000":
                xprint("                 Star ",stars.index(star)+1," - ",decodestarsensestar(star))
                pixellist.append(starsensepixel(star,ssxres,ssyres))
        if starsensesave:
            img = Image.new('L', (ssxres, ssyres))
            imagedata = [0] * ssxres * ssyres
            for pixel in pixellist:
                imagedata[pixel[0]+pixel[1]*ssxres] = 255
                if pixel[2]>1:
                    imagedata[(pixel[0]+1)+pixel[1]*ssxres] = 255
                if pixel[2]>2:
                    imagedata[(pixel[0]-1)+pixel[1]*ssxres] = 255
                if pixel[2]>3:
                    imagedata[(pixel[0]+2)+pixel[1]*ssxres] = 255
                if pixel[3]>1:
                    imagedata[pixel[0]+(pixel[1]+1)*ssxres] = 255
                if pixel[3]>2:
                    imagedata[pixel[0]+(pixel[1]-1)*ssxres] = 255
                if pixel[3]>3:
                    imagedata[pixel[0]+(pixel[1]+2)*ssxres] = 255
            img.putdata(imagedata)
            img.save('starsense-image.png')
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
  data = "5eda6942894f6b4406ea6942ebc25144d9f66942dbe241449d7d6a42b06bca43d95b6942c914a743b94a6c4252ed38433d9d694289d4204400006a4201203744f7c56942f4a8ba4212f16942ce74134359b56942e1adea42ef0e6a4299571b443ee169427734ed43485c6a423c9a3e44922f6a4288b34743477f6a42d77d474201006a4200201644ff7f784300203344b21a6b420000e14343946a4298f75a4443946a426788004416ed68422bc26144d60f6942a8bb274456556942b0486544ffbf764441f94f4444a96942be4666445fdc6a4251892c44bfb869420080b043a123694252c90a445fdc6a42528953440bf86a4254f60144a52e6942fce21e43b6a26942a0b2634256556942ac89844379c56a42f3f5be43a8937644cbd74843cfa4764406059143883a6942ccd7dd42883a694207c5074479c56a42fafa3244449d6a42fafa9a43ea646a423b05bb4362476942760a41439eb86a42b453e041c48e6a420000b34317649a44c91a1a445555784300002943abaa6a4200004b444dd66a422f08124466ad764417f55b43087f6a42ba0264440dc96a420000d3437a9b6a42d9821e440dc96a420000b54387646942da42674487646942dac246440000000000000000"
  data = "13166b4290b09842ddac7644a8dc5044819f6942fc415644a6e56c42cc3138439a998a43cd4c324434246b42e66d0a4311fe6842e00f3744fc920344af170d44e6a374438c5d6b42cb476942270a134300c08a43000073435555784300808f4301006c4200403544d0bfea420d100c445555694200405c44df7e684219a030437aa186433958e442096469423fbd1d44025978437c7ae74323649a44c41b1a4402597843c2422044045d784308ba9e429a85694204432a44a3a4e64356956d44333d9f42519209444dcf8243128c9643386669438e59d34300809143abe6e3425419564339531044e550b143b4ca7342c6eb764400002544520d6f431baf3443abaa554455553a430000000000000000"
  length = "{:08x}".format(int(len(data)/2))
  data = length + data
  valuesum = sum(int(data[c:c+2],16) for c in range(0,len(data),2)) 
  summa = 0 + valuesum
  summa=65536-summa
  summa=summa&255
  output1 = "{:02x}".format(preamble2)
  output2 = data
  output3 = "{:02x}".format(summa)
  output = output1 + output2 + output3
  output = "3c00000320908086434f114844b3707144fb581c44b3e02a4472103644c014fe43b3b4c443372e934458245044232e5143fed1f04377709b445b440e4419355944d59ebb4274dbf6415fb65a443eff2e439b9d5d44a8a57244433f384458fb3944f5085b4444cb3f4306152e4466ca8a440c844d44928939449a141b4451a1e943afa54842ad8f2f440cbc2d4458e98f4492de4f43bd318c44f017e242913f3343eebf5444538883442cbb0b443581594376c34f44ce359944a1816b430e2ff843bf26b743b31c1c43f164c043f96c1644a155b343b5fb2e44d0756c44894b79441b956b44203a3d44e0744d4404d8744467ed5243c1b24444e745bf43e2d17344ee63e243c88ba6438d432f44959be643ab3c3344f1fabc436a03e7430e148344fd245f44e8698344e74c05433ecb93444941b9437f6a8d4469d6c942e6ae6e444f32d943b66d1a44e9600144575a4c449b591f431d41a0432a0cfb436ced664356ddc941a1f25e447fec674343d6d44285ea9e43cfa69044e72536448de978449c424f44071193447b408a42a9000044166f63443188dd43672d48433b020250c24324ccc543d5140c44c75d324308de51444fe63c449809a44327415f4498078143d7e58043057a6b44fb018543c0ed064471fb8a431a6c1e447b8d2c43cc6b6d4463c7bc43b3113144535a6c44b7094b4419432144e2a410441ada25444a76e343a4b46644e74d7144a3de2e44d808974446521e44f0545344d0c39a42c7d05a4453143644389690429188db4398a38d438da25d44b7d4d442f8b4e643ad787a425d1aa7436c072e443c9e4944ecdc7b43d32827447b21e84223633a442efab2439d159443a4e865446d70bb438d073144d8856444456f6a42bcfaa54342a71644a5ca4a438f6f6c43d501d1432ca47544d6f46c440987ca4201c0024446a2c443ebd78a43552a4d44a9983a44f03ee3431c591744d6a2b2437a38c94371938d43054d404476241d446cda3944d1964f445ed2414369f604449c446a449998664340012c443f346a42aa329a428f6e6a42314a3f44978246445aaf3244b302e2430040334454132944d2911b44dc6a7d4344a2314401006a42306629440000000000000000f5"
  if connmode == "hc":
    msgqueue = msgqueue + output
    processmsgqueue()
# decodemsg3c(output)
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
  lasttx = 0
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

  printhelpmenu()
  
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

#### TKINTER
def validate(P):
    test = re.compile('(^\d{0,3}$|^\d{1,3}\.\d{0,3}$|^\d{1,3}\.\d{1,3}\.\d{0,3}$|^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{0,3}$)')
    if test.match(P):
        return True
    else:
        return False

def serial_ports():
    ports = serial.tools.list_ports.comports()
    portlist = []
    for port in sorted(ports):
        portlist.append(port.device)
    return portlist

def connect():
    global connectbutton_text
    if connectbutton_text.get() == "Connect":
        if radioValue.get() != ' ':
            connmode = radioValue.get()
            if (radioValue.get() == 'wifi'):
                port = ipadd.get()
            else:
                port = comboExample.get().split(' ', 1)[0]
        else:
            return
    ##messagebox.showinfo(connmode,port)
        initializeconn(connmode, port)
        appstartup()
        connectbutton_text.set("Disconnect")
    else:
        closeconn()
        connectbutton_text.set("Connect")
    
def appendLine(event): 
    line = q.get_nowait()
    text_area.insert(tk.END, str(line)+"\n")
    text_area.see(tk.END)

def triggerbusscan():
    global triggerscan 
    triggerscan = 'known'

def updateCBvar():
    global keepalive
    global verbose
    global filecsvoutput
    global rawfileoutput
    global emulategps
    keepalive = CBkeepalive.get()
    verbose = CBverbose.get()
    filecsvoutput = CBfilecsvoutput.get()
    rawfileoutput = CBrawfileoutput.get()
    emulategps = CBemulategps.get()


def tkinterinit():
    global keepalive
    global verbose
    global filecsvoutput
    global rawfileoutput
    global emulategps
    global q
    global app
    global radioValue,connectbutton_text,comboExample,ipadd,text_area
    global CBkeepalive,CBverbose,CBfilecsvoutput,CBrawfileoutput,CBemulategps

    q = queue.Queue()
    app = tk.Tk() 
    app.geometry('1024x768')
    app_title = tk.StringVar()
    app_title.set("Celestron AUXBUS Scanner " + __version__)
    app.title(app_title.get())
    app.bind('<<AppendLine>>', appendLine)

    radioValue = tk.StringVar() 
    radioValue.set(' ')
    radioOne = tk.Radiobutton(app, text='Serial', variable=radioValue, value="serial") 
    radioTwo = tk.Radiobutton(app, text='Hand Controller', variable=radioValue, value="hc") 
    radioThree = tk.Radiobutton(app, text='WiFi', variable=radioValue, value="wifi")
    connectbutton_text = tk.StringVar()
    connectbutton_text.set("Connect")
    connectbutton = tk.Button(app, textvariable=connectbutton_text, command=connect)
    scanbutton = tk.Button(app, text='Rescan AUXBUS', command=triggerbusscan)
    devicebutton = tk.Button(app, text='Device List', command=printactivedevices)
    comboExample = ttk.Combobox(app, values=serial_ports())
    comboExample.current(0)
    varip = tk.StringVar()
    varip.set('1.2.3.4')
    vcmd = app.register(validate)
    ipadd = tk.Entry(app, textvariable = varip, width = 23, validate = 'key', validatecommand = (vcmd, '%P'))
    text_area = scrolledtext.ScrolledText(app, wrap = tk.WORD, width = 120, height = 40)
    CBkeepalive = tk.BooleanVar()
    CBverbose = tk.BooleanVar()
    CBfilecsvoutput = tk.BooleanVar()
    CBrawfileoutput = tk.BooleanVar()
    CBemulategps = tk.BooleanVar()
    checkButton1 = tk.Checkbutton(app, text='Send Keepalives',variable=CBkeepalive, onvalue=True, offvalue=False,command=updateCBvar)
    checkButton2 = tk.Checkbutton(app, text='Verbose Output',variable=CBverbose, onvalue=True, offvalue=False,command=updateCBvar)
    checkButton3 = tk.Checkbutton(app, text='CSV Output',variable=CBfilecsvoutput, onvalue=True, offvalue=False,command=updateCBvar)
    checkButton4 = tk.Checkbutton(app, text='Write rawoutput',variable=CBrawfileoutput, onvalue=True, offvalue=False,command=updateCBvar)
    checkButton5 = tk.Checkbutton(app, text='GPS Emulator',variable=CBemulategps, onvalue=True, offvalue=False,command=updateCBvar)
    radioOne.grid(column=0, row=0)
    radioTwo.grid(column=1, row=0)
    radioThree.grid(column=2, row=0)
    scanbutton.grid(column=3,row=0,rowspan=1)
    devicebutton.grid(column=3,row=1,rowspan=1)
    connectbutton.grid(column=4,row=0,rowspan=2)
    comboExample.grid(column=0, row=1, columnspan=2)
    ipadd.grid(row = 1, column = 2, padx = 5, pady = 5)
    checkButton1.grid(column=0, row=2)
    checkButton2.grid(column=1, row=2)
    checkButton3.grid(column=2, row=2)
    checkButton4.grid(column=3, row=2)
    checkButton5.grid(column=4, row=2)
    text_area.grid(row = 3, column = 0, pady = 10, padx = 10, columnspan = 5)
    app.mainloop()

##### TKNTER

def main():
  if __mode__ == 'text': 
    parser = argparse.ArgumentParser()
    parser.add_argument('connmode', help='connection mode (wifi / serial / hc)')
    parser.add_argument('port', help='connection port (ip address / COM Port')
    args = parser.parse_args()
    initializeconn(args.connmode, args.port)
    appstartup()
    mainloop()
  if __mode__ == 'UI':   
    tkinterinit()

if __name__ == '__main__':
    main()
