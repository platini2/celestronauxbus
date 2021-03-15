#!/usr/bin/env python

"""Celestron.py: Celestron AUXBUS Scanner"""
__author__ = "Patricio Latini"
__copyright__ = "Copyright 2020, Patricio Latini"
__credits__ = "Patricio Latini"
__license__ = "GPLv3"
__version__ = "0.8.9"
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
            0x1687 : 'Nexstar Evolution 8',
            0x1788 : 'CGX'}

devices = {
            0x01 : 'Main Board',
            0x04 : 'Nexstar HC',
            0x0d : 'Nexstar+ HC',
            0x0e : 'Starsense HC',
            0x10 : 'AZM MC',
            0x11 : 'ALT MC', 
            0x12 : 'Focuser',
            0x17 : '?????', 
            0x20 : 'CPWI',
            0x21 : 'CFM',
            0x22 : 'AUXBUS Scanner',
            0x30 : 'CGX RA Switch',
            0x31 : 'CGX DEC Switch',
            0x32 : 'CGX DEC Autoguide Port',
            0xb0 : 'GPS',
            0xb2 : 'RTC',
            0xb3 : 'Skyportal Accessory',
            0xb4 : 'Starsense Camera',
            0xb5 : 'Nextstar EVO WiFi',
            0xb6 : 'Battery Power Controller',
            0xb7 : 'Charge Port',
            0xb8 : 'Starsense Camera SkyW',
            0xbf : 'Mount Lights'}

controllers = [ 0x04 , 0x0d , 0x0e , 0x20, 0x21, 0x22 ]
activedevices = {}

commands = {  
            (0x01, 0xfe) : 'MB_GET_FW_VER', 
            (0x04, 0xfe) : 'NXS_GET_FW_VER',
            (0x0d, 0xfe) : 'NXS_GET_FW_VER',
            (0x0e, 0xfe) : 'NXS_GET_FW_VER',
            (0x10, 0x01) : 'MC_GET_POSITION', 
            (0x10, 0x02) : 'MC_GOTO_FAST', 
            (0x10, 0x04) : 'MC_SET_POSITION', 
            (0x10, 0x05) : 'MC_GET_MODEL',
            (0x10, 0x06) : 'MC_SET_POS_GUIDERATE',
            (0x10, 0x07) : 'MC_SET_NEG_GUIDERATE',
            (0x10, 0x0b) : 'MC_LEVEL_START',
            (0x10, 0x0c) : 'MC_PEC_RECORD_START',
            (0x10, 0x0d) : 'MC_PEC_PLAYBACK',
            (0x10, 0x10) : 'MC_SET_POS_BACKLASH',
            (0x10, 0x11) : 'MC_SET_NEG_BACKLASH',
            (0x10, 0x12) : 'MC_LEVEL_DONE',   
            (0x10, 0x13) : 'MC_SLEW_DONE',
            (0x10, 0x14) : 'MC_XXXX',
            (0x10, 0x15) : 'MC_PEC_RECORD_DONE',
            (0x10, 0x16) : 'MC_PEC_RECORD_STOP',
            (0x10, 0x17) : 'MC_GOTO_SLOW',
            (0x10, 0x21) : 'MC_GET_MAX_SLEW_RATE',
            (0x10, 0x23) : 'MC_GET_MAX_RATE',
            (0x10, 0x24) : 'MC_MOVE_POS',
            (0x10, 0x25) : 'MC_MOVE_NEG',
            (0x10, 0x3a) : 'MC_SET_CORDWRAP_POS',
            (0x10, 0x3b) : 'MC_POLL_CORDWRAP',
            (0x10, 0x3c) : 'MC_GET_CORDWRAP_POS',
            (0x10, 0x40) : 'MC_GET_POS_BACKLASH',
            (0x10, 0x41) : 'MC_GET_NEG_BACKLASH',
            (0x10, 0x47) : 'MC_GET_AUTOGUIDE_RATE',
            (0x10, 0xfc) : 'MC_GET_APPROACH',       
            (0x10, 0xfe) : 'MC_GET_FW_VER',
            (0x11, 0x01) : 'MC_GET_POSITION', 
            (0x11, 0x02) : 'MC_GOTO_FAST', 
            (0x11, 0x05) : 'MC_GET_MODEL',
            (0x11, 0x06) : 'MC_SET_POS_GUIDERATE',
            (0x11, 0x13) : 'MC_SLEW_DONE',
            (0x11, 0x21) : 'MC_GET_MAX_SLEW_RATE',
            (0x11, 0x23) : 'MC_GET_MAX_RATE',
            (0x11, 0x24) : 'MC_MOVE_POS',
            (0x11, 0x25) : 'MC_MOVE_NEG',
            (0x11, 0x3a) : 'MC_SET_CORDWRAP_POS',
            (0x11, 0x3b) : 'MC_POLL_CORDWRAP',
            (0x11, 0x3c) : 'MC_GET_CORDWRAP_POS',
            (0x11, 0x40) : 'MC_GET_POS_BACKLASH',
            (0x11, 0x41) : 'MC_GET_NEG_BACKLASH',
            (0x11, 0x47) : 'MC_GET_AUTOGUIDE_RATE',
            (0x11, 0xfc) : 'MC_GET_APPROACH',       
            (0x11, 0xfe) : 'MC_GET_FW_VER',
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
            (0xb0, 0x33) : 'GPS_GET_TIME',
            (0xb0, 0x36) : 'GPS_TIME_VALID',
            (0xb0, 0x37) : 'GPS_LINKED',
            (0xb0, 0xfe) : 'GPS_GET_FW_VER',
            (0xb3, 0xfe) : 'WIFI_GET_FW_VER',
            (0xb4, 0xfe) : 'SS_GET_FW_VER',
            (0xb5, 0xfe) : 'WIFI_GET_FW_VER',
            (0xb6, 0x10) : 'BAT_GET_VOLTAGE',
            (0xb6, 0x18) : 'BAT_GET_CURRENT',
            (0xb6, 0xfe) : 'BAT_GET_FW_VER',
            (0xb7, 0x10) : 'CHG_GET_MODE',
            (0xb7, 0xfe) : 'CHG_GET_FW_VER',
            (0xbf, 0x10) : 'LIGHT_GET_LEVEL',
            (0xbf, 0xfe) : 'LIGHT_GET_FW_VER'}

SERVER_IP = '1.2.3.4'
SERVER_PORT = 2000
BUFFER_SIZE = 100
KEEP_ALIVE_INTERVAL = 10

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
          if len(commandvalue)<4:
            commandvalue = '.'.join([format(int(c, 16)) for c in commandvalue])
          else:
            commandvalue = format(int(commandvalue[0], 16)) + '.' + format(int(commandvalue[1], 16))+ '.' + str(int(format(int(commandvalue[2],16), '02x')+format(int(commandvalue[3],16), '02x'),16))
          if len(commandvalue)>0:
            activedevices.update({hex(sender):commandvalue}) if hex(sender) not in activedevices else activedevices
        else:
          commandvaluehex = ''.join([format(int(c, 16), '02x') for c in commandvalue])
          commandvalue = (int(commandvaluehex,16))
          if hex(command) == '0x5' and hex(sender) == '0x10':
            mount = commandvalue
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
      output = str(round(time.time()-starttime,6)) + " - " + sendertext + " (" + str(hex(sender)) + ") " + "-> " + receivertext + " (" + str(hex(receiver)) + ") " + "--- " + commandtext + " (" + str(hex(command)) + ") " + "--- " + str(commandvalue) + dumptext
      print (output)
      if filecsvoutput:
          fileoutput = str(round(time.time()-starttime,6)) + "," + sendertext + "," + str(hex(sender)) + ","  + receivertext + "," + str(hex(receiver)) + ","  + commandtext + "," + str(hex(command)) + "," + str(commandvalue) + "," + str(msg)
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
      print (hex(sender)," -> ", hex(receiver), "---", hex(command), "---", commandvalue, "CRC FAIL!")

def decodemsg3c(msg):
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
        output = str(round(time.time()-starttime,6)) + " - " + "Starsense Data: " + str(length) + " Bytes - Data: " + msg[5*2:-2] + dumptext
        print (output)
        if filecsvoutput:
        	fileoutput = str(round(time.time()-starttime,6)) + "," + "Starsense Camera" + "," + "0xb4" + ","  + "All" + "," + "0x00" + ","  + "Data" + "," + "0x00" + "," + "[]" + "," + str(msg)
        	print(fileoutput,  file=open('auxbuslog.csv', 'a'))
    else:
    	print ("Starsense Data: CRC FAIL!")


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
  if connmode == "hc" or connmode == "wifi" :
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
  global keepalive
  print ("-----------------------")
  print ("Initiating AUXBUS SCAN ")
  print ("-----------------------")
  if target=='known':
    for device in devices:
      transmitmsg('3b','',device,0xfe,'')
  if target=='all':
    for device in range(0x01,0xff):
      transmitmsg('3b','',device,0xfe,'')
  identifymount()
  time.sleep(1.5)  
  print ("-----------------------")
  print (" Finished AUXBUS SCAN  ")
  print ("-----------------------")
  printactivedevices()
  if connmode=="wifi":
    keepalive=True

def identifymount():
  device = 0x10
  if str(hex(device)) in activedevices:
    transmitmsg('3b','',device,0x05,'')

def printactivedevices():
  if mount in mounts:
    mounttext = mounts[mount]
  else: 
    mounttext = 'UNKNOWN' + " (" + str(hex(mount))+ ")" if len(mount)>0 else 'NOT DETECTED'  
  print ("-----------------------")
  print (" Mount :", mounttext )
  print ("-----------------------")
  print ("-----------------------")
  print ("   Detected Devices    ")
  print ("-----------------------")
  listactivedevices=list(activedevices)
  for device in activedevices:
    output = str(listactivedevices.index(device))+ ") " + devices[int(device,16)] + " (" + str(device) + ") - " + activedevices[device]
    print (output)
  
def resettime():
    global starttime
    starttime=time.time()

def printhelpmenu():
  print ("-----------------------")
  print ("      Commands         ")
  print ("-----------------------")
  print ("d) show Device list    ")
  print ("c) send Command to device")
  print ("k) toggle Keepalive send")
  print ("s) reScan AUXBUS       ")
  print ("a) rescan AUXBUS for All")
  print ("v) toggle Verbose output")
  print ("f) toggle csv File output")
  print ("g) toggle GPS simulator")
  print ("8) Read raw capture from file rawinput.txt")
  print ("9) Write raw capture to file rawoutput.txt")
  print ("r) Reset Packet Timer  ")
  print ("o) Out of frame counter") 
  print ("h) print this Help menu")
  print ("q) Quit                ")
  print ("-----------------------")

def tosigned24(hexnum):
    n = int(hexnum,16)
    n = n & 0xffffff
    return n | (-(n & 0x800000))

def hextoposition(hexnum):
    position = tosigned24(hexnum)/pow(2,24)*360
    return position

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
    time.sleep(0.25)

def keep_alive(interval):
    global endthread
    while not endthread:
        if keepalive:
            transmitmsg('3b','',0x10,0xfe,'')
        time.sleep(interval)
    print ("Finished Keep Alive")

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
  print ("Finished Receive Data")

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
    print ("Finished File Processing")




def initializeconn():
    if connmode=='wifi':
        global sock
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.connect((SERVER_IP, SERVER_PORT))

    if connmode=='serial' or connmode=='hc': 
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

def closeconn():
  print ("-----------------------")
  print ("      Closing          ")
  print ("-----------------------")
  if connmode=='wifi': 
    sock.close()
  if connmode=='serial' or connmode=='hc':
    ser.close()

def launchthreads():
    global t0,t1,t2
    global keepalive

    keepalive = False
    
    t0 = threading.Thread(target=receivedata)
    t0.daemon = True
    t0.start()

    t2 = threading.Thread(target=keep_alive, args = (KEEP_ALIVE_INTERVAL,))
    t2.daemon = True
    t2.start()


def execute_code(connmodearg, port):
  global emulategps
  global connmode
  global SERVER_IP, COM_PORT
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

  connmode = connmodearg

  if connmode=='wifi': 
    SERVER_IP = port
  if connmode=='serial' or connmode=='hc':
    COM_PORT = port
  print ("-------------------------------")
  print (" AUXBUS SCANNER VERSION",__version__)
  print ("-------------------------------") 
  initializeconn()
  starttime=time.time()
  launchthreads()
  scanauxbus('known')
  print ("-----------------------")
  print ("Starting AUXBUS Monitor")
  print ("-----------------------")
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
        scanauxbus('known')
    if inputkey == "a":
        activedevices = {}
        mount = ''
        scanauxbus('all')
    if inputkey == "i":
        identifymount()
    if inputkey == "v":
        verbose = not verbose
    if inputkey == "f":
        filecsvoutput = not filecsvoutput
        if filecsvoutput:
            fileoutput = 'timestamp,'+'sender,'+'sender_id,'+'receiver,'+'receiver_id,'+'command,'+'command_id,'+'command_data,'+'raw_packet'
            print(fileoutput, file=open('auxbuslog.csv','w'))
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

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('connmode', help='connection mode (wifi / serial / hc)')
    parser.add_argument('port', help='connection port (ip address / COM Port')
    args = parser.parse_args()
    execute_code(args.connmode, args.port)

if __name__ == '__main__':
    main()




