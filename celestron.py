#!/usr/bin/env python

"""Celestron.py: Celestron AUXBUS Scanner"""
__author__ = "Patricio Latini"
__copyright__ = "Copyright 2020, Patricio Latini"
__credits__ = "Patricio Latini"
__license__ = "GPL"
__version__ = "0.6.1"
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
from datetime import datetime,timezone

global msgqueue
msgqueue = ''
global emulategps
emulategps = False
global mount
mount = ''

scannerid = 0x22
preamble = 0x3b

mounts = {
            0x0783 : 'Nexstar SLT',
            0x1189 : 'CPC Deluxe',
            0x1687 : 'Nexstar Evolution 8'}

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
BUFFER_SIZE = 1024
KEEP_ALIVE_INTERVAL = 10

def decodemsg (msg):
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
      output = sendertext + " (" + str(hex(sender)) + ") " + "-> " + receivertext + " (" + str(hex(receiver)) + ") " + "--- " + commandtext + " (" + str(hex(command)) + ") " + "--- " + str(commandvalue)
      print (output)
      if emulategps:
        global gpslat,gpslon    
        if str(hex(receiver)) == '0xb0':
          if str(hex(command)) == '0x36':
            transmitmsg(receiver,sender,command,'01')
          if str(hex(command)) == '0xfe':
            transmitmsg(receiver,sender,command,'0b01')
          if str(hex(command)) == '0x33':
            transmitmsg(receiver,sender,command,format(datetime.now(timezone.utc).hour, '02x')+format(datetime.now(timezone.utc).minute, '02x')+format(datetime.now(timezone.utc).second, '02x'))
          if str(hex(command)) == '0x3':
            transmitmsg(receiver,sender,command,format(datetime.now(timezone.utc).month, '02x')+format(datetime.now(timezone.utc).day, '02x'))
          if str(hex(command)) == '0x4':
            transmitmsg(receiver,sender,command,format(datetime.now(timezone.utc).year, '04x'))
          if str(hex(command)) == '0x37':
            transmitmsg(receiver,sender,command,'01')
          if str(hex(command)) == '0x2':
            if gpslon>=0:
                gpslonhex=format(int(gpslon/360*pow(2,24)),'06x')
            else: 
                gpslonhex=format(int((gpslon+360)/360*pow(2,24)),'06x')
            transmitmsg(receiver,sender,command,gpslonhex)
          if str(hex(command)) == '0x1':
            if gpslat>=0:
                gpslathex=format(int(gpslat/360*pow(2,24)),'06x')
            else: 
                gpslathex=format(int((gpslat+360)/360*pow(2,24)),'06x')
            transmitmsg(receiver,sender,command,gpslathex)
    else:
      print (hex(sender)," -> ", hex(receiver), "---", hex(command), "---", commandvalue, "CRC FAIL!")

def processmsgqueue():
  global msgqueue
  if len(msgqueue)>1:
    while len(msgqueue)>1 and msgqueue[0:2] != str(hex(preamble))[2:]:
      msgqueue=msgqueue[1:]
  emptyqueue=0
  while len(msgqueue)>=(2*6) and msgqueue[0:2] == str(hex(preamble))[2:] and emptyqueue==0:
    length = int(msgqueue[2:4],16)
    if len(msgqueue)>=(2*(length+3)):
      decodemsg(msgqueue[0:2*(length+3)])
      msgqueue=msgqueue[2*(length+3):]
    else:
      emptyqueue=1

def sendmsg(sender,receiver,command,value):
  global preamble
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
  decodemsg(output)
  hexoutput = binascii.unhexlify(output)
  return hexoutput

def scanauxbus(target):
  global keepalive
  print ("-----------------------")
  print ("Initiating AUXBUS SCAN ")
  print ("-----------------------")
  if target=='known':
    for device in devices:
      transmitmsg('',device,0xfe,'')
  if target=='all':
    for device in range(0x01,0xff):
      transmitmsg('',device,0xfe,'')
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
    transmitmsg('',device,0x05,'')

def printactivedevices():
  if mount in mounts:
    mounttext = mounts[mount]
  else: 
    mounttext = 'UNKNOWN' + " (" + str(hex(mount)) + ")" 
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
  

def printhelpmenu():
  print ("-----------------------")
  print ("      Commands         ")
  print ("-----------------------")
  print ("d) Show Device List    ")
  print ("c) Send Command to Device")
  print ("k) Toggle Keepalive Send")
  print ("s) Rescan AUXBUS       ")
  print ("a) Scan AUXBUS for Unknown")  
  print ("g) Toggle GPS Emulator ")
  print ("h) Print this menu     ")
  print ("q) Quit                ")
  print ("-----------------------")


def transmitmsg(sender,receiver,command,value):
    data = sendmsg(sender,receiver,command,value)
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
    while True:
        if keepalive:
            transmitmsg('',0x10,0xfe,'')
        time.sleep(interval)

def receivedata():
  global msgqueue
  data=''
  while True:
      if connmode=='wifi':
        data = sock.recv(BUFFER_SIZE)
      if connmode=='serial' or connmode=='hc':
        if (ser.inWaiting()>0):
            data = ser.read(ser.inWaiting())
            time.sleep(.05)
      if len(data)>0:
          stringdata = binascii.hexlify(data)
          msgqueue = msgqueue + str(stringdata,'utf-8')
          processmsgqueue()
          data=''

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

  connmode = connmodearg

  if connmode=='wifi': 
    SERVER_IP = port
  if connmode=='serial' or connmode=='hc':
    COM_PORT = port

  print ("-----------------------")
  print (" AUXBUS SCANNER VERSION",__version__)
  print ("-----------------------")

  initializeconn()
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
        transmitmsg('',int(listactivedevices[int(key1)],16),filtercommands[ord(key2)-97][0],'')

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
    if inputkey == "h":
        printhelpmenu()
    if inputkey == "q":
        break
    time.sleep(.1)
  closeconn()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('connmode', help='connection mode (wifi / serial / hc)')
    parser.add_argument('port', help='connection port (ip address / COM Port')
    args = parser.parse_args()
    execute_code(args.connmode, args.port)

if __name__ == '__main__':
    main()




