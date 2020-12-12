#!/usr/bin/env python
import sys, getopt
import socket
import time
import threading
import binascii
import serial
import keyboard
import argparse

global msgqueue
msgqueue = ''

preamble = 0x3b

devices = { 0x01 : 'Main Board / Interconnection',
            0x04 : 'Nexstar HC',
            0x0d : 'Nexstar+ HC',
            0x0e : 'Starsense HC',
            0x10 : 'AZM MC',
            0x11 : 'ALT MC', 
            0x12 : 'Focuser', 
            0x20 : 'Skyportal APP',
            0xb0 : 'GPS',
            0xb3 : 'Skyportal Accessory',
            0xb4 : 'Starsense Camera',
            0xb6 : 'Battery Power Controller',
            0xb7 : 'Charge Port',
            0xbf : 'Mount Lights'}

controllers = [ 0x04 , 0x0d , 0x0e , 0x20 ]
activedevices = []

commands = { (0x01, 0xfe) : 'MB_GET_FW_VER', 
            (0x04, 0xfe) : 'NXS_GET_FW_VER',
            (0x0d, 0xfe) : 'NXS_GET_FW_VER',
            (0x0e, 0xfe) : 'NXS_GET_FW_VER',
            (0x10, 0x01) : 'MC_GET_POSITION', 
            (0x10, 0x02) : 'MC_GOTO_FAST', 
            (0x10, 0x05) : 'MC_GET_ANGLE_DATA',
            (0x10, 0x06) : 'MC_SET_POS_GUIDERATE',
            (0x10, 0x13) : 'MC_SLEW_DONE',
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
            (0x11, 0x05) : 'MC_GET_ANGLE_DATA',
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
            (0xb4, 0xfe) : 'SS_GET_FW_VER'}

SERVER_IP = '1.2.3.4'
SERVER_PORT = 2000
BUFFER_SIZE = 1024
KEEP_ALIVE_INTERVAL = 10

def decodemsg (msg):
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
    if sender not in controllers:
       device = sender
    else:
       device = receiver
    if checksumok:
      if len(commandvalue)>0:
        if hex(command) == '0xfe':
          commandvalue = '.'.join([format(int(c, 16)) for c in commandvalue])
          if len(commandvalue)>0:
            activedevices.append(hex(sender)) if hex(sender) not in activedevices else activedevices
        else:
          commandvaluehex = ''.join([format(int(c, 16), '02x') for c in commandvalue])
          commandvalue = (int(commandvaluehex,16))
      if (device,command) in commands:
          commandtext = commands[(device,command)]
      else:
          commandtext = 'UNKNOWN'

      output = devices[sender] + " (" + str(hex(sender)) + ") " + "-> " + devices[receiver] + " (" + str(hex(receiver)) + ") " + "--- " + commandtext + " (" + str(hex(command)) + ") " + "--- " + str(commandvalue)
      print (output)
    else:
      print (hex(sender)," -> ", hex(receiver), "---", hex(command), "---", commandvalue, "CRC FAIL!")

def processmsgqueue():
  global msgqueue
  if len(msgqueue)>1:
    while msgqueue[0:2] != str(hex(preamble))[2:]:
      msgqueue=msgqueue[2:]
  emptyqueue=0
  while len(msgqueue)>=(2*6) and emptyqueue==0:
    length = int(msgqueue[2:4],16)
    if len(msgqueue)>=(2*(length+3)):
      decodemsg(msgqueue[0:2*(length+3)])
      msgqueue=msgqueue[2*(length+3):]
    else:
      emptyqueue=1

def sendmsg(receiver,command):
  global preamble
  if connmode=='wifi' or connmode=='hc' :
      sender = 0x20
  if connmode=='serial':
      sender = 0x04
  length = 3
  sum = length + sender + receiver + command
  sum=65536-sum
  sum=sum&255
  output = "{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}".format(preamble,length,sender,receiver,command,sum)
  decodemsg(output)
  hexoutput = binascii.unhexlify(output)
  return hexoutput

def scanauxbus(interval):
  global keepalive
  print ("-----------------------")
  print ("Initiating AUXBUS SCAN ")
  print ("-----------------------")
  for device in devices:
    transmitmsg(device,0xfe)
  print ("-----------------------")
  print (" Finished AUXBUS SCAN  ")
  print ("-----------------------")
  printactivedevices()
  print ("-----------------------")
  print ("Starting AUXBUS Monitor")
  print ("-----------------------")
  printhelpmenu()
  if connmode=="wifi":
    keepalive=True

def printactivedevices():
  print ("-----------------------")
  print ("   Detected Devices    ")
  print ("-----------------------")
  for device in activedevices:
    output = str(activedevices.index(device))+ ") " + devices[int(device,16)] + " (" + str(device) + ") "
    print (output)

def printhelpmenu():
  print ("-----------------------")
  print ("      Commands         ")
  print ("-----------------------")
  print ("d) Show Device List    ")
  print ("c) Send Command to Device")
  print ("k) Toggle Keepalive Send")
  print ("x) Disable Keyboard Input")
  print ("h) Print this menu     ")
  print ("q) Quit                ")
  print ("-----------------------")


def transmitmsg(receiver,command):
    data = sendmsg(receiver,command)
    if connmode == 'wifi':
        sock.send(data)
    if connmode == 'serial' or connmode=='hc':
        ser.rts=True
        ser.write(data)
        ser.rts=False
        ser.rts=True
        ser.rts=False
    time.sleep(0.25)

def keep_alive(interval):
    while True:
        if keepalive:
            transmitmsg(0x10,0xfe)
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

    t1 = threading.Thread(target=scanauxbus, args = (1,))
    t1.start()
        
    t2 = threading.Thread(target=keep_alive, args = (KEEP_ALIVE_INTERVAL,))
    t2.daemon = True
    t2.start()


def execute_code(connmodearg, port):
  global connmode
  global SERVER_IP, COM_PORT
  global keepalive

  connmode = connmodearg

  if connmode=='wifi': 
    SERVER_IP = port
  if connmode=='serial' or connmode=='hc':
    COM_PORT = port

  initializeconn()
  launchthreads()

  while True:
    if keyboard.read_key() == "d":
        printactivedevices()

    if keyboard.read_key() == "c":
        printactivedevices()
        time.sleep(0.2)
        print ("-----------------------")
        print ("Choose device")
        key1 = keyboard.read_key()
        filtercommands=[(k[1], v) for k, v in commands.items() if k[0]==int(activedevices[int(key1)],16)]
        for command in filtercommands:
            output = chr(97+filtercommands.index(command)) + ") " + str(hex(command[0])) + " (" + str(command[1]) + ") "
            print (output)
        time.sleep(0.2)
        print ("-----------------------")
        print ("Choose command")
        key2 = keyboard.read_key()
        transmitmsg(int(activedevices[int(key1)],16),filtercommands[ord(key2)-97][0])

    if keyboard.read_key() == "x":
        print ("-----------------------")
        print ("   Key Input Disable   ")
        print ("  Press y to Reenable  ")
        print ("-----------------------")
        while (keyboard.read_key() != "y"):
            True
        print ("-----------------------")
        print ("   Key Input Enabled   ")
        print ("-----------------------")
    if keyboard.read_key() == "k":
        print ("-----------------------")
        print ("   Toggle Keepalive    ")
        print ("-----------------------")
        if keepalive:
            keepalive=False
            print ("   Keepalive Disabled    ")
        else:
            keepalive=True
            print ("   Keepalive Enabled    ")
    if keyboard.read_key() == "h":
        printhelpmenu()
    if keyboard.read_key() == "q":
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

