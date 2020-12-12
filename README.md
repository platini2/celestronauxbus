# Celestron AUXBUS Scanner

One Paragraph of project description goes here

## Getting Started

Download Python and install
Clone this repository
Install Preequisites

### Prerequisites

pip install -r requirements.txt

### Usage

python celestron.py connmode port

connmode
  wifi - Use TCP-IP connection 
  serial - Use PC port of mount
  hc - Use hand controller USB connection - Will disable the hand controller as will put it in serial passthrough mode.

port
  wifi - Use IP address of the Skyportal adapter
        AP Mode = 1.2.3.4
        Client Mode = Custom Address
  serial - COM port used by Serial port connected to PC port of the mount
  hc - COM port used by Serial port assigned to hand controller
 
