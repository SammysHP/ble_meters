#!/usr/bin/env python

import bleak
from bleak import BleakClient
from bleak import BleakScanner
import asyncio
import datetime
import queue
import threading
import time
import argparse, configparser
import csv
import sys, os
import math
import re
from collections import defaultdict
from collections import namedtuple
import shutil

# this list is only used for autodetection
known_devices = [
    {'prefix': '98:7B:F3:', 'name': 'bde spp dev', 'decoder': 'TS04'},
    {'prefix': '01:B4:05:', 'name': 'FS9721-LP3', 'decoder': 'HP90EPD'},
    {'prefix': 'FC:58:FA:', 'name': 'Bluetooth DMM', 'decoder': 'AN9002'},
    {'prefix': '20:91:48:', 'name': 'UT383BT', 'decoder': 'UT383BT'},
    {'prefix': 'E8:D0:3C:', 'name': 'UT383BT', 'decoder': 'UT383BT'},
    {'prefix': '7C:01:0A:', 'name': 'LuxMeter', 'decoder': 'WT81B'},
    {'prefix': '48:7E:48:', 'name': 'TP357 (*', 'decoder': 'TP357'},
    {'prefix': '86:28:A9:', 'name': 'ToolSmart-AngleFinder', 'decoder': 'TS02'},
    {'prefix': 'BB:DD:55:', 'name': 'Gotobake*', 'decoder': 'K1705'},
    {'prefix': '01:BC:EC:', 'name': '980F', 'decoder': 'BT980D'},
    {'prefix': '01:BC:EC:', 'name': 'AiLink_*', 'decoder': 'BT7200_APP'},
    {'prefix': '07:B4:EC:', 'name': 'SWAN', 'decoder': 'BT985C_APP'},
]

Device = namedtuple('Device', 'd decoder model')

class LCD_Decoder(object):
    def __init__(self):
        self.model = ''
        self.notify_uuid = None
        self.init_msg = None
        self.poll_msg = None
        self.stop_msg = None
        self.flip_bits = []
        self.flags = []
        self.segments = {}
        self.strings = {}
        self.mode_strings = {}
        self.scaling = {
            'negative': -1,
            'positive':  1,
            '/1000':  0.001,
            '/100':  0.01,
            '/10':  0.1,
            'kilo': 1000,
            'mega': 1e6,
            'milli': 0.001,
            'micro': 1e-6,
            'nano': 1e-9,
            'x10': 10,
            'x100': 100,
        }
    def decode_digits(self, data):
        pass
    def decode_lcd(self, data):
        data = list(data)
        lcd = {}
        for flag,byte,bit in self.flags:
            if data[byte] & (1<<bit):
                lcd[flag] = True
        lcd['digits'] = self.decode_digits(data)
        if lcd['digits'] in self.mode_strings:
            flag = self.mode_strings[lcd['digits']]
            lcd[flag] = True
        return lcd
    def lcd_to_number(self, lcd):
        if lcd['digits'] in self.strings:
            return self.strings[lcd['digits']]
        n = int(lcd['digits'], 10)
        for flag,x in self.scaling.items():
            if flag in lcd:
                n *= x
        if '(overload)' in lcd:
            return float('inf')
        return n
    def lcd_to_units(self, lcd):
        modes = ['DC', 'AC', 'volts', 'amps', 'ohms', 'NCV', 'diode', 'continuity', 'celsius', 'fahrenheit', 'farads', 'hertz', '%duty', 'lux', 'fc', 'degrees', '%RH', 'grams', '(auto)', '(hold)', '(relative)', '(maximum)', '(minimum)', '(low_batt)']
        return ' '.join(m for m in modes if m in lcd)
    def decode(self, data):
        lcd = self.decode_lcd(data)
        return [(lcd, self.lcd_to_number(lcd), self.lcd_to_units(lcd))]
    def match(self, data, pattern):
        if len(pattern) != len(data):
            return False
        for p,d in zip(pattern, data):
            if p == '.':
                continue
            if p != d:
                return False
        return True
    def match2(self, data, pattern):
        pattern = pattern.replace(' ', '')
        if len(pattern) != len(data)*2:
            return False
        for i,d in enumerate(data):
            d1 = (d & 0xF0) >> 4
            p1 = pattern[i*2]
            if p1 != '.' and int(p1, 16) != d1:
                return False
            d2 = (d & 0x0F)
            p2 = pattern[i*2+1]
            if p2 != '.' and int(p2, 16) != d2:
                return False
        return True

class Dummy_Decoder(LCD_Decoder):
    def __init__(self):
        super().__init__()
        self.model = 'dummy'
        self.hide_known = True
    def binary(self, data):
        return ' '.join('{0:08b}'.format(x) for x in data)
    def hex(self, data):
        return ' '.join('0x%02X' % x for x in data)
    def unknown_binary(self, data):
        bits = self.binary(data)
        bits = list(bits)
        for flag,byte,bit in self.flags:
            x = 9 * byte + (7-bit)
            bits[x] = '_'
        return ''.join(bits)
    def decode(self, data):
        for i,x in enumerate(self.flip_bits):
            data[i] ^= x
        lcd = self.decode_lcd(data)
        lcd['dummy'] = True
        if self.hide_known:
            bits = self.unknown_binary(data)
        else:
            bits = self.binary(data)
            #bits = self.hex(data)
        return [(lcd, bits, ' '.join(set(lcd) - set(['digits'])))]

class TS04_Decoder(LCD_Decoder):
    def __init__(self):
        super().__init__()
        self.model = 'TS04'
        self.notify_uuid = "0000{0:x}-0000-1000-8000-00805f9b34fb".format(0xFFB2)
        self.flags = [
            ('negative', 1, 4),  # name, byte, bit  
            ('(auto)', 1, 2),
            ('DC', 1, 1),
            ('AC', 1, 0),
            ('/1000', 2, 4),
            ('/100', 3, 4),
            ('/10', 4, 4),
            ('diode', 5, 7),
            ('kilo', 5, 6),
            ('micro', 5, 4),
            ('(hold)', 6, 7),
            ('ohms', 6, 5),
            ('continuity', 6, 3),
            ('mega', 6, 2),
            ('milli', 6, 0),
            ('NCV', 7, 7),
            ('bluetooth', 7, 6),
            ('celsius', 7, 5),
            ('fahrenheit', 7, 4),
            ('(low_batt)', 7, 3),
            ('volts', 7, 1),
            ('amps', 7, 0),
            ('auto_off', 8, 0),
        ]
        self.segments = {
            0b00000000: ' ',
            0b11101011: '0',
            0b00001010: '1',
            0b10101101: '2',
            0b10001111: '3',
            0b01001110: '4',
            0b11000111: '5',
            0b11100111: '6',
            0b10001010: '7',
            0b11101111: '8',
            0b11001111: '9',
            0b01100001: 'L',
            0b11100101: 'E',
            0b11100100: 'F',
            0b00000100: '-',
        }
        self.strings = {
            '    ': '?',
            ' EF ': 0,
            '   -': 1,
            '  --': 2,
            ' ---': 3,
            '----': 4,
            ' 0L ': float('inf'),
        }
    def merge_digit(self, byte1, byte2):
        return self.segments[byte1 & 0b11100000 | byte2 & 0b1111]
    def decode_digits(self, data):
        digit1 = self.merge_digit(data[1], data[2])
        digit2 = self.merge_digit(data[2], data[3])
        digit3 = self.merge_digit(data[3], data[4])
        digit4 = self.merge_digit(data[4], data[5])
        return digit1 + digit2 + digit3 + digit4
    def decode(self, data):
        if data == b'SPP:sendData 08\\s\\n\\':
            return [(None, None, None)]
        if len(data) != 9:
            return [(None, None, None)]
        lcd = self.decode_lcd(data)
        return [(lcd, self.lcd_to_number(lcd), self.lcd_to_units(lcd))]

class HP90EPD_Decoder(LCD_Decoder):
    def __init__(self):
        super().__init__()
        self.model = 'HP90EPD'
        self.notify_uuid = "0000{0:x}-0000-1000-8000-00805f9b34fb".format(0xFFB2)
        self.buffer = []
        # lcd has hFE but its unused
        self.flags = [
            ('(auto)', 0, 1),  # name, byte, bit
            ('AC', 0, 3),
            ('(hold)', 11, 0),
            ('mega', 10, 1),
            ('kilo', 9, 1),
            ('milli', 10, 3),
            ('micro', 9, 3),
            ('nano', 9, 2),
            ('diode', 9, 0),
            ('continuity', 10, 0),
            ('%duty', 10, 2),
            ('(relative)', 11, 1),
            ('ohms', 11, 2),
            ('farads', 11, 3),
            ('hertz', 12, 1),
            ('volts', 12, 2),
            ('amps', 12, 3),
            ('celsius', 13, 2),
            ('negative', 1, 3),
            ('/1000', 3, 3),
            ('/100', 5, 3),
            ('/10', 7, 3),
            ('(low_batt)', 12, 0),
            ('mystery_1', 0, 2),
            ('mystery_2', 13, 0),
        ]
        self.segments = {
            0b0000000: ' ',
            0b1111101: '0',
            0b0000101: '1',
            0b1011011: '2',
            0b0011111: '3',
            0b0100111: '4',
            0b0111110: '5',
            0b1111110: '6',
            0b0010101: '7',
            0b1111111: '8',
            0b0111111: '9',
            0b1101000: 'L',
        }
        self.strings = {
            '    ': '?',
            ' 0L ': float('inf'),
        }
    def merge_digit(self, byte1, byte2):
        # lo left      hi left       top       bottom       lo right        center        hi right
        return self.segments[(byte1 & 0b111) << 4 | (byte2 & 0b1111)]
    def decode_digits(self, data):
        digit1 = self.merge_digit(data[1], data[2])
        digit2 = self.merge_digit(data[3], data[4])
        digit3 = self.merge_digit(data[5], data[6])
        digit4 = self.merge_digit(data[7], data[8])
        return digit1 + digit2 + digit3 + digit4
    def decode(self, data):
        if len(data) == 8:
            self.buffer = data
            return [(None, None, None)]
        if len(data) == 6 and len(self.buffer) == 8:
            data = self.buffer + data
        else:
            self.buffer = []
            return None, None, None
        lcd = self.decode_lcd(data)
        if 'volts' in lcd or 'amps' in lcd:
            if 'AC' not in lcd:
                lcd['DC'] = True
        self.buffer = []
        return [(lcd, self.lcd_to_number(lcd), self.lcd_to_units(lcd))]

class AN9002_Decoder(LCD_Decoder):
    def __init__(self):
        super().__init__()
        self.model = 'AN9002'
        self.notify_uuid = "0000{0:x}-0000-1000-8000-00805f9b34fb".format(0xFFF4)
        self.flip_bits = [0x1B,0x84,0x70,0x55,0xA2,0xC1,0x32,0x71,0x66,0xAA,0x3B]
        self.flags = [
            ('(auto)', 10, 0),  # name, byte, bit
            ('/1000', 4, 4),
            ('/100', 5, 4),
            ('/10', 6, 4),
            ('(relative)', 3, 1),
            ('(maximum)', 8, 0),
            ('(minimum)', 8, 1),
            ('AC', 8, 3),
            ('DC', 9, 6),
            ('hertz', 9, 0),
            ('%duty', 8, 2),
            ('(hold)', 7, 4),
            ('milli', 9, 5),  # mV
            ('negative', 3, 4),
            ('celsius', 7, 6),
            ('fahrenheit', 7, 5),
            ('volts', 9, 4),
            ('ohms', 9, 1),
            ('mega', 9, 3),  # M ohm
            ('kilo', 9, 2),  # k ohm
            ('farads', 8, 4),
            ('nano', 8, 7),  # nF
            ('micro', 8, 5),  # uF
            ('milli', 8, 6),  # mF
            ('amps', 9, 7),
            ('milli', 10, 3),  # mA
            ('micro', 10, 2),  # uA
            ('diode', 7, 7),
            ('continuity', 3, 3),
            ('(low_batt)', 3, 0),
        ]
        self.segments = dict(TS04_Decoder().segments)
        self.segments.update({
            0b11101110: 'A',
            0b00100011: 'u',
            0b01100101: 't',
            0b00100111: 'o',
        })
        self.strings = {
            'Auto': '?',
            '    ': '?',
            ' EF ': 0,
            '-   ': 1,
            '--  ': 2,
            '--- ': 3,
            '----': 4,
            ' 0L ': float('inf'),
        }
        self.mode_strings = {
            ' EF ': 'NCV',
            '-   ': 'NCV',
            '--  ': 'NCV',
            '--- ': 'NCV',
            '----': 'NCV',
        }
    def merge_digit(self, byte1, byte2):
        x = byte1 & 0b11100000 | byte2 & 0b1111
        return self.segments[byte1 & 0b11100000 | byte2 & 0b1111]
    def decode_digits(self, data):
        digit1 = self.merge_digit(data[3], data[4])
        digit2 = self.merge_digit(data[4], data[5])
        digit3 = self.merge_digit(data[5], data[6])
        digit4 = self.merge_digit(data[6], data[7])
        return digit1 + digit2 + digit3 + digit4
    def decode(self, data):
        if len(data) != 11:
            return [(None, None, None)]
        # bytes [0:2] are constant?
        for i,x in enumerate(self.flip_bits):
            data[i] ^= x
        lcd = self.decode_lcd(data)
        return [(lcd, self.lcd_to_number(lcd), self.lcd_to_units(lcd))]

class V05B_Decoder(AN9002_Decoder):
    def __init__(self):
        super().__init__()
        self.model = 'V05B'
        self.flip_bits = self.flip_bits[:10]
        self.flags = [
            ('/1000', 4, 4),
            ('/100', 5, 4),
            ('/10', 6, 4),
            ('AC', 8, 3),
            ('DC', 8, 2),
            ('hertz', 9, 5),
            ('(hold)', 3, 1),
            ('high_volt', 3, 2),
            ('buzzer', 3, 3),
            ('negative', 3, 4),
            ('celsius', 9, 7),
            ('fahrenheit', 9, 6),
            ('volts', 8, 1),
            ('ohms', 9, 0),
            ('mega', 9, 3),  # M ohm
            ('kilo', 9, 1),  # k ohm
            ('farads', 8, 4),
            ('nano', 8, 0),
            ('micro', 8, 7),
            ('milli', 9, 2),
            ('amps', 8, 6),
            ('diode', 8, 5),
            # auto_off?  low_batt?  continuity?  %duty?
        ]
    def decode(self, data):
        if len(data) != 10:
            return [(None, None, None)]
        for i,x in enumerate(self.flip_bits):
            data[i] ^= x
        lcd = self.decode_lcd(data)
        #lcd['auto'] = True
        return [(lcd, self.lcd_to_number(lcd), self.lcd_to_units(lcd))]

class WT81B_Decoder(LCD_Decoder):
    def __init__(self):
        super().__init__()
        self.model = 'WT81B'
        self.notify_uuid = "0000{0:x}-0000-1000-8000-00805f9b34fb".format(0xFF02)
        self.poll_msg = {'uuid': "0000{0:x}-0000-1000-8000-00805f9b34fb".format(0xFF01), 'payload': [0x57, 0x48, 0x01], 'sleep':0.5}
        self.flags = [
            ('x100', 3, 1),  # name, byte, bit
            ('x10', 3, 0),
        ]
        # missing flags: rec read del bt auto-off bat-0/1/2/3 hold max min delta hi-lum lo-lum neg-temp backlight
    def decode_lcd(self, data):
        data = list(data)
        lcd = {}
        for flag,byte,bit in self.flags:
            if data[byte] & (1<<bit):
                lcd[flag] = True
        lcd['temperature'] = ((data[4] << 8) | data[5]) / 10  # what about below 0?
        lcd['lux'] = ((data[6] << 8) | data[7]) / 10
        if 'x10' in lcd:
            lcd['lux'] *= 10
        if 'x100' in lcd:
            lcd['lux'] *= 100
        # OL = 0x0E16 x1000
        if lcd['lux'] == 360600:
            lcd['lux'] = float('inf')
        return lcd
    def decode(self, data):
        data = list(data)
        if not self.match(data, [0xFF, 0x57, 0x4C, '.', '.', '.', '.', '.']) or data[3] > 3:
            print('WARNING: unrecognized', self.model, 'data', ' '.join('0x%02X' % n for n in data)) 
            return [(None, None, None)]
        lcd = self.decode_lcd(data)
        return [(lcd, lcd['lux'], 'lux'),
                (lcd, lcd['temperature'], 'celsius')]

class UT383BT_Decoder(LCD_Decoder):
    def __init__(self):
        super().__init__()
        self.model = 'UT383BT'
        self.notify_uuid = "0000{0:x}-0000-1000-8000-00805f9b34fb".format(0xFF02)
        self.poll_msg = {'uuid': "0000{0:x}-0000-1000-8000-00805f9b34fb".format(0xFF01), 'payload': [0x5E], 'sleep':0.5}
        self.flags = [
            ('(hold)', 16, 0),  # name, byte, bit
            ('(maximum)', 16, 3),
            ('(minimum)', 16, 2),
            #('lux', 14, 1),
            #('fc', 14, 2),  # the reported number is still lux despite the on-screen unit
            ('(low_batt)', 16, 6),
        ]
        self.strings = {
            '    OL': float('inf'),
        }
        # missing flags: auto_off
    def decode(self, data):
        data = list(data)
        if not self.match(data, [0xAA, 0xBB, 0x10, 0x01, 0x3A, '.', '.', '.', '.', '.', '.', 0x4C, 0x55, 0x58, '.', 0x30, '.', '.', '.']):
            print('WARNING: unrecognized', self.model, 'data', ' '.join('0x%02X' % n for n in data)) 
            return [(None, None, None)]
        lcd = self.decode_lcd(data)
        lcd['lux'] = True
        lcd['digits'] = bytes(data[5:11]).decode('ascii')
        return [(lcd, self.lcd_to_number(lcd), self.lcd_to_units(lcd))]

class TP357_Decoder(LCD_Decoder):
    def __init__(self):
        super().__init__()
        self.model = 'TP357'
        self.notify_uuid = '00010203-0405-0607-0809-0a0b0c0d{0:x}'.format(0x2B10)
        self.flags = [
            ('(???)', 2, 0),  # name, byte, bit
        ]
        # missing flags: low_batt comfort
    def decode_lcd(self, data):
        data = list(data)
        lcd = {}
        for flag,byte,bit in self.flags:
            if data[byte] & (1<<bit):
                lcd[flag] = True
        temp = (data[4] << 8) | data[3]
        if temp & 0x8000: 
            temp = n - 0x10000
        lcd['temperature'] = temp / 10
        lcd['humidity'] = data[5]
        return lcd
    def decode(self, data):
        data = list(data)
        if not self.match(data, [0xC2, 0x00, '.', '.', '.', '.', 0x2C]) or data[2] > 1:
            print('WARNING: unrecognized', self.model, 'data', ' '.join('0x%02X' % n for n in data)) 
            return [(None, None, None)]
        lcd = self.decode_lcd(data)
        return [(lcd, lcd['temperature'], 'celsius'),
                (lcd, lcd['humidity'], '%RH')]

class TS02_Decoder(LCD_Decoder):
    def __init__(self):
        super().__init__()
        self.model = 'TS02'
        self.notify_uuid = "0783b03e-8535-b5a0-7140-a304d249{0:x}".format(0x5cb8)
        self.poll_msg = {'uuid': "0783b03e-8535-b5a0-7140-a304d249{0:x}".format(0x5cb9), 'payload': [0x00, 0x00], 'sleep':1.0}
        # 5cb8   notify "Server TX Data"
        # 5cba   write "Server RX Data"
        # 5cb9   read/write/notify "Flow Control"
        self.flags = [
            ('negative', 0, 2),  # name, byte, bit
            ('positive', 0, 1),
        ]
        # low battery?
    def check(self, data):
        if data[0] & 0b11111001 != 0b00101001:
            return False
        if data[1] & 0xF0 != 0x30:
            return False
        if data[2] & 0xF0 != 0x30:
            return False
        if data[3] & 0xF0 != 0x30:
            return False
        if data[4] & 0xF0 != 0x30:
            return False
        if data[5] != 0x30:
            return False
        return True
    def decode_digits(self, data):
        # binary coded decimal
        digit1 = str(data[1] & 0x0F)
        digit2 = str(data[2] & 0x0F)
        digit3 = str(data[3] & 0x0F)
        digit4 = str(data[4] & 0x0F)
        return digit1 + digit2 + digit3 + digit4
    def decode(self, data):
        data = list(data)
        if not self.check(data):
            print('WARNING: unrecognized', self.model, 'data', ' '.join('0x%02X' % n for n in data)) 
            return [(None, None, None)]
        lcd = self.decode_lcd(data)
        lcd['degrees'] = True
        lcd['/10'] = True
        return [(lcd, self.lcd_to_number(lcd), self.lcd_to_units(lcd))]

class K1705_Decoder(LCD_Decoder):
    def __init__(self):
        super().__init__()
        self.model = 'K1705'
        self.notify_uuid = "0000{0:x}-0000-1000-8000-00805f9b34fb".format(0xfff1)
        self.flags = [
            ('(overload)', 10, 7),  # name, byte, bit  
            ('negative', 10, 4),
        ]
        # low battery?
    def decode_digits(self, data):
        n = (data[11] << 16) + (data[12] << 8) + data[13]
        return str(n)  # stupid
    def decode(self, data):
        data = list(data)
        if len(data) == 128:
            return [(None, None, None)]
        if not self.match(data, [0xA3, 0xBE, 0x15, 0x92, 0x93, 0, 0, 0xA0, 0, 0, '.', '.', '.', '.', 0xFF, 0x3E, 0xBA]):
            print('WARNING: unrecognized', self.model, 'data', ' '.join('0x%02X' % n for n in data)) 
            return [(None, None, None)]
        lcd = self.decode_lcd(data)
        lcd['grams'] = True
        lcd['/100'] = True
        return [(lcd, self.lcd_to_number(lcd), self.lcd_to_units(lcd))]

class BT980D_Decoder(LCD_Decoder):
    def __init__(self):
        super().__init__()
        self.model = 'BT980D'
        self.notify_uuid = "0000{0:x}-0000-1000-8000-00805f9b34fb".format(0xffe2)
        #self.init_msg = {'uuid': "0000{0:x}-0000-1000-8000-00805f9b34fb".format(0xffe1), 'payload': self.build_message([3, 1]), 'sleep':1.0}
        self.poll_msg = {'uuid': "0000{0:x}-0000-1000-8000-00805f9b34fb".format(0xffe1), 'payload': self.build_message([3, 1]), 'sleep':1.0}
        self.flags = [
            ('laser', 5, 2),  # name, byte, bit  
            ('celsius', 5, 0),
            ('fahrenheit', 5, 1),
            ('backlight', 5, 3,)
        ]
        # batt scan [H] BT laser H L C F temperature LAL MAX HAL AVG MEM E MIN NO emissivity
        # auto-off?
    def build_message(self, data):
        length = len(data)
        checksum = (0x20 + length + sum(data)) & 0xFF
        return [0xA7, 0, 0x20, length] + list(data) + [checksum, 0x7A]
    def decode(self, data):
        data = list(data)
        if self.match(data, [0xA7, 0x00, 0x20, 0x07, 0x85, 0x7D, 0x43, 0x33, 0x48, 0xDE, 0x70, 0x35, 0x7A]):
            return [(None, None, None)]
        if not self.match(data, [0xA7, 0x00, 0x20, 0x0B, 0x8D, '.', '.', 0xC9, '.', '.', 0x8F, '.', '.', 0xCC, 0xBD, '.', 0x7A]):
            print('WARNING: unrecognized', self.model, 'data', ' '.join('0x%02X' % n for n in data)) 
            return [(None, None, None)]
        lcd = self.decode_lcd(data)
        return [(lcd, Dummy_Decoder().hex(data), ' '.join(sorted(list(set(lcd) - set(['digits'])))))]

class BT7200_APP_Decoder(LCD_Decoder):
    def __init__(self):
        super().__init__()
        self.model = 'BT7200_APP'
        self.notify_uuid = "0000{0:x}-0000-1000-8000-00805f9b34fb".format(0xffe2)
        #self.init_msg = {'uuid': "0000{0:x}-0000-1000-8000-00805f9b34fb".format(0xffe1), 'payload': self.build_message([3, 1]), 'sleep':1.0}
        #self.poll_msg = {'uuid': "0000{0:x}-0000-1000-8000-00805f9b34fb".format(0xffe1), 'payload': [171, 205, 6], 'sleep':1.0, 'response':False}
        self.poll_msg = {'uuid': "0000{0:x}-0000-1000-8000-00805f9b34fb".format(0xffe1), 'payload': [13, 151], 'sleep':1.0, 'response':False}
        # brute force found "(13, 151) 81" but doesn't work?
        self.flags = [
            ('(hold)', 11, 3),  # name, byte, bit
            ('(auto)', 0, 2),
            ('(minimum)', 14, 1),
            ('(maximum)', 14, 3),
            ('(relative)', 11, 2),
            ('(low_batt)', 12, 3),
            ('diode', 9, 3),
            ('continuity', 10, 3),
            ('/1000', 3, 0),
            ('/100', 5, 0),
            ('/10', 7, 0),
            ('negative', 1, 0),
            ('milli', 10, 0),
            ('mega', 10, 2),
            ('DC', 0, 1),
            ('AC', 0, 0),
            ('ohms', 11, 1),
            ('hertz', 12, 2),
            ('%duty', 10, 1),
            ('celsius', 13, 1),
            ('fahrenheit', 13, 0),
            ('NCV', 13, 3),
            ('amps', 12, 0),
            ('volts', 12, 1),
        ]
        # there is no auto-off?
        # no flag for the backlight
        # todo: farads, nano, micro, kilo, auto-off, overload
        self.segments = dict(TS04_Decoder().segments)
        self.strings = dict(AN9002_Decoder().strings)
    def merge_digit(self, byte1, byte2):
        return self.segments[((byte1 & 0b1110)<<4) | byte2 & 0b1111]
    def decode_digits(self, data):
        digit1 = self.merge_digit(data[1], data[2])
        digit2 = self.merge_digit(data[3], data[4])
        digit3 = self.merge_digit(data[5], data[6])
        digit4 = self.merge_digit(data[7], data[8])
        return digit1 + digit2 + digit3 + digit4
    def decode(self, data):
        data = list(data)
        # it gets sloppy with blocks of data
        # attempt to recover
        if self.match2(data, '1.2.3.4.5.6.7.8.9.A.B.C.D.E.'):
            data.append(0xF0)
        if self.match2(data, 'F.1.2.3.4.5.6.7.8.9.A.B.C.D.E.F.'):
            data = data[1:]
        if not self.match2(data, '1.2.3.4.5.6.7.8.9.A.B.C.D.E.F.'):
            print('WARNING: unrecognized', self.model, 'data', ' '.join('0x%02X' % n for n in data)) 
            return [(None, None, None)]
        lcd = self.decode_lcd(data)
        #return [(lcd, Dummy_Decoder().hex(data), ' '.join(sorted(list(set(lcd) - set(['digits'])))))]
        return [(lcd, self.lcd_to_number(lcd), self.lcd_to_units(lcd))]

class BT985C_APP_Decoder(LCD_Decoder):
    def __init__(self):
        super().__init__()
        self.model = 'BT985C_APP'
        self.commands = {'up':1, 'down':2, 'mode':4, 'mem':8, 'unit':16,
            'rate':32, 'stop':33, 'off':64, 'emissivity':80}
        # brute force scan for other commands?
        btn_boot = [256-84,256-1,256-2, 21, 1, 0,256-52,256-32]  # why is this checksum off by one?
        self.notify_uuid = "0000{0:x}-0000-1000-8000-00805f9b34fb".format(0xffb2)
        self.init_msg = {'uuid': "0000{0:x}-0000-1000-8000-00805f9b34fb".format(0xffb1), 'payload': self.message('rate', 0), 'sleep':0.5}
        #self.init_msg = {'uuid': "0000{0:x}-0000-1000-8000-00805f9b34fb".format(0xffb1), 'payload': btn_boot, 'sleep':0.5}
        self.poll_msg = {'uuid': "0000{0:x}-0000-1000-8000-00805f9b34fb".format(0xffb1), 'payload': self.message('rate', 0), 'sleep':5}
        #self.stop_msg = {'uuid': "0000{0:x}-0000-1000-8000-00805f9b34fb".format(0xffb1), 'payload': self.message('stop'), 'sleep':0.1}
        self.stop_msg = {'uuid': "0000{0:x}-0000-1000-8000-00805f9b34fb".format(0xffb1), 'payload': self.message('off'), 'sleep':0.1}
        self.flags = [
            ('fahrenheit', 6, 6),  # name, byte, bit
            ('(scan)', 6, 0),
            ('(memory)', 6, 1),
            ('(laser)', 6, 2),
            ('(backlight)', 6, 3),
            ('(low_batt)', 6, 4),
        ]
        # auto-off?
        # sends data on every button press!  sometimes two packets are concatenated
        # writing data into ffb1 causes the button to happen, also sends data matching as if the button were pressed?
        # ... it won't stop sampling after BLE disconnect, need to send a shutdown message
        # rate of 10 = every 5 seconds
        # rate of 20 = every 9 seconds
        # rate of 0 = every 0.65 seconds
    def message(self, command, value=0):
        command = self.commands[command]
        message = [0xBC, command, (value>>8) & 0xFF, value & 0xFF]
        message.append(sum(message[1:]) & 0xFF)
        return message
    def _16bit_temperature(self, b1, b2):
        t = b1 + (b2<<8)
        if b2 & 0x80:
            t -= 2**16
        return t / 10.0
    def decode_lcd(self, data):
        data = list(data)
        lcd = {}
        for flag,byte,bit in self.flags:
            if data[byte] & (1<<bit):
                lcd[flag] = True
        if 'fahrenheit' not in lcd:
            lcd['celsius'] = True
        if '(scan)' not in lcd:
            lcd['(hold)'] = True
        mode_table = {0:'max_celsius', 1:'avg_celsius', 2:'min_celsius',
                      3:'low_alarm_celsius', 4:'high_alarm_celsius', 5:'ε'}
        mode = data[1]
        if mode in [0, 1, 2, 3, 4]:
            temp2 = self._16bit_temperature(data[2], data[3])
            lcd['minor_reading'] = temp2
        if mode == 5:
            lcd['minor_reading'] = data[3] / 100
        lcd['minor_unit'] = mode_table[mode]
        lcd['temperature'] = self._16bit_temperature(data[4], data[5])
        # what about memory stuff?
        return lcd
    def decode(self, data):
        data = list(data)
        if not self.match2(data, 'BC 0. .. .. .. .. .. ..'):
            print('WARNING: unrecognized', self.model, 'data', ' '.join('0x%02X' % n for n in data)) 
            return [(None, None, None)]
        lcd = self.decode_lcd(data)
        #return [(lcd, Dummy_Decoder().hex(data), ' '.join(sorted(list(set(lcd) - set(['digits'])))))]
        # temperature unit is cosmetic
        # always reports in C
        return [(lcd, lcd['minor_reading'], lcd['minor_unit']),
                (lcd, lcd['temperature'], 'celsius')]
        # something is wonky and it occasionally locks up after connecting?
        # might be missing an important message


class BLE_Session(object):
    def __init__(self, message_queue=None):
        self.devices = {}
        self.messages = message_queue
        if self.messages is None:
            self.messages = queue.Queue()
        self._thread = None
        self._dbus_lock = asyncio.Lock()
        self.running = threading.Lock()
        self.running.acquire()
        self.last_flush = datetime.datetime.now(datetime.UTC)
        self.live_report = False
        self.live_count = defaultdict(int)
        self.start_time = None
        self.last_messages = {}
        self.recycle = set()
    def is_running(self):
        return self.running.locked()
    def register_device(self, address, notify_uuid, decode=None, callback=None, poll_msg=None, init_msg=None, stop_msg=None, alias=None, recycle=False):
        if decode is None:
            decode = lambda x: x
        if callback is None:
            callback = lambda s, d: self._message_callback(address, s, d)
        self.devices[address] = {'uuid':notify_uuid, 'cb':callback, 'decode':decode, 'client':None, 'alias':alias, 'lastseen':0}
        if poll_msg:
            self.devices[address]['poll_msg'] = poll_msg
        if init_msg:
            self.devices[address]['init_msg'] = init_msg
        if stop_msg:
            self.devices[address]['stop_msg'] = stop_msg
        if self.recycle:
            self.recycle.add(address)
    async def _poll_device(self, client, d):
        poll = d['poll_msg']
        delay_till = time.time() + poll['sleep']
        while self.is_running():
            await asyncio.sleep(0.1)  # hard cap at 10/sec
            waiting = delay_till - time.time()
            if waiting > 0.1:
                continue
            if waiting > 0:
                await asyncio.sleep(waiting)
            # does this need a dbus_lock?
            rep = 'response' in poll and poll['response']
            await client.write_gatt_char(poll['uuid'], poll['payload'], response=rep)
            delay_till += poll['sleep']
    async def _connect_to_device(self, address):
        d = self.devices[address]
        await self._dbus_lock.acquire()
        if not self.is_running():
            self._dbus_lock.release()
            return
        try:
            async with BleakClient(address, timeout=20) as client:
                await client.start_notify(d['uuid'], d['cb'])
                await asyncio.sleep(0.5)
                self._dbus_lock.release()
                if 'init_msg' in d:
                    rep = 'response' in d['init_msg'] and d['init_msg']['response']
                    await client.write_gatt_char(d['init_msg']['uuid'], d['init_msg']['payload'], response=rep)
                    await asyncio.sleep(d['init_msg']['sleep'])
                if 'poll_msg' in d:
                    #await client.start_notify(d['poll_msg']['uuid'], d['cb'])
                    await self._poll_device(client, d)
                while self.is_running():
                    await asyncio.sleep(0.1)
                    if self.devices[address]['lastseen'] != 0 and (datetime.datetime.now(datetime.UTC) - self.devices[address]['lastseen']).total_seconds() > 2:
                        self.devices[address]['lastseen'] = 0
                        raise asyncio.exceptions.TimeoutError("Lost connection to device")
                if 'stop_msg' in d:
                    rep = 'response' in d['stop_msg'] and d['stop_msg']['response']
                    await client.write_gatt_char(d['stop_msg']['uuid'], d['stop_msg']['payload'], response=rep)
                    await asyncio.sleep(d['stop_msg']['sleep'])
                await client.stop_notify(d['uuid'])
        except bleak.exc.BleakError as e:
            print('BleakError:', e)
            if self._dbus_lock.locked():
                self._dbus_lock.release()
            await asyncio.sleep(2)
            await self._connect_to_device(address)
        except asyncio.exceptions.TimeoutError:
            if self._dbus_lock.locked():
                self._dbus_lock.release()
            if self.devices[address]['alias']:
                print('TIMEOUT: "%s" retrying....' % self.devices[address]['alias'])
            else:
                print('TIMEOUT:', address, 'retrying....')
            await asyncio.sleep(2)
            await self._connect_to_device(address)
        except Exception as e:
            print('Unknown exception:', e)
            await self._messy_cleanup(address)
    async def _messy_cleanup(self, address):
        d = self.devices[address]
        if self._dbus_lock.locked():
            self._dbus_lock.release()
        if self.is_running():
            self.running.release()
            # disabled for fuzzing!
            if d['alias']:
                print('ERROR: unable to connect to "%s"' % d['alias'], address)
            else:
                print('ERROR: unable to connect to', address)
    async def _run(self):
        tasks = [self._connect_to_device(address) for address in self.devices]
        await asyncio.gather(*tasks)
    def _async_launch(self):
        try:
            asyncio.run(self._run())
        except KeyboardInterrupt:
            print('\nCleaning up connections.  Please wait....')
            self.running.release()
    def start(self):
        self._thread = threading.Thread(target=self._async_launch, daemon=True)
        self._thread.start()
    def _message_callback(self, address, sender, data):
        #print(sender, len(data), data)
        results = self.devices[address]['decode'](data)
        for r in results:
            m = (datetime.datetime.now(datetime.UTC), address, r)
            self.messages.put(m)
            self.reporting(address, r[2])
            self.devices[address]['lastseen'] = m[0]
    def message_iter(self):
        # will this drop a message if it is used multiple times?
        while self.is_running():
            try:
                m = self.messages.get(timeout=0.05)
            except KeyboardInterrupt:
                print('\nCleaning up connections.  Please wait....')
                self.running.release()
                continue
            except queue.Empty:
                continue
            yield m
    def message_flush(self, drop=False, clear_count=True):
        while not self.messages.empty():
            try:
                m = self.messages.get_nowait()
                self.last_messages[m[1]] = m  # address:m
                if not drop:
                    yield m
            except queue.Empty:
                break
        self.last_flush = datetime.datetime.now(datetime.UTC)
        if clear_count:
            self.live_count = defaultdict(int)
        for address in self.recycle:
            if address in self.last_messages:
                self.messages.put(last_messages[address])
    def close(self):
        if self.is_running():
            self.running.release()
        self._thread.join()
    async def _scan(self):
        devices = await BleakScanner.discover(timeout=10)
        return devices
    def scan(self):
        return asyncio.run(self._scan())
    def wait_for_meters(self):
        waiting_for = set(self.devices)
        timeout = time.time() + 30
        try:
            for m in self.message_iter():
                timestamp, address, data = m
                waiting_for.discard(address)
                if not waiting_for:
                    break
                if time.time() > timeout:
                    break
            list(self.message_flush(drop=True))
        except KeyboardInterrupt:
            print('\nCleaning up connections.  Please wait....')
            pass
        return waiting_for
    def check_units(self, conf):
        # broken with meters that have multiple units
        checking = set(self.devices)
        for m in self.message_iter():
            #print(m)
            timestamp, address, data = m
            if address not in checking:
                continue
            lcd, n, units = data
            alias = self.devices[address]['alias']
            u = conf[alias]['unit']
            if u not in units:
                address, units
            checking.discard(address)
        return None, None
    def reporting(self, address, units):
        if units is None:
            return
        name = self.devices[address]['alias']
        datum = '{} ({})'.format(name, units)
        self.live_count[datum] += 1
        if self.live_report:
            if self.start_time:
                start = self.start_time
            else:
                start = self.last_flush
            seconds = int((datetime.datetime.now(datetime.UTC) - start).total_seconds())
            report = '    '.join('{}: {}'.format(*kv) for kv in sorted(self.live_count.items()))
            report = 'seconds: {}    '.format(seconds) + report
            width = shutil.get_terminal_size()[0]
            tighten = [('    ','  '), ('u',''), ('o',''), ('e',''), ('a',''), ('i',''), ]
            for long,short in tighten:
                if len(report) < width:
                    break
                report = report.replace(long, short)
            print('\r' + report + ' '*(width - len(report)), end='')

def make_decoder(model):
    return {
        'TS04': TS04_Decoder,
        '90EPD': HP90EPD_Decoder,
        'AN9002': AN9002_Decoder,
        'ZT300AB': AN9002_Decoder,
        'V05B': V05B_Decoder,
        'ZT5B': V05B_Decoder,
        'WT81B': WT81B_Decoder,
        'UT383BT': UT383BT_Decoder,
        'TP357': TP357_Decoder,
        'TS02': TS02_Decoder,
        'K1705': K1705_Decoder,
        'BT980D': BT980D_Decoder,
        'BT7200_APP': BT7200_APP_Decoder,
        'BT985C_APP': BT985C_APP_Decoder,
        'dummy': Dummy_Decoder,
    }[model]()

def find_meters(devices):
    address_check = True
    found = set()
    for _ in range(2):
        for d in devices:
            for known in known_devices:
                if address_check and not d.address.startswith(known['prefix']):
                    continue
                if known['name'].endswith('*'):
                    if not d.name.startswith(known['name'][:-1]):
                        continue
                elif d.name != known['name']:
                    continue
                if d in found:
                    continue
                # something to check the notify uuid?
                # work around pointless use of __slots__
                d2 = Device(d, make_decoder(known['decoder']), known['decoder'])
                yield d2
                found.add(d)
        # OSX uses unpredictable UUIDs instead of MACs
        address_check = False

def meter_autoregister():
    print('Attempting to auto-detect meters....')
    addresses = list(find_meters(session.scan()))
    for a in addresses:
        print('Found "%s"' % a.d.name, a.model, a.d.address)
        session.register_device(a.d.address, a.decoder.notify_uuid, decode=a.decoder.decode, poll_msg=a.decoder.poll_msg, init_msg=a.decoder.init_msg, stop_msg=a.decoder.stop_msg)
        session.devices[a.d.address]['model'] = a.model

def load_ini(path):
    config = configparser.ConfigParser(interpolation=None)
    config.read(path)
    if 'duration' in config['DEFAULT']:
        d = config['DEFAULT']['duration'].lower().strip()
        if d == 'manual':
            return config
        n = float(re.match('[0123456789.]+', d).group(0))
        if 'minute' in d:
            n *= 60
        config['DEFAULT']['duration'] = str(n)
    return config

def meter_ini_register(path):
    conf = load_ini(path)
    meter_types = ['ble:dmm', 'ble:luxmeter', 'ble:ir_thermometer']
    for section in conf:
        if 'Type' not in conf[section]:
            continue
        if conf[section]['Type'] not in meter_types:
            continue
        d = make_decoder(conf[section]['Model'])
        session.register_device(conf[section]['Address'], d.notify_uuid, decode=d.decode, poll_msg=d.poll_msg, init_msg=d.init_msg, stop_msg=d.stop_msg, alias=section)
        session.devices[conf[section]['Address']]['model'] = conf[section]['Model']

def mean(values):
    return sum(values) / len(values)

def statistics(messages, start_time, stop_time):
    columns = defaultdict(list)
    for m in messages:
        timestamp, address, data = m
        if data == (None, None, None):
            continue
        lcd, n, units = data
        name = (address, units.split('(')[0].strip())
        columns[name].append((timestamp, n))
    if not columns:
        return []
    for name,values in columns.items():
        values = sorted(n for t,n in values)
        if len(values) == 0:
            continue
        m = mean(values)
        stats = {'timestamp': stop_time,
            'duration': (stop_time - start_time).total_seconds(),
            'address': name[0], 'unit': name[1],
            'mean': m, 'samples': len(values),
            'deviation': math.sqrt(mean([(v - m)**2 for v in values])),
            'minimum': min(values),
            'quartile1': values[int(round(len(values) * 0.25))],
            'median': values[len(values)//2],
            'quartile3': values[min(int(round(len(values) * 0.75)), len(values)-1)],
            'maximum': max(values)}
        if stats['minimum'] == stats['maximum']:
            stats['deviation'] = 0
        yield stats

def manual_wait():
    print()
    input('Press ENTER to start logging a data point or control-C to exit.')
    list(session.message_flush(drop=True))
    session.live_report = True
    input('Press ENTER when the data point is complete.\n')
    session.live_report = False
    print()

def simple_columns(path, conf):
    simple = defaultdict(dict)
    header = set()
    with open(path, newline='') as csvfile:
        reader = csv.DictReader(csvfile, dialect=conf['DEFAULT']['Dialect'])
        for row in reader:
            ts = row['timestamp']
            simple[ts]['timestamp'] = ts
            head = '{} ({})'.format(row['name'], row['unit'])
            header.add(head)
            simple[ts][head] = row['mean']
    header = ['timestamp'] + sorted(list(header))
    simple_path = [os.path.dirname(path), 'simple ' + os.path.basename(path)]
    simple_path = os.path.join(*simple_path)
    with open(simple_path, 'w', newline='') as csvfile:
        writer = csv.DictWriter(csvfile, fieldnames=header, dialect=conf['DEFAULT']['Dialect'], extrasaction='ignore')
        writer.writeheader()
        for ts,row in sorted(simple.items()):
            writer.writerow(row)

def brute_force():
    # this is for devs so none of it is made easy to use
    address = 'xx:xx:xx:xx:xx:xx'
    decoder = BT7200_APP_Decoder
    # brute force found "(13, 151) 81" but doesn't work?
    #for i in range(35, 256):
    for i in range(3, 256):
        for j in range(256):
            attempted = False
            for _ in range(10):
                session = BLE_Session()
                d = decoder()
                d.poll_msg = {'uuid': "0000{0:x}-0000-1000-8000-00805f9b34fb".format(0xffe3), 'payload': [i, j], 'sleep':1.0, 'response':True}
                session.register_device(address, d.notify_uuid, decode=d.decode, poll_msg=d.poll_msg, init_msg=d.init_msg, stop_msg=d.stop_msg)
                session.start()
                rx_count = 0
                for _ in session.message_iter():
                    rx_count += 1
                    if rx_count > 60:
                        break
                #print('(%i, %i)' % (i, j), rx_count)
                session.close()
                time.sleep(2)
                if rx_count == 0:
                    continue
                attempted = True
                if rx_count > 20:
                    print('(%i, %i)' % (i, j), rx_count)
                    return
                break
            if not attempted:
                print('error with', '(%i, %i)' % (i, j))
        print('finished (%i, *)' % i) 

def main(args):
    #brute_force(); return
    logging_fh = sys.stdout
    if args.output:
        if os.path.exists(args.output):
            print('ERROR:', args.output, 'already exists')
            sys.exit(1)
    if args.config:
        meter_ini_register(args.config)
        conf = load_ini(args.config)
    else:
        meter_autoregister()
        conf = {'DEFAULT':{'mode':'live', 'duration':'1'}, }
    if not session.devices:
        print('ERROR: no supported meters found.')
        sys.exit(1)

    auto_warning = True
    session.start()
    print('Waiting for meters....')
    print('Press ^C to exit the application.')
    missing = session.wait_for_meters()
    if missing:
        #print('ERROR: could not find devices')
        #for d in missing:
        #    if session.devices[d]['alias']:
        #        print(session.devices[d]['alias'], d)
        #    else:
        #        print(d)
        session.close()
        sys.exit(1)
    #if args.config:
    #    address,unit = session.check_units(load_ini(args.config))     
    #    if address:
    #        print('ERROR: "{}" set to "{}"'.format(session.devices[address]['alias'], unit))
    #        session.close()
    #        sys.exit(1)
    print('Connected to meters.')
    #if conf['DEFAULT']['mode'] == 'live' or conf['DEFAULT']['duration'] != 'manual':
    #    input('Press ENTER to begin logging data.')
    keyboard_prev = {}
    keyboard_needed = any(conf[name]['Type'].startswith('keyboard') for name in conf if name != 'DEFAULT')

    # put off creating the file as long as possible to make it startup failures less annoying
    if args.output:
        logging_fh = open(args.output, 'wt')
    if args.config:
        fields = conf['DEFAULT']['Columns'].split()
        logging_csv = csv.DictWriter(logging_fh, dialect=conf['DEFAULT']['Dialect'], fieldnames=fields, extrasaction='ignore')
    else:
        fields = ['timestamp', 'model', 'address', 'value', 'unit']
        logging_csv = csv.DictWriter(logging_fh, dialect='excel-tab', fieldnames=fields, extrasaction='ignore')

    # needs a big refactoring
    try:
        if args.output:
            session.live_report = True
        if conf['DEFAULT']['duration'] == 'manual':
            session.live_report = False
        logging_csv.writeheader()
        logging_fh.flush()
        if not args.config:
            for m in session.message_iter():
                #print(m)
                timestamp, address, data = m
                lcd, n, units = data
                if lcd is None:
                    continue
                if auto_warning and 'auto_off' in lcd:
                    print('WARNING: Automatic power off is enabled')
                    auto_warning = False
                if type(n) == float:
                    n = format(n, '.4g')
                model = session.devices[address]['model']
                row = {'timestamp':str(timestamp), 'address':address, 'value':str(n), 'unit':units, 'model':model}
                logging_csv.writerow(row)
                logging_fh.flush()
        else:
            if conf['DEFAULT']['mode'] == 'live':
                for m in session.message_iter():
                    timestamp, address, data = m
                    lcd, n, units = data
                    if lcd is None:
                        continue
                    if auto_warning and 'auto_off' in lcd:
                        print('WARNING: Automatic power off is enabled')
                        auto_warning = False
                    if type(n) == float:
                        n = format(n, '.4g')
                    alias = session.devices[address]['alias']
                    model = session.devices[address]['model']
                    row = {'timestamp':str(timestamp), 'address':address, 'value':str(n), 'unit':units, 'name':alias, 'model':model}
                    logging_csv.writerow(row)
                    logging_fh.flush()
            if conf['DEFAULT']['mode'] == 'summary':
                if conf['DEFAULT']['duration'] == 'manual':
                    wait_fn = manual_wait
                    clear_count = True
                else:
                    wait_fn = lambda: time.sleep(float(conf['DEFAULT']['duration']))
                    clear_count = False
                    session.start_time = datetime.datetime.now(datetime.UTC)
                while session.is_running():
                    wait_fn()
                    start_time = session.last_flush
                    messages = list(session.message_flush(clear_count=clear_count))
                    stop_time = session.last_flush
                    for stats in statistics(messages, start_time, stop_time):
                        stats['name'] = session.devices[stats['address']]['alias']
                        stats['model'] = session.devices[stats['address']]['model']
                        stats['duration'] = (stop_time - start_time).total_seconds()
                        for k,n in stats.items():
                            if type(n) == float:
                                stats[k] = format(n, '.4g')
                        logging_csv.writerow(stats)
                        logging_fh.flush()
                    # keyboard data entry is a little weird since it doesn't have stats
                    if keyboard_needed:
                        print('Manual entries for previous data point:')
                    for name in conf:
                        if name == 'DEFAULT':
                            continue
                        if not conf[name]['Type'].startswith('keyboard'):
                            continue
                        if name in keyboard_prev:
                            value = input('    {} in {} (blank to keep {}): '.format(name, conf[name]['Unit'], keyboard_prev[name]))
                            if value == '':
                                value = keyboard_prev[name]
                        else:
                            value = input('    {} in {}: '.format(name, conf[name]['Unit']))
                        keyboard_prev[name] = value
                        stats = {'timestamp': stop_time,
                            'duration': (stop_time - start_time).total_seconds(),
                            'address': 'keyboard',
                            'model': 'keyboard',
                            'name': name,
                            'unit': conf[name]['Unit'],
                            'mean': value,
                            'samples': 1}
                        logging_csv.writerow(stats)
                        logging_fh.flush()
                    if keyboard_needed:
                        print('Data point saved.')
    except KeyboardInterrupt:
        print('\nCleaning up connections.  Please wait....')
        pass
    session.live_report = False
    if args.output:
        logging_fh.close()
    try:
        if args.output and conf['DEFAULT']['Mode'] == 'summary':
            simple_columns(args.output, conf)
    except:
        print('ERROR: unable to produce simplified summary.')
    session.close()

class BulletFormatter(argparse.HelpFormatter):
    def _fill_text(self, text, width, indent):
        filled = []
        for i,line in enumerate(text.split('\n* ')):
            if i == 0:
                filled.extend(indent + line for line in self._split_lines(line, width - len(indent)))
                continue
            wrapped = list(self._split_lines(line, width - len(indent) - 2))
            filled.extend(indent + '* ' + w for w in wrapped)
        return '\n'.join(filled)

session = BLE_Session()

epilog = """Supported models include TS04, AN9002, ZT300AB, 90EPD, V05B, ZT5B, UT383BT, WT81B, TP357, TS02, K1705. To disable auto-off:
* TS04: hold FUNC during power on
* AN9002: hold SEL during power on
* ZT300AB: hold SEL during power on
* UT383BT: hold HOLD during power on
* WT81B: hold POWER during power on
* WT81B: hold MODE and HOLD to toggle bluetooth"""

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='GPL3 bluetooth meter logging library/utility.  Runs until stopped with ^C. It may take several seconds to close the BLE connections.',
        formatter_class=BulletFormatter, epilog=epilog)
    parser.add_argument('-c', '--config', metavar='setup.ini', 
                        help='INI describing the hardware and logging configuration.  If omitted it will autodetect active meters.')
    parser.add_argument('-o', '--output', metavar='log.tsv', 
                        help='File to log to.  If omitted it will dump to stdout.')
    args = parser.parse_args()

    if args.config and not os.path.exists(args.config):
        print('ERROR:', args.config, 'does not exist')
        sys.exit(1)

    main(args)

