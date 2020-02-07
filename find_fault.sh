#!/bin/sh

# generates the python script that uses Z3 to find the model
python identify_fault.py indexpetri1.txt > indexpetri1.txt.py

# runs the python script that uses Z3 to find the model
python indexpetri1.txt.py
