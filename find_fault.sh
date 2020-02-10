#!/bin/sh

# generates the python script that uses Z3 to find the model
python identify_fault.py indexpetri0.txt > indexpetri0.txt.py

# runs the python script that uses Z3 to find the model
python indexpetri0.txt.py
