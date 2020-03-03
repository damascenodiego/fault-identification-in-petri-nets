#!/bin/bash

for i in 0 1 2 3 4 5 6; do 
	python identify_fault.py indexpetri$i.txt > scripts/indexpetri$i.py; 
	python scripts/indexpetri$i.py > scripts/indexpetri$i.out; 
done