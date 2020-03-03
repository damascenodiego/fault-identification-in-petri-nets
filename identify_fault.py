#!/bin/python

import ast
import sys
import re

places = []
transitions = []
mu0 = {}
pre = {}
post = {}
in_Lf = {}
not_in_Lf = {}

try:
	fname = sys.argv[1]
	f = open(fname,'r')
	
	# Read number of places and its IDs
	f.readline().strip() # read line with 'places'
	n_places = int(f.readline().strip())
	for i in range(n_places):
		line = f.readline().strip()
		places.append(line)
	# print(''%s'' % str(places))
	f.readline().strip() # jump blank line
	
	# Read number of transitions and its IDs
	f.readline().strip() # read line with 'transitions'
	n_trs = int(f.readline().strip())
	for i in range(n_trs):
		line = f.readline().strip()
		transitions.append(line)
	# print(''%s'' % str(transitions))
	f.readline().strip() # jump blank line

	# Read the initial markings
	f.readline().strip() # read line with 'mu0'
	for i in range(n_places):
		line = f.readline().strip()
		mu0[places[i]] = line
	# print(''%s'' % str(mu0))
	f.readline().strip() # jump blank line

	# Read the matrix of pre-conditions
	f.readline().strip() # read line with 'pre'
	for _pn in range(n_places):
		line = f.readline().strip()
		line = line.split(' ')
		pre[places[_pn]] = {}
		# print(line)
		for _tn in range(n_trs):
			pre[places[_pn]][transitions[_tn]] = line[_tn]
	# print(''%s'' % str(pre))
	f.readline().strip() # jump blank line

	# Read the matrix of pre-conditions
	f.readline().strip() # read line with 'post'
	for _pn in range(n_places):
		line = f.readline().strip()
		line = line.split(' ')
		post[places[_pn]] = {}
		# print(line)
		for _tn in range(n_trs):
			post[places[_pn]][transitions[_tn]] = line[_tn]
	# print(''%s'' % str(post))
	f.readline().strip() # jump blank line

	# Read the list of sequences in_Lf
	f.readline().strip() # read line with 'in_Lf'
	sz_Lf = int(f.readline().strip())
	for _sn in range(sz_Lf):
		_seq = f.readline().strip().split(',')
		f.readline()
		# _mrk = ast.literal_eval(f.readline().strip())
		in_Lf[_sn] = _seq
	# print('in_Lf: '%s'' % str(in_Lf))
	f.readline().strip() # jump blank line
	
	# Read the list of sequences not_in_Lf
	f.readline().strip() # read line with 'not_in_Lf'
	sz_not_in_Lf = int(f.readline().strip())
	for _sn in range(sz_not_in_Lf):
		_seq = f.readline().strip().split(',')
		f.readline()
		# _mrk = ast.literal_eval(f.readline().strip())
		not_in_Lf[_sn] = _seq
	# print('not_in_Lf: '%s'' % str(not_in_Lf))
	f.readline().strip() # jump blank line
	f.close()

	# 'Starting to print the script'
	print('#!/bin/python')
	print('')
	print('from z3 import *')
	print('')
	print('# we have that')
	print('s = Solver()')
	print('## mu0_px is the initial marking for place px; ')
	print('%s = %s' % (\
		', '.join(['mu_'+places[_pn] for _pn in range(n_places)]), \
		', '.join([mu0[places[_pn]] for _pn in range(n_places)])) \
	)

	print('')
	print('## pi_tj is the pre-condition from place pi to transition tj')
	for _pn in range(n_places):
		print('%s = %s' % (\
		', '.join([places[_pn]+'_'+transitions[_tn] for _tn in range(n_trs)]), \
		', '.join([pre[places[_pn]][transitions[_tn]] for _tn in range(n_trs)])) \
	)
	print('')
	print('## tj_pi is the post-condition from transition tj to place pi')
	for _pn in range(n_places):
		print('%s = %s' % (\
			', '.join([transitions[_tn]+'_'+places[_pn] for _tn in range(n_trs)]), \
			', '.join([post[places[_pn]][transitions[_tn]] for _tn in range(n_trs)]))
		)
	print('')
	print('## find the values for the faulty transitions ')
	for _pn in range(n_places):
		print('f_%s, %s_f = Ints(\'f_%s %s_f\')' % (places[_pn],places[_pn],places[_pn],places[_pn]))
	print('')
	print('# where they should be ')
	print('s.add( %s )' % ', '.join('f_%s >= 0' % places[_pn] for _pn in range(n_places)))
	print('s.add( %s )' % ', '.join('%s_f >= 0' % places[_pn] for _pn in range(n_places)))
	print('')
	print('# and no self-loop should exist')
	print('s.add(')
	print('   And(')
	
	for _pn in range(n_places):
		a_place = places[_pn]
		print('      Or(And((f_%s >= 0, %s_f == 0)),And((f_%s == 0, %s_f >= 0)),And((f_%s == 0, %s_f == 0))),' % (a_place,a_place,a_place,a_place,a_place,a_place))
	print('   )')
	print(')')
	print('## l \\in Naturals ; ')
	# print('%s = Ints(\'%s\')' % (\
	# 	', '.join(['l'+str(_sn) for _sn in range(sz_Lf)]), \
	# 	' '.join(['l'+str(_sn) for _sn in range(sz_Lf)])
	# 	)
	# )
	# print('%s = Ints(\'%s\')' % (\
	# 	', '.join(['l'+str(_sn+sz_Lf) for _sn in range(sz_not_in_Lf)]), \
	# 	' ' .join(['l'+str(_sn+sz_Lf) for _sn in range(sz_not_in_Lf)])
	# 	)
	# )	

	for _sn in range(sz_Lf): print('l'+str(_sn)+' = Int(\'l'+str(_sn)+'\')')
	for _sn in range(sz_not_in_Lf): print('l'+str(_sn+sz_Lf)+' = Int(\'l'+str(_sn+sz_Lf)+'\')')
	print('')
	print('########################################')
	print('## \\in L^f (Equation 4.1)')
	print('########################################')
	for _sn in range(sz_Lf):
		# set counters for each symbol to zero
		_counter = {transitions[_tn]:0 for _tn in range(n_trs)}
		_counter['f'] = 0 # set counters for f to zero
		# count for all symbols, except the last
		for _idx in range(len(in_Lf[_sn])-1):
			_counter[in_Lf[_sn][_idx]]+=1
		# get the last symbol
		last_transition = in_Lf[_sn][-1]
		# print(_counter)
		print('# Sequence %d: %s' % (_sn,','.join(in_Lf[_sn])))
		print('%s = %s' % (\
			', '.join(['s'+str(_sn)+'_'+transitions[_tn] for _tn in range(n_trs)]), \
			', '.join([ str(_counter[transitions[_tn]]) for _tn in range(n_trs)]))
		)
		# print('s.add( l%d >= %d )' % (_sn,_counter['f']))
		# print('')		
		print('s.add(')
		print('   Exists([l%d],'%_sn)
		print('      And( Implies(l%d >= %d, ' % (_sn,_counter['f']))
		print('      And(l%d >= %d, ' % (_sn,_counter['f']))
		for _pn in range(n_places):
			line = '         mu_'+places[_pn]+' + '
			line += ' + '.join(['('+transitions[_tn]+'_'+places[_pn]+'-'+places[_pn]+'_'+transitions[_tn]+')*s'+str(_sn)+'_'+transitions[_tn] for _tn in range(n_trs)])
			line += ' + '+'l'+str(_sn)+' * ('+'f_'+places[_pn]+' - '+places[_pn]+'_f'+')'
			line += ' >= '+places[_pn]+'_'+last_transition+','
			print(line)
		print('      )')
		print('      ))')
		print('   )')
		print(')')
		print('')


	print('')
	print('########################################')
	print('## \\not \\in L^f (Equation 4.2)')
	print('########################################')
	for _sn in range(sz_not_in_Lf):
		# set counters for each symbol to zero
		_counter = {transitions[_tn]:0 for _tn in range(n_trs)}
		_counter['f'] = 0 # set counters for f to zero
		# count for all symbols, except the last
		for _idx in range(len(not_in_Lf[_sn])-1):
			_counter[not_in_Lf[_sn][_idx]]+=1
		# get the last symbol
		last_transition = not_in_Lf[_sn][-1]
		# print(_counter)
		print('# Sequence %d: %s' % (_sn+sz_Lf,','.join(not_in_Lf[_sn])))
		print('%s = %s' % (\
			', '.join(['s'+str(_sn+sz_Lf)+'_'+transitions[_tn] for _tn in range(n_trs)]), \
			', '.join([ str(_counter[transitions[_tn]]) for _tn in range(n_trs)]))
		)
		# print('s.add( l%d >= %d )' % (_sn+sz_Lf,_counter['f']))
		# print('')		
		print('s.add(')
		print('   ForAll([l%d],' % (_sn+sz_Lf))
		print('      And( Implies(l%d >= %d, ' % (_sn+sz_Lf,_counter['f']))
		print('      Or(')
		for _pn in range(n_places):
			line = '         And(l%d >= %d, ' % (_sn+sz_Lf,_counter['f'])
			line += ' mu_'+places[_pn]+' + '
			line += ' + '.join(['('+transitions[_tn]+'_'+places[_pn]+'-'+places[_pn]+'_'+transitions[_tn]+')*s'+str(_sn+sz_Lf)+'_'+transitions[_tn] for _tn in range(n_trs)])
			line += ' + '+'l'+str(_sn+sz_Lf)+' * ('+'f_'+places[_pn]+' - '+places[_pn]+'_f'+')'
			line += ' < '+places[_pn]+'_'+last_transition+'),'
			print(line)
		print('      )')
		print('      ))')
		print('   )')
		print(')')
		print('')
	print('')
	# print('print(s)')
	print('print(s.check())')
	print('print(s.model())')	
	print('#print(s.sexpr());print(\'(check-sat)\\n(get-model)\')')
except Exception as e:
	print(e)