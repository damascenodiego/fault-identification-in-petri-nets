#!/bin/python

from z3 import *

# Let
## mu0_p be the initial marking for place p; 
mu_p1, mu_p2, mu_p3 = 0,0,1

## pi(\sigma) be the number of times each transition has been activated given sequence \sigma; 

#  \in L^f
s1_t1, s1_t2, s1_t3 = 0,0,0 # \sigma t_j = \empty t3
s2_t1, s2_t2, s2_t3 = 0,0,0 # \sigma t_j = \empty t1
s3_t1, s3_t2, s3_t3 = 1,0,0 # \sigma t_j =    t1  t2
s4_t1, s4_t2, s4_t3 = 1,1,0 # \sigma t_j = t1 t2  t1

# \not \in L^f
s5_t1, s5_t2, s5_t3 	= 0, 0, 0 ## sequence t2
s6_t1, s6_t2, s6_t3 	= 1, 0, 0 ## sequence t1_t1
s7_t1, s7_t2, s7_t3 	= 1, 0, 0 ## sequence t1_t3

## l \in Naturals ; 
l1, l2, l3, l4 = Ints('l1 l2 l3 l4')
l5, l6, l7, l17, l18       = Ints('l5 l6 l7 l17 l18')

## C(p) be the vector of pre-post conditions for place p; 
## Pre(p,f)  be the pre-condition  from place p to transition f; and
p1_t1, p1_t2, p1_t3 = 1,0,0
p2_t1, p2_t2, p2_t3 = 0,1,0
p3_t1, p3_t2, p3_t3 = 0,0,1

## Post(p,f) be the post-condition from transition f to place p. 
# post-conditions
t1_p1, t2_p1, t3_p1 = 0,1,0
t1_p2, t2_p2, t3_p2 = 1,0,0
t1_p3, t2_p3, t3_p3 = 0,0,0

# find these
f_p1, p1_f = Ints('f_p1 p1_f')
f_p2, p2_f = Ints('f_p2 p2_f')
f_p3, p3_f = Ints('f_p3 p3_f')


# we have that
s = Solver()


s.add(
	# And(f_p2 == 0,f_p3 == 0,p1_f == 0,p2_f == 0,p3_f == 1,f_p1 == 1), # expected solution
	And(f_p1 >= 0,f_p2 >= 0,f_p3 >= 0,p1_f >= 0,p2_f >= 0,p3_f >= 0),
	)


s.add(And(l1 >= 0,l2 >= 1,l3 >= 1,l4 >= 1,)) # l>=M
s.add(And(l5 >= 0,l6 >= 0,l7 >= 0,)) # l>=M

# for every \sigma \cdot tj \in L^f   (Equation 4.1)
# for some l \in N mu0(p) + C(p) * pi(\sigma) + l * (Post(p,f) - Pre(p,f) >= Pre(p,tj) for all p \in P 

# Inequations to s1 = t3
s.add(
	Exists([l1],
		And(
		mu_p1 +  ((t1_p1-p1_t1)*s1_t1 + (t2_p1-p1_t2)*s1_t2 + (t3_p1-p1_t3)*s1_t3) + l1 * (f_p1 - p1_f) >= p1_t3,
		mu_p2 +  ((t1_p2-p2_t1)*s1_t1 + (t2_p2-p2_t2)*s1_t2 + (t3_p2-p2_t3)*s1_t3) + l1 * (f_p2 - p2_f) >= p2_t3,
		mu_p3 +  ((t1_p3-p3_t1)*s1_t1 + (t2_p3-p3_t2)*s1_t2 + (t3_p3-p3_t3)*s1_t3) + l1 * (f_p3 - p3_f) >= p3_t3,
		)
	)
)

# Inequations to s2 = t1
s.add(
	Exists([l2],
		And(
		mu_p1 +  ((t1_p1-p1_t1)*s2_t1 + (t2_p1-p1_t2)*s2_t2 + (t3_p1-p1_t3)*s2_t3) + l2 * (f_p1 - p1_f) >= p1_t1,
		mu_p2 +  ((t1_p2-p2_t1)*s2_t1 + (t2_p2-p2_t2)*s2_t2 + (t3_p2-p2_t3)*s2_t3) + l2 * (f_p2 - p2_f) >= p2_t1,
		mu_p3 +  ((t1_p3-p3_t1)*s2_t1 + (t2_p3-p3_t2)*s2_t2 + (t3_p3-p3_t3)*s2_t3) + l2 * (f_p3 - p3_f) >= p3_t1,
		)
	)
)

# Inequations to s3 = t1 t2
s.add(
	Exists([l3],
		And(
		mu_p1 +  ((t1_p1-p1_t1)*s3_t1 + (t2_p1-p1_t2)*s3_t2 + (t3_p1-p1_t3)*s3_t3) + l3 * (f_p1 - p1_f) >= p1_t2,
		mu_p2 +  ((t1_p2-p2_t1)*s3_t1 + (t2_p2-p2_t2)*s3_t2 + (t3_p2-p2_t3)*s3_t3) + l3 * (f_p2 - p2_f) >= p2_t2,
		mu_p3 +  ((t1_p3-p3_t1)*s3_t1 + (t2_p3-p3_t2)*s3_t2 + (t3_p3-p3_t3)*s3_t3) + l3 * (f_p3 - p3_f) >= p3_t2,
		)
	)
)

# Inequations to s4 = t1 t2 t1
s.add(
	Exists([l4],
		And(
		mu_p1 +  ((t1_p1-p1_t1)*s4_t1 + (t2_p1-p1_t2)*s4_t2 + (t3_p1-p1_t3)*s4_t3) + l4 * (f_p1 - p1_f) >= p1_t1,
		mu_p2 +  ((t1_p2-p2_t1)*s4_t1 + (t2_p2-p2_t2)*s4_t2 + (t3_p2-p2_t3)*s4_t3) + l4 * (f_p2 - p2_f) >= p2_t1,
		mu_p3 +  ((t1_p3-p3_t1)*s4_t1 + (t2_p3-p3_t2)*s4_t2 + (t3_p3-p3_t3)*s4_t3) + l4 * (f_p3 - p3_f) >= p3_t1,
		)
	)
)

# for every \sigma \cdot tj \not\in L^f   (Equation 4.2)
# mu0(p) + C(p) * pi(\sigma) + l * (Post(p,f) - Pre(p,f) <  Pre(p,tj)
# for all l \in N mu0(p) + C(p) * pi(\sigma) + l * (Post(p,f) - Pre(p,f) < Pre(p,tj) for some p \in P

# TODO include the remainder inequalities if \sigma tj \not\in L^f...

s.add(
	ForAll([l5],
		Or(
			mu_p1 +  ((t1_p1-p1_t1)*s5_t1  + (t2_p1-p1_t2)*s5_t2  + (t3_p1-p1_t3)*s5_t3)  + l5  * (f_p1 - p1_f) <  p1_t2,	 	
			mu_p2 +  ((t1_p2-p2_t1)*s5_t1  + (t2_p2-p2_t2)*s5_t2  + (t3_p2-p2_t3)*s5_t3)  + l5  * (f_p2 - p2_f) <  p2_t2,	 	
			mu_p3 +  ((t1_p3-p3_t1)*s5_t1  + (t2_p3-p3_t2)*s5_t2  + (t3_p3-p3_t3)*s5_t3)  + l5  * (f_p3 - p3_f) <  p3_t2,
		)
	)
)
s.add(
	ForAll([l6],
		Or(
			mu_p1 +  ((t1_p1-p1_t1)*s6_t1  + (t2_p1-p1_t2)*s6_t2  + (t3_p1-p1_t3)*s6_t3)  + l6  * (f_p1 - p1_f) < p1_t1,	 	
			mu_p2 +  ((t1_p2-p2_t1)*s6_t1  + (t2_p2-p2_t2)*s6_t2  + (t3_p2-p2_t3)*s6_t3)  + l6  * (f_p2 - p2_f) < p2_t1,	 	
			mu_p3 +  ((t1_p3-p3_t1)*s6_t1  + (t2_p3-p3_t2)*s6_t2  + (t3_p3-p3_t3)*s6_t3)  + l6  * (f_p3 - p3_f) < p3_t1,	 	
		)
	)
)
s.add(
	ForAll([l7],
		Or(
			mu_p1 +  ((t1_p1-p1_t1)*s7_t1  + (t2_p1-p1_t2)*s7_t2  + (t3_p1-p1_t3)*s7_t3)  + l7  * (f_p1 - p1_f) <  p1_t3,	 	
			mu_p2 +  ((t1_p2-p2_t1)*s7_t1  + (t2_p2-p2_t2)*s7_t2  + (t3_p2-p2_t3)*s7_t3)  + l7  * (f_p2 - p2_f) <  p2_t3,	 	
			mu_p3 +  ((t1_p3-p3_t1)*s7_t1  + (t2_p3-p3_t2)*s7_t2  + (t3_p3-p3_t3)*s7_t3)  + l7  * (f_p3 - p3_f) <  p3_t3,	 	
		)
	)
)


print s
print s.check()
print s.model()