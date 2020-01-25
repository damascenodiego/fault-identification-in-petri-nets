#!/bin/python

from z3 import *

# Let
## mu0_p be the initial marking for place p; 
mu_p1, mu_p2, mu_p3 = 0,0,1

## pi(\sigma) be the number of times each transition has been activated given sequence \sigma; 
s1_t1, s1_t2, s1_t3 = 0,0,0 # s1 = t3
s2_t1, s2_t2, s2_t3 = 0,1,0 # s2 = t1
s3_t1, s3_t2, s3_t3 = 1,0,0 # s3 = t1 t2
s4_t1, s4_t2, s4_t3 = 0,1,0 # s4 = t1 t2 t1

## l \in Naturals ; 
l1, l2, l3, l4 = Ints('l1 l2 l3 l4')

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


s.add(f_p1 > 0)
s.add(f_p2 > 0)
s.add(f_p3 > 0)
s.add(p1_f > 0)
s.add(p2_f > 0)
s.add(p3_f > 0)

s.add(l1 >= 4)
s.add(l2 >= 4)
s.add(l3 >= 4)
s.add(l4 >= 4)

# for every \sigma \cdot tj \in L^f   (Equation 4.1)
# for some l \in N mu0(p) + C(p) * pi(\sigma) + l * (Post(p,f) - Pre(p,f) >= Pre(p,tj) for all p \in P 

# Inequations to s1
s.add(
	Exists([l1],
		And(mu_p1 +  (p1_t1*s1_t1 + p1_t2*s1_t2 + p1_t3*s1_t3) + l1 * (f_p1 - p1_f) >= p1_t3, 
	        mu_p2 +  (p2_t1*s1_t1 + p2_t2*s1_t2 + p2_t3*s1_t3) + l1 * (f_p2 - p2_f) >= p2_t3,
	        mu_p3 +  (p3_t1*s1_t1 + p3_t2*s1_t2 + p3_t3*s1_t3) + l1 * (f_p3 - p3_f) >= p3_t3)
	)
)


# for every \sigma \cdot tj \not\in L^f   (Equation 4.2)
# mu0(p) + C(p) * pi(\sigma) + l * (Post(p,f) - Pre(p,f) <  Pre(p,tj)
# for all l \in N mu0(p) + C(p) * pi(\sigma) + l * (Post(p,f) - Pre(p,f) < Pre(p,tj) for some p \in P

# Inequations to s2
s.add(
	ForAll([l2],
		And(mu_p1 +  (p1_t1*s2_t1 + p1_t2*s2_t2 + p1_t3*s2_t3) + l2 * (f_p1 - p1_f) >= p1_t1,
		    mu_p3 +  (p3_t1*s2_t1 + p3_t2*s2_t2 + p3_t3*s2_t3) + l2 * (f_p3 - p3_f) >= p3_t1,
		    mu_p2 +  (p2_t1*s2_t1 + p2_t2*s2_t2 + p2_t3*s2_t3) + l2 * (f_p2 - p2_f) >= p2_t1) 
	)
)

# Inequations to s3
s.add(
	ForAll([l3],
		And(mu_p1 +  (p1_t1*s3_t1 + p1_t2*s3_t2 + p1_t3*s3_t3) + l3 * (f_p1 - p1_f) >= p1_t2,
		    mu_p2 +  (p2_t1*s3_t1 + p2_t2*s3_t2 + p2_t3*s3_t3) + l3 * (f_p2 - p2_f) >= p2_t2,
		    mu_p3 +  (p3_t1*s3_t1 + p3_t2*s3_t2 + p3_t3*s3_t3) + l3 * (f_p3 - p3_f) >= p3_t2) 
	)
)

# Inequations to s4
s.add(
	ForAll([l4],
		And(mu_p1 +  (p1_t1*s4_t1 + p1_t2*s4_t2 + p1_t3*s4_t3) + l4 * (f_p1 - p1_f) >= p1_t1,
		    mu_p2 +  (p2_t1*s4_t1 + p2_t2*s4_t2 + p2_t3*s4_t3) + l4 * (f_p2 - p2_f) >= p2_t1,
		    mu_p3 +  (p3_t1*s4_t1 + p3_t2*s4_t2 + p3_t3*s4_t3) + l4 * (f_p3 - p3_f) >= p3_t1) 
	)
)

print s.check()
print s.model()