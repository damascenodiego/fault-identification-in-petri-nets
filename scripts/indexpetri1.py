#!/bin/python

from z3 import *

# we have that
s = Solver()
## mu0_px is the initial marking for place px; 
mu_p1, mu_p2 = 1, 1

## pi_tj is the pre-condition from place pi to transition tj
p1_t1, p1_t2, p1_t3 = 1, 1, 0
p2_t1, p2_t2, p2_t3 = 1, 1, 1

## tj_pi is the post-condition from transition tj to place pi
t1_p1, t2_p1, t3_p1 = 0, 0, 0
t1_p2, t2_p2, t3_p2 = 1, 0, 0

## find the values for the faulty transitions 
f_p1, p1_f = Ints('f_p1 p1_f')
f_p2, p2_f = Ints('f_p2 p2_f')

# where they should be 
s.add( f_p1 >= 0, f_p2 >= 0 )
s.add( p1_f >= 0, p2_f >= 0 )

# and no self-loop should exist
s.add(
   And(
      Or(And((f_p1 >= 0, p1_f == 0)),And((f_p1 == 0, p1_f >= 0)),And((f_p1 == 0, p1_f == 0))),
      Or(And((f_p2 >= 0, p2_f == 0)),And((f_p2 == 0, p2_f >= 0)),And((f_p2 == 0, p2_f == 0))),
   )
)
## l \in Naturals ; 
l0 = Int('l0')
l1 = Int('l1')
l2 = Int('l2')
l3 = Int('l3')
l4 = Int('l4')
l5 = Int('l5')
l6 = Int('l6')
l7 = Int('l7')
l8 = Int('l8')

########################################
## \in L^f (Equation 4.1)
########################################
# Sequence 0: t1
s0_t1, s0_t2, s0_t3 = 0, 0, 0
s.add(
   Exists([l0],
      And( Implies(l0 >= 0, 
      And(l0 >= 0, 
         mu_p1 + (t1_p1-p1_t1)*s0_t1 + (t2_p1-p1_t2)*s0_t2 + (t3_p1-p1_t3)*s0_t3 + l0 * (f_p1 - p1_f) >= p1_t1,
         mu_p2 + (t1_p2-p2_t1)*s0_t1 + (t2_p2-p2_t2)*s0_t2 + (t3_p2-p2_t3)*s0_t3 + l0 * (f_p2 - p2_f) >= p2_t1,
      )
      ))
   )
)

# Sequence 1: t2
s1_t1, s1_t2, s1_t3 = 0, 0, 0
s.add(
   Exists([l1],
      And( Implies(l1 >= 0, 
      And(l1 >= 0, 
         mu_p1 + (t1_p1-p1_t1)*s1_t1 + (t2_p1-p1_t2)*s1_t2 + (t3_p1-p1_t3)*s1_t3 + l1 * (f_p1 - p1_f) >= p1_t2,
         mu_p2 + (t1_p2-p2_t1)*s1_t1 + (t2_p2-p2_t2)*s1_t2 + (t3_p2-p2_t3)*s1_t3 + l1 * (f_p2 - p2_f) >= p2_t2,
      )
      ))
   )
)

# Sequence 2: t3
s2_t1, s2_t2, s2_t3 = 0, 0, 0
s.add(
   Exists([l2],
      And( Implies(l2 >= 0, 
      And(l2 >= 0, 
         mu_p1 + (t1_p1-p1_t1)*s2_t1 + (t2_p1-p1_t2)*s2_t2 + (t3_p1-p1_t3)*s2_t3 + l2 * (f_p1 - p1_f) >= p1_t3,
         mu_p2 + (t1_p2-p2_t1)*s2_t1 + (t2_p2-p2_t2)*s2_t2 + (t3_p2-p2_t3)*s2_t3 + l2 * (f_p2 - p2_f) >= p2_t3,
      )
      ))
   )
)

# Sequence 3: t1,t3
s3_t1, s3_t2, s3_t3 = 1, 0, 0
s.add(
   Exists([l3],
      And( Implies(l3 >= 0, 
      And(l3 >= 0, 
         mu_p1 + (t1_p1-p1_t1)*s3_t1 + (t2_p1-p1_t2)*s3_t2 + (t3_p1-p1_t3)*s3_t3 + l3 * (f_p1 - p1_f) >= p1_t3,
         mu_p2 + (t1_p2-p2_t1)*s3_t1 + (t2_p2-p2_t2)*s3_t2 + (t3_p2-p2_t3)*s3_t3 + l3 * (f_p2 - p2_f) >= p2_t3,
      )
      ))
   )
)

# Sequence 4: t3,t3
s4_t1, s4_t2, s4_t3 = 0, 0, 1
s.add(
   Exists([l4],
      And( Implies(l4 >= 0, 
      And(l4 >= 0, 
         mu_p1 + (t1_p1-p1_t1)*s4_t1 + (t2_p1-p1_t2)*s4_t2 + (t3_p1-p1_t3)*s4_t3 + l4 * (f_p1 - p1_f) >= p1_t3,
         mu_p2 + (t1_p2-p2_t1)*s4_t1 + (t2_p2-p2_t2)*s4_t2 + (t3_p2-p2_t3)*s4_t3 + l4 * (f_p2 - p2_f) >= p2_t3,
      )
      ))
   )
)


########################################
## \not \in L^f (Equation 4.2)
########################################
# Sequence 5: t1,t1
s5_t1, s5_t2, s5_t3 = 1, 0, 0
s.add(
   ForAll([l5],
      And( Implies(l5 >= 0, 
      Or(
         And(l5 >= 0,  mu_p1 + (t1_p1-p1_t1)*s5_t1 + (t2_p1-p1_t2)*s5_t2 + (t3_p1-p1_t3)*s5_t3 + l5 * (f_p1 - p1_f) < p1_t1),
         And(l5 >= 0,  mu_p2 + (t1_p2-p2_t1)*s5_t1 + (t2_p2-p2_t2)*s5_t2 + (t3_p2-p2_t3)*s5_t3 + l5 * (f_p2 - p2_f) < p2_t1),
      )
      ))
   )
)

# Sequence 6: t1,t2
s6_t1, s6_t2, s6_t3 = 1, 0, 0
s.add(
   ForAll([l6],
      And( Implies(l6 >= 0, 
      Or(
         And(l6 >= 0,  mu_p1 + (t1_p1-p1_t1)*s6_t1 + (t2_p1-p1_t2)*s6_t2 + (t3_p1-p1_t3)*s6_t3 + l6 * (f_p1 - p1_f) < p1_t2),
         And(l6 >= 0,  mu_p2 + (t1_p2-p2_t1)*s6_t1 + (t2_p2-p2_t2)*s6_t2 + (t3_p2-p2_t3)*s6_t3 + l6 * (f_p2 - p2_f) < p2_t2),
      )
      ))
   )
)

# Sequence 7: t3,t1
s7_t1, s7_t2, s7_t3 = 0, 0, 1
s.add(
   ForAll([l7],
      And( Implies(l7 >= 0, 
      Or(
         And(l7 >= 0,  mu_p1 + (t1_p1-p1_t1)*s7_t1 + (t2_p1-p1_t2)*s7_t2 + (t3_p1-p1_t3)*s7_t3 + l7 * (f_p1 - p1_f) < p1_t1),
         And(l7 >= 0,  mu_p2 + (t1_p2-p2_t1)*s7_t1 + (t2_p2-p2_t2)*s7_t2 + (t3_p2-p2_t3)*s7_t3 + l7 * (f_p2 - p2_f) < p2_t1),
      )
      ))
   )
)

# Sequence 8: t3,t2
s8_t1, s8_t2, s8_t3 = 0, 0, 1
s.add(
   ForAll([l8],
      And( Implies(l8 >= 0, 
      Or(
         And(l8 >= 0,  mu_p1 + (t1_p1-p1_t1)*s8_t1 + (t2_p1-p1_t2)*s8_t2 + (t3_p1-p1_t3)*s8_t3 + l8 * (f_p1 - p1_f) < p1_t2),
         And(l8 >= 0,  mu_p2 + (t1_p2-p2_t1)*s8_t1 + (t2_p2-p2_t2)*s8_t2 + (t3_p2-p2_t3)*s8_t3 + l8 * (f_p2 - p2_f) < p2_t2),
      )
      ))
   )
)


print(s.check())
print(s.model())
#print(s.sexpr());print('(check-sat)\n(get-model)')
