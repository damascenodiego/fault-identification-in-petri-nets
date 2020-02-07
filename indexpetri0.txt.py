#!/bin/python

from z3 import *

# we have that
s = Solver()
## mu0_px is the initial marking for place px; 
mu_p1, mu_p2, mu_p3 = 0, 0, 1

## pi_tj is the pre-condition from place pi to transition tj
p1_t1, p1_t2, p1_t3 = 1, 0, 0
p2_t1, p2_t2, p2_t3 = 0, 1, 0
p3_t1, p3_t2, p3_t3 = 0, 0, 1

## tj_pi is the post-condition from transition tj to place pi
t1_p1, t2_p1, t3_p1 = 0, 1, 0
t1_p2, t2_p2, t3_p2 = 1, 0, 0
t1_p3, t2_p3, t3_p3 = 0, 0, 0

## find the values for the faulty transitions 
f_p1, p1_f = Ints('f_p1 p1_f')
f_p2, p2_f = Ints('f_p2 p2_f')
f_p3, p3_f = Ints('f_p3 p3_f')

# where they should be 
s.add( f_p1 >= 0, f_p2 >= 0, f_p3 >= 0 )
s.add( p1_f >= 0, p2_f >= 0, p3_f >= 0 )

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
l9 = Int('l9')
l10 = Int('l10')
l11 = Int('l11')

########################################
## \in L^f (Equation 4.1)
########################################
# Sequence 0: t3
s0_t1, s0_t2, s0_t3 = 0, 0, 0
s.add( l0 >= 0 )
s.add(
   Exists([l0],
      And(
         mu_p1 + (t1_p1-p1_t1)*s0_t1 + (t2_p1-p1_t2)*s0_t2 + (t3_p1-p1_t3)*s0_t3 + l0 * (f_p1 - p1_f) >= p1_t3,
         mu_p2 + (t1_p2-p2_t1)*s0_t1 + (t2_p2-p2_t2)*s0_t2 + (t3_p2-p2_t3)*s0_t3 + l0 * (f_p2 - p2_f) >= p2_t3,
         mu_p3 + (t1_p3-p3_t1)*s0_t1 + (t2_p3-p3_t2)*s0_t2 + (t3_p3-p3_t3)*s0_t3 + l0 * (f_p3 - p3_f) >= p3_t3,
      )
   )
)

# Sequence 1: f,t1
s1_t1, s1_t2, s1_t3 = 0, 0, 0
s.add( l1 >= 1 )
s.add(
   Exists([l1],
      And(
         mu_p1 + (t1_p1-p1_t1)*s1_t1 + (t2_p1-p1_t2)*s1_t2 + (t3_p1-p1_t3)*s1_t3 + l1 * (f_p1 - p1_f) >= p1_t1,
         mu_p2 + (t1_p2-p2_t1)*s1_t1 + (t2_p2-p2_t2)*s1_t2 + (t3_p2-p2_t3)*s1_t3 + l1 * (f_p2 - p2_f) >= p2_t1,
         mu_p3 + (t1_p3-p3_t1)*s1_t1 + (t2_p3-p3_t2)*s1_t2 + (t3_p3-p3_t3)*s1_t3 + l1 * (f_p3 - p3_f) >= p3_t1,
      )
   )
)

# Sequence 2: f,t1,t2
s2_t1, s2_t2, s2_t3 = 1, 0, 0
s.add( l2 >= 1 )
s.add(
   Exists([l2],
      And(
         mu_p1 + (t1_p1-p1_t1)*s2_t1 + (t2_p1-p1_t2)*s2_t2 + (t3_p1-p1_t3)*s2_t3 + l2 * (f_p1 - p1_f) >= p1_t2,
         mu_p2 + (t1_p2-p2_t1)*s2_t1 + (t2_p2-p2_t2)*s2_t2 + (t3_p2-p2_t3)*s2_t3 + l2 * (f_p2 - p2_f) >= p2_t2,
         mu_p3 + (t1_p3-p3_t1)*s2_t1 + (t2_p3-p3_t2)*s2_t2 + (t3_p3-p3_t3)*s2_t3 + l2 * (f_p3 - p3_f) >= p3_t2,
      )
   )
)

# Sequence 3: f,t1,t2,t1
s3_t1, s3_t2, s3_t3 = 1, 1, 0
s.add( l3 >= 1 )
s.add(
   Exists([l3],
      And(
         mu_p1 + (t1_p1-p1_t1)*s3_t1 + (t2_p1-p1_t2)*s3_t2 + (t3_p1-p1_t3)*s3_t3 + l3 * (f_p1 - p1_f) >= p1_t1,
         mu_p2 + (t1_p2-p2_t1)*s3_t1 + (t2_p2-p2_t2)*s3_t2 + (t3_p2-p2_t3)*s3_t3 + l3 * (f_p2 - p2_f) >= p2_t1,
         mu_p3 + (t1_p3-p3_t1)*s3_t1 + (t2_p3-p3_t2)*s3_t2 + (t3_p3-p3_t3)*s3_t3 + l3 * (f_p3 - p3_f) >= p3_t1,
      )
   )
)


########################################
## \not \in L^f (Equation 4.2)
########################################
# Sequence 4: t1
s4_t1, s4_t2, s4_t3 = 0, 0, 0
s.add( l4 >= 0 )
s.add(
   ForAll([l4],
      Or(
         mu_p1 + (t1_p1-p1_t1)*s4_t1 + (t2_p1-p1_t2)*s4_t2 + (t3_p1-p1_t3)*s4_t3 + l4 * (f_p1 - p1_f) < p1_t1,
         mu_p2 + (t1_p2-p2_t1)*s4_t1 + (t2_p2-p2_t2)*s4_t2 + (t3_p2-p2_t3)*s4_t3 + l4 * (f_p2 - p2_f) < p2_t1,
         mu_p3 + (t1_p3-p3_t1)*s4_t1 + (t2_p3-p3_t2)*s4_t2 + (t3_p3-p3_t3)*s4_t3 + l4 * (f_p3 - p3_f) < p3_t1,
      )
   )
)

# Sequence 5: t2
s5_t1, s5_t2, s5_t3 = 0, 0, 0
s.add( l5 >= 0 )
s.add(
   ForAll([l5],
      Or(
         mu_p1 + (t1_p1-p1_t1)*s5_t1 + (t2_p1-p1_t2)*s5_t2 + (t3_p1-p1_t3)*s5_t3 + l5 * (f_p1 - p1_f) < p1_t2,
         mu_p2 + (t1_p2-p2_t1)*s5_t1 + (t2_p2-p2_t2)*s5_t2 + (t3_p2-p2_t3)*s5_t3 + l5 * (f_p2 - p2_f) < p2_t2,
         mu_p3 + (t1_p3-p3_t1)*s5_t1 + (t2_p3-p3_t2)*s5_t2 + (t3_p3-p3_t3)*s5_t3 + l5 * (f_p3 - p3_f) < p3_t2,
      )
   )
)

# Sequence 6: t1,t1
s6_t1, s6_t2, s6_t3 = 1, 0, 0
s.add( l6 >= 0 )
s.add(
   ForAll([l6],
      Or(
         mu_p1 + (t1_p1-p1_t1)*s6_t1 + (t2_p1-p1_t2)*s6_t2 + (t3_p1-p1_t3)*s6_t3 + l6 * (f_p1 - p1_f) < p1_t1,
         mu_p2 + (t1_p2-p2_t1)*s6_t1 + (t2_p2-p2_t2)*s6_t2 + (t3_p2-p2_t3)*s6_t3 + l6 * (f_p2 - p2_f) < p2_t1,
         mu_p3 + (t1_p3-p3_t1)*s6_t1 + (t2_p3-p3_t2)*s6_t2 + (t3_p3-p3_t3)*s6_t3 + l6 * (f_p3 - p3_f) < p3_t1,
      )
   )
)

# Sequence 7: t1,t3
s7_t1, s7_t2, s7_t3 = 1, 0, 0
s.add( l7 >= 0 )
s.add(
   ForAll([l7],
      Or(
         mu_p1 + (t1_p1-p1_t1)*s7_t1 + (t2_p1-p1_t2)*s7_t2 + (t3_p1-p1_t3)*s7_t3 + l7 * (f_p1 - p1_f) < p1_t3,
         mu_p2 + (t1_p2-p2_t1)*s7_t1 + (t2_p2-p2_t2)*s7_t2 + (t3_p2-p2_t3)*s7_t3 + l7 * (f_p2 - p2_f) < p2_t3,
         mu_p3 + (t1_p3-p3_t1)*s7_t1 + (t2_p3-p3_t2)*s7_t2 + (t3_p3-p3_t3)*s7_t3 + l7 * (f_p3 - p3_f) < p3_t3,
      )
   )
)

# Sequence 8: t3,t1
s8_t1, s8_t2, s8_t3 = 0, 0, 1
s.add( l8 >= 0 )
s.add(
   ForAll([l8],
      Or(
         mu_p1 + (t1_p1-p1_t1)*s8_t1 + (t2_p1-p1_t2)*s8_t2 + (t3_p1-p1_t3)*s8_t3 + l8 * (f_p1 - p1_f) < p1_t1,
         mu_p2 + (t1_p2-p2_t1)*s8_t1 + (t2_p2-p2_t2)*s8_t2 + (t3_p2-p2_t3)*s8_t3 + l8 * (f_p2 - p2_f) < p2_t1,
         mu_p3 + (t1_p3-p3_t1)*s8_t1 + (t2_p3-p3_t2)*s8_t2 + (t3_p3-p3_t3)*s8_t3 + l8 * (f_p3 - p3_f) < p3_t1,
      )
   )
)

# Sequence 9: t3,t2
s9_t1, s9_t2, s9_t3 = 0, 0, 1
s.add( l9 >= 0 )
s.add(
   ForAll([l9],
      Or(
         mu_p1 + (t1_p1-p1_t1)*s9_t1 + (t2_p1-p1_t2)*s9_t2 + (t3_p1-p1_t3)*s9_t3 + l9 * (f_p1 - p1_f) < p1_t2,
         mu_p2 + (t1_p2-p2_t1)*s9_t1 + (t2_p2-p2_t2)*s9_t2 + (t3_p2-p2_t3)*s9_t3 + l9 * (f_p2 - p2_f) < p2_t2,
         mu_p3 + (t1_p3-p3_t1)*s9_t1 + (t2_p3-p3_t2)*s9_t2 + (t3_p3-p3_t3)*s9_t3 + l9 * (f_p3 - p3_f) < p3_t2,
      )
   )
)

# Sequence 10: t3,t3
s10_t1, s10_t2, s10_t3 = 0, 0, 1
s.add( l10 >= 0 )
s.add(
   ForAll([l10],
      Or(
         mu_p1 + (t1_p1-p1_t1)*s10_t1 + (t2_p1-p1_t2)*s10_t2 + (t3_p1-p1_t3)*s10_t3 + l10 * (f_p1 - p1_f) < p1_t3,
         mu_p2 + (t1_p2-p2_t1)*s10_t1 + (t2_p2-p2_t2)*s10_t2 + (t3_p2-p2_t3)*s10_t3 + l10 * (f_p2 - p2_f) < p2_t3,
         mu_p3 + (t1_p3-p3_t1)*s10_t1 + (t2_p3-p3_t2)*s10_t2 + (t3_p3-p3_t3)*s10_t3 + l10 * (f_p3 - p3_f) < p3_t3,
      )
   )
)

# Sequence 11: t1,t2,t2
s11_t1, s11_t2, s11_t3 = 1, 1, 0
s.add( l11 >= 0 )
s.add(
   ForAll([l11],
      Or(
         mu_p1 + (t1_p1-p1_t1)*s11_t1 + (t2_p1-p1_t2)*s11_t2 + (t3_p1-p1_t3)*s11_t3 + l11 * (f_p1 - p1_f) < p1_t2,
         mu_p2 + (t1_p2-p2_t1)*s11_t1 + (t2_p2-p2_t2)*s11_t2 + (t3_p2-p2_t3)*s11_t3 + l11 * (f_p2 - p2_f) < p2_t2,
         mu_p3 + (t1_p3-p3_t1)*s11_t1 + (t2_p3-p3_t2)*s11_t2 + (t3_p3-p3_t3)*s11_t3 + l11 * (f_p3 - p3_f) < p3_t2,
      )
   )
)


print(s)
print(s.check())
print(s.model())
#print(s.sexpr());print('(check-sat)\n(get-model)')
