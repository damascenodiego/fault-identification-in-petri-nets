#!/bin/python

from z3 import *

# we have that
s = Solver()
## mu0_px is the initial marking for place px; 
mu_p1, mu_p2, mu_p3 = 0, 1, 0

## pi_tj is the pre-condition from place pi to transition tj
p1_t1, p1_t2, p1_t3 = 1, 0, 0
p2_t1, p2_t2, p2_t3 = 0, 1, 0
p3_t1, p3_t2, p3_t3 = 0, 0, 1

## tj_pi is the post-condition from transition tj to place pi
t1_p1, t2_p1, t3_p1 = 0, 0, 1
t1_p2, t2_p2, t3_p2 = 1, 0, 1
t1_p3, t2_p3, t3_p3 = 0, 1, 0

## find the values for the faulty transitions 
f_p1, p1_f = Ints('f_p1 p1_f')
f_p2, p2_f = Ints('f_p2 p2_f')
f_p3, p3_f = Ints('f_p3 p3_f')

# where they should be 
s.add( f_p1 >= 0, f_p2 >= 0, f_p3 >= 0 )
s.add( p1_f >= 0, p2_f >= 0, p3_f >= 0 )

# and no self-loop should exist
s.add(
   And(
      Or(And((f_p1 >= 0, p1_f == 0)),And((f_p1 == 0, p1_f >= 0)),And((f_p1 == 0, p1_f == 0))),
      Or(And((f_p2 >= 0, p2_f == 0)),And((f_p2 == 0, p2_f >= 0)),And((f_p2 == 0, p2_f == 0))),
      Or(And((f_p3 >= 0, p3_f == 0)),And((f_p3 == 0, p3_f >= 0)),And((f_p3 == 0, p3_f == 0))),
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
l9 = Int('l9')
l10 = Int('l10')
l11 = Int('l11')
l12 = Int('l12')
l13 = Int('l13')
l14 = Int('l14')
l15 = Int('l15')
l16 = Int('l16')
l17 = Int('l17')
l18 = Int('l18')
l19 = Int('l19')
l20 = Int('l20')
l21 = Int('l21')
l22 = Int('l22')
l23 = Int('l23')
l24 = Int('l24')
l25 = Int('l25')
l26 = Int('l26')
l27 = Int('l27')
l28 = Int('l28')
l29 = Int('l29')

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
         mu_p3 + (t1_p3-p3_t1)*s0_t1 + (t2_p3-p3_t2)*s0_t2 + (t3_p3-p3_t3)*s0_t3 + l0 * (f_p3 - p3_f) >= p3_t1,
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
         mu_p3 + (t1_p3-p3_t1)*s1_t1 + (t2_p3-p3_t2)*s1_t2 + (t3_p3-p3_t3)*s1_t3 + l1 * (f_p3 - p3_f) >= p3_t2,
      )
      ))
   )
)

# Sequence 2: t1,t1
s2_t1, s2_t2, s2_t3 = 1, 0, 0
s.add(
   Exists([l2],
      And( Implies(l2 >= 0, 
      And(l2 >= 0, 
         mu_p1 + (t1_p1-p1_t1)*s2_t1 + (t2_p1-p1_t2)*s2_t2 + (t3_p1-p1_t3)*s2_t3 + l2 * (f_p1 - p1_f) >= p1_t1,
         mu_p2 + (t1_p2-p2_t1)*s2_t1 + (t2_p2-p2_t2)*s2_t2 + (t3_p2-p2_t3)*s2_t3 + l2 * (f_p2 - p2_f) >= p2_t1,
         mu_p3 + (t1_p3-p3_t1)*s2_t1 + (t2_p3-p3_t2)*s2_t2 + (t3_p3-p3_t3)*s2_t3 + l2 * (f_p3 - p3_f) >= p3_t1,
      )
      ))
   )
)

# Sequence 3: t1,t2
s3_t1, s3_t2, s3_t3 = 1, 0, 0
s.add(
   Exists([l3],
      And( Implies(l3 >= 0, 
      And(l3 >= 0, 
         mu_p1 + (t1_p1-p1_t1)*s3_t1 + (t2_p1-p1_t2)*s3_t2 + (t3_p1-p1_t3)*s3_t3 + l3 * (f_p1 - p1_f) >= p1_t2,
         mu_p2 + (t1_p2-p2_t1)*s3_t1 + (t2_p2-p2_t2)*s3_t2 + (t3_p2-p2_t3)*s3_t3 + l3 * (f_p2 - p2_f) >= p2_t2,
         mu_p3 + (t1_p3-p3_t1)*s3_t1 + (t2_p3-p3_t2)*s3_t2 + (t3_p3-p3_t3)*s3_t3 + l3 * (f_p3 - p3_f) >= p3_t2,
      )
      ))
   )
)

# Sequence 4: t2,t3
s4_t1, s4_t2, s4_t3 = 0, 1, 0
s.add(
   Exists([l4],
      And( Implies(l4 >= 0, 
      And(l4 >= 0, 
         mu_p1 + (t1_p1-p1_t1)*s4_t1 + (t2_p1-p1_t2)*s4_t2 + (t3_p1-p1_t3)*s4_t3 + l4 * (f_p1 - p1_f) >= p1_t3,
         mu_p2 + (t1_p2-p2_t1)*s4_t1 + (t2_p2-p2_t2)*s4_t2 + (t3_p2-p2_t3)*s4_t3 + l4 * (f_p2 - p2_f) >= p2_t3,
         mu_p3 + (t1_p3-p3_t1)*s4_t1 + (t2_p3-p3_t2)*s4_t2 + (t3_p3-p3_t3)*s4_t3 + l4 * (f_p3 - p3_f) >= p3_t3,
      )
      ))
   )
)

# Sequence 5: t1,t1,t1
s5_t1, s5_t2, s5_t3 = 2, 0, 0
s.add(
   Exists([l5],
      And( Implies(l5 >= 0, 
      And(l5 >= 0, 
         mu_p1 + (t1_p1-p1_t1)*s5_t1 + (t2_p1-p1_t2)*s5_t2 + (t3_p1-p1_t3)*s5_t3 + l5 * (f_p1 - p1_f) >= p1_t1,
         mu_p2 + (t1_p2-p2_t1)*s5_t1 + (t2_p2-p2_t2)*s5_t2 + (t3_p2-p2_t3)*s5_t3 + l5 * (f_p2 - p2_f) >= p2_t1,
         mu_p3 + (t1_p3-p3_t1)*s5_t1 + (t2_p3-p3_t2)*s5_t2 + (t3_p3-p3_t3)*s5_t3 + l5 * (f_p3 - p3_f) >= p3_t1,
      )
      ))
   )
)

# Sequence 6: t1,t1,t2
s6_t1, s6_t2, s6_t3 = 2, 0, 0
s.add(
   Exists([l6],
      And( Implies(l6 >= 0, 
      And(l6 >= 0, 
         mu_p1 + (t1_p1-p1_t1)*s6_t1 + (t2_p1-p1_t2)*s6_t2 + (t3_p1-p1_t3)*s6_t3 + l6 * (f_p1 - p1_f) >= p1_t2,
         mu_p2 + (t1_p2-p2_t1)*s6_t1 + (t2_p2-p2_t2)*s6_t2 + (t3_p2-p2_t3)*s6_t3 + l6 * (f_p2 - p2_f) >= p2_t2,
         mu_p3 + (t1_p3-p3_t1)*s6_t1 + (t2_p3-p3_t2)*s6_t2 + (t3_p3-p3_t3)*s6_t3 + l6 * (f_p3 - p3_f) >= p3_t2,
      )
      ))
   )
)

# Sequence 7: t1,t2,t3
s7_t1, s7_t2, s7_t3 = 1, 1, 0
s.add(
   Exists([l7],
      And( Implies(l7 >= 0, 
      And(l7 >= 0, 
         mu_p1 + (t1_p1-p1_t1)*s7_t1 + (t2_p1-p1_t2)*s7_t2 + (t3_p1-p1_t3)*s7_t3 + l7 * (f_p1 - p1_f) >= p1_t3,
         mu_p2 + (t1_p2-p2_t1)*s7_t1 + (t2_p2-p2_t2)*s7_t2 + (t3_p2-p2_t3)*s7_t3 + l7 * (f_p2 - p2_f) >= p2_t3,
         mu_p3 + (t1_p3-p3_t1)*s7_t1 + (t2_p3-p3_t2)*s7_t2 + (t3_p3-p3_t3)*s7_t3 + l7 * (f_p3 - p3_f) >= p3_t3,
      )
      ))
   )
)

# Sequence 8: t2,t3,t1
s8_t1, s8_t2, s8_t3 = 0, 1, 1
s.add(
   Exists([l8],
      And( Implies(l8 >= 0, 
      And(l8 >= 0, 
         mu_p1 + (t1_p1-p1_t1)*s8_t1 + (t2_p1-p1_t2)*s8_t2 + (t3_p1-p1_t3)*s8_t3 + l8 * (f_p1 - p1_f) >= p1_t1,
         mu_p2 + (t1_p2-p2_t1)*s8_t1 + (t2_p2-p2_t2)*s8_t2 + (t3_p2-p2_t3)*s8_t3 + l8 * (f_p2 - p2_f) >= p2_t1,
         mu_p3 + (t1_p3-p3_t1)*s8_t1 + (t2_p3-p3_t2)*s8_t2 + (t3_p3-p3_t3)*s8_t3 + l8 * (f_p3 - p3_f) >= p3_t1,
      )
      ))
   )
)

# Sequence 9: t2,t3,t2
s9_t1, s9_t2, s9_t3 = 0, 1, 1
s.add(
   Exists([l9],
      And( Implies(l9 >= 0, 
      And(l9 >= 0, 
         mu_p1 + (t1_p1-p1_t1)*s9_t1 + (t2_p1-p1_t2)*s9_t2 + (t3_p1-p1_t3)*s9_t3 + l9 * (f_p1 - p1_f) >= p1_t2,
         mu_p2 + (t1_p2-p2_t1)*s9_t1 + (t2_p2-p2_t2)*s9_t2 + (t3_p2-p2_t3)*s9_t3 + l9 * (f_p2 - p2_f) >= p2_t2,
         mu_p3 + (t1_p3-p3_t1)*s9_t1 + (t2_p3-p3_t2)*s9_t2 + (t3_p3-p3_t3)*s9_t3 + l9 * (f_p3 - p3_f) >= p3_t2,
      )
      ))
   )
)

# Sequence 10: t2,t3,t1,t2
s10_t1, s10_t2, s10_t3 = 1, 1, 1
s.add(
   Exists([l10],
      And( Implies(l10 >= 0, 
      And(l10 >= 0, 
         mu_p1 + (t1_p1-p1_t1)*s10_t1 + (t2_p1-p1_t2)*s10_t2 + (t3_p1-p1_t3)*s10_t3 + l10 * (f_p1 - p1_f) >= p1_t2,
         mu_p2 + (t1_p2-p2_t1)*s10_t1 + (t2_p2-p2_t2)*s10_t2 + (t3_p2-p2_t3)*s10_t3 + l10 * (f_p2 - p2_f) >= p2_t2,
         mu_p3 + (t1_p3-p3_t1)*s10_t1 + (t2_p3-p3_t2)*s10_t2 + (t3_p3-p3_t3)*s10_t3 + l10 * (f_p3 - p3_f) >= p3_t2,
      )
      ))
   )
)

# Sequence 11: t2,t3,t1,t1
s11_t1, s11_t2, s11_t3 = 1, 1, 1
s.add(
   Exists([l11],
      And( Implies(l11 >= 0, 
      And(l11 >= 0, 
         mu_p1 + (t1_p1-p1_t1)*s11_t1 + (t2_p1-p1_t2)*s11_t2 + (t3_p1-p1_t3)*s11_t3 + l11 * (f_p1 - p1_f) >= p1_t1,
         mu_p2 + (t1_p2-p2_t1)*s11_t1 + (t2_p2-p2_t2)*s11_t2 + (t3_p2-p2_t3)*s11_t3 + l11 * (f_p2 - p2_f) >= p2_t1,
         mu_p3 + (t1_p3-p3_t1)*s11_t1 + (t2_p3-p3_t2)*s11_t2 + (t3_p3-p3_t3)*s11_t3 + l11 * (f_p3 - p3_f) >= p3_t1,
      )
      ))
   )
)

# Sequence 12: t2,t3,t2,t1
s12_t1, s12_t2, s12_t3 = 0, 2, 1
s.add(
   Exists([l12],
      And( Implies(l12 >= 0, 
      And(l12 >= 0, 
         mu_p1 + (t1_p1-p1_t1)*s12_t1 + (t2_p1-p1_t2)*s12_t2 + (t3_p1-p1_t3)*s12_t3 + l12 * (f_p1 - p1_f) >= p1_t1,
         mu_p2 + (t1_p2-p2_t1)*s12_t1 + (t2_p2-p2_t2)*s12_t2 + (t3_p2-p2_t3)*s12_t3 + l12 * (f_p2 - p2_f) >= p2_t1,
         mu_p3 + (t1_p3-p3_t1)*s12_t1 + (t2_p3-p3_t2)*s12_t2 + (t3_p3-p3_t3)*s12_t3 + l12 * (f_p3 - p3_f) >= p3_t1,
      )
      ))
   )
)

# Sequence 13: t2,t3,t2,t3
s13_t1, s13_t2, s13_t3 = 0, 2, 1
s.add(
   Exists([l13],
      And( Implies(l13 >= 0, 
      And(l13 >= 0, 
         mu_p1 + (t1_p1-p1_t1)*s13_t1 + (t2_p1-p1_t2)*s13_t2 + (t3_p1-p1_t3)*s13_t3 + l13 * (f_p1 - p1_f) >= p1_t3,
         mu_p2 + (t1_p2-p2_t1)*s13_t1 + (t2_p2-p2_t2)*s13_t2 + (t3_p2-p2_t3)*s13_t3 + l13 * (f_p2 - p2_f) >= p2_t3,
         mu_p3 + (t1_p3-p3_t1)*s13_t1 + (t2_p3-p3_t2)*s13_t2 + (t3_p3-p3_t3)*s13_t3 + l13 * (f_p3 - p3_f) >= p3_t3,
      )
      ))
   )
)

# Sequence 14: t1,t2,t3,t1
s14_t1, s14_t2, s14_t3 = 1, 1, 1
s.add(
   Exists([l14],
      And( Implies(l14 >= 0, 
      And(l14 >= 0, 
         mu_p1 + (t1_p1-p1_t1)*s14_t1 + (t2_p1-p1_t2)*s14_t2 + (t3_p1-p1_t3)*s14_t3 + l14 * (f_p1 - p1_f) >= p1_t1,
         mu_p2 + (t1_p2-p2_t1)*s14_t1 + (t2_p2-p2_t2)*s14_t2 + (t3_p2-p2_t3)*s14_t3 + l14 * (f_p2 - p2_f) >= p2_t1,
         mu_p3 + (t1_p3-p3_t1)*s14_t1 + (t2_p3-p3_t2)*s14_t2 + (t3_p3-p3_t3)*s14_t3 + l14 * (f_p3 - p3_f) >= p3_t1,
      )
      ))
   )
)

# Sequence 15: t1,t2,t3,t2
s15_t1, s15_t2, s15_t3 = 1, 1, 1
s.add(
   Exists([l15],
      And( Implies(l15 >= 0, 
      And(l15 >= 0, 
         mu_p1 + (t1_p1-p1_t1)*s15_t1 + (t2_p1-p1_t2)*s15_t2 + (t3_p1-p1_t3)*s15_t3 + l15 * (f_p1 - p1_f) >= p1_t2,
         mu_p2 + (t1_p2-p2_t1)*s15_t1 + (t2_p2-p2_t2)*s15_t2 + (t3_p2-p2_t3)*s15_t3 + l15 * (f_p2 - p2_f) >= p2_t2,
         mu_p3 + (t1_p3-p3_t1)*s15_t1 + (t2_p3-p3_t2)*s15_t2 + (t3_p3-p3_t3)*s15_t3 + l15 * (f_p3 - p3_f) >= p3_t2,
      )
      ))
   )
)

# Sequence 16: t1,t1,t1,t1
s16_t1, s16_t2, s16_t3 = 3, 0, 0
s.add(
   Exists([l16],
      And( Implies(l16 >= 0, 
      And(l16 >= 0, 
         mu_p1 + (t1_p1-p1_t1)*s16_t1 + (t2_p1-p1_t2)*s16_t2 + (t3_p1-p1_t3)*s16_t3 + l16 * (f_p1 - p1_f) >= p1_t1,
         mu_p2 + (t1_p2-p2_t1)*s16_t1 + (t2_p2-p2_t2)*s16_t2 + (t3_p2-p2_t3)*s16_t3 + l16 * (f_p2 - p2_f) >= p2_t1,
         mu_p3 + (t1_p3-p3_t1)*s16_t1 + (t2_p3-p3_t2)*s16_t2 + (t3_p3-p3_t3)*s16_t3 + l16 * (f_p3 - p3_f) >= p3_t1,
      )
      ))
   )
)

# Sequence 17: t1,t1,t1,t2
s17_t1, s17_t2, s17_t3 = 3, 0, 0
s.add(
   Exists([l17],
      And( Implies(l17 >= 0, 
      And(l17 >= 0, 
         mu_p1 + (t1_p1-p1_t1)*s17_t1 + (t2_p1-p1_t2)*s17_t2 + (t3_p1-p1_t3)*s17_t3 + l17 * (f_p1 - p1_f) >= p1_t2,
         mu_p2 + (t1_p2-p2_t1)*s17_t1 + (t2_p2-p2_t2)*s17_t2 + (t3_p2-p2_t3)*s17_t3 + l17 * (f_p2 - p2_f) >= p2_t2,
         mu_p3 + (t1_p3-p3_t1)*s17_t1 + (t2_p3-p3_t2)*s17_t2 + (t3_p3-p3_t3)*s17_t3 + l17 * (f_p3 - p3_f) >= p3_t2,
      )
      ))
   )
)


########################################
## \not \in L^f (Equation 4.2)
########################################
# Sequence 18: t3
s18_t1, s18_t2, s18_t3 = 0, 0, 0
s.add(
   ForAll([l18],
      And( Implies(l18 >= 0, 
      Or(
         And(l18 >= 0,  mu_p1 + (t1_p1-p1_t1)*s18_t1 + (t2_p1-p1_t2)*s18_t2 + (t3_p1-p1_t3)*s18_t3 + l18 * (f_p1 - p1_f) < p1_t3),
         And(l18 >= 0,  mu_p2 + (t1_p2-p2_t1)*s18_t1 + (t2_p2-p2_t2)*s18_t2 + (t3_p2-p2_t3)*s18_t3 + l18 * (f_p2 - p2_f) < p2_t3),
         And(l18 >= 0,  mu_p3 + (t1_p3-p3_t1)*s18_t1 + (t2_p3-p3_t2)*s18_t2 + (t3_p3-p3_t3)*s18_t3 + l18 * (f_p3 - p3_f) < p3_t3),
      )
      ))
   )
)

# Sequence 19: f,t1,t3
s19_t1, s19_t2, s19_t3 = 1, 0, 0
s.add(
   ForAll([l19],
      And( Implies(l19 >= 1, 
      Or(
         And(l19 >= 1,  mu_p1 + (t1_p1-p1_t1)*s19_t1 + (t2_p1-p1_t2)*s19_t2 + (t3_p1-p1_t3)*s19_t3 + l19 * (f_p1 - p1_f) < p1_t3),
         And(l19 >= 1,  mu_p2 + (t1_p2-p2_t1)*s19_t1 + (t2_p2-p2_t2)*s19_t2 + (t3_p2-p2_t3)*s19_t3 + l19 * (f_p2 - p2_f) < p2_t3),
         And(l19 >= 1,  mu_p3 + (t1_p3-p3_t1)*s19_t1 + (t2_p3-p3_t2)*s19_t2 + (t3_p3-p3_t3)*s19_t3 + l19 * (f_p3 - p3_f) < p3_t3),
      )
      ))
   )
)

# Sequence 20: t2,t1
s20_t1, s20_t2, s20_t3 = 0, 1, 0
s.add(
   ForAll([l20],
      And( Implies(l20 >= 0, 
      Or(
         And(l20 >= 0,  mu_p1 + (t1_p1-p1_t1)*s20_t1 + (t2_p1-p1_t2)*s20_t2 + (t3_p1-p1_t3)*s20_t3 + l20 * (f_p1 - p1_f) < p1_t1),
         And(l20 >= 0,  mu_p2 + (t1_p2-p2_t1)*s20_t1 + (t2_p2-p2_t2)*s20_t2 + (t3_p2-p2_t3)*s20_t3 + l20 * (f_p2 - p2_f) < p2_t1),
         And(l20 >= 0,  mu_p3 + (t1_p3-p3_t1)*s20_t1 + (t2_p3-p3_t2)*s20_t2 + (t3_p3-p3_t3)*s20_t3 + l20 * (f_p3 - p3_f) < p3_t1),
      )
      ))
   )
)

# Sequence 21: t2,t2
s21_t1, s21_t2, s21_t3 = 0, 1, 0
s.add(
   ForAll([l21],
      And( Implies(l21 >= 0, 
      Or(
         And(l21 >= 0,  mu_p1 + (t1_p1-p1_t1)*s21_t1 + (t2_p1-p1_t2)*s21_t2 + (t3_p1-p1_t3)*s21_t3 + l21 * (f_p1 - p1_f) < p1_t2),
         And(l21 >= 0,  mu_p2 + (t1_p2-p2_t1)*s21_t1 + (t2_p2-p2_t2)*s21_t2 + (t3_p2-p2_t3)*s21_t3 + l21 * (f_p2 - p2_f) < p2_t2),
         And(l21 >= 0,  mu_p3 + (t1_p3-p3_t1)*s21_t1 + (t2_p3-p3_t2)*s21_t2 + (t3_p3-p3_t3)*s21_t3 + l21 * (f_p3 - p3_f) < p3_t2),
      )
      ))
   )
)

# Sequence 22: f,t1,t1,t3
s22_t1, s22_t2, s22_t3 = 2, 0, 0
s.add(
   ForAll([l22],
      And( Implies(l22 >= 1, 
      Or(
         And(l22 >= 1,  mu_p1 + (t1_p1-p1_t1)*s22_t1 + (t2_p1-p1_t2)*s22_t2 + (t3_p1-p1_t3)*s22_t3 + l22 * (f_p1 - p1_f) < p1_t3),
         And(l22 >= 1,  mu_p2 + (t1_p2-p2_t1)*s22_t1 + (t2_p2-p2_t2)*s22_t2 + (t3_p2-p2_t3)*s22_t3 + l22 * (f_p2 - p2_f) < p2_t3),
         And(l22 >= 1,  mu_p3 + (t1_p3-p3_t1)*s22_t1 + (t2_p3-p3_t2)*s22_t2 + (t3_p3-p3_t3)*s22_t3 + l22 * (f_p3 - p3_f) < p3_t3),
      )
      ))
   )
)

# Sequence 23: f,t1,t2,t1
s23_t1, s23_t2, s23_t3 = 1, 1, 0
s.add(
   ForAll([l23],
      And( Implies(l23 >= 1, 
      Or(
         And(l23 >= 1,  mu_p1 + (t1_p1-p1_t1)*s23_t1 + (t2_p1-p1_t2)*s23_t2 + (t3_p1-p1_t3)*s23_t3 + l23 * (f_p1 - p1_f) < p1_t1),
         And(l23 >= 1,  mu_p2 + (t1_p2-p2_t1)*s23_t1 + (t2_p2-p2_t2)*s23_t2 + (t3_p2-p2_t3)*s23_t3 + l23 * (f_p2 - p2_f) < p2_t1),
         And(l23 >= 1,  mu_p3 + (t1_p3-p3_t1)*s23_t1 + (t2_p3-p3_t2)*s23_t2 + (t3_p3-p3_t3)*s23_t3 + l23 * (f_p3 - p3_f) < p3_t1),
      )
      ))
   )
)

# Sequence 24: f,t1,t2,t2
s24_t1, s24_t2, s24_t3 = 1, 1, 0
s.add(
   ForAll([l24],
      And( Implies(l24 >= 1, 
      Or(
         And(l24 >= 1,  mu_p1 + (t1_p1-p1_t1)*s24_t1 + (t2_p1-p1_t2)*s24_t2 + (t3_p1-p1_t3)*s24_t3 + l24 * (f_p1 - p1_f) < p1_t2),
         And(l24 >= 1,  mu_p2 + (t1_p2-p2_t1)*s24_t1 + (t2_p2-p2_t2)*s24_t2 + (t3_p2-p2_t3)*s24_t3 + l24 * (f_p2 - p2_f) < p2_t2),
         And(l24 >= 1,  mu_p3 + (t1_p3-p3_t1)*s24_t1 + (t2_p3-p3_t2)*s24_t2 + (t3_p3-p3_t3)*s24_t3 + l24 * (f_p3 - p3_f) < p3_t2),
      )
      ))
   )
)

# Sequence 25: t2,t3,t3
s25_t1, s25_t2, s25_t3 = 0, 1, 1
s.add(
   ForAll([l25],
      And( Implies(l25 >= 0, 
      Or(
         And(l25 >= 0,  mu_p1 + (t1_p1-p1_t1)*s25_t1 + (t2_p1-p1_t2)*s25_t2 + (t3_p1-p1_t3)*s25_t3 + l25 * (f_p1 - p1_f) < p1_t3),
         And(l25 >= 0,  mu_p2 + (t1_p2-p2_t1)*s25_t1 + (t2_p2-p2_t2)*s25_t2 + (t3_p2-p2_t3)*s25_t3 + l25 * (f_p2 - p2_f) < p2_t3),
         And(l25 >= 0,  mu_p3 + (t1_p3-p3_t1)*s25_t1 + (t2_p3-p3_t2)*s25_t2 + (t3_p3-p3_t3)*s25_t3 + l25 * (f_p3 - p3_f) < p3_t3),
      )
      ))
   )
)

# Sequence 26: t2,t3,t2,t2
s26_t1, s26_t2, s26_t3 = 0, 2, 1
s.add(
   ForAll([l26],
      And( Implies(l26 >= 0, 
      Or(
         And(l26 >= 0,  mu_p1 + (t1_p1-p1_t1)*s26_t1 + (t2_p1-p1_t2)*s26_t2 + (t3_p1-p1_t3)*s26_t3 + l26 * (f_p1 - p1_f) < p1_t2),
         And(l26 >= 0,  mu_p2 + (t1_p2-p2_t1)*s26_t1 + (t2_p2-p2_t2)*s26_t2 + (t3_p2-p2_t3)*s26_t3 + l26 * (f_p2 - p2_f) < p2_t2),
         And(l26 >= 0,  mu_p3 + (t1_p3-p3_t1)*s26_t1 + (t2_p3-p3_t2)*s26_t2 + (t3_p3-p3_t3)*s26_t3 + l26 * (f_p3 - p3_f) < p3_t2),
      )
      ))
   )
)

# Sequence 27: f,t2,t3,t1,t3
s27_t1, s27_t2, s27_t3 = 1, 1, 1
s.add(
   ForAll([l27],
      And( Implies(l27 >= 1, 
      Or(
         And(l27 >= 1,  mu_p1 + (t1_p1-p1_t1)*s27_t1 + (t2_p1-p1_t2)*s27_t2 + (t3_p1-p1_t3)*s27_t3 + l27 * (f_p1 - p1_f) < p1_t3),
         And(l27 >= 1,  mu_p2 + (t1_p2-p2_t1)*s27_t1 + (t2_p2-p2_t2)*s27_t2 + (t3_p2-p2_t3)*s27_t3 + l27 * (f_p2 - p2_f) < p2_t3),
         And(l27 >= 1,  mu_p3 + (t1_p3-p3_t1)*s27_t1 + (t2_p3-p3_t2)*s27_t2 + (t3_p3-p3_t3)*s27_t3 + l27 * (f_p3 - p3_f) < p3_t3),
      )
      ))
   )
)

# Sequence 28: f,t1,t1,t1,t3
s28_t1, s28_t2, s28_t3 = 3, 0, 0
s.add(
   ForAll([l28],
      And( Implies(l28 >= 1, 
      Or(
         And(l28 >= 1,  mu_p1 + (t1_p1-p1_t1)*s28_t1 + (t2_p1-p1_t2)*s28_t2 + (t3_p1-p1_t3)*s28_t3 + l28 * (f_p1 - p1_f) < p1_t3),
         And(l28 >= 1,  mu_p2 + (t1_p2-p2_t1)*s28_t1 + (t2_p2-p2_t2)*s28_t2 + (t3_p2-p2_t3)*s28_t3 + l28 * (f_p2 - p2_f) < p2_t3),
         And(l28 >= 1,  mu_p3 + (t1_p3-p3_t1)*s28_t1 + (t2_p3-p3_t2)*s28_t2 + (t3_p3-p3_t3)*s28_t3 + l28 * (f_p3 - p3_f) < p3_t3),
      )
      ))
   )
)

# Sequence 29: f,t1,t2,t3,t3
s29_t1, s29_t2, s29_t3 = 1, 1, 1
s.add(
   ForAll([l29],
      And( Implies(l29 >= 1, 
      Or(
         And(l29 >= 1,  mu_p1 + (t1_p1-p1_t1)*s29_t1 + (t2_p1-p1_t2)*s29_t2 + (t3_p1-p1_t3)*s29_t3 + l29 * (f_p1 - p1_f) < p1_t3),
         And(l29 >= 1,  mu_p2 + (t1_p2-p2_t1)*s29_t1 + (t2_p2-p2_t2)*s29_t2 + (t3_p2-p2_t3)*s29_t3 + l29 * (f_p2 - p2_f) < p2_t3),
         And(l29 >= 1,  mu_p3 + (t1_p3-p3_t1)*s29_t1 + (t2_p3-p3_t2)*s29_t2 + (t3_p3-p3_t3)*s29_t3 + l29 * (f_p3 - p3_f) < p3_t3),
      )
      ))
   )
)


print(s.check())
print(s.model())
#print(s.sexpr());print('(check-sat)\n(get-model)')
