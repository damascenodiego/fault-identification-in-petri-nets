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
s.add( f_p1 == 1, f_p2 == 0, f_p3 == 0 )
s.add( p1_f == 0, p2_f == 0, p3_f == 1 )

## l \in Naturals ; 
l11 = Int('l11')

# Sequence 11: t1,t2,t3
s11_t1, s11_t2, s11_t3 = 1, 1, 0


# # It does not work! :(
# s.add( l11 == 1 )
# s.add(
#    ForAll([l11],
#       Or(
#          mu_p1 + (t1_p1-p1_t1)*s11_t1 + (t2_p1-p1_t2)*s11_t2 + (t3_p1-p1_t3)*s11_t3 + l11 * (f_p1 - p1_f) < p1_t3,
#          mu_p2 + (t1_p2-p2_t1)*s11_t1 + (t2_p2-p2_t2)*s11_t2 + (t3_p2-p2_t3)*s11_t3 + l11 * (f_p2 - p2_f) < p2_t3,
#          mu_p3 + (t1_p3-p3_t1)*s11_t1 + (t2_p3-p3_t2)*s11_t2 + (t3_p3-p3_t3)*s11_t3 + l11 * (f_p3 - p3_f) < p3_t3,
#       )
#    )
# )


# It works!
l11 = 1
s.add(
   # ForAll([l11],
      Or(
         mu_p1 + (t1_p1-p1_t1)*s11_t1 + (t2_p1-p1_t2)*s11_t2 + (t3_p1-p1_t3)*s11_t3 + l11 * (f_p1 - p1_f) < p1_t3,
         mu_p2 + (t1_p2-p2_t1)*s11_t1 + (t2_p2-p2_t2)*s11_t2 + (t3_p2-p2_t3)*s11_t3 + l11 * (f_p2 - p2_f) < p2_t3,
         mu_p3 + (t1_p3-p3_t1)*s11_t1 + (t2_p3-p3_t2)*s11_t2 + (t3_p3-p3_t3)*s11_t3 + l11 * (f_p3 - p3_f) < p3_t3,
      )
   # )
)


print(s)
print(s.check())
print(s.model())