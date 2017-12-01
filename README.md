# dieudonne-modules

This is Magma code for computing the mod p Dieudonne module of the Jacobian of
a hyperelliptic curve over F_p. Elementary modifications to the code will allow
one to compute the canonical and final types for the Jacobian of any
hyperelliptic curve the user may desire.

In its current state (v1), the code is not optimal --- improvements are
certainly possible. For a fixed curve, the code runs quickly, but it grows
exponentially in the genus when counting the different final types (for a fixed
prime p).

The reader is referred to Devalapurkar-Halliday, "The Dieudonn'e modules and
Ekedahl-Oort types of Jacobians of hyperelliptic curves in odd characteristic",
for a derivation of the formulae implemented here.
