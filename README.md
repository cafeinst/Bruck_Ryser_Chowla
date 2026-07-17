# Bruck–Ryser–Chowla Theorem in Isabelle/HOL

This repository contains a machine-checked formalization of the Bruck–Ryser–Chowla theorem for symmetric balanced incomplete block designs in Isabelle/HOL.

The formalization proves both parts of the theorem:

- If the order v is even, then k − λ is a perfect square.
- If the order v is odd, then there exist integers x, y, and z, not all zero, satisfying:

  x² = (k − λ)y² + (−1)^((v − 1)/2) λz².

The proof uses the incidence-matrix quadratic identity, a four-square change of variables, rational diagonal elimination, and the clearing of denominators to obtain integer solutions.

The formalization follows the proof presented by Douglas R. Stinson in *Combinatorial Designs: Constructions and Analysis*.

## Main theorems

- `bruck_ryser_chowla_even`
- `bruck_ryser_chowla_odd`

The Isabelle theory contains no `sorry` statements or additional axioms.

## Dependencies

- Isabelle/HOL
- `Fishers_Inequality`
- `SumSquares`
- `Pell`

## Author

Craig Alan Feinstein
