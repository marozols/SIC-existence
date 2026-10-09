/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.RingTheory.NormTrace

/-!
# Degree-Two Algebras

Shared `Fin 2` bases and the degree-two trace–norm relation.

This file supplies the shared linear-algebra infrastructure for degree-two algebras. A finite
free module of rank two first receives a basis indexed by `Fin 2`. For a commutative algebra with
such a basis, the characteristic polynomial of left multiplication by `x` is

`X² - Tr(x) X + Nm(x)`.

Evaluating this polynomial at `x` through Cayley--Hamilton gives

`x² = Tr(x) x - Nm(x)`.

The statements use only the module and algebra hypotheses needed for these constructions, so
number fields and their rings of integers can share the same coordinate convention and proof.

## Main definitions and results

- `DegreeTwoAlgebra.basisFinTwo`: a `Fin 2`-indexed basis of a finite free rank-two module.
- `DegreeTwoAlgebra.charpoly_lmul_eq_trace_norm_of_basis`: the trace--norm characteristic
  polynomial of left multiplication.
- `DegreeTwoAlgebra.sq_eq_trace_mul_sub_norm_of_basis`: the degree-two trace--norm form of
  Cayley--Hamilton.

## References

- Cayley--Hamilton, as formalized by Mathlib's `Algebra.aeval_self_charpoly_lmul`
-/

noncomputable section

namespace SIC

namespace DegreeTwoAlgebra

/-- A basis of a finite free rank-two module, indexed by `Fin 2`.

This specializes Mathlib's `Module.finBasisOfFinrankEq` to degree two. -/
noncomputable def basisFinTwo (R M : Type*) [Semiring R] [StrongRankCondition R]
    [AddCommMonoid M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (hfin : Module.finrank R M = 2) : Module.Basis (Fin 2) R M :=
  Module.finBasisOfFinrankEq R M hfin

/-- With respect to a `Fin 2` basis, left multiplication by `x` has characteristic polynomial
`X² - Tr(x) X + Nm(x)`.

This combines Mathlib's two-by-two characteristic-polynomial formula with its matrix formulas
for algebra trace and norm. -/
lemma charpoly_lmul_eq_trace_norm_of_basis (R S : Type*) [CommRing R] [Nontrivial R]
    [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]
    (b : Module.Basis (Fin 2) R S) (x : S) :
    (Algebra.lmul R S x).charpoly =
      Polynomial.X ^ 2 - Polynomial.C (Algebra.trace R S x) * Polynomial.X +
        Polynomial.C (Algebra.norm R x) := by
  rw [← LinearMap.charpoly_toMatrix (Algebra.lmul R S x) b]
  change (Algebra.leftMulMatrix b x).charpoly = _
  rw [Matrix.charpoly_fin_two, Algebra.trace_eq_matrix_trace b,
    Algebra.norm_eq_matrix_det b]

/-- A degree-two commutative algebra element satisfies
`x² = Tr(x) x - Nm(x)`.

This is the `Fin 2` matrix specialization of Cayley--Hamilton, using Mathlib's
`Algebra.aeval_self_charpoly_lmul`. -/
lemma sq_eq_trace_mul_sub_norm_of_basis (R S : Type*) [CommRing R] [Nontrivial R]
    [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]
    (b : Module.Basis (Fin 2) R S) (x : S) :
    x ^ 2 = algebraMap R S (Algebra.trace R S x) * x -
      algebraMap R S (Algebra.norm R x) := by
  have h := Algebra.aeval_self_charpoly_lmul (R := R) x
  rw [charpoly_lmul_eq_trace_norm_of_basis R S b x] at h
  simp only [map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C] at h
  linear_combination h

end DegreeTwoAlgebra

end SIC
