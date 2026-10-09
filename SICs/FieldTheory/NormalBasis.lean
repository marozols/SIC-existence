/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.FieldTheory.Galois.NormalBasis

/-!
# Coordinates in a normal basis

The Galois group permutes a normal basis of a finite Galois extension `L/K`, so it permutes the
coordinates of every element in that basis, and the coordinate at `1` of the trace
$\sum_\sigma \sigma x$ is the sum of all coordinates of `x`.

These are the computations behind the statement that `L` is a free $K[G]$-module on one
generator (Mathlib's `IsGalois.normalBasis`), used for the normal-basis lattice of Serre,
*Local class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number
Theory* (1967), Chapter VI, §1.4, Proposition 3, in `SICs.ClassField.Local.UnitCohomology`.

## The argument

Mathlib's normal basis `b` satisfies $b_\sigma = \sigma(b_1)$, so $\tau(b_\sigma) = b_{\tau\sigma}$.
Writing $x = \sum_\rho c_\rho b_\rho$ gives $\tau x = \sum_\rho c_\rho b_{\tau\rho}$, whose
coordinate at `σ` is $c_{\tau^{-1}\sigma}$. Summing over `τ`, the coordinate at `1` of
$\sum_\tau \tau x$ is $\sum_\tau c_{\tau^{-1}} = \sum_\rho c_\rho$.
-/

namespace SIC

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The Galois group permutes the normal basis: $\tau(b_\sigma) = b_{\tau\sigma}$.
Mathlib's `IsGalois.normalBasis_apply`. -/
theorem algEquiv_normalBasis (τ σ : L ≃ₐ[K] L) :
    τ (IsGalois.normalBasis K L σ) = IsGalois.normalBasis K L (τ * σ) := by
  rw [IsGalois.normalBasis_apply σ, IsGalois.normalBasis_apply (τ * σ),
    AlgEquiv.mul_apply]

/-- The Galois group permutes normal-basis coordinates: the coordinate of $\tau x$ at `σ` is the
coordinate of `x` at $\tau^{-1}\sigma$. Derived from `algEquiv_normalBasis`. -/
theorem normalBasis_repr_algEquiv (τ : L ≃ₐ[K] L) (x : L) (σ : L ≃ₐ[K] L) :
    (IsGalois.normalBasis K L).repr (τ x) σ = (IsGalois.normalBasis K L).repr x (τ⁻¹ * σ) := by
  let b := IsGalois.normalBasis K L
  have hx : τ x = ∑ ρ : L ≃ₐ[K] L, b.repr x ρ • b (τ * ρ) := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul]
    congr 1
    ext ρ
    rw [algEquiv_normalBasis]
  have hsum : (∑ ρ : L ≃ₐ[K] L, b.repr x ρ • b (τ * ρ)) =
      ∑ ρ : L ≃ₐ[K] L, b.repr x (τ⁻¹ * ρ) • b ρ := by
    apply Fintype.sum_equiv (Equiv.mulLeft τ)
    intro ρ
    simp
  rw [hx, hsum, b.repr_sum_self]

/-- The coordinate at `1` of the trace $\sum_\sigma \sigma x$ is the sum of the coordinates of
`x`. Derived from `normalBasis_repr_algEquiv`. -/
theorem normalBasis_repr_sum_algEquiv (x : L) :
    (IsGalois.normalBasis K L).repr (∑ σ : L ≃ₐ[K] L, σ x) 1 =
      ∑ σ : L ≃ₐ[K] L, (IsGalois.normalBasis K L).repr x σ := by
  let b := IsGalois.normalBasis K L
  rw [map_sum]
  rw [Finsupp.finsetSum_apply]
  simp_rw [normalBasis_repr_algEquiv, mul_one]
  apply Fintype.sum_equiv (Equiv.inv (L ≃ₐ[K] L))
  intro σ
  simp

end SIC
