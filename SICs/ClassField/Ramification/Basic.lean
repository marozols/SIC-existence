/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import SICs.Source

/-!
# Ramification index one and trivial inertia

Ramification index one in towers, and its equivalence with trivial inertia at a prime over a
nonzero prime in a Galois extension of number fields.

This module follows [83, Neukirch (1999), Chapter I, Proposition 9.6]. It supplies the
ideal-theoretic and Galois facts used by `SICs.ClassField.Frobenius.Basic` and
`SICs.ClassField.Ramification.Kummer`.

## The argument

In a tower, each relative ramification index divides the total index, so both are one when the
total index is one. In a Galois extension of number fields, inertia has cardinality equal to the
ramification index, so inertia is trivial exactly when the index is one.
-/

noncomputable section

open NumberField

namespace SIC

universe u

/-! ### Ramification indices in a tower

Each relative index divides the total index, so either is one when the total index is one. -/

/-- If $e(r\mid R)=1$ in a tower $R\subseteq S\subseteq T$, then $e(q\mid R)=1$ for the
prime $q$ below $r$. -/
theorem ramificationIdx_below_eq_one {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (q : Ideal S) (r : Ideal T) [r.LiesOver q] [Module.Flat S T]
    (h : r.ramificationIdx R = 1) : q.ramificationIdx R = 1 :=
  Nat.eq_one_of_dvd_one (h ▸ Ideal.ramificationIdx_below_dvd q r)

/-- If $e(r\mid R)=1$ in a tower $R\subseteq S\subseteq T$, then $e(r\mid S)=1$. -/
theorem ramificationIdx_above_eq_one {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (q : Ideal S) (r : Ideal T) [r.LiesOver q] [Module.Flat S T]
    (h : r.ramificationIdx R = 1) : r.ramificationIdx S = 1 :=
  Nat.eq_one_of_dvd_one (h ▸ Ideal.ramificationIdx_above_dvd q r)

/-! ### Trivial inertia

For a nonzero prime in a Galois extension of number fields, the order of inertia is the
ramification index [83, Neukirch (1999), Chapter I, Proposition 9.6]. -/

variable {K : Type u} [Field K] [NumberField K]

/-- **Trivial inertia at a prime of ramification index one**: if `L/K` is a Galois extension of
number fields and `𝔓` is a prime of `𝒪_L` above `𝔭 ≠ 0` with `e(𝔓|𝔭) = 1`, its inertia group in
`Gal(L/K)` is trivial, since that group has order `e(𝔓|𝔭)` [83, Neukirch (1999), Chapter I,
Proposition 9.6] (`Ideal.card_inertia_eq_ramificationIdxIn`). -/
@[source "83, Chapter I, Proposition 9.6, p. 57 (#I_𝔓 = e, at e = 1)"]
theorem inertia_eq_bot_of_ramificationIdx_eq_one {L : Type*} [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] {p : Ideal (𝓞 K)} (hp : p ≠ ⊥) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    [𝔓.LiesOver p] (h : 𝔓.ramificationIdx (𝓞 K) = 1) : 𝔓.inertia (L ≃ₐ[K] L) = ⊥ := by
  have : p.IsPrime := Ideal.isPrime_of_liesOver 𝔓 p
  have : p.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot p hp
  have : Finite ((𝓞 K) ⧸ p) := inferInstance
  have : Finite p.ResidueField := inferInstance
  have : PerfectField p.ResidueField := PerfectField.ofFinite
  apply Subgroup.eq_bot_of_card_eq
  calc
    Nat.card ↑(𝔓.inertia (L ≃ₐ[K] L)) = p.ramificationIdxIn (𝓞 L) :=
      Ideal.card_inertia_eq_ramificationIdxIn p 𝔓
    _ = 𝔓.ramificationIdx (𝓞 K) :=
      Ideal.ramificationIdxIn_eq_ramificationIdx p 𝔓 (L ≃ₐ[K] L)
    _ = 1 := h

/-- **Ramification index one from trivial inertia**: the converse of
`inertia_eq_bot_of_ramificationIdx_eq_one`, since the inertia group of `𝔓` has order
`e(𝔓|𝔭)` [83, Neukirch (1999), Chapter I, Proposition 9.6]. -/
@[source "83, Chapter I, Proposition 9.6, p. 57 (#I_𝔓 = e, converse at e = 1)"]
theorem ramificationIdx_eq_one_of_inertia_eq_bot {L : Type*} [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] {p : Ideal (𝓞 K)} (hp : p ≠ ⊥) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime]
    [𝔓.LiesOver p] (h : 𝔓.inertia (L ≃ₐ[K] L) = ⊥) : 𝔓.ramificationIdx (𝓞 K) = 1 := by
  have : p.IsPrime := Ideal.isPrime_of_liesOver 𝔓 p
  have : p.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot p hp
  have : Finite ((𝓞 K) ⧸ p) := inferInstance
  have : Finite p.ResidueField := inferInstance
  have : PerfectField p.ResidueField := PerfectField.ofFinite
  calc
    𝔓.ramificationIdx (𝓞 K) = p.ramificationIdxIn (𝓞 L) :=
      (Ideal.ramificationIdxIn_eq_ramificationIdx p 𝔓 (L ≃ₐ[K] L)).symm
    _ = Nat.card ↑(𝔓.inertia (L ≃ₐ[K] L)) :=
      (Ideal.card_inertia_eq_ramificationIdxIn p 𝔓).symm
    _ = 1 := by rw [h, Subgroup.card_bot]


end SIC

end
