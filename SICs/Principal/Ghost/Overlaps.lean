/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Ghost.OverlapData
import SICs.Principal.Ghost.DoubleSineProduct

/-!
# Principal Normalized Ghost Overlaps

`ν_d` on integer indices: realness, periodicity, `ν_d(p)ν_d(-p)=1`, and its `GhostOverlapData`.

This file defines the principal coefficient function `ν_d` on integer indices. It agrees with
the normalized ghost overlap of [AFK25, Definition 1.32, `dfn:GhostOverlaps`, equation (1.46),
`eq:ghostoverlapformula`] at the origin and outside the zero residue class, using the
three-factor double-sine product of `SICs.Principal.Ghost.DoubleSineProduct` at the canonical
representative, transported to an arbitrary integer index by the symplectic root of unity, with a
separate sign correction on the zero residue class. Its values at other points of that class are
an auxiliary extension, unused by the candidate operator. It proves that the overlap is real,
satisfies the quasi-periodicity of [AFK25, Lemma 5.7, `lem:nupperiodicity`], is `d̄`-periodic, and
obeys the reciprocity `ν_d(p) ν_d(-p) = 1` of [AFK25, Theorem 5.8, `thm:nupnumpeq1`] for every
index off the zero class. It then packages the real, quotient-indexed overlap as `GhostOverlapData`.

The reciprocity proof is elementary: reflection cancels the six double-sine factors of a nonzero
canonical pair and its negation, the boundary cancellation of
`SICs.Principal.Ghost.DoubleSineProduct` handles a zero coordinate, and a parity computation on
the sign exponent absorbs the transport phase. No cocycle or zeta-value input is used; the
identification with the phased real Shintani--Faddeev value is proved in
`SICs.Principal.Ghost.PhasedOverlaps`.

## Main definitions and results

- `principalNormGhostOverlap`: the overlap `ν_d` on integer indices, with
  `principalNormGhostOverlap_of_mod_ne_zero`, `_of_mod_eq_zero`, `_ne_zero`, and `_canonRep`.
- `principalNormGhostOverlap_isReal`: realness at every integer index.
- `principalNormGhostOverlap_transport` and `principalNormGhostOverlap_quasiperiodic`: the
  transport law between congruent indices, and [AFK25, Lemma 5.7, `lem:nupperiodicity`].
- `principalNormGhostOverlap_dbar_periodic`: periodicity modulo `d̄`.
- `principalNormGhostOverlapReal`: the real-valued overlap, with its cast and periodicity lemmas.
- `principalNormGhostOverlap_reciprocal_canon` and `principalNormGhostOverlap_reciprocal`: the
  reciprocity clause of [AFK25, Theorem 5.8, `thm:nupnumpeq1`], first at canonical
  representatives and then at every integer lift.
- `principalNormGhostOverlapQuotient` and `principalGhostOverlapData`: the quotient-indexed
  overlap and the faithful `GhostOverlapData d` instance.

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Definition 1.32, Lemma 5.7, and
  Theorem 5.8
- [42, Flammia (2024), Zauner.jl]
-/

noncomputable section

namespace SIC

/-! ### The integer-indexed normalized ghost overlap

The canonical three-factor value is extended to every integer phase-space lift with the required
root-of-unity transport law. A separate origin correction supplies the sign remaining after the
SF phase's exponential cancels the cocycle's exponential at the origin. The same corrected value
is assigned to the rest of the zero residue class as an auxiliary coefficient convention.
-/

/-- The principal coefficient function `ν_d`, on integer indices. It agrees with
[AFK25, Definition 1.32, `dfn:GhostOverlaps`, equation (1.46), `eq:ghostoverlapformula`] for the
principal tuple `t_d`, `ν̃_p(t_d) = Φ_{t_d}(p) ש^{p/d}_{A_d}(ρ_d)`, given in closed form rather than
through the cocycle, at the literal origin and outside the zero residue class. At other points of
the zero residue class its auxiliary extension need not agree with the source, whose value is
defined there as well. The candidate operator uses neither of those normalized values at such
indices. `SICs.Principal.Ghost.PhasedOverlaps`'s `principalPhasedGhostOverlap_eq_overlap` and
`principalPhasedGhostOverlap_zero` prove that this agrees with `principalPhasedGhostOverlap`
outside the zero residue class and at the literal origin.

Away from the zero residue class it is the canonical three-factor product at the canonical
representative, transported to the given integer index by the root-of-unity factor of
`principalNormGhostOverlap_transport`. Defining it instead by reducing indices modulo `d` would be
wrong: the exact overlaps are not `d`-periodic in even dimensions, where `ξ_d^d = -1`.

**Deviation from [42, Flammia (2024), Zauner.jl], on the zero residue class only.** The
three-factor product's sign exponent `principalSignExp` is the package's, and vanishes at `(0,0)`,
whereas the source's sign factor contributes `(-1)^{s_d(0)} = (-1)^{2d+1} = -1`. The full SF phase
also contains `exp(-πi Ψ(A_d)/12)`, which cancels the cocycle's exponential. The correction factor
below restores the remaining minus sign. `Zauner.jl`'s `_principal_ghost` never evaluates
`_triple_double_sine` at the origin -- it
writes the origin entry `√(d+1)` directly -- so its caller does not use the product formula there.
This definition assigns the origin value to the whole zero
residue class by canonical reduction. It does not assert that the source's regularized cocycle
has the same value at every integral characteristic: `sfModularCocycleReal_add_intVec` excludes
integral characteristics. -/
noncomputable def principalNormGhostOverlap (d : ℕ) [NeZero d] (p : IntPhaseSpace) : ℂ :=
  (if intPhaseSpaceMod d p = 0 then -1 else 1) *
    (displacementPhase d ^ intSymplecticForm p (canonicalIntPhaseSpaceRep d p) *
      (principalTripleDoubleSine d (canonicalIntPhaseSpaceRep d p 0)
        (canonicalIntPhaseSpaceRep d p 1) : ℂ))

/-- Off the zero residue class the origin correction is inactive: the overlap is the transported
three-factor product. -/
lemma principalNormGhostOverlap_of_mod_ne_zero (d : ℕ) [NeZero d] {p : IntPhaseSpace}
    (hp : intPhaseSpaceMod d p ≠ 0) :
    principalNormGhostOverlap d p =
      displacementPhase d ^ intSymplecticForm p (canonicalIntPhaseSpaceRep d p) *
        (principalTripleDoubleSine d (canonicalIntPhaseSpaceRep d p 0)
          (canonicalIntPhaseSpaceRep d p 1) : ℂ) := by
  rw [principalNormGhostOverlap, ite_eq_right hp, one_mul]

/-- On the zero residue class the overlap is the negative of the transported three-factor
product. -/
lemma principalNormGhostOverlap_of_mod_eq_zero (d : ℕ) [NeZero d] {p : IntPhaseSpace}
    (hp : intPhaseSpaceMod d p = 0) :
    principalNormGhostOverlap d p =
      -(displacementPhase d ^ intSymplecticForm p (canonicalIntPhaseSpaceRep d p) *
        (principalTripleDoubleSine d (canonicalIntPhaseSpaceRep d p 0)
          (canonicalIntPhaseSpaceRep d p 1) : ℂ)) := by
  rw [principalNormGhostOverlap, ite_eq_left hp]
  ring

/-- The principal normalized ghost overlap never vanishes. -/
lemma principalNormGhostOverlap_ne_zero (d : ℕ) [NeZero d] (p : IntPhaseSpace) :
    principalNormGhostOverlap d p ≠ 0 := by
  rw [principalNormGhostOverlap]
  refine mul_ne_zero (by split_ifs <;> norm_num)
    (mul_ne_zero (zpow_ne_zero _ (displacementPhase_ne_zero d)) ?_)
  exact Complex.ofReal_ne_zero.mpr (principalTripleDoubleSine_ne_zero d _ _)

/-- On canonical representatives off the zero residue class the transport factor is trivial, so
the overlap is exactly the real three-factor product. -/
lemma principalNormGhostOverlap_canonRep (d : ℕ) [NeZero d] (p : IntPhaseSpace)
    (hp : intPhaseSpaceMod d p ≠ 0) :
    principalNormGhostOverlap d (canonicalIntPhaseSpaceRep d p) =
      (principalTripleDoubleSine d (canonicalIntPhaseSpaceRep d p 0)
        (canonicalIntPhaseSpaceRep d p 1) : ℂ) := by
  have hidem := canonicalIntPhaseSpaceRep_idem d p
  have hmod := intPhaseSpaceMod_canonicalIntPhaseSpaceRep d p
  rw [principalNormGhostOverlap_of_mod_ne_zero d (hmod ▸ hp), hidem, intSymplecticForm]
  ring_nf
  simp

/-! ### Quasi-periodicity

The source quasi-periodicity law states that congruent nonzero indices have overlaps
differing by the symplectic root of unity. For the transported definition above this is a cocycle
computation: the exponent discrepancy is a multiple of `d²`, and `ξ_d^(d²k) = 1` because `d(d + 1)`
is even in every dimension. No parity case split on `d` is needed.
-/

/-- The transport exponent is always a multiple of `d`, since the index and its canonical
representative are congruent. -/
private lemma symplectic_canonRep_eq_d_mul (d : ℕ) (p : IntPhaseSpace) :
    ∃ k : ℤ, intSymplecticForm p (canonicalIntPhaseSpaceRep d p) = (d : ℤ) * k := by
  have hdvd : ∀ i, ∃ k : ℤ, p i = canonicalIntPhaseSpaceRep d p i + (d : ℤ) * k := by
    intro i
    have h : Int.ModEq (d : ℤ) (canonicalIntPhaseSpaceRep d p i) (p i) :=
      canonicalIntPhaseSpaceRep_emod d p i
    obtain ⟨k, hk⟩ := Int.ModEq.dvd h
    exact ⟨k, by linarith⟩
  obtain ⟨m0, hm0⟩ := hdvd 0
  obtain ⟨m1, hm1⟩ := hdvd 1
  refine ⟨m1 * canonicalIntPhaseSpaceRep d p 0 - m0 * canonicalIntPhaseSpaceRep d p 1, ?_⟩
  simp only [intSymplecticForm, hm0, hm1]
  ring

/-- **[AFK25, Theorem 5.8, `thm:nupnumpeq1`], realness, for the principal family.** Every principal
normalized
ghost overlap is real, at every integer index.

This is much cheaper than the general argument of the paper: the three-factor product is
`ℝ`-valued by construction, since `doubleSine` is, and the transport factor is `±1` because its
exponent is a multiple of `d` and `ξ_d^d = ±1`. -/
theorem principalNormGhostOverlap_isReal (d : ℕ) [NeZero d] (p : IntPhaseSpace) :
    ∃ x : ℝ, principalNormGhostOverlap d p = (x : ℂ) := by
  obtain ⟨k, hk⟩ := symplectic_canonRep_eq_d_mul d p
  set y : ℝ := (-1 : ℝ) ^ ((((d : ℕ) + 1 : ℕ) : ℤ) * k) *
    principalTripleDoubleSine d (canonicalIntPhaseSpaceRep d p 0)
      (canonicalIntPhaseSpaceRep d p 1) with hy
  have hval : displacementPhase d ^ intSymplecticForm p (canonicalIntPhaseSpaceRep d p) *
      (principalTripleDoubleSine d (canonicalIntPhaseSpaceRep d p 0)
        (canonicalIntPhaseSpaceRep d p 1) : ℂ) = (y : ℂ) := by
    rw [hk, displacementPhase_zpow_d_mul, hy]
    push_cast
    ring
  by_cases hp : intPhaseSpaceMod d p = 0
  · refine ⟨-y, ?_⟩
    rw [principalNormGhostOverlap_of_mod_eq_zero d hp, hval]
    push_cast
    ring
  · exact ⟨y, by rw [principalNormGhostOverlap_of_mod_ne_zero d hp, hval]⟩

/-- The transport law underlying `principalNormGhostOverlap_quasiperiodic`, stated without the
nonzero hypothesis: for
any two congruent integer indices the overlaps differ by the symplectic root of unity. -/
theorem principalNormGhostOverlap_transport (d : ℕ) [NeZero d] (p p' : IntPhaseSpace)
    (hmod : intPhaseSpaceMod d p' = intPhaseSpaceMod d p) :
    principalNormGhostOverlap d p' =
      displacementPhase d ^ intSymplecticForm p' p * principalNormGhostOverlap d p := by
  -- Congruent indices have the same canonical representative.
  have hcan := canonicalIntPhaseSpaceRep_eq_of_mod_eq d hmod
  -- Write the index shift and the canonical shift as multiples of `d`.
  have hshift : ∀ i, ∃ k : ℤ, p' i = p i + (d : ℤ) * k := by
    intro i
    obtain ⟨k, hk⟩ := ((ZMod.intCast_eq_intCast_iff _ _ _).mp (congrFun hmod i)).dvd
    exact ⟨-k, by linarith⟩
  have hcshift : ∀ i, ∃ k : ℤ, canonicalIntPhaseSpaceRep d p i = p i + (d : ℤ) * k := by
    intro i
    have h : Int.ModEq (d : ℤ) (canonicalIntPhaseSpaceRep d p i) (p i) :=
      canonicalIntPhaseSpaceRep_emod d p i
    obtain ⟨k, hk⟩ := Int.ModEq.dvd h
    exact ⟨-k, by linarith⟩
  obtain ⟨q0, hq0⟩ := hshift 0
  obtain ⟨q1, hq1⟩ := hshift 1
  obtain ⟨m0, hm0⟩ := hcshift 0
  obtain ⟨m1, hm1⟩ := hcshift 1
  -- The exponent discrepancy is a multiple of `d²`.
  have hexp : intSymplecticForm p' (canonicalIntPhaseSpaceRep d p) =
      intSymplecticForm p' p + intSymplecticForm p (canonicalIntPhaseSpaceRep d p) +
        (d : ℤ) * ((d : ℤ) * (q1 * m0 - q0 * m1)) := by
    simp only [intSymplecticForm, hq0, hq1, hm0, hm1]
    ring
  rw [principalNormGhostOverlap, principalNormGhostOverlap, hmod, hcan, hexp,
    zpow_add₀ (displacementPhase_ne_zero d), zpow_add₀ (displacementPhase_ne_zero d),
    displacementPhase_zpow_d_sq_mul]
  ring

/-- **[AFK25, Lemma 5.7, `lem:nupperiodicity`], for the principal family.** Translating a nonzero
integer index by `d k` multiplies the principal normalized ghost overlap by the prescribed
symplectic power of `ξ_d`. Thus it satisfies `IsGhostOverlapQuasiperiodic`, the input used to make
the displacement-operator summand independent of the chosen residue representatives. -/
theorem principalNormGhostOverlap_quasiperiodic (d : ℕ) [NeZero d] :
    IsGhostOverlapQuasiperiodic d (principalNormGhostOverlap d) :=
  fun p p' hmod _ ↦ principalNormGhostOverlap_transport d p p' hmod

/-! ### Periodicity modulo `d̄`

The overlaps are not `d`-periodic in even dimensions, but they are `d̄`-periodic in every
dimension, because `ξ_d` is a `d̄`-th root of unity. This is what allows the descent to the
quotient index type `PhaseSpaceMod (dbar d)` used by `GhostOverlapData`.
-/

/-- The principal normalized ghost overlap is `d̄`-periodic: it depends only on the index modulo
`dbar d`. This is the exact periodicity available, and it is strictly weaker than `d`-periodicity
in even dimensions. -/
theorem principalNormGhostOverlap_dbar_periodic (d : ℕ) [NeZero d] (p p' : IntPhaseSpace)
    (hmod : intPhaseSpaceMod (dbar d) p' = intPhaseSpaceMod (dbar d) p) :
    principalNormGhostOverlap d p' = principalNormGhostOverlap d p := by
  -- Congruence modulo `d̄` implies congruence modulo `d`.
  have hmodEq : ∀ i, Int.ModEq (dbar d : ℤ) (p' i) (p i) := fun i ↦
    (ZMod.intCast_eq_intCast_iff _ _ _).mp (congrFun hmod i)
  have hd : ∀ i, Int.ModEq (d : ℤ) (p' i) (p i) := fun i ↦
    Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr (dvd_dbar d)) (hmodEq i)
  have hmodd : intPhaseSpaceMod d p' = intPhaseSpaceMod d p := by
    funext i
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr (hd i)
  -- The symplectic exponent is a multiple of `d̄`, so the transport factor is one.
  have hshift : ∀ i, ∃ k : ℤ, p' i = p i + (dbar d : ℤ) * k := by
    intro i
    obtain ⟨k, hk⟩ := (hmodEq i).dvd
    exact ⟨-k, by linarith⟩
  obtain ⟨q0, hq0⟩ := hshift 0
  obtain ⟨q1, hq1⟩ := hshift 1
  have hexp : intSymplecticForm p' p = (dbar d : ℤ) * (q1 * p 0 - q0 * p 1) := by
    simp only [intSymplecticForm, hq0, hq1]
    ring
  have hxi : displacementPhase d ^ ((dbar d : ℤ) * (q1 * p 0 - q0 * p 1)) = 1 :=
    displacementPhase_zpow_eq_one_of_dbar_dvd (dvd_mul_right _ _)
  rw [principalNormGhostOverlap_transport d p p' hmodd, hexp, hxi, one_mul]

/-! ### The real-valued overlap

All canonical double-sine factors and transport signs are real. This section exposes a real-valued
version of the overlap and proves that its complex coercion recovers the original definition.
-/

/-- The principal normalized ghost overlap as a real number. Since
`principalNormGhostOverlap_isReal` shows the complex value is real, taking the real part loses
nothing; `ofReal_principalNormGhostOverlapReal` records the round trip. -/
noncomputable def principalNormGhostOverlapReal (d : ℕ) [NeZero d] (p : IntPhaseSpace) : ℝ :=
  (principalNormGhostOverlap d p).re

/-- The real-valued overlap casts back to the complex one. -/
@[simp]
lemma ofReal_principalNormGhostOverlapReal (d : ℕ) [NeZero d] (p : IntPhaseSpace) :
    ((principalNormGhostOverlapReal d p : ℝ) : ℂ) = principalNormGhostOverlap d p := by
  obtain ⟨x, hx⟩ := principalNormGhostOverlap_isReal d p
  rw [principalNormGhostOverlapReal, hx]
  simp

/-- The real-valued overlap is `d̄`-periodic. -/
theorem principalNormGhostOverlapReal_dbar_periodic (d : ℕ) [NeZero d] (p p' : IntPhaseSpace)
    (hmod : intPhaseSpaceMod (dbar d) p' = intPhaseSpaceMod (dbar d) p) :
    principalNormGhostOverlapReal d p' = principalNormGhostOverlapReal d p := by
  rw [principalNormGhostOverlapReal, principalNormGhostOverlapReal,
    principalNormGhostOverlap_dbar_periodic d p p' hmod]

/-! ### The reciprocal identity, at canonical representatives

Reflection cancels the six double-sine factors for a nonzero canonical residue pair, while the
sign-exponent calculation cancels the remaining phases. Hence `ν_d(p)ν_d(-p)=1` canonically.
-/

/-- A residue in `[0, d)` that vanishes modulo `d` is zero. Used below to see that a canonical
pair other than `(0,0)` lies off the zero residue class, so that the origin correction in
`principalNormGhostOverlap` is inactive. -/
private lemma eq_zero_of_canon_intCast_eq_zero {d : ℕ} {c : ℤ} (hc : 0 ≤ c) (hc' : c < (d : ℤ))
    (h : ((c : ZMod d) = 0)) : c = 0 :=
  Int.eq_zero_of_abs_lt_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
    (by rw [abs_of_nonneg hc]; exact hc')

/-- The canonical-representative core of `principalNormGhostOverlap_reciprocal`.

For `0 ≤ c₀,c₁ < d`, not both zero, the double-sine reflection and the boundary sign cancellation
give `ν_d(c₀,c₁) ν_d(-c₀,-c₁) = 1`. The public theorem below transports this identity to every
integer lift. -/
theorem principalNormGhostOverlap_reciprocal_canon (d : RankOneDimension) (c0 c1 : ℤ)
    (hc0 : 0 ≤ c0) (hc0' : c0 < (d : ℤ)) (hc1 : 0 ≤ c1) (hc1' : c1 < (d : ℤ))
    (hne : ¬ (c0 = 0 ∧ c1 = 0)) :
    principalNormGhostOverlap d ![c0, c1] * principalNormGhostOverlap d ![-c0, -c1] = 1 := by
  have htriple := principalTripleDoubleSine_mul_negRes d d.property c0 c1 hc0 hc0' hc1 hc1' hne
  have htripleC : (principalTripleDoubleSine d c0 c1 : ℂ) *
      (principalTripleDoubleSine d (negRes d c0) (negRes d c1) : ℂ) =
      (-1 : ℂ) ^ (principalSignExp d c0 c1 +
        principalSignExp d (negRes d c0) (negRes d c1)) := by
    have := congrArg (Complex.ofReal) htriple
    push_cast at this
    exact this
  have hcan0 : canonicalIntPhaseSpaceRep d ![c0, c1] = ![c0, c1] := by
    funext i
    fin_cases i <;> simp [canonicalIntPhaseSpaceRep, Int.emod_eq_of_lt, hc0, hc0', hc1, hc1']
  have hcan1 : canonicalIntPhaseSpaceRep d ![-c0, -c1] = ![negRes d c0, negRes d c1] := by
    funext i
    fin_cases i <;> simp [canonicalIntPhaseSpaceRep, negRes]
  have hmodne : intPhaseSpaceMod d (![c0, c1] : IntPhaseSpace) ≠ 0 := by
    intro h
    exact hne ⟨eq_zero_of_canon_intCast_eq_zero hc0 hc0'
        (by simpa [intPhaseSpaceMod] using congrFun h 0),
      eq_zero_of_canon_intCast_eq_zero hc1 hc1'
        (by simpa [intPhaseSpaceMod] using congrFun h 1)⟩
  have hmodne' : intPhaseSpaceMod d (![-c0, -c1] : IntPhaseSpace) ≠ 0 := by
    intro h
    refine hmodne ?_
    funext i
    have hi := congrFun h i
    fin_cases i <;> simpa [intPhaseSpaceMod, neg_eq_zero] using hi
  rw [principalNormGhostOverlap_of_mod_ne_zero d hmodne,
    principalNormGhostOverlap_of_mod_ne_zero d hmodne', hcan0, hcan1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hself : intSymplecticForm (![c0, c1] : IntPhaseSpace) (![c0, c1] : IntPhaseSpace) = 0 := by
    simp [intSymplecticForm]; ring
  rw [hself, zpow_zero, one_mul]
  rcases eq_or_ne c0 0 with hc0z | hc0nz
  · have hc1nz : c1 ≠ 0 := fun h ↦ hne ⟨hc0z, h⟩
    have hc1pos : 0 < c1 := lt_of_le_of_ne hc1 (Ne.symm hc1nz)
    have hσ' : intSymplecticForm (![-c0, -c1] : IntPhaseSpace)
        (![negRes d c0, negRes d c1] : IntPhaseSpace) = 0 := by
      simp [intSymplecticForm, hc0z, negRes_zero]
    rw [hσ', zpow_zero, one_mul, htripleC]
    refine Even.neg_one_zpow ?_
    rw [hc0z, negRes_zero, negRes_eq_sub c1 hc1pos hc1']
    exact reciprocal_sign_even_zero_fst d c1 hc1pos hc1'
  · rcases eq_or_ne c1 0 with hc1z | hc1nz
    · have hc0pos : 0 < c0 := lt_of_le_of_ne hc0 (Ne.symm hc0nz)
      have hσ' : intSymplecticForm (![-c0, -c1] : IntPhaseSpace)
          (![negRes d c0, negRes d c1] : IntPhaseSpace) = 0 := by
        simp [intSymplecticForm, hc1z, negRes_zero]
      rw [hσ', zpow_zero, one_mul, htripleC]
      refine Even.neg_one_zpow ?_
      rw [hc1z, negRes_zero, principalSignExp_comm d c0 0, principalSignExp_comm d (negRes d c0) 0,
        negRes_eq_sub c0 hc0pos hc0']
      exact reciprocal_sign_even_zero_fst d c0 hc0pos hc0'
    · have hc0pos : 0 < c0 := lt_of_le_of_ne hc0 (Ne.symm hc0nz)
      have hc1pos : 0 < c1 := lt_of_le_of_ne hc1 (Ne.symm hc1nz)
      have hnc0 : negRes d c0 = (d : ℤ) - c0 := negRes_eq_sub c0 hc0pos hc0'
      have hnc1 : negRes d c1 = (d : ℤ) - c1 := negRes_eq_sub c1 hc1pos hc1'
      have hσ' : intSymplecticForm (![-c0, -c1] : IntPhaseSpace)
          (![negRes d c0, negRes d c1] : IntPhaseSpace) = (d : ℤ) * (c0 - c1) := by
        simp only [intSymplecticForm, Matrix.cons_val_zero, Matrix.cons_val_one, hnc0, hnc1]
        ring
      rw [hσ', displacementPhase_zpow_d_mul,
        show (principalTripleDoubleSine d c0 c1 : ℂ) *
            ((-1 : ℂ) ^ (((d + 1 : ℕ) : ℤ) * (c0 - c1)) *
              (principalTripleDoubleSine d (negRes d c0) (negRes d c1) : ℂ)) =
            ((principalTripleDoubleSine d c0 c1 : ℂ) *
              (principalTripleDoubleSine d (negRes d c0) (negRes d c1) : ℂ)) *
            (-1 : ℂ) ^ (((d + 1 : ℕ) : ℤ) * (c0 - c1)) from by ring,
        htripleC, ← zpow_add₀ (show (-1 : ℂ) ≠ 0 by norm_num)]
      refine Even.neg_one_zpow ?_
      rw [hnc0, hnc1, add_comm]
      exact_mod_cast reciprocal_sign_even_generic d c0 c1

/-! ### The reciprocal identity, at an arbitrary integer lift

Quasi-periodic transport carries canonical reciprocity to arbitrary integer indices. The two
transport phases are inverse because the indices are negatives modulo `d`.
-/

/-- **The reciprocity clause of [AFK25, Theorem 5.8, `thm:nupnumpeq1`], for the principal family.**
For every integer index `p ≢ 0 (mod d)`, `ν_d(p) ν_d(-p) = 1`. This extends
`principalNormGhostOverlap_reciprocal_canon` from canonical
representatives to any integer point congruent to a nonzero pair modulo `d`, using
`principalNormGhostOverlap_transport` to relate `p` and `-p` to their canonical representatives.
The extra transport exponent beyond the canonical-representative case is always even: it equals
twice the symplectic pairing of `p` with its canonical representative, which is itself an integer
multiple of `d` by `symplectic_canonRep_eq_d_mul`. -/
theorem principalNormGhostOverlap_reciprocal (d : RankOneDimension) (p : IntPhaseSpace)
    (hp : intPhaseSpaceMod d p ≠ 0) :
    principalNormGhostOverlap d p * principalNormGhostOverlap d (-p) = 1 := by
  set c0 := canonicalIntPhaseSpaceRep d p 0 with hc0def
  set c1 := canonicalIntPhaseSpaceRep d p 1 with hc1def
  have hc0 : 0 ≤ c0 := canonicalIntPhaseSpaceRep_nonneg (by omega) p 0
  have hc0' : c0 < (d : ℤ) := canonicalIntPhaseSpaceRep_lt (by omega) p 0
  have hc1 : 0 ≤ c1 := canonicalIntPhaseSpaceRep_nonneg (by omega) p 1
  have hc1' : c1 < (d : ℤ) := canonicalIntPhaseSpaceRep_lt (by omega) p 1
  have hne : ¬ (c0 = 0 ∧ c1 = 0) := by
    rintro ⟨h0, h1⟩
    apply hp
    funext i
    fin_cases i
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.dvd_of_emod_eq_zero h0)
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.dvd_of_emod_eq_zero h1)
  have hceq : canonicalIntPhaseSpaceRep d p = ![c0, c1] := by
    funext i; fin_cases i <;> rfl
  have hmod_pc := intPhaseSpaceMod_canonicalIntPhaseSpaceRep d p
  have hmod_nc : intPhaseSpaceMod d (-(canonicalIntPhaseSpaceRep d p)) =
      intPhaseSpaceMod d (-p) := by
    funext i
    simp only [intPhaseSpaceMod, Pi.neg_apply, Int.cast_neg]
    exact congrArg Neg.neg (congrFun hmod_pc i)
  have hstep1 :=
    principalNormGhostOverlap_transport d (canonicalIntPhaseSpaceRep d p) p hmod_pc.symm
  have hstep2 := principalNormGhostOverlap_transport d (-(canonicalIntPhaseSpaceRep d p)) (-p)
    hmod_nc.symm
  have hrecip := principalNormGhostOverlap_reciprocal_canon d c0 c1 hc0 hc0' hc1 hc1' hne
  have hnegeq : -(![c0, c1] : IntPhaseSpace) = (![-c0, -c1] : IntPhaseSpace) := by
    funext i; fin_cases i <;> simp
  rw [hstep1, hstep2, hceq, hnegeq, mul_mul_mul_comm, hrecip, mul_one]
  have hexp : intSymplecticForm p (![c0, c1] : IntPhaseSpace) +
      intSymplecticForm (-p) (![-c0, -c1] : IntPhaseSpace)
      = 2 * intSymplecticForm p (![c0, c1] : IntPhaseSpace) := by
    simp only [intSymplecticForm, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.neg_apply]
    ring
  rw [← zpow_add₀ (displacementPhase_ne_zero d), hexp]
  obtain ⟨k, hk⟩ := symplectic_canonRep_eq_d_mul d p
  rw [hceq] at hk
  rw [hk]
  have h2dk : (2 : ℤ) * ((d : ℤ) * k) = (((2 * d : ℕ) : ℤ)) * k := by push_cast; ring
  rw [h2dk, zpow_mul, zpow_natCast, displacementPhase_pow_two_d, one_zpow]

/-! ### Packaging as `GhostOverlapData`

The real-valued overlap, its `d̄`-periodicity, and its reciprocal identity define
`GhostOverlapData` for the principal family. -/

/-- The real normalized ghost overlap for the principal family, indexed by the quotient type
`PhaseSpaceMod (dbar d)` used by `GhostOverlapData`, via the canonical `ZMod.val` lift. -/
noncomputable def principalNormGhostOverlapQuotient (d : ℕ) [NeZero d]
    (q : PhaseSpaceMod (dbar d)) : ℝ :=
  principalNormGhostOverlapReal d (fun i => ((q i).val : ℤ))

/-- The quotient-indexed overlap agrees with the integer-indexed one at any integer lift, by
`d̄`-periodicity. -/
lemma principalNormGhostOverlapQuotient_eq (d : ℕ) [NeZero d] (p : IntPhaseSpace) :
    principalNormGhostOverlapQuotient d (intPhaseSpaceMod (dbar d) p) =
      principalNormGhostOverlapReal d p := by
  unfold principalNormGhostOverlapQuotient
  have hd0 : d ≠ 0 := NeZero.ne d
  apply principalNormGhostOverlapReal_dbar_periodic
  funext i
  simp [intPhaseSpaceMod]

/-- **The principal family's `GhostOverlapData` instance.** This packages
`principalNormGhostOverlapReal`, its `d̄`-periodicity
(`principalNormGhostOverlapReal_dbar_periodic`), and the reciprocal identity
(`principalNormGhostOverlap_reciprocal`) into the faithful interface of `SICs.Ghost.Fiducials`. -/
noncomputable def principalGhostOverlapData (d : RankOneDimension) : GhostOverlapData d :=
  { normalized := principalNormGhostOverlapQuotient d
    reciprocal := fun p hp => by
      rw [principalNormGhostOverlapQuotient_eq, principalNormGhostOverlapQuotient_eq]
      have hcomplex := principalNormGhostOverlap_reciprocal d p hp
      have h1 := ofReal_principalNormGhostOverlapReal d p
      have h2 := ofReal_principalNormGhostOverlapReal d (-p)
      have hcast : ((principalNormGhostOverlapReal d p *
          principalNormGhostOverlapReal d (-p) : ℝ) : ℂ) = (1 : ℂ) := by
        rw [Complex.ofReal_mul, h1, h2, hcomplex]
      exact_mod_cast hcast }

end SIC

end
