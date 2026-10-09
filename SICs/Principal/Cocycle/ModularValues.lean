/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Cocycle.Word

/-!
# Modular Cocycle Values of the Principal Family

The general `ש` at `A_d` agrees with the principal value at the origin and at every index outside
the zero residue class.

This module compares the general real construction of [AFK25, Definition 1.18, `def:shin`] with
its independently computed principal-family values at `A_d`. The word-value comparison is proved
in `SICs.Principal.Cocycle.Word`; the present comparisons transport it to modular cocycle values.

## The argument

At a nonzero canonical pair, both modular values divide the same word value by the same finite
`q`-Pochhammer factor. Membership in `Γ_{(p/d,q/d)}` and the index identity `n_QP = -ℓ` give
`sfModularCocycleReal_principalA`. At the origin the integral clause instead reads the zero word
directly, and the principal finite factor is one.

The periodicity of [AFK25, Lemma 2.14, `lm:shinperiodicity`] then extends the comparison to every
nonzero residue class. That lemma excludes integral characteristics: the comparison on the zero
residue class is asserted only at the literal origin.

## Main declarations

- `principalA_mem_gammaSubgroup` and `intCast_neg_principalReductionL_eq_nQP`: the subgroup and
  index identities.
- `sfModularCocycleReal_principalA`: the values at canonical pairs.
- `sfModularCocycleReal_principalA_intIndex`: the values outside the zero residue class.
- `sfModularCocycleReal'_principalA`: the totalized comparison at exactly the indices evaluated by
  a qualifying transversal.

## References

- [AFK25, Definition 1.17, `dfn:gammarDef`] and [AFK25, Definition 1.18, `def:shin`]
- [AFK25, Lemma 2.14, `lm:shinperiodicity`]
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### From `σ` to `ש`: the general modular cocycle at `A_d`

The bridge theorem. `wordSigmaS_principalA` identifies the two sides one level down, at `σ`;
both `ש`-values divide that by the *same* finite `q`-Pochhammer factor, so the identification lifts
once the general `ש` of [AFK25, Definition 1.18, `def:shin`] exists
(`sfModularCocycleReal`). The three ingredients are the rational point
`r = (p/d, q/d)` and its symplectic form, `A_d`'s membership in `Γ_r`, and `A_d`'s own index
`n_QP(r,A_d) = -ℓ`. -/

/-- The fractional symplectic form of `sfModularCocycleReal` at
`r = (p/d,q/d)`, `τ = ρ_d`, is the principal family's cocycle argument `z = (qρ_d - p)/d`. -/
lemma fracSymplecticFormRat_principalRoot (d : ℕ) (hd : 3 < d) (p q : ℤ) :
    fracSymplecticFormRat ![(p : ℚ) / d, (q : ℚ) / d] (principalRoot d) =
      principalZ d p q := by
  have hd0 : ((d : ℝ)) ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < (d : ℝ))
  rw [fracSymplecticFormRat, principalZ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Rat.cast_div, Rat.cast_intCast,
    Rat.cast_natCast]
  field_simp

/-- **`A_d ∈ Γ_{(p/d,q/d)}`**, `sfModularCocycleReal`'s hypothesis at the
principal family:
`A_d ≡ I (mod d)` (`principalA_mem_Gamma`) and `d·(p/d, q/d) ∈ ℤ²`, so
`mem_gammaSubgroup_of_mem_Gamma` applies. -/
lemma principalA_mem_gammaSubgroup (d : ℕ) (hd : 3 < d) (p q : ℤ) :
    principalA d ∈ gammaSubgroup ![(p : ℚ) / d, (q : ℚ) / d] := by
  have hd0 : ((d : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine mem_gammaSubgroup_of_mem_Gamma (principalA_mem_Gamma d) (fun i => ?_)
  fin_cases i
  · exact ⟨p, by simp only [Fin.zero_eta, Matrix.cons_val_zero]; field_simp⟩
  · exact ⟨q, by simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]; field_simp⟩

/-- The phase-space form of `principalA_mem_gammaSubgroup`: `A_d ∈ Γ_{p/d}`. -/
lemma principalA_mem_gammaSubgroup_shiftRationalPoint (d : ℕ) (hd : 3 < d)
    (p : IntPhaseSpace) : principalA d ∈ gammaSubgroup (shiftRationalPoint d p) := by
  simpa [shiftRationalPoint_eq_cons] using principalA_mem_gammaSubgroup d hd (p 0) (p 1)

/-- **`A_d`'s index is `-ℓ`.** The index `nQP`,
`n_QP(r,A_d) = ((I-A_d)r)₂` at `r = (p/d,q/d)`, is the negative of the canonical reduction's shift
`ℓ = (d-2)p - q`, in the integer form
`sfModularCocycleReal_eq_of_nQP` consumes. -/
lemma intCast_neg_principalReductionL_eq_nQP (d : ℕ) (hd : 3 < d) (p q : ℤ) :
    ((-principalReductionL d p q : ℤ) : ℚ) =
      nQP ![(p : ℚ) / d, (q : ℚ) / d] (principalA d : Mat(2, ℤ)) := by
  have h := principalN_shift_eq_neg_nQP d (by omega) p q
  push_cast at h ⊢
  rw [principalReductionL]
  push_cast
  linarith

/-- **The general modular cocycle at `A_d` is the principal family's own value.** This is the
bridge theorem, at every canonical index pair, the origin included:
`sfModularCocycleReal`, with its separate integral-characteristic clause, computes
`principalSFModularCocycleAdCanonical`. At the origin both constructions give the independently
computed zero word. At a nonzero canonical pair the characteristic is nonintegral, and both
sides divide by the same `ϖ_{-ℓ}(z/j_{A_d}(ρ_d), ρ_d)`, so the content is entirely
`wordSigmaS_principalA`; what makes the statement possible is that the general index `n_QP(r,A_d)`
is available as an honest integer (`intCast_neg_principalReductionL_eq_nQP`) and that `A_d` lies in
`Γ_r` (`principalA_mem_gammaSubgroup`), the hypothesis the source definition itself imposes.

Stated at canonical `(p,q)` only, matching `wordSigmaS_principalA`;
`sfModularCocycleReal_principalA_intIndex` below lifts it to every index *outside* the zero
residue class, using `ℤ²`-periodicity of the *general* `ש`
(`sfModularCocycleReal_add_intVec`), whose hypothesis `r ∉ ℤ²` excludes that
class. Inside it only the index `(0,0)` itself is reached, which is this theorem's own origin
case -- and that is exactly the index [AFK25, Definition 1.34, `dfn:shift`]'s convolution sum
evaluates there, since the transversal represents the zero class by `0`. -/
theorem sfModularCocycleReal_principalA (d : ℕ) (hd : 3 < d) (p q : ℤ)
    (hp0 : 0 ≤ p) (hp1 : p < (d : ℤ)) (hq0 : 0 ≤ q) (hq1 : q < (d : ℤ)) :
    sfModularCocycleReal ![(p : ℚ) / d, (q : ℚ) / d] (principalA d)
        (principalA_mem_gammaSubgroup d hd p q) (principalA_lowerLeft_nonneg d hd)
        (principalRoot d) =
      principalSFModularCocycleAdCanonical d p q := by
  by_cases hzero : p = 0 ∧ q = 0
  · rcases hzero with ⟨rfl, rfl⟩
    simp only [Int.cast_zero, zero_div,
      show ![(0 : ℚ), (0 : ℚ)] = 0 by ext i; fin_cases i <;> simp,
      sfModularCocycleReal_zero]
    simpa [principalZ, principalSFModularCocycleAdCanonical, principalReductionL,
      qPochhammerFin] using
      wordSigmaS_principalA d hd 0 0 hp0 hp1 hq0 hq1 (principalA_lowerLeft_nonneg d hd)
  have hres : intPhaseSpaceMod d ![p, q] ≠ 0 := by
    intro hz
    obtain ⟨hp, hq⟩ := (intPhaseSpaceMod_eq_zero_iff_dvd d ![p, q]).mp hz
    exact hzero ⟨Int.eq_zero_of_dvd_of_nonneg_of_lt hp0 hp1 hp,
      Int.eq_zero_of_dvd_of_nonneg_of_lt hq0 hq1 hq⟩
  have hr : ¬ IsIntegralIndex ![(p : ℚ) / d, (q : ℚ) / d] := by
    simpa [shiftRationalPoint_eq_cons] using
      not_isIntegralIndex_shiftRationalPoint d (by omega) hres
  rw [sfModularCocycleReal_eq_of_nQP hr _ _ _
      (intCast_neg_principalReductionL_eq_nQP d hd p q),
    fracSymplecticFormRat_principalRoot d hd p q,
    fltDenominator_principalA_principalRoot d, flt_principalA_principalRoot d hd,
    wordSigmaS_principalA d hd p q hp0 hp1 hq0 hq1, principalSFModularCocycleAdCanonical]

/-! ### From canonical index pairs to arbitrary integer indices

The bridge theorem is proved above at canonically reduced index pairs, because the word walk it
rests on is. `SICs.Cocycle.Modular.Shifts`'s `ℤ²`-periodicity
([AFK25, Lemma 2.14, `lm:shinperiodicity`])
lifts it to every integer index outside the zero residue class, which is the form
`principalDilogValue_shiftRationalPoint` needs: it evaluates at integer phase-space points, not
at the points of a transversal chosen in advance. The residue
hypothesis `¬(d ∣ p ∧ d ∣ q)` is exactly the source's
`r ∉ ℤ²` at `r = (p/d, q/d)` (`not_isIntegralIndex_div`). -/

/-- **`ρ_d ∈ D_{A_d}`**, the `sfDomain` condition for this
family: on the real
line it is positivity of the Jacobi denominator (`SICs.Cocycle.Domains.mem_sfDomain_ofReal_iff`),
which at `A_d`, `ρ_d` is `principalJacobiFactor_pos`. -/
lemma ofReal_principalRoot_mem_sfDomain (d : ℕ) (hd : 3 < d) :
    ((principalRoot d : ℝ) : ℂ) ∈ sfDomain ((principalA d) : Mat(2, ℤ)) := by
  rw [mem_sfDomain_ofReal_iff, fltDenominator_principalA_principalRoot]
  exact principalJacobiFactor_pos d hd

/-- **The general modular cocycle at `A_d`, at an arbitrary integer index.**
`sfModularCocycleReal_principalA` lifted off canonical pairs by
`sfModularCocycleReal_congr_of_sub_intVec`: the two indices `(p/d, q/d)` and
`(p₀/d, q₀/d)` differ by the integer vector `(p/d, q/d)` (integer division), so the general `ש`
takes the same value at both, while `principalSFModularCocycleAd` is *defined* by canonical
reduction.

At every index outside the zero residue class,
`sfModularCocycleReal` computes the principal family's own `A_d` value. The canonical origin
`(0,0)` is handled separately by `sfModularCocycleReal_principalA`. The periodicity argument
used here applies only outside the zero residue class, since
[AFK25, Lemma 2.14, `lm:shinperiodicity`] requires `r ∉ ℤ²`. -/
theorem sfModularCocycleReal_principalA_intIndex (d : ℕ) (hd : 3 < d) (p q : ℤ)
    (hne : ¬((d : ℤ) ∣ p ∧ (d : ℤ) ∣ q)) :
    sfModularCocycleReal ![(p : ℚ) / d, (q : ℚ) / d] (principalA d)
        (principalA_mem_gammaSubgroup d hd p q) (principalA_lowerLeft_nonneg d hd)
        (principalRoot d) =
      principalSFModularCocycleAd d ![p, q] := by
  have hd0 : (0 : ℤ) < (d : ℤ) := by exact_mod_cast (by omega : 0 < d)
  have hdQ : ((d : ℚ)) ≠ 0 := by
    have : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd0
    exact this.ne'
  have hp0 : 0 ≤ p % (d : ℤ) := Int.emod_nonneg _ hd0.ne'
  have hp1 : p % (d : ℤ) < (d : ℤ) := Int.emod_lt_of_pos _ hd0
  have hq0 : 0 ≤ q % (d : ℤ) := Int.emod_nonneg _ hd0.ne'
  have hq1 : q % (d : ℤ) < (d : ℤ) := Int.emod_lt_of_pos _ hd0
  have hne' : ¬((d : ℤ) ∣ p % (d : ℤ) ∧ (d : ℤ) ∣ q % (d : ℤ)) := by
    rintro ⟨h1, h2⟩
    refine hne ⟨?_, ?_⟩
    · exact Int.mul_ediv_add_emod p (d : ℤ) ▸ dvd_add (Dvd.intro _ rfl) h1
    · exact Int.mul_ediv_add_emod q (d : ℤ) ▸ dvd_add (Dvd.intro _ rfl) h2
  have hcan : principalSFModularCocycleAd d ![p, q] =
      principalSFModularCocycleAdCanonical d (p % (d : ℤ)) (q % (d : ℤ)) := by
    rfl
  have hres_ne : intPhaseSpaceMod d ![p % (d : ℤ), q % (d : ℤ)] ≠ 0 := by
    intro hzero
    exact hne' ((intPhaseSpaceMod_eq_zero_iff_dvd d _).mp hzero)
  have hnonint :
      ¬ IsIntegralIndex ![((p % (d : ℤ) : ℤ) : ℚ) / d, ((q % (d : ℤ) : ℤ) : ℚ) / d] := by
    simpa [shiftRationalPoint_eq_cons] using
      not_isIntegralIndex_shiftRationalPoint d (by omega) hres_ne
  have hmod : intPhaseSpaceMod d ![p, q] =
      intPhaseSpaceMod d ![p % (d : ℤ), q % (d : ℤ)] := by
    funext i
    fin_cases i <;> simp [intPhaseSpaceMod]
  rw [hcan, ← sfModularCocycleReal_principalA d hd (p % (d : ℤ)) (q % (d : ℤ)) hp0 hp1 hq0 hq1]
  refine sfModularCocycleReal_congr_of_sub_intVec _ _ _ _ _ _ (principalRoot_irrational d hd)
    hnonint (ofReal_principalRoot_mem_sfDomain d hd)
    (flt_principalA_principalRoot d hd) ?_
  simpa [shiftRationalPoint_eq_cons] using
    exists_intCast_shiftRationalPoint_sub_of_mod_eq d (by omega) hmod

/-! ### Comparisons at the indices used by a transversal

A qualifying transversal reaches the zero residue only at the literal origin. The comparison
below combines that origin case with the nonzero-residue identity above.
-/

/-- **The totalized general cocycle at `A_d` is the principal family's value** at every index that
is either the origin or outside the zero residue class -- exactly the indices the convolution sum
of a qualifying transversal evaluates. -/
theorem sfModularCocycleReal'_principalA (d : ℕ) (hd : 3 < d) (p q : ℤ)
    (hq : (p = 0 ∧ q = 0) ∨ ¬((d : ℤ) ∣ p ∧ (d : ℤ) ∣ q)) :
    sfModularCocycleReal' ![(p : ℚ) / d, (q : ℚ) / d] (principalA d) (principalRoot d) =
      principalSFModularCocycleAd d ![p, q] := by
  rw [sfModularCocycleReal'_of_mem (principalA_mem_gammaSubgroup d hd p q),
    sfModularCocycleRealTotal_of_nonneg _ (principalA_lowerLeft_nonneg d hd)]
  rcases hq with ⟨hp, hq⟩ | hne
  · subst hp
    subst hq
    rw [sfModularCocycleReal_principalA d hd 0 0 le_rfl (by omega) le_rfl (by omega),
      principalSFModularCocycleAd_eq_canonical d 0 0 le_rfl (by omega) le_rfl (by omega)]
  · exact sfModularCocycleReal_principalA_intIndex d hd p q hne

end SIC
