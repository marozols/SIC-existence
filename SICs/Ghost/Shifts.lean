/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Admissible.AssociatedStabilizers
import SICs.Admissible.ShiftArithmetic
import SICs.Cocycle.Modular.Values
import SICs.Ghost.Fiducials

/-!
# Ghost Shifts

Rational-index bridges, the shift convolution, and `IsShift`.

This file formalizes the convolution identity defining shifts in [AFK25, Definition 1.34,
`dfn:shift`] for arbitrary admissible tuples. The rational-index API proves that congruent
integer representatives give cocycle indices differing by an integer vector, and that every
nonzero residue class gives a nonintegral index.

## Mathematical argument

The associated-stabilizer relation is imported before any shift predicate is declared.  It places
the level generator in the congruence subgroup required by both Shintani--Faddeev factors.

[AFK25, Definition 1.34, `dfn:shift`] declares a shift to be an element of `ℤ/dℤ`, whereas
`IsShift` takes an integer representative `λ`, since the convolution identity is stated with
integral matrix and phase-space data.

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Definitions 1.28 and 1.34
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### Shifts [AFK25, Definition 1.34, `dfn:shift`]

The definitions below make [AFK25, Definition 1.34, `dfn:shift`] literal for an arbitrary
admissible tuple, with an arbitrary integer shift and an arbitrary complete transversal `I`
containing `0` and `p`.

The cocycle factors use the exact real-line word values of `SICs.Cocycle.Modular.Values`,
evaluated at the
real quadratic point `ρ_t`: there is no upper-half-plane product or floored index. For arbitrary
matrix arguments the Lean value is total. At an associated stabilizer, the off-`Γ_r` branch is
unreachable by `IsAssociatedStabilizerPair.A_mem_gammaSubgroup`, the sign restriction is handled by
`sfModularCocycleRealTotal`, and `SICs.Admissible.StabilizerDomain` proves `ρ_t ∈ D_{A_t} ∩
D_{A_t⁻¹}`. At nonintegral characteristics the finite denominator is nonzero by
`qPochhammerFin_nQPInt_ne_zero_of_irrational`; integral characteristics use the regularized
branch of `sfModularCocycleRealTotal`. Neither requires an extra hypothesis in the source's
shift predicate. Comparison with the meromorphically continued cocycle remains separate. -/

/-- The shifted Zauner action `(λI + L_{z,t})q` appearing in the convolution identity
`AdmissibleTuple.shiftConvolutionSum`. -/
def shiftZaunerAction (lam : ℤ) (Lz : Mat(2, ℤ)) (q : IntPhaseSpace) :
    IntPhaseSpace :=
  Matrix.mulVec (lam • (1 : Mat(2, ℤ)) + Lz) q

/-- The rational point `q/d` used by the Shintani--Faddeev cocycle arguments in
`AdmissibleTuple.shiftConvolutionSum`. -/
def shiftRationalPoint (d : ℕ) (q : IntPhaseSpace) : Fin 2 → ℚ :=
  fun i => (q i : ℚ) / (d : ℚ)

/-- The rational phase-space point `q/d`, displayed through its two coordinates. -/
lemma shiftRationalPoint_eq_cons (d : ℕ) (q : IntPhaseSpace) :
    shiftRationalPoint d q = ![(q 0 : ℚ) / d, (q 1 : ℚ) / d] := by
  funext i
  fin_cases i <;> rfl

/-- The rational point of the origin is the zero characteristic: `0/d = 0`. -/
@[simp]
lemma shiftRationalPoint_zero (d : ℕ) : shiftRationalPoint d 0 = 0 := by
  funext i
  simp [shiftRationalPoint]

/-- **The rational point is odd in its integer index**: `(-q)/d = -(q/d)`. This transports the
index reflection `p ↦ -p` of [AFK25, Theorem 5.8, `thm:nupnumpeq1`] to the characteristic
reflection `r ↦ -r` that the Shintani--Faddeev cocycle sees. -/
lemma shiftRationalPoint_neg (d : ℕ) (q : IntPhaseSpace) :
    shiftRationalPoint d (-q) = -shiftRationalPoint d q := by
  funext i
  simp only [shiftRationalPoint, Pi.neg_apply, Int.cast_neg, neg_div]

/-- Taking the difference of rational phase-space points agrees with dividing the difference of
their integer indices by `d`. -/
lemma shiftRationalPoint_sub (d : ℕ) (q p : IntPhaseSpace) :
    shiftRationalPoint d q - shiftRationalPoint d p = shiftRationalPoint d (q - p) := by
  funext i
  simp only [Pi.sub_apply, shiftRationalPoint]
  push_cast
  ring

/-- Rational points attached to congruent integer phase-space representatives differ by an
integer vector. This is the index-change hypothesis used by
`sfModularCocycleReal_congr_of_sub_intVec`. -/
lemma exists_intCast_shiftRationalPoint_sub_of_mod_eq (d : ℕ) (hd : 0 < d)
    {p p' : IntPhaseSpace} (h : intPhaseSpaceMod d p' = intPhaseSpaceMod d p) :
    ∀ i, ∃ m : ℤ,
      (shiftRationalPoint d p' - shiftRationalPoint d p) i = (m : ℚ) := by
  obtain ⟨a, ha⟩ := exists_eq_add_smul_of_intPhaseSpaceMod_eq d h
  intro i
  refine ⟨a i, ?_⟩
  rw [ha]
  simp only [Pi.sub_apply, shiftRationalPoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hdQ : (d : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- A nonzero residue class modulo a positive `d` gives a nonintegral rational index `p/d`.
This is the phase-space form of `not_isIntegralIndex_div`. -/
theorem not_isIntegralIndex_shiftRationalPoint (d : ℕ) (hd : 0 < d)
    {p : IntPhaseSpace} (hp : intPhaseSpaceMod d p ≠ 0) :
    ¬ IsIntegralIndex (shiftRationalPoint d p) := by
  rw [shiftRationalPoint_eq_cons]
  apply not_isIntegralIndex_div d hd
  intro hdvd
  exact hp ((intPhaseSpaceMod_eq_zero_iff_dvd d p).mpr hdvd)

/-- A zero residue class modulo `d` gives an integral rational index `p/d`. -/
theorem isIntegralIndex_shiftRationalPoint_of_mod_eq_zero (d : ℕ) [NeZero d]
    (p : IntPhaseSpace) (hp : intPhaseSpaceMod d p = 0) :
    IsIntegralIndex (shiftRationalPoint d p) := by
  obtain ⟨h0, h1⟩ := (intPhaseSpaceMod_eq_zero_iff_dvd d p).mp hp
  have hdQ : (((d : ℤ) : ℚ)) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  exact isIntegralIndex_of_coords ⟨p 0 / (d : ℤ), by
    simpa only [shiftRationalPoint_eq_cons, Matrix.cons_val_zero, Int.cast_natCast] using
      (Int.cast_div h0 hdQ).symm⟩ ⟨p 1 / (d : ℤ), by
    simpa [shiftRationalPoint_eq_cons] using (Int.cast_div h1 hdQ).symm⟩

/-- **`q/d` has denominator dividing `d`**: `d·(q/d) = q ∈ ℤ`. This is the hypothesis of
`SICs.SL2Z.Characteristics.mem_gammaSubgroup_of_mem_Gamma` at the first cocycle factor of
`AdmissibleTuple.shiftConvolutionSum`. -/
lemma exists_intCast_mul_shiftRationalPoint (d : ℕ) (q : IntPhaseSpace) (i : Fin 2) :
    ∃ n : ℤ, (d : ℚ) * shiftRationalPoint d q i = (n : ℚ) := by
  rcases eq_or_ne ((d : ℚ)) 0 with h | h
  · exact ⟨0, by simp [shiftRationalPoint, h]⟩
  · refine ⟨q i, ?_⟩
    simp only [shiftRationalPoint]
    field_simp

/-- **`q/d - p/d` has denominator dividing `d`**, the same hypothesis at the second cocycle factor
of `AdmissibleTuple.shiftConvolutionSum`. -/
lemma exists_intCast_mul_shiftRationalPoint_sub (d : ℕ) (q p : IntPhaseSpace) (i : Fin 2) :
    ∃ n : ℤ, (d : ℚ) * (shiftRationalPoint d q - shiftRationalPoint d p) i = (n : ℚ) := by
  rcases eq_or_ne ((d : ℚ)) 0 with h | h
  · exact ⟨0, by simp [shiftRationalPoint, h]⟩
  · refine ⟨q i - p i, ?_⟩
    simp only [Pi.sub_apply, shiftRationalPoint]
    field_simp
    push_cast
    ring

/-- Translating the shift translates `shiftZaunerAction` by the corresponding multiple of the
acted-on point. -/
lemma shiftZaunerAction_add (lam c : ℤ) (Lz : Mat(2, ℤ))
    (q : IntPhaseSpace) :
    shiftZaunerAction (lam + c) Lz q = shiftZaunerAction lam Lz q + c • q := by
  unfold shiftZaunerAction
  rw [add_smul, add_right_comm, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- Linearity of the integral symplectic form in the translated second argument. -/
lemma intSymplecticForm_add_smul (p x q : IntPhaseSpace) (c : ℤ) :
    intSymplecticForm p (x + c • q) = intSymplecticForm p x + c * intSymplecticForm p q := by
  simp only [intSymplecticForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Linearity of the integral symplectic form in the translated first argument. -/
lemma intSymplecticForm_add_smul_left (p a q : IntPhaseSpace) (c : ℤ) :
    intSymplecticForm (p + c • a) q = intSymplecticForm p q + c * intSymplecticForm a q := by
  simp only [intSymplecticForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

namespace AdmissibleTuple

/-- **The level generator lies in `Γ_r` for every index `r` of denominator dividing `d`.**
`A_t ∈ Γ(d)` is half of `A_mem_stabilityGroupLevel`, and `Γ(d) ⊆ Γ_r` there
([AFK25, Definition 1.17, `dfn:gammarDef`]'s remark, formalized as
`SICs.SL2Z.Characteristics.mem_gammaSubgroup_of_mem_Gamma`). This supplies
[AFK25, Definition 1.18, `def:shin`]'s hypothesis at each summand of `shiftConvolutionSum`, whose
indices are `c/d` and `(c-p)/d`. -/
lemma IsAssociatedStabilizerPair.A_mem_gammaSubgroup {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (hp : t.IsAssociatedStabilizerPair A_t Lz) {r : Fin 2 → ℚ}
    (hr : ∀ i, ∃ n : ℤ, (t.d : ℚ) * r i = (n : ℚ)) :
    A_t ∈ gammaSubgroup r :=
  mem_gammaSubgroup_of_mem_Gamma
    (BinaryQF.mem_stabilityGroupLevel_iff.mp hp.A_mem_stabilityGroupLevel).2 hr

/-- **The first cocycle factor of `shiftConvolutionSum` takes no junk branch.** At an associated
stabilizer pair `A_t ∈ Γ_{c/d}`, so the totalized `sfModularCocycleReal'` there is the cocycle
`ש^{c/d}_{A_t}` itself. -/
lemma IsAssociatedStabilizerPair.sfModularCocycleReal'_A {t : AdmissibleTuple}
    {A_t Lz : SL(2, ℤ)} (hp : t.IsAssociatedStabilizerPair A_t Lz) (q : IntPhaseSpace) (τ : ℝ) :
    sfModularCocycleReal' (shiftRationalPoint t.d q) A_t τ =
      sfModularCocycleRealTotal (shiftRationalPoint t.d q) A_t
        (hp.A_mem_gammaSubgroup (exists_intCast_mul_shiftRationalPoint t.d q)) τ :=
  sfModularCocycleReal'_of_mem _ _

/-- **The second cocycle factor of `shiftConvolutionSum` takes no junk branch either.** `Γ_r` is
closed under inversion (`SICs.SL2Z.Characteristics.inv_mem_gammaSubgroup`), so the value at
`A_t⁻¹` and index `(c-p)/d` is the cocycle `ש^{(c-p)/d}_{A_t⁻¹}`. -/
lemma IsAssociatedStabilizerPair.sfModularCocycleReal'_A_inv {t : AdmissibleTuple}
    {A_t Lz : SL(2, ℤ)} (hp : t.IsAssociatedStabilizerPair A_t Lz) (q p : IntPhaseSpace) (τ : ℝ) :
    sfModularCocycleReal' (shiftRationalPoint t.d q - shiftRationalPoint t.d p) A_t⁻¹ τ =
      sfModularCocycleRealTotal (shiftRationalPoint t.d q - shiftRationalPoint t.d p) A_t⁻¹
        (inv_mem_gammaSubgroup
          (hp.A_mem_gammaSubgroup (exists_intCast_mul_shiftRationalPoint_sub t.d q p))) τ :=
  sfModularCocycleReal'_of_mem _ _

/-! #### The arbitrary-rank predicates

Nothing in the source's shift and associated-stabilizer definitions is special to rank one: the
coprimality condition is on `2λ + d_j - 1`, where `d_j = d_{j,1}` is the dimension-tower value
(`AdmissibleTriple.towerDimension`, *not* the tuple's own dimension `d_{j,m}`), the convolution
identity is the same sum with the rank `r` in the `ω_d` exponent, and the level generator is
`A_t = L_{z,t}^{2m+1}`. -/

/-- The convolution sum on the left of [AFK25, equation (1.49), `eq:tcc`], for a complete
transversal `I`, shift `λ`, associated stabilizers `A_t`, `L_{z,t}`, and phase-space point `p`:
`∑_c ω_d^{r⟨p, (λI + L_{z,t})c⟩} ש^{c/d}_{A_t}(ρ_t) ש^{(c-p)/d}_{A_t⁻¹}(ρ_t)`.

Both cocycle factors are the exact real-line value `sfModularCocycleReal'` at
the real quadratic point `ρ_t = ρ_{Q,+}`, computed using word products and the reciprocal
identity [AFK25, Lemma 2.13, `lm:sfam1sfaeq1`], with no sign hypothesis on either matrix.
The `Γ_r` membership those values require is `IsAssociatedStabilizerPair.A_mem_gammaSubgroup`;
where it fails the totalized `sfModularCocycleReal'` returns `0`, so the sum is defined for every
`A_t`, exactly as the surrounding predicates quantify over it. -/
noncomputable def shiftConvolutionSum (t : AdmissibleTuple)
    (A_t Lz : SL(2, ℤ)) (lam : ℤ)
    (I : PhaseSpaceTransversal t.d) (p : IntPhaseSpace) : ℂ :=
  ∑ c : PhaseSpaceMod t.d,
    (standardRoot t.d) ^
        ((t.r : ℤ) * intSymplecticForm p
          (shiftZaunerAction lam (Lz : Mat(2, ℤ)) (I.repr c))) *
      sfModularCocycleReal' (shiftRationalPoint t.d (I.repr c)) A_t t.Q.rootPlus *
      sfModularCocycleReal'
        (shiftRationalPoint t.d (I.repr c) - shiftRationalPoint t.d p) A_t⁻¹ t.Q.rootPlus

/-- `λ` is a shift for the admissible tuple `t`, with associated stabilizers `A_t` and
`L_{z,t}`: [AFK25, Definition 1.34, `dfn:shift`]. The convolution identity is required for every
`p ∈ ℤ²` and every complete transversal `I` whose chosen representatives of the classes of `0` and
`p` are `0` and `p`, matching the paper's “any complete set of coset representatives ... containing
`0` and `p`”. -/
@[source "AFK25, Definition 1.34, p. 17, dfn:shift" (symbol := "Z_t")]
def IsShift (t : AdmissibleTuple) (A_t Lz : SL(2, ℤ))
    (lam : ℤ) : Prop :=
  t.IsShiftCoprime lam ∧
    ∀ (p : IntPhaseSpace) (I : PhaseSpaceTransversal t.d),
      I.repr 0 = 0 → I.repr (intPhaseSpaceMod t.d p) = p →
      t.shiftConvolutionSum A_t Lz lam I p =
        if intPhaseSpaceMod t.d p = 0 then (t.d : ℂ) ^ 2 else 0

/-- A shift satisfies the coprimality condition in `IsShift`. -/
theorem IsShift.isShiftCoprime {t : AdmissibleTuple} {A Lz : SL(2, ℤ)} {lam : ℤ}
    (h : t.IsShift A Lz lam) : t.IsShiftCoprime lam := h.1

/-- The convolution equation of a shift is `d²` at the zero class and zero elsewhere. -/
theorem IsShift.convolution_eq {t : AdmissibleTuple} {A Lz : SL(2, ℤ)} {lam : ℤ}
    (h : t.IsShift A Lz lam) (p : IntPhaseSpace) (I : PhaseSpaceTransversal t.d)
    (hI0 : I.repr 0 = 0) (hIp : I.repr (intPhaseSpaceMod t.d p) = p) :
    t.shiftConvolutionSum A Lz lam I p =
      if intPhaseSpaceMod t.d p = 0 then (t.d : ℂ) ^ 2 else 0 := h.2 p I hI0 hIp

/-- Coprimality and the convolution equation supply a shift. -/
theorem IsShift.intro {t : AdmissibleTuple} {A Lz : SL(2, ℤ)} {lam : ℤ}
    (hc : t.IsShiftCoprime lam)
    (he : ∀ (p : IntPhaseSpace) (I : PhaseSpaceTransversal t.d),
      I.repr 0 = 0 → I.repr (intPhaseSpaceMod t.d p) = p →
        t.shiftConvolutionSum A Lz lam I p =
          if intPhaseSpaceMod t.d p = 0 then (t.d : ℂ) ^ 2 else 0) :
    t.IsShift A Lz lam := ⟨hc, he⟩

end AdmissibleTuple

end SIC

end
