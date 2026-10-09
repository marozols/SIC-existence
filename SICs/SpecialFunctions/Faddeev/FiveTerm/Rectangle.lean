/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.FiveTerm.Bounds
import SICs.SpecialFunctions.Faddeev.FiveTerm.Residues
import SICs.Analysis.RectangleResidues

/-!
# Finite rectangles for the upper-half-plane five-term kernel

The boundary integral of the five-term kernel over a finite rectangle is the sum of its genuine
right-pole residues, including when removable denominator zeros lie on the boundary.

This module follows the contour closing in [RW26, Radchenko, Wheeler (2026), Appendix A.2,
`app:mod.fad`], in the proof of Theorem 3, `thm:5term.mod.fad`, at `n = h = 0`.

## The argument

What the argument needs is local: no genuine right pole on the boundary of the closed rectangle
and no shifted left pole in it. Their lattice coordinates make the right poles in a compact
rectangle finite. We remove both denominator zero sets from the rectangle, retaining every
boundary zero among the removable exceptions. The global kernel bound gives local boundedness
there because the two genuine pole sets are closed subsets of the period lattice. The known
residue limit at each right pole and the rectangle residue theorem then give the boundary
identity. This applies to a small rectangle around a right pole lying to the left of the shifted
left poles, as needed near a real period.

The pole geometry supplies the local conditions from conditions on lines: the shifted left poles
lie to the left of a vertical line right of their real bound, so a rectangle whose left side lies
on such a line contains none, and a rectangle whose four side lines meet no right pole has none
on its boundary. Finitely many right poles may lie to the left of that left side; the rectangle
contains those to its right.
-/

noncomputable section

open Complex Real Filter Set MeasureTheory
open scoped Topology MatrixGroups

namespace SIC

/-! ### Finite pole indices and denominator exceptions

The closed rectangle is compact. The right denominator zeros in it are finite, and pole
injectivity pulls this finiteness back to exactly the indexed genuine poles in its interior. -/

/-- The closed rectangle `[x,X] × [a,b]` is compact; used for both denominator zero sets. -/
private lemma fiveTerm_closedRectangle_isCompact (x X a b : ℝ) :
    IsCompact (Icc x X ×ℂ Icc a b) := isCompact_Icc.reProdIm isCompact_Icc

/-- The right poles in the open rectangle are indexed by a finite set of `(k,j)` with
`kc-ja+m ≥ 0`; this is the finite portion of the pole indexing of
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`]. -/
theorem exists_finset_fiveTermPoles_in_rectangle
    (γ : SL(2, ℤ)) (m : ℤ) (τ : ℂ) (hτ : 0 < τ.im)
    (x X a b : ℝ) :
    ∃ S : Finset (ℤ × ℕ), ∀ kj : ℤ × ℕ,
      kj ∈ S ↔ 0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2 ∧
        x < (faddeevModularUHPPole γ τ kj.1 kj.2).re ∧
        (faddeevModularUHPPole γ τ kj.1 kj.2).re < X ∧
        a < (faddeevModularUHPPole γ τ kj.1 kj.2).im ∧
        (faddeevModularUHPPole γ τ kj.1 kj.2).im < b := by
  let A : Set ℂ := Icc x X ×ℂ Icc a b
  let D : Set ℂ := {z | qPochhammer
    (z / fltDenominator (γ : Mat(2, ℤ)) τ)
    (flt (γ : Mat(2, ℤ)) τ) = 0}
  let pole : ℤ × ℕ → ℂ := fun kj => faddeevModularUHPPole γ τ kj.1 kj.2
  let T : Set (ℤ × ℕ) := {kj | 0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2 ∧
    x < (pole kj).re ∧ (pole kj).re < X ∧ a < (pole kj).im ∧ (pole kj).im < b}
  have hAD : (A ∩ D).Finite :=
    finite_qPochhammer_div_zeros_inter_compact γ τ hτ
      (fiveTerm_closedRectangle_isCompact x X a b)
  have hpre : (pole ⁻¹' (A ∩ D)).Finite :=
    hAD.preimage (fun _ _ _ _ h => faddeevModularUHPPole_injective γ τ hτ h)
  have hsub : T ⊆ pole ⁻¹' (A ∩ D) := by
    intro kj hkj
    rcases hkj with ⟨_, hx, hX, ha, hb⟩
    refine ⟨⟨⟨hx.le, hX.le⟩, ⟨ha.le, hb.le⟩⟩, ?_⟩
    exact (qPochhammer_div_fltDenominator_eq_zero_iff γ τ hτ (pole kj)).mpr
      ⟨kj.1, kj.2, rfl⟩
  refine ⟨(hpre.subset hsub).toFinset, ?_⟩
  intro kj
  simp only [Set.Finite.mem_toFinset, T, Set.mem_ofPred_eq, pole]

/-- Both denominator zero sets have a finite union inside the closed rectangle, including
possible boundary points; used by the removable-singularity form of the rectangle theorem. -/
private lemma finite_fiveTerm_denominatorZeros_in_rectangle
    (γ : SL(2, ℤ)) (m p : ℤ) (y τ : ℂ) (hτ : 0 < τ.im)
    (x X a b : ℝ) :
    ((Icc x X ×ℂ Icc a b) ∩
      ({z | qPochhammer (z / fltDenominator (γ : Mat(2, ℤ)) τ)
        (flt (γ : Mat(2, ℤ)) τ) = 0} ∪
       {z | qPochhammer (z + y + ((m + p : ℤ) : ℂ) * τ) τ = 0})).Finite := by
  have hR := finite_qPochhammer_div_zeros_inter_compact γ τ hτ
    (fiveTerm_closedRectangle_isCompact x X a b)
  have hL := finite_qPochhammer_add_int_mul_zeros_inter_compact τ y hτ (m + p)
    (fiveTerm_closedRectangle_isCompact x X a b)
  rw [inter_union_distrib_left]
  exact hR.union hL

/-! ### Exceptional points in the rectangle

The local conditions place every genuine right pole of the closed rectangle in its interior and
exclude shifted left poles throughout it. Thus any denominator zero outside the indexed right
poles is removable. -/

/-- Every point of the closed rectangle outside the finite right-pole image avoids both
genuine pole families. Used to make denominator exceptions removable. -/
private lemma fiveTerm_no_genuine_pole_off_image
    (γ : SL(2, ℤ)) (p m : ℤ) (y τ : ℂ) (hτ : 0 < τ.im)
    (x X a b : ℝ)
    (hP : ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ, u ∈ Icc x X ×ℂ Icc a b →
      x < u.re ∧ u.re < X ∧ a < u.im ∧ u.im < b)
    (hL : ∀ z ∈ Icc x X ×ℂ Icc a b, z + y ∉ faddeevModularUHPZeros γ (m + p) τ)
    (S : Finset (ℤ × ℕ))
    (hS : ∀ kj : ℤ × ℕ,
      kj ∈ S ↔ 0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2 ∧
        x < (faddeevModularUHPPole γ τ kj.1 kj.2).re ∧
        (faddeevModularUHPPole γ τ kj.1 kj.2).re < X ∧
        a < (faddeevModularUHPPole γ τ kj.1 kj.2).im ∧
        (faddeevModularUHPPole γ τ kj.1 kj.2).im < b)
    (z : ℂ) (hz : z ∈ Icc x X ×ℂ Icc a b)
    (hnot : z ∉ S.image (fun kj => faddeevModularUHPPole γ τ kj.1 kj.2)) :
    z ∉ faddeevModularUHPPoles γ (m + 1) τ ∧
      z + y ∉ faddeevModularUHPZeros γ (m + p) τ := by
  constructor
  · intro hp
    obtain ⟨k, j, hpole, hN⟩ := (mem_faddeevModularUHPPoles_iff γ m hτ).mp hp
    obtain ⟨hxr, hzr, hza, hzb⟩ := hP z hp hz
    have hkj : (k, j) ∈ S := by
      apply (hS (k, j)).mpr
      simpa [hpole] using (show 0 ≤ faddeevModularUHPIndex γ m k j ∧
        x < z.re ∧ z.re < X ∧ a < z.im ∧ z.im < b from
          ⟨hN, hxr, hzr, hza, hzb⟩)
    exact hnot (Finset.mem_image.mpr ⟨(k, j), hkj, hpole.symm⟩)
  · exact hL z hz

/-- The two denominator zero sets are discrete, so the kernel is differentiable on a
punctured neighborhood of any point; used for removable exceptions. -/
private lemma eventually_differentiableAt_kernelUHP
    (γ : SL(2, ℤ)) (ℓ p m : ℤ) (w y τ e : ℂ) (hτ : 0 < τ.im) :
    ∀ᶠ z in 𝓝[≠] e, DifferentiableAt ℂ
      (fiveTermKernelUHP γ ℓ p w y τ m) z := by
  filter_upwards [eventually_qPochhammer_div_fltDenominator_ne_zero γ τ hτ e,
    eventually_qPochhammer_add_int_mul_ne_zero τ y hτ (m + p) e]
    with z hR hL
  apply differentiableAt_fiveTermKernelUHP γ ℓ p w y τ hτ m z hR
  convert hL using 1; push_cast; ring

/-- The kernel is differentiable wherever both denominator q-products are nonzero; used by
`exists_fiveTerm_rectangle_removable_set`. -/
private lemma fiveTerm_differentiableOn_off_denominators
    (γ : SL(2, ℤ)) (ℓ p m : ℤ) (w y τ : ℂ) (hτ : 0 < τ.im) :
    DifferentiableOn ℂ (fiveTermKernelUHP γ ℓ p w y τ m)
      {z | qPochhammer (z / fltDenominator (γ : Mat(2, ℤ)) τ)
        (flt (γ : Mat(2, ℤ)) τ) ≠ 0 ∧
        qPochhammer (z + y + ((m + p : ℤ) : ℂ) * τ) τ ≠ 0} := by
  intro z hz
  apply (differentiableAt_fiveTermKernelUHP γ ℓ p w y τ hτ m z hz.1
    (by convert hz.2 using 1; push_cast; ring)).differentiableWithinAt

/-- The finite exceptional set covers every denominator zero in the rectangle outside the
selected poles; used by `exists_fiveTerm_rectangle_removable_set`. -/
private lemma fiveTerm_finite_exception_cover {A D : Set ℂ} (hF : (A ∩ D).Finite)
    (P : Finset ℂ) :
    A ∩ D ⊆ (P : Set ℂ) ∪ ((hF.toFinset \ P : Finset ℂ) : Set ℂ) := by
  intro z hz
  by_cases hp : z ∈ P
  · exact Or.inl hp
  · exact Or.inr (Finset.mem_sdiff.mpr ⟨hF.mem_toFinset.mpr hz, hp⟩)

/-- The union of both denominator zero sets, minus the right poles, is a finite set of
removable exceptions for the kernel on a closed rectangle; used by the residue theorem. -/
private lemma exists_fiveTerm_rectangle_removable_set
    (γ : SL(2, ℤ)) (ℓ p m : ℤ) (w y τ : ℂ) (hτ : 0 < τ.im)
    (x X a b : ℝ)
    (hP : ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ, u ∈ Icc x X ×ℂ Icc a b →
      x < u.re ∧ u.re < X ∧ a < u.im ∧ u.im < b)
    (hL : ∀ z ∈ Icc x X ×ℂ Icc a b, z + y ∉ faddeevModularUHPZeros γ (m + p) τ)
    (S : Finset (ℤ × ℕ))
    (hS : ∀ kj : ℤ × ℕ,
      kj ∈ S ↔ 0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2 ∧
        x < (faddeevModularUHPPole γ τ kj.1 kj.2).re ∧
        (faddeevModularUHPPole γ τ kj.1 kj.2).re < X ∧
        a < (faddeevModularUHPPole γ τ kj.1 kj.2).im ∧
        (faddeevModularUHPPole γ τ kj.1 kj.2).im < b) :
    ∃ E : Finset ℂ,
      Disjoint (S.image (fun kj => faddeevModularUHPPole γ τ kj.1 kj.2)) E ∧
      DifferentiableOn ℂ (fiveTermKernelUHP γ ℓ p w y τ m)
        ((Icc x X ×ℂ Icc a b) \
          (((S.image (fun kj => faddeevModularUHPPole γ τ kj.1 kj.2) : Finset ℂ) : Set ℂ) ∪ E)) ∧
      (∀ e ∈ E, ∀ᶠ z in 𝓝[≠] e,
        DifferentiableAt ℂ (fiveTermKernelUHP γ ℓ p w y τ m) z) ∧
      (∀ e ∈ E, IsBoundedUnder (· ≤ ·) (𝓝[≠] e)
        (fun z => ‖fiveTermKernelUHP γ ℓ p w y τ m z‖)) := by
  let A : Set ℂ := Icc x X ×ℂ Icc a b
  let D : Set ℂ :=
    {z | qPochhammer (z / fltDenominator (γ : Mat(2, ℤ)) τ)
      (flt (γ : Mat(2, ℤ)) τ) = 0} ∪
    {z | qPochhammer (z + y + ((m + p : ℤ) : ℂ) * τ) τ = 0}
  let pole : ℤ × ℕ → ℂ := fun kj => faddeevModularUHPPole γ τ kj.1 kj.2
  have hF : (A ∩ D).Finite :=
    finite_fiveTerm_denominatorZeros_in_rectangle γ m p y τ hτ x X a b
  let E : Finset ℂ := hF.toFinset \ S.image pole
  have hcover : A ∩ D ⊆ (S.image pole : Set ℂ) ∪ E :=
    fiveTerm_finite_exception_cover hF (S.image pole)
  have hEmem (e : ℂ) (heE : e ∈ E) : e ∈ A ∧ e ∉ S.image pole := by
    have h := Finset.mem_sdiff.mp heE
    exact ⟨(hF.mem_toFinset.mp h.1).1, h.2⟩
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro e heS heE
    exact (hEmem e heE).2 heS
  · apply (fiveTerm_differentiableOn_off_denominators γ ℓ p m w y τ hτ).mono
    intro z hz
    have hnotD : z ∉ D := fun hD => hz.2 (hcover ⟨hz.1, hD⟩)
    exact ⟨fun h => hnotD (Or.inl h), fun h => hnotD (Or.inr h)⟩
  · intro e heE
    exact eventually_differentiableAt_kernelUHP γ ℓ p m w y τ e hτ
  · intro e heE
    obtain ⟨heA, henot⟩ := hEmem e heE
    obtain ⟨heR, heL⟩ := fiveTerm_no_genuine_pole_off_image
      γ p m y τ hτ x X a b hP hL S hS e heA henot
    exact isBoundedUnder_fiveTermKernelUHP_punctured
      γ ℓ p m w y τ e hτ heR heL

/-! ### The finite-rectangle residue identity

At each indexed right pole, the shifted q-product is nonzero by its finite-product splitting.
The existing residue limit therefore applies. Injectivity transfers the residue sum from points
in the rectangle to their `(k,j)` indices. -/

/-- The residue limit holds at each indexed pole with nonnegative forward index; used by
`integral_boundary_rect_fiveTermKernelUHP_of_local`. -/
private lemma fiveTerm_residue_limit_on_pole_image
    (γ : SL(2, ℤ)) (ℓ p m : ℤ) (w y τ : ℂ) (hτ : 0 < τ.im)
    (hden : qPochhammer ((p : ℂ) * τ + y) τ ≠ 0)
    (S : Finset (ℤ × ℕ))
    (hS : ∀ kj ∈ S, 0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2) :
    ∀ z ∈ S.image (fun kj => faddeevModularUHPPole γ τ kj.1 kj.2),
      Tendsto (fun ζ => (ζ - z) * fiveTermKernelUHP γ ℓ p w y τ m ζ)
        (𝓝[≠] z) (𝓝 (fiveTermResidueUHP γ ℓ p w y τ
          (faddeevModularUHPIndex γ m
            (Function.invFun (fun kj : ℤ × ℕ =>
              faddeevModularUHPPole γ τ kj.1 kj.2) z).1
            (Function.invFun (fun kj : ℤ × ℕ =>
              faddeevModularUHPPole γ τ kj.1 kj.2) z).2)
          (Function.invFun (fun kj : ℤ × ℕ =>
            faddeevModularUHPPole γ τ kj.1 kj.2) z).2)) := by
  have hleft := Function.leftInverse_invFun (faddeevModularUHPPole_injective γ τ hτ)
  intro z hz
  obtain ⟨⟨k, j⟩, hkj, rfl⟩ := Finset.mem_image.mp hz
  have hN := hS (k, j) hkj
  have hden' := qPochhammer_add_intCast_mul_ne_zero
    (faddeevModularUHPIndex γ m k j) ((p : ℂ) * τ + y) τ hN hτ hden
  simp only [hleft (k, j)]
  exact tendsto_fiveTermKernelUHP_residue γ ℓ p w y τ hτ m k j hden'

/-- The pole image selected by strict rectangle inequalities lies in its interior; used by
`integral_boundary_rect_fiveTermKernelUHP_of_local`. -/
private lemma fiveTerm_pole_image_inside_rectangle (γ : SL(2, ℤ)) (τ : ℂ)
    (S : Finset (ℤ × ℕ)) (x X a b : ℝ)
    (hS : ∀ kj ∈ S,
      x < (faddeevModularUHPPole γ τ kj.1 kj.2).re ∧
      (faddeevModularUHPPole γ τ kj.1 kj.2).re < X ∧
      a < (faddeevModularUHPPole γ τ kj.1 kj.2).im ∧
      (faddeevModularUHPPole γ τ kj.1 kj.2).im < b) :
    ∀ z ∈ S.image (fun kj => faddeevModularUHPPole γ τ kj.1 kj.2),
      ((x : ℂ) + a * I).re < z.re ∧ z.re < ((X : ℂ) + b * I).re ∧
      ((x : ℂ) + a * I).im < z.im ∧ z.im < ((X : ℂ) + b * I).im := by
  intro z hz
  obtain ⟨kj, hkj, rfl⟩ := Finset.mem_image.mp hz
  simpa using hS kj hkj

/-- Injectivity transfers a finite residue sum from pole points to their indices; used by
`integral_boundary_rect_fiveTermKernelUHP_of_local`. -/
private lemma fiveTerm_sum_residue_image (γ : SL(2, ℤ)) (τ : ℂ) (hτ : 0 < τ.im)
    (S : Finset (ℤ × ℕ)) (coeff : ℤ × ℕ → ℂ) :
    (∑ z ∈ S.image (fun kj => faddeevModularUHPPole γ τ kj.1 kj.2),
      coeff (Function.invFun (fun kj : ℤ × ℕ =>
        faddeevModularUHPPole γ τ kj.1 kj.2) z)) = ∑ kj ∈ S, coeff kj := by
  have hinj := faddeevModularUHPPole_injective γ τ hτ
  have hleft := Function.leftInverse_invFun hinj
  rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
  apply Finset.sum_congr rfl
  intro kj _
  rw [hleft kj]

/-- The finite-rectangle residue identity under conditions on the closed rectangle alone: no
genuine right pole lies on its boundary and no shifted left pole lies in it. The counterclockwise
boundary integral is `2πi` times the residues at the indexed right poles strictly inside the
rectangle, which may lie to the left of the shifted left poles. This is the rectangle step of
[RW26, Radchenko, Wheeler (2026), Appendix A.2, `app:mod.fad`], in the proof of Theorem 3,
`thm:5term.mod.fad`, at `n = h = 0`, for a small rectangle around a right pole. -/
theorem integral_boundary_rect_fiveTermKernelUHP_of_local
    (γ : SL(2, ℤ)) (ℓ p m : ℤ) (w y τ : ℂ) (hτ : 0 < τ.im)
    (x X a b : ℝ) (hxX : x < X) (hab : a < b)
    (hP : ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ, u ∈ Icc x X ×ℂ Icc a b →
      x < u.re ∧ u.re < X ∧ a < u.im ∧ u.im < b)
    (hL : ∀ z ∈ Icc x X ×ℂ Icc a b, z + y ∉ faddeevModularUHPZeros γ (m + p) τ)
    (hden : qPochhammer ((p : ℂ) * τ + y) τ ≠ 0) :
    ∃ S : Finset (ℤ × ℕ),
      (∀ kj : ℤ × ℕ, kj ∈ S ↔
        0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2 ∧
          x < (faddeevModularUHPPole γ τ kj.1 kj.2).re ∧
          (faddeevModularUHPPole γ τ kj.1 kj.2).re < X ∧
          a < (faddeevModularUHPPole γ τ kj.1 kj.2).im ∧
          (faddeevModularUHPPole γ τ kj.1 kj.2).im < b) ∧
      (∫ s : ℝ in x..X, fiveTermKernelUHP γ ℓ p w y τ m (s + a * I)) -
        (∫ s : ℝ in x..X, fiveTermKernelUHP γ ℓ p w y τ m (s + b * I)) +
        I * (∫ t : ℝ in a..b, fiveTermKernelUHP γ ℓ p w y τ m (X + t * I)) -
        I * (∫ t : ℝ in a..b, fiveTermKernelUHP γ ℓ p w y τ m (x + t * I)) =
      2 * π * I * ∑ kj ∈ S, fiveTermResidueUHP γ ℓ p w y τ
        (faddeevModularUHPIndex γ m kj.1 kj.2) kj.2 := by
  obtain ⟨S, hS⟩ :=
    exists_finset_fiveTermPoles_in_rectangle γ m τ hτ x X a b
  obtain ⟨E, hSE, hdiff, hEd, hEb⟩ :=
    exists_fiveTerm_rectangle_removable_set
      γ ℓ p m w y τ hτ x X a b hP hL S hS
  let pole : ℤ × ℕ → ℂ := fun kj => faddeevModularUHPPole γ τ kj.1 kj.2
  let coeff : ℤ × ℕ → ℂ := fun kj => fiveTermResidueUHP γ ℓ p w y τ
    (faddeevModularUHPIndex γ m kj.1 kj.2) kj.2
  let R : ℂ → ℂ := fun z => coeff (Function.invFun pole z)
  have hres : ∀ z ∈ S.image pole,
      Tendsto (fun ζ => (ζ - z) * fiveTermKernelUHP γ ℓ p w y τ m ζ)
        (𝓝[≠] z) (𝓝 (R z)) :=
    fiveTerm_residue_limit_on_pole_image γ ℓ p m w y τ hτ hden S
      (fun kj hkj => ((hS kj).mp hkj).1)
  have hinside : ∀ z ∈ S.image pole,
      ((x : ℂ) + a * I).re < z.re ∧ z.re < ((X : ℂ) + b * I).re ∧
      ((x : ℂ) + a * I).im < z.im ∧ z.im < ((X : ℂ) + b * I).im :=
    fiveTerm_pole_image_inside_rectangle γ τ S x X a b
      (fun kj hkj => ((hS kj).mp hkj).2)
  have hsum : (∑ z ∈ S.image pole, R z) = ∑ kj ∈ S, coeff kj := by
    exact fiveTerm_sum_residue_image γ τ hτ S coeff
  have hrect := integral_boundary_rect_eq_sum_residues_of_bounded
    (fiveTermKernelUHP γ ℓ p w y τ m)
    ((x : ℂ) + a * I) ((X : ℂ) + b * I) (S.image pole) E R
    hSE hinside (by simpa [hxX.le, hab.le] using hdiff) hres hEd hEb
  refine ⟨S, hS, ?_⟩
  rw [hsum] at hrect
  simpa [coeff, Complex.add_re, Complex.add_im, Complex.mul_I_re,
    Complex.mul_I_im, smul_eq_mul] using hrect

/-- The finite-rectangle residue identity when the left side lies to the right of the
shifted left poles and meets no genuine right pole, while finitely many right poles may lie to
its left: the counterclockwise boundary integral is `2πi` times the residues at the indexed
right poles strictly inside the rectangle. This is the case of
`integral_boundary_rect_fiveTermKernelUHP_of_local` whose conditions hold on the lines
through the sides, the rectangle step of [RW26, Radchenko, Wheeler (2026), Appendix A.2,
`app:mod.fad`], in the proof of Theorem 3, `thm:5term.mod.fad`, at `n = h = 0`. -/
theorem integral_boundary_rect_fiveTermKernelUHP_of_regular
    (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (ℓ p m : ℤ) (w y τ : ℂ)
    (hτ : 0 < τ.im) (he : 0 ≤ (fltDenominator (γ : Mat(2, ℤ)) τ).re)
    (x X a b : ℝ) (hxX : x < X) (hab : a < b)
    (hxP : ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ, u.re ≠ x)
    (hxL : (-((m + p : ℤ) : ℝ) * (fltDenominator (γ : Mat(2, ℤ)) τ).re - 1) /
      (γ 1 0 : ℝ) - y.re < x)
    (hden : qPochhammer ((p : ℂ) * τ + y) τ ≠ 0)
    (ha : ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ, u.im ≠ a)
    (hb : ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ, u.im ≠ b)
    (hX : ∀ u ∈ faddeevModularUHPPoles γ (m + 1) τ, u.re ≠ X) :
    ∃ S : Finset (ℤ × ℕ),
      (∀ kj : ℤ × ℕ, kj ∈ S ↔
        0 ≤ faddeevModularUHPIndex γ m kj.1 kj.2 ∧
          x < (faddeevModularUHPPole γ τ kj.1 kj.2).re ∧
          (faddeevModularUHPPole γ τ kj.1 kj.2).re < X ∧
          a < (faddeevModularUHPPole γ τ kj.1 kj.2).im ∧
          (faddeevModularUHPPole γ τ kj.1 kj.2).im < b) ∧
      (∫ s : ℝ in x..X, fiveTermKernelUHP γ ℓ p w y τ m (s + a * I)) -
        (∫ s : ℝ in x..X, fiveTermKernelUHP γ ℓ p w y τ m (s + b * I)) +
        I * (∫ t : ℝ in a..b, fiveTermKernelUHP γ ℓ p w y τ m (X + t * I)) -
        I * (∫ t : ℝ in a..b, fiveTermKernelUHP γ ℓ p w y τ m (x + t * I)) =
      2 * π * I * ∑ kj ∈ S, fiveTermResidueUHP γ ℓ p w y τ
        (faddeevModularUHPIndex γ m kj.1 kj.2) kj.2 := by
  apply integral_boundary_rect_fiveTermKernelUHP_of_local
    γ ℓ p m w y τ hτ x X a b hxX hab
  · intro u hu hrect
    exact ⟨lt_of_le_of_ne hrect.1.1 (Ne.symm (hxP u hu)),
      lt_of_le_of_ne hrect.1.2 (hX u hu),
      lt_of_le_of_ne hrect.2.1 (Ne.symm (ha u hu)),
      lt_of_le_of_ne hrect.2.2 (hb u hu)⟩
  · intro z hz hp
    have hbound := re_upperBound_of_mem_faddeevModularUHPZeros
      γ hc (m + p) hτ he hp
    have hreal : (z + y).re = z.re + y.re := by simp
    rw [hreal] at hbound
    have hx := hz.1.1
    linarith
  · exact hden

end SIC
