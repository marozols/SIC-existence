/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.FiveTerm.Parameters

/-!
# The window of source pairs representing the finite group

The source pairs with first coordinate in `[0, c)` and lattice index in a window of `N`
consecutive integers represent every class of `G` exactly once.

This module follows the residue bookkeeping of [RW26, Radchenko, Wheeler (2026), Section 3.2,
the proof of Theorem 2, `thm:fg.equs`]: the strip between a contour and its translate by
`(ε-1)/c` contains, over all `m ∈ ℤ/c`, one kernel pole for every class of `G`. For
`γ = (a b; c d)` the kernel poles of the summed residue kernel are at `-(ε-1)S(x)/(cN)`, so the
strip is a window of `N` consecutive values of the lattice index `S(x) = (1-d)x₁ + cx₂`. The
principal case, with index `S/d`, is proved directly in
`SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ClassWindow`.

## The argument

The kernel of the residue map is the row lattice spanned by `λ₁ = (a-1,b)` and `λ₂ = (c,d-1)`,
with `S(λ₁) = N` and `S(λ₂) = 0`. If two pairs of a window have the same residue, their
difference `sλ₁ + tλ₂` has `|S| = |s|N < N`, so `s = 0`, and its first coordinate `tc` has
absolute value below `c`, so `t = 0`: the residue map is injective on the window. Every pair is
moved into the window by subtracting a multiple of `λ₁` (fixing the index modulo `N`) and then a
multiple of `λ₂` (fixing the first coordinate modulo `c`); hence the window represents every class
of `G` exactly once, and sums over `G` are sums over the window.

Choosing representatives with `0 ≤ S(u) < N` and `1 ≤ S(v) ≤ N` (and the canonical pairs `0`
and `λ₁` for the zero classes of `u` and `u+v`) gives the positive representatives of the
crossed-pole argument.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The window -/

/-- The source pairs `x` with `0 ≤ x₁ < c` and `a ≤ S(x) < a + N`, as a finite set: since
`c ≥ 1`, the second coordinate is bounded by `|a| + |1-d|c + N`. -/
def fiveTermWindow (γ : SL(2, ℤ)) (a : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Ico (0 : ℤ) (γ 1 0)) ×ˢ
      (Finset.Icc (-(|a| + |1 - γ 1 1| * γ 1 0 + finiteDilogOrder γ))
        (|a| + |1 - γ 1 1| * γ 1 0 + finiteDilogOrder γ))).filter
    (fun x => a ≤ fiveTermLatticeIndex γ x.1 x.2 ∧
      fiveTermLatticeIndex γ x.1 x.2 < a + finiteDilogOrder γ)

/-- Membership in the window of source pairs. -/
theorem mem_fiveTermWindow {γ : SL(2, ℤ)} {τ : ℝ} (h : IsAttractiveFixedPoint γ τ)
    (a : ℤ) (x : ℤ × ℤ) :
    x ∈ fiveTermWindow γ a ↔
      0 ≤ x.1 ∧ x.1 < γ 1 0 ∧ a ≤ fiveTermLatticeIndex γ x.1 x.2 ∧
        fiveTermLatticeIndex γ x.1 x.2 < a + finiteDilogOrder γ := by
  have hc : 1 ≤ γ 1 0 := by have := h.lowerLeft_pos; omega
  simp only [fiveTermWindow, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Ico, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨hx0, hxc⟩, _⟩, hlo, hhi⟩
    exact ⟨hx0, hxc, hlo, hhi⟩
  · rintro ⟨hx0, hxc, hlo, hhi⟩
    let q : ℤ := 1 - γ 1 1
    let c : ℤ := γ 1 0
    let N : ℤ := finiteDilogOrder γ
    let B : ℤ := |a| + |q| * c + N
    have habs : -|q| ≤ q ∧ q ≤ |q| := abs_le.mp le_rfl
    have hqlo : -(|q| * c) ≤ q * x.1 := by
      have h₁ := mul_nonneg (abs_nonneg q) (show 0 ≤ c - x.1 by omega)
      have h₂ := mul_nonneg (show 0 ≤ |q| + q by omega) hx0
      nlinarith
    have hqhi : q * x.1 ≤ |q| * c := by
      have h₁ := mul_nonneg (abs_nonneg q) (show 0 ≤ c - x.1 by omega)
      have h₂ := mul_nonneg (show 0 ≤ |q| - q by omega) hx0
      nlinarith
    have hS : fiveTermLatticeIndex γ x.1 x.2 = q * x.1 + c * x.2 := rfl
    have hB : -B ≤ c * x.2 ∧ c * x.2 ≤ B := by
      rw [hS] at hlo hhi
      have ha₁ := le_abs_self a
      have ha₂ := neg_abs_le a
      constructor <;> dsimp [B] <;> omega
    have hk : -B ≤ x.2 ∧ x.2 ≤ B := by
      have hc' : 0 ≤ c - 1 := by omega
      constructor
      · by_cases hx2 : x.2 ≤ 0
        · nlinarith [mul_nonneg hc' (show 0 ≤ -x.2 by omega)]
        · have hB0 : 0 ≤ B := by dsimp [B]; positivity
          omega
      · by_cases hx2 : 0 ≤ x.2
        · nlinarith [mul_nonneg hc' hx2]
        · have hB0 : 0 ≤ B := by dsimp [B]; positivity
          omega
    exact ⟨⟨⟨hx0, hxc⟩, by simpa [q, c, N, B] using hk⟩, hlo, hhi⟩

/-! ### The window represents `G` once -/

/-- Row-lattice pairs have zero residue; used to move representatives between windows. -/
private theorem fiveTermCharacteristicResidue_rows_zero {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (s t : ℤ) :
    fiveTermCharacteristicResidue γ (s * (γ 0 0 - 1) + t * γ 1 0)
      (s * γ 0 1 + t * (γ 1 1 - 1)) = 0 :=
  (fiveTermCharacteristicResidue_eq_zero_iff h _ _).2 ⟨s, t, rfl, rfl⟩

/-- Adding `sλ₁+tλ₂` changes the index by `sN` and preserves the residue. -/
private theorem fiveTerm_rows_shift {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m k s t : ℤ) :
    fiveTermLatticeIndex γ (m + s * (γ 0 0 - 1) + t * γ 1 0)
        (k + s * γ 0 1 + t * (γ 1 1 - 1)) =
        fiveTermLatticeIndex γ m k + s * finiteDilogOrder γ ∧
      fiveTermCharacteristicResidue γ (m + s * (γ 0 0 - 1) + t * γ 1 0)
        (k + s * γ 0 1 + t * (γ 1 1 - 1)) =
        fiveTermCharacteristicResidue γ m k := by
  have hI := fiveTermLatticeIndex_add γ m k
    (s * (γ 0 0 - 1) + t * γ 1 0) (s * γ 0 1 + t * (γ 1 1 - 1))
  have hR := fiveTermCharacteristicResidue_add γ m k
    (s * (γ 0 0 - 1) + t * γ 1 0) (s * γ 0 1 + t * (γ 1 1 - 1))
  constructor
  · rw [fiveTermLatticeIndex_rows h] at hI
    simpa only [add_assoc] using hI
  · rw [fiveTermCharacteristicResidue_rows_zero h, add_zero] at hR
    simpa only [add_assoc] using hR

/-- The residue map is injective on every window. -/
theorem fiveTermCharacteristicResidue_injOn {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (a : ℤ) :
    Set.InjOn (fun x : ℤ × ℤ => fiveTermCharacteristicResidue γ x.1 x.2)
      (fiveTermWindow γ a : Set (ℤ × ℤ)) := by
  intro x hx y hy hxy
  obtain ⟨hx0, hxc, hxlo, hxhi⟩ := (mem_fiveTermWindow h a x).1 hx
  obtain ⟨hy0, hyc, hylo, hyhi⟩ := (mem_fiveTermWindow h a y).1 hy
  have hc : 0 < γ 1 0 := h.lowerLeft_pos
  have hN : 0 < (finiteDilogOrder γ : ℤ) := by exact_mod_cast finiteDilogOrder_pos h
  change fiveTermCharacteristicResidue γ x.1 x.2 =
    fiveTermCharacteristicResidue γ y.1 y.2 at hxy
  have hz : fiveTermCharacteristicResidue γ (x.1 - y.1) (x.2 - y.2) = 0 := by
    have hadd := fiveTermCharacteristicResidue_add γ (x.1 - y.1) (x.2 - y.2) y.1 y.2
    simp only [sub_add_cancel] at hadd
    rw [hxy] at hadd
    apply add_right_cancel (b := fiveTermCharacteristicResidue γ y.1 y.2)
    simpa only [zero_add] using hadd.symm
  obtain ⟨s, t, hfirst, hsecond⟩ :=
    (fiveTermCharacteristicResidue_eq_zero_iff h _ _).1 hz
  have hS : fiveTermLatticeIndex γ x.1 x.2 - fiveTermLatticeIndex γ y.1 y.2 =
      s * finiteDilogOrder γ := by
    have hsub : fiveTermLatticeIndex γ (x.1 - y.1) (x.2 - y.2) =
        fiveTermLatticeIndex γ x.1 x.2 - fiveTermLatticeIndex γ y.1 y.2 := by
      simp only [fiveTermLatticeIndex]
      ring
    rw [← hsub, hfirst, hsecond, fiveTermLatticeIndex_rows h]
  have hs : s = 0 := by
    by_contra hs0
    rcases lt_or_gt_of_ne hs0 with hsneg | hspos
    · have hsle : s ≤ -1 := by omega
      nlinarith [mul_nonneg (show 0 ≤ -s - 1 by omega) hN.le]
    · have hsge : 1 ≤ s := by omega
      nlinarith [mul_nonneg (show 0 ≤ s - 1 by omega) hN.le]
  have hdiff : x.1 - y.1 = t * γ 1 0 := by simpa [hs] using hfirst
  have hxdiff : x.1 - y.1 = 0 := by
    have hdvd : γ 1 0 ∣ x.1 - y.1 := ⟨t, by simpa [mul_comm] using hdiff⟩
    by_cases hpos : 0 ≤ x.1 - y.1
    · exact Int.eq_zero_of_dvd_of_nonneg_of_lt hpos (by omega) hdvd
    · have hneg : -(x.1 - y.1) = 0 :=
        Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) (by omega) (dvd_neg.mpr hdvd)
      omega
  have ht : t = 0 := by
    have : t * γ 1 0 = 0 := by omega
    exact (mul_eq_zero.mp this).resolve_right hc.ne'
  apply Prod.ext
  · omega
  · exact sub_eq_zero.mp (by simpa [hs, ht] using hsecond)

/-- The second row moves a pair into the first-coordinate strip without changing its index or
residue; used by `exists_mem_fiveTermWindow_residue_eq` and the index-fiber identity. -/
private theorem fiveTermWindow_of_index_interval {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (a m k : ℤ)
    (hlo : a ≤ fiveTermLatticeIndex γ m k)
    (hhi : fiveTermLatticeIndex γ m k < a + finiteDilogOrder γ) :
    ∃ x ∈ fiveTermWindow γ a,
      fiveTermLatticeIndex γ x.1 x.2 = fiveTermLatticeIndex γ m k ∧
      fiveTermCharacteristicResidue γ x.1 x.2 =
        fiveTermCharacteristicResidue γ m k := by
  let c : ℤ := γ 1 0
  let t : ℤ := m / c
  have hc : 0 < c := h.lowerLeft_pos
  have hm : m - t * c = m % c := by
    have := Int.emod_add_mul_ediv m c
    calc
      m - t * c = m - c * (m / c) := by dsimp [t]; ring
      _ = m % c := by omega
  have hshift := fiveTerm_rows_shift h m k 0 (-t)
  have hI : fiveTermLatticeIndex γ (m - t * c) (k - t * (γ 1 1 - 1)) =
      fiveTermLatticeIndex γ m k := by
    simpa [c, sub_eq_add_neg] using hshift.1
  have hR : fiveTermCharacteristicResidue γ (m - t * c) (k - t * (γ 1 1 - 1)) =
      fiveTermCharacteristicResidue γ m k := by
    simpa [c, sub_eq_add_neg] using hshift.2
  refine ⟨(m - t * c, k - t * (γ 1 1 - 1)), ?_, hI, hR⟩
  apply (mem_fiveTermWindow h a _).2
  rw [hI, hm]
  exact ⟨Int.emod_nonneg _ hc.ne', Int.emod_lt_of_pos _ hc, hlo, hhi⟩

/-- Every class of `G` has a representative in every window. -/
private theorem exists_mem_fiveTermWindow_residue_eq {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (a : ℤ) {g : Fin 2 → ZMod (finiteDilogOrder γ)}
    (hg : g ∈ finiteDilogGroup γ) :
    ∃ x ∈ fiveTermWindow γ a, fiveTermCharacteristicResidue γ x.1 x.2 = g := by
  obtain ⟨m, k, hr⟩ := exists_fiveTermCharacteristicResidue_eq h hg
  let N : ℤ := finiteDilogOrder γ
  have hN : 0 < N := by dsimp [N]; exact_mod_cast finiteDilogOrder_pos h
  let q : ℤ := -((fiveTermLatticeIndex γ m k - a) / N)
  let m' : ℤ := m + q * (γ 0 0 - 1)
  let k' : ℤ := k + q * γ 0 1
  have hshift := fiveTerm_rows_shift h m k q 0
  have hI : fiveTermLatticeIndex γ m' k' =
      (fiveTermLatticeIndex γ m k - a) % N + a := by
    calc
      _ = fiveTermLatticeIndex γ m k + q * N := by simpa [m', k', N] using hshift.1
      _ = _ := by
        have := Int.emod_add_mul_ediv (fiveTermLatticeIndex γ m k - a) N
        calc
          fiveTermLatticeIndex γ m k + q * N =
              fiveTermLatticeIndex γ m k -
                N * ((fiveTermLatticeIndex γ m k - a) / N) := by dsimp [q]; ring
          _ = _ := by omega
  have hR : fiveTermCharacteristicResidue γ m' k' = g := by
    simpa [m', k'] using hshift.2.trans hr
  have hlo : a ≤ fiveTermLatticeIndex γ m' k' := by
    rw [hI]
    have := Int.emod_nonneg (fiveTermLatticeIndex γ m k - a) hN.ne'
    omega
  have hhi : fiveTermLatticeIndex γ m' k' < a + finiteDilogOrder γ := by
    rw [hI]
    have := Int.emod_lt_of_pos (fiveTermLatticeIndex γ m k - a) hN
    omega
  obtain ⟨x, hx, _, hxR⟩ := fiveTermWindow_of_index_interval h a m' k' hlo hhi
  exact ⟨x, hx, hxR.trans hR⟩

/-- A sum over a window of a function of the residue is the sum over `G`. -/
theorem sum_fiveTermWindow {γ : SL(2, ℤ)} {τ : ℝ} (h : IsAttractiveFixedPoint γ τ)
    [NeZero (finiteDilogOrder γ)] (a : ℤ) (f : (Fin 2 → ZMod (finiteDilogOrder γ)) → ℂ) :
    (∑ x ∈ fiveTermWindow γ a, f (fiveTermCharacteristicResidue γ x.1 x.2)) =
      ∑ g : finiteDilogGroup γ, f g := by
  let F : ℤ × ℤ → finiteDilogGroup γ := fun x =>
    ⟨fiveTermCharacteristicResidue γ x.1 x.2,
      fiveTermCharacteristicResidue_mem h x.1 x.2⟩
  change (∑ x ∈ fiveTermWindow γ a, f (F x).1) =
    ∑ g ∈ (Finset.univ : Finset (finiteDilogGroup γ)), f g.1
  apply Finset.sum_bij (fun x _ => F x)
  · intro x hx
    exact Finset.mem_univ _
  · intro x hx y hy hxy
    apply fiveTermCharacteristicResidue_injOn h a hx hy
    exact congrArg Subtype.val hxy
  · intro g _
    obtain ⟨x, hx, hr⟩ := exists_mem_fiveTermWindow_residue_eq h a g.2
    exact ⟨x, hx, Subtype.ext hr⟩
  · intro x hx
    rfl

/-- The first row changes an exact index by `qN`; the second row restores the first-coordinate
strip. Used by `sum_fiveTermWindow_index_sub`. -/
private theorem fiveTermWindow_index_transport {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (m k s q : ℤ)
    (hS : fiveTermLatticeIndex γ m k = s) :
    ∃ x ∈ fiveTermWindow γ (s + q * finiteDilogOrder γ),
      fiveTermLatticeIndex γ x.1 x.2 = s + q * finiteDilogOrder γ ∧
      fiveTermCharacteristicResidue γ x.1 x.2 =
        fiveTermCharacteristicResidue γ m k := by
  let m' : ℤ := m + q * (γ 0 0 - 1)
  let k' : ℤ := k + q * γ 0 1
  have hshift := fiveTerm_rows_shift h m k q 0
  have hI : fiveTermLatticeIndex γ m' k' = s + q * finiteDilogOrder γ := by
    simpa [m', k', hS] using hshift.1
  have hR : fiveTermCharacteristicResidue γ m' k' =
      fiveTermCharacteristicResidue γ m k := by
    simpa [m', k'] using hshift.2
  have hN : 0 < (finiteDilogOrder γ : ℤ) := by exact_mod_cast finiteDilogOrder_pos h
  obtain ⟨x, hx, hxI, hxR⟩ := fiveTermWindow_of_index_interval h
    (s + q * finiteDilogOrder γ) m' k' (by omega) (by omega)
  exact ⟨x, hx, hxI.trans hI, hxR.trans hR⟩

/-- The residue images of the two exact-index fibers agree; used by
`sum_fiveTermWindow_index_sub`. -/
private theorem fiveTermWindow_index_fiber_image {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (s : ℤ) :
    ((fiveTermWindow γ s).filter
      (fun x => fiveTermLatticeIndex γ x.1 x.2 = s)).image
        (fun x => fiveTermCharacteristicResidue γ x.1 x.2) =
      ((fiveTermWindow γ (s - finiteDilogOrder γ)).filter
        (fun x => fiveTermLatticeIndex γ x.1 x.2 = s - finiteDilogOrder γ)).image
          (fun x => fiveTermCharacteristicResidue γ x.1 x.2) := by
  ext r
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyS, hyR⟩ := fiveTermWindow_index_transport h x.1 x.2 s (-1)
      (Finset.mem_filter.mp hx).2
    refine ⟨y, Finset.mem_filter.mpr ⟨?_, ?_⟩, hyR⟩
    · simpa only [neg_one_mul, sub_eq_add_neg] using hy
    · simpa only [neg_one_mul, sub_eq_add_neg] using hyS
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxS, hxR⟩ := fiveTermWindow_index_transport h y.1 y.2
      (s - finiteDilogOrder γ) 1 (Finset.mem_filter.mp hy).2
    refine ⟨x, Finset.mem_filter.mpr ⟨?_, ?_⟩, hxR⟩
    · simpa using hx
    · simpa using hxS

/-- The pairs of the window starting at `s` with index `s` and those of the window starting at
`s - N` with index `s - N` have the same residues: adding `λ₁` matches them. -/
theorem sum_fiveTermWindow_index_sub {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) (s : ℤ) (f : (Fin 2 → ZMod (finiteDilogOrder γ)) → ℂ) :
    (∑ x ∈ fiveTermWindow γ s with fiveTermLatticeIndex γ x.1 x.2 = s,
        f (fiveTermCharacteristicResidue γ x.1 x.2)) =
      ∑ x ∈ fiveTermWindow γ (s - finiteDilogOrder γ) with
          fiveTermLatticeIndex γ x.1 x.2 = s - finiteDilogOrder γ,
        f (fiveTermCharacteristicResidue γ x.1 x.2) := by
  let R : ℤ × ℤ → Fin 2 → ZMod (finiteDilogOrder γ) :=
    fun x => fiveTermCharacteristicResidue γ x.1 x.2
  let A := (fiveTermWindow γ s).filter
    (fun x => fiveTermLatticeIndex γ x.1 x.2 = s)
  let B := (fiveTermWindow γ (s - finiteDilogOrder γ)).filter
    (fun x => fiveTermLatticeIndex γ x.1 x.2 = s - finiteDilogOrder γ)
  have himage : A.image R = B.image R := fiveTermWindow_index_fiber_image h s
  change (∑ x ∈ A, f (R x)) = ∑ x ∈ B, f (R x)
  calc
    _ = ∑ r ∈ A.image R, f r := (Finset.sum_image (by
      intro x hx y hy hxy
      exact fiveTermCharacteristicResidue_injOn h s
        (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy)).symm
    _ = ∑ r ∈ B.image R, f r := by rw [himage]
    _ = _ := Finset.sum_image (by
      intro x hx y hy hxy
      exact fiveTermCharacteristicResidue_injOn h (s - finiteDilogOrder γ)
        (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy)

/-! ### Positive source representatives -/

/-- A complement to `v` in the first row represents `-v` and has index `N-S(v)`; used by
`exists_fiveTerm_positive_representatives`. -/
private theorem fiveTerm_positive_complement {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) {u v : Fin 2 → ZMod (finiteDilogOrder γ)}
    (huv : u + v = 0) (v₁ v₂ : ℤ)
    (hvRes : fiveTermCharacteristicResidue γ v₁ v₂ = v)
    (hvBound : 1 ≤ fiveTermLatticeIndex γ v₁ v₂ ∧
      fiveTermLatticeIndex γ v₁ v₂ ≤ finiteDilogOrder γ) :
    ∃ u₁ u₂ : ℤ, fiveTermCharacteristicResidue γ u₁ u₂ = u ∧
      (0 ≤ fiveTermLatticeIndex γ u₁ u₂ ∧
        fiveTermLatticeIndex γ u₁ u₂ < finiteDilogOrder γ) ∧
      u₁ + v₁ = γ 0 0 - 1 ∧ u₂ + v₂ = γ 0 1 := by
  let a : ℤ := γ 0 0 - 1
  let b : ℤ := γ 0 1
  have hrow : fiveTermCharacteristicResidue γ a b = 0 := by
    simpa [a, b] using fiveTermCharacteristicResidue_rows_zero h 1 0
  have hresComp : fiveTermCharacteristicResidue γ (a - v₁) (b - v₂) = -v := by
    have hadd := fiveTermCharacteristicResidue_add γ (a - v₁) (b - v₂) v₁ v₂
    simp only [sub_add_cancel] at hadd
    rw [hrow, hvRes] at hadd
    exact eq_neg_of_add_eq_zero_left hadd.symm
  have hindexComp : fiveTermLatticeIndex γ (a - v₁) (b - v₂) =
      finiteDilogOrder γ - fiveTermLatticeIndex γ v₁ v₂ := by
    have hadd := fiveTermLatticeIndex_add γ (a - v₁) (b - v₂) v₁ v₂
    simp only [sub_add_cancel] at hadd
    rw [show fiveTermLatticeIndex γ a b = finiteDilogOrder γ by
      simpa [a, b] using fiveTermLatticeIndex_firstRow h] at hadd
    omega
  refine ⟨a - v₁, b - v₂, ?_, ?_, ?_, ?_⟩
  · rw [hresComp]
    simpa only [zero_sub] using (eq_neg_of_add_eq_zero_left huv).symm
  · rw [hindexComp]
    constructor <;> omega
  · dsimp [a]
    omega
  · dsimp [b]
    omega

/-- For classes `u, v` of `G` with `v ≠ 0` there are source representatives with
`0 ≤ S(u) < N` and `1 ≤ S(v) ≤ N`, the zero pair when `u = 0`, and representatives summing to
`(a-1,b)` when `u + v = 0`; these are the positive representatives of the crossed-pole argument
in [RW26, Radchenko, Wheeler (2026), Section 3.2]. -/
theorem exists_fiveTerm_positive_representatives {γ : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint γ τ) {u v : Fin 2 → ZMod (finiteDilogOrder γ)}
    (hu : u ∈ finiteDilogGroup γ) (hv : v ∈ finiteDilogGroup γ) (hv0 : v ≠ 0) :
    ∃ u₁ u₂ v₁ v₂ : ℤ,
      fiveTermCharacteristicResidue γ u₁ u₂ = u ∧
      fiveTermCharacteristicResidue γ v₁ v₂ = v ∧
      (0 ≤ fiveTermLatticeIndex γ u₁ u₂ ∧ fiveTermLatticeIndex γ u₁ u₂ < finiteDilogOrder γ) ∧
      (1 ≤ fiveTermLatticeIndex γ v₁ v₂ ∧ fiveTermLatticeIndex γ v₁ v₂ ≤ finiteDilogOrder γ) ∧
      (u = 0 → u₁ = 0 ∧ u₂ = 0) ∧
      (u + v = 0 → u₁ + v₁ = γ 0 0 - 1 ∧ u₂ + v₂ = γ 0 1) := by
  obtain ⟨⟨v₁, v₂⟩, hvWindow, hvRes⟩ :=
    exists_mem_fiveTermWindow_residue_eq h 1 hv
  obtain ⟨_, _, hvLo, hvHi⟩ := (mem_fiveTermWindow h 1 (v₁, v₂)).1 hvWindow
  simp only at hvLo hvHi
  have hN := finiteDilogOrder_pos h
  have hvBound : 1 ≤ fiveTermLatticeIndex γ v₁ v₂ ∧
      fiveTermLatticeIndex γ v₁ v₂ ≤ finiteDilogOrder γ := by omega
  by_cases hu0 : u = 0
  · refine ⟨0, 0, v₁, v₂, ?_, hvRes, ?_, hvBound, ?_, ?_⟩
    · simpa [hu0] using fiveTermCharacteristicResidue_rows_zero h 0 0
    · simp only [fiveTermLatticeIndex, zero_add, mul_zero]
      exact ⟨le_refl 0, by exact_mod_cast hN⟩
    · exact fun _ => ⟨rfl, rfl⟩
    · intro huv0
      exact (hv0 (by simpa [hu0] using huv0)).elim
  · by_cases huv0 : u + v = 0
    · obtain ⟨u₁, u₂, huRes, huBound, huSum1, huSum2⟩ :=
        fiveTerm_positive_complement h huv0 v₁ v₂ hvRes hvBound
      refine ⟨u₁, u₂, v₁, v₂, huRes, hvRes, huBound, hvBound, ?_, ?_⟩
      · exact fun hu => (hu0 hu).elim
      · exact fun _ => ⟨huSum1, huSum2⟩
    · obtain ⟨⟨u₁, u₂⟩, huWindow, huRes⟩ :=
        exists_mem_fiveTermWindow_residue_eq h 0 hu
      obtain ⟨_, _, huLo, huHi⟩ := (mem_fiveTermWindow h 0 (u₁, u₂)).1 huWindow
      simp only at huLo huHi
      refine ⟨u₁, u₂, v₁, v₂, huRes, hvRes, ?_, hvBound, ?_, ?_⟩
      · exact ⟨huLo, by simpa only [zero_add] using huHi⟩
      · exact fun hu => (hu0 hu).elim
      · exact fun huv => (huv0 huv).elim

end SIC

end
