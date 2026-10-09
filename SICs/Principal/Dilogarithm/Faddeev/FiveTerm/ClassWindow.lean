/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.FiniteCharacteristics

/-!
# The window of source pairs representing the principal finite group

The source pairs with first coordinate in `[0, c)` and lattice index in a window of `d(d-3)`
consecutive integers represent every class of `G_d` exactly once.

This module follows the residue bookkeeping of [RW26, Radchenko, Wheeler (2026), Section 3.2,
the proof of Theorem 2, `thm:fg.equs`]: the strip between a contour and its translate by
`(ε-1)/c` contains, over all `m ∈ ℤ/c`, one kernel pole for every class of `G`. With
`c = d(d-2)`, `N = d²(d-3)`, and `H = d(d-3)`, the kernel poles of the summed residue kernel are
at `-(ε-1)S_d(x)/(cH)`, so the strip is a window of `H` consecutive values of the lattice index
`S_d(x) = x₁ + (d-2)x₂`.

## The argument

A pair `x = (m, k)` in `Λ`, the kernel of the residue map, has `d ∣ m` and `H ∣ S_d(x)`: reading
the residue `(-dk - cm, -ck - d(d²-3d+1)m)` modulo `N = dH` gives `k ≡ -(d-2)m (mod H)` and then
`(d-3)m ≡ 0 (mod H)`. Two pairs of the window with the same class differ by such a pair `λ`
with `|S_d(λ)| < H`, so `S_d(λ) = 0`, `m_λ = -(d-2)k_λ`, `d ∣ (d-2)k_λ`, and `|m_λ| < c` leaves
`k_λ ∈ {0, ±d/2}`; the residue excludes `±d/2` for even `d`. Hence the residue map is injective
on the window. Every class has a representative with index in the window, since a transport
that preserves the residue shifts the index by multiples of `H`; adding a multiple of the
`Λ`-pair `(c, -d)`, whose index is `0`, then moves its first coordinate into `[0, c)`
(`exists_mem_principalFiveTermWindow_residue_eq`). Hence the
residue map is a bijection from the window onto `G_d`, and sums over `G_d` are sums over the
window.
-/

noncomputable section

namespace SIC

/-! ### Pairs in the kernel of the residue map -/

/-- A residue coordinate with factor `d` vanishes modulo `N` exactly when its remaining
factor is divisible by `H = N/d`. -/
private theorem principalFiveTermCoord_zero_iff (d : ℕ) (hd : 3 < d) (z : ℤ) :
    ((-(d : ℤ) * z : ℤ) : ZMod (principalDilogOrder d)) = 0 ↔
      principalFiveTermUpperIndexBound d ∣ z := by
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hN : (principalDilogOrder d : ℤ) =
      (d : ℤ) * principalFiveTermUpperIndexBound d := by
    simp [principalDilogOrder, principalFiveTermUpperIndexBound,
      Nat.cast_sub (by omega : 3 ≤ d)]
    ring
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hN]
  simpa only [neg_mul, dvd_neg] using
    (mul_dvd_mul_iff_left hd0 :
      (d : ℤ) * principalFiveTermUpperIndexBound d ∣ (d : ℤ) * z ↔
        principalFiveTermUpperIndexBound d ∣ z)

/-- A source pair has zero residue exactly when both reduced lattice coordinates are
divisible by `H = d(d-3)`. -/
theorem principalFiveTermCharacteristicResidue_eq_zero_iff
    (d : ℕ) (hd : 3 < d) (m k : ℤ) :
    principalFiveTermCharacteristicResidue d m k = 0 ↔
      principalFiveTermUpperIndexBound d ∣ k + ((d : ℤ) - 2) * m ∧
      principalFiveTermUpperIndexBound d ∣
        ((d : ℤ) - 2) * k + ((d : ℤ) ^ 2 - 3 * d + 1) * m := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Pi.zero_apply, principalFiveTermCharacteristicResidue,
      principalDilogOfLattice_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at h0 h1
    constructor
    · apply (principalFiveTermCoord_zero_iff d hd _).mp
      convert h0 using 1; push_cast; ring
    · apply (principalFiveTermCoord_zero_iff d hd _).mp
      convert h1 using 1; push_cast; ring
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i
    · simp only [Pi.zero_apply, principalFiveTermCharacteristicResidue,
        principalDilogOfLattice_apply, Matrix.cons_val_zero]
      convert (principalFiveTermCoord_zero_iff d hd _).mpr h0 using 1
      push_cast
      ring
    · simp only [Pi.zero_apply, principalFiveTermCharacteristicResidue,
        principalDilogOfLattice_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      convert (principalFiveTermCoord_zero_iff d hd _).mpr h1 using 1
      push_cast
      ring

/-- Every multiple of `(c,-d)` has zero source residue. -/
theorem principalFiveTermCharacteristicResidue_mul_neg_mul
    (d : ℕ) (hd : 3 < d) (t : ℤ) :
    principalFiveTermCharacteristicResidue d
      (((d : ℤ) * ((d : ℤ) - 2)) * t) (-(d : ℤ) * t) = 0 := by
  apply (principalFiveTermCharacteristicResidue_eq_zero_iff d hd _ _).2
  constructor
  · refine ⟨((d : ℤ) - 1) * t, ?_⟩
    simp only [principalFiveTermUpperIndexBound]
    ring
  · refine ⟨((d : ℤ) * ((d : ℤ) - 2)) * t, ?_⟩
    simp only [principalFiveTermUpperIndexBound]
    ring

/-- A pair with residue zero has first coordinate divisible by `d`. -/
theorem dvd_of_residue_eq_zero (d : ℕ) (hd : 3 < d) (m k : ℤ)
    (h : principalFiveTermCharacteristicResidue d m k = 0) : (d : ℤ) ∣ m := by
  obtain ⟨h0, h1⟩ := (principalFiveTermCharacteristicResidue_eq_zero_iff d hd m k).1 h
  have hcomb : principalFiveTermUpperIndexBound d ∣ ((d : ℤ) - 3) * m := by
    convert h1.sub (h0.mul_left ((d : ℤ) - 2)) using 1
    ring
  have h3 : ((d : ℤ) - 3) ≠ 0 := by
    have hdI : (3 : ℤ) < d := by exact_mod_cast hd
    omega
  apply (mul_dvd_mul_iff_left h3).mp
  simpa only [principalFiveTermUpperIndexBound, mul_comm] using hcomb

/-- A pair with residue zero has lattice index divisible by `H = d(d-3)`. -/
theorem principalFiveTermUpperIndexBound_dvd_latticeIndex (d : ℕ) (hd : 3 < d) (m k : ℤ)
    (h : principalFiveTermCharacteristicResidue d m k = 0) :
    principalFiveTermUpperIndexBound d ∣ principalFiveTermLatticeIndex d m k := by
  have h0 := (principalFiveTermCharacteristicResidue_eq_zero_iff d hd m k).1 h |>.1
  obtain ⟨t, ht⟩ := dvd_of_residue_eq_zero d hd m k h
  have hterm : principalFiveTermUpperIndexBound d ∣
      ((d : ℤ) - 1) * ((d : ℤ) - 3) * m := by
    refine ⟨((d : ℤ) - 1) * t, ?_⟩
    rw [ht]
    simp only [principalFiveTermUpperIndexBound]
    ring
  convert (h0.mul_left ((d : ℤ) - 2)).sub hterm using 1
  simp only [principalFiveTermLatticeIndex]
  ring

/-- A pair with residue zero and lattice index zero is an integer multiple of `(c, -d)`. -/
theorem eq_mul_lowerLeft_of_residue_eq_zero (d : ℕ) (hd : 3 < d) (m k : ℤ)
    (h : principalFiveTermCharacteristicResidue d m k = 0)
    (hS : principalFiveTermLatticeIndex d m k = 0) :
    ∃ t : ℤ, m = t * ((d : ℤ) * ((d : ℤ) - 2)) ∧ k = -(t * (d : ℤ)) := by
  have h0 := (principalFiveTermCharacteristicResidue_eq_zero_iff d hd m k).1 h |>.1
  have hm : m = -((d : ℤ) - 2) * k := by
    dsimp [principalFiveTermLatticeIndex] at hS
    linear_combination hS
  have h1 : principalFiveTermUpperIndexBound d ∣
      -(((d : ℤ) - 3) * (((d : ℤ) - 1) * k)) := by
    convert h0 using 1
    rw [hm]
    ring
  have h3 : ((d : ℤ) - 3) ≠ 0 := by
    have hdI : (3 : ℤ) < d := by exact_mod_cast hd
    omega
  have hdk1 : (d : ℤ) ∣ ((d : ℤ) - 1) * k :=
    (mul_dvd_mul_iff_left h3).mp (by
      simpa only [principalFiveTermUpperIndexBound, mul_comm, dvd_neg] using h1)
  have hdk : (d : ℤ) ∣ k := by
    have hdk' : (d : ℤ) ∣ (d : ℤ) * k - ((d : ℤ) - 1) * k :=
      (dvd_mul_right (d : ℤ) k).sub hdk1
    convert hdk' using 1
    ring
  obtain ⟨t, ht⟩ := hdk
  refine ⟨-t, ?_, ?_⟩
  · rw [hm, ht]
    ring
  · rw [ht]
    ring

/-! ### The window

For an integer `a`, the window is the finite set of pairs `(m, k)` with `0 ≤ m < c` and
`a ≤ S_d(m, k) < a + H`; a bounding box on `k` makes it a `Finset`. -/

/-- The window of source pairs with first coordinate in `[0, c)` and lattice index in
`[a, a + H)`, as a finite set: the `k`-coordinate is bounded by `|a| + c + H` because
`|(d-2)k| = |S - m|`. -/
def principalFiveTermWindow (d : ℕ) (a : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Ico (0 : ℤ) ((d : ℤ) * ((d : ℤ) - 2))) ×ˢ
      (Finset.Icc (-(|a| + (d : ℤ) * ((d : ℤ) - 2) + principalFiveTermUpperIndexBound d))
        (|a| + (d : ℤ) * ((d : ℤ) - 2) + principalFiveTermUpperIndexBound d))).filter
    (fun x => a ≤ principalFiveTermLatticeIndex d x.1 x.2 ∧
      principalFiveTermLatticeIndex d x.1 x.2 < a + principalFiveTermUpperIndexBound d)

/-- The index interval and the first-coordinate bound imply the finite bounding box on
the second coordinate used in `principalFiveTermWindow`. -/
private theorem principalFiveTermWindow_second_bounds (d : ℕ) (hd : 3 < d) (a : ℤ)
    (x : ℤ × ℤ) (hm0 : 0 ≤ x.1) (hmc : x.1 < (d : ℤ) * ((d : ℤ) - 2))
    (hlo : a ≤ principalFiveTermLatticeIndex d x.1 x.2)
    (hhi : principalFiveTermLatticeIndex d x.1 x.2 < a + principalFiveTermUpperIndexBound d) :
    -(|a| + (d : ℤ) * ((d : ℤ) - 2) + principalFiveTermUpperIndexBound d) ≤ x.2 ∧
      x.2 ≤ |a| + (d : ℤ) * ((d : ℤ) - 2) + principalFiveTermUpperIndexBound d := by
  have hdI : (3 : ℤ) < d := by exact_mod_cast hd
  have ha₁ : a ≤ |a| := le_abs_self a
  have ha₂ : -|a| ≤ a := neg_abs_le a
  change a ≤ x.1 + ((d : ℤ) - 2) * x.2 at hlo
  change x.1 + ((d : ℤ) - 2) * x.2 < a + principalFiveTermUpperIndexBound d at hhi
  have hc0 : 0 ≤ (d : ℤ) * ((d : ℤ) - 2) := mul_nonneg (by omega) (by omega)
  have hH0 : 0 ≤ principalFiveTermUpperIndexBound d := by
    dsimp [principalFiveTermUpperIndexBound]
    exact mul_nonneg (by omega) (by omega)
  constructor
  · by_cases hk : x.2 ≤ 0
    · have hmul : ((d : ℤ) - 2) * x.2 ≤ x.2 := by
        nlinarith [mul_nonneg (show 0 ≤ (d : ℤ) - 3 by omega)
          (show 0 ≤ -x.2 by omega)]
      omega
    · omega
  · by_cases hk : 0 ≤ x.2
    · have hmul : x.2 ≤ ((d : ℤ) - 2) * x.2 := by
        nlinarith [mul_nonneg (show 0 ≤ (d : ℤ) - 3 by omega) hk]
      omega
    · omega

/-- Membership in the window is the pair of conditions on the first coordinate and the index. -/
theorem mem_principalFiveTermWindow (d : ℕ) (hd : 3 < d) (a : ℤ) (x : ℤ × ℤ) :
    x ∈ principalFiveTermWindow d a ↔
      0 ≤ x.1 ∧ x.1 < (d : ℤ) * ((d : ℤ) - 2) ∧
        a ≤ principalFiveTermLatticeIndex d x.1 x.2 ∧
          principalFiveTermLatticeIndex d x.1 x.2 < a + principalFiveTermUpperIndexBound d := by
  simp only [principalFiveTermWindow, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Ico, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨hm0, hmc⟩, _⟩, hlo, hhi⟩
    exact ⟨hm0, hmc, hlo, hhi⟩
  · rintro ⟨hm0, hmc, hlo, hhi⟩
    obtain ⟨hlow, hupp⟩ :=
      principalFiveTermWindow_second_bounds d hd a x hm0 hmc hlo hhi
    exact ⟨⟨⟨hm0, hmc⟩, ⟨hlow, hupp⟩⟩, hlo, hhi⟩

/-- A multiple strictly between the negative and positive modulus is zero. -/
private theorem eq_zero_of_dvd_of_mem_open_interval (H s : ℤ)
    (hdvd : H ∣ s) (hlo : -H < s) (hhi : s < H) : s = 0 := by
  by_cases hs : 0 ≤ s
  · exact Int.eq_zero_of_dvd_of_nonneg_of_lt hs hhi hdvd
  · have hneg : -s = 0 :=
      Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) (by omega) (dvd_neg.mpr hdvd)
    omega

/-- The residue map is injective on the window: two window pairs with the same class differ by
a pair of `Λ` with index in `(-H, H)`, hence of index zero, hence a multiple of `(c, -d)`,
which the bound on the first coordinates forces to vanish. -/
theorem principalFiveTermCharacteristicResidue_injOn (d : ℕ) (hd : 3 < d) (a : ℤ) :
    Set.InjOn (fun x : ℤ × ℤ => principalFiveTermCharacteristicResidue d x.1 x.2)
      (principalFiveTermWindow d a : Set (ℤ × ℤ)) := by
  intro x hx y hy hxy
  obtain ⟨hx0, hxc, hxlo, hxhi⟩ := (mem_principalFiveTermWindow d hd a x).1 hx
  obtain ⟨hy0, hyc, hylo, hyhi⟩ := (mem_principalFiveTermWindow d hd a y).1 hy
  change principalFiveTermCharacteristicResidue d x.1 x.2 =
    principalFiveTermCharacteristicResidue d y.1 y.2 at hxy
  have hzero : principalFiveTermCharacteristicResidue d (x.1 - y.1) (x.2 - y.2) =
      0 := by rw [principalFiveTermCharacteristicResidue_sub, hxy, sub_self]
  have hindex : principalFiveTermLatticeIndex d (x.1 - y.1) (x.2 - y.2) =
      principalFiveTermLatticeIndex d x.1 x.2 -
        principalFiveTermLatticeIndex d y.1 y.2 := by
    simp only [principalFiveTermLatticeIndex]
    ring
  have hS : principalFiveTermLatticeIndex d (x.1 - y.1) (x.2 - y.2) = 0 := by
    apply eq_zero_of_dvd_of_mem_open_interval (principalFiveTermUpperIndexBound d)
      _ (principalFiveTermUpperIndexBound_dvd_latticeIndex d hd _ _ hzero)
    all_goals rw [hindex]; omega
  obtain ⟨t, hfirst, hsecond⟩ :=
    eq_mul_lowerLeft_of_residue_eq_zero d hd _ _ hzero hS
  have hc : 0 < (d : ℤ) * ((d : ℤ) - 2) := by
    have hdI : (3 : ℤ) < d := by exact_mod_cast hd
    nlinarith
  have hdiff : x.1 - y.1 = 0 := by
    apply eq_zero_of_dvd_of_mem_open_interval _ _ ⟨t, by rw [mul_comm]; exact hfirst⟩
    all_goals omega
  have ht : t = 0 := by nlinarith [hfirst]
  simp only [ht, zero_mul, neg_zero] at hsecond
  apply Prod.ext
  · omega
  · omega

/-- An index-normalized pair can be moved into the window by a multiple of `(c,-d)`
without changing its exact index or residue. -/
private theorem principalFiveTermWindow_of_index_interval (d : ℕ) (hd : 3 < d)
    (a m k : ℤ) (hlo : a ≤ principalFiveTermLatticeIndex d m k)
    (hhi : principalFiveTermLatticeIndex d m k < a + principalFiveTermUpperIndexBound d) :
    ∃ x ∈ principalFiveTermWindow d a,
      principalFiveTermLatticeIndex d x.1 x.2 = principalFiveTermLatticeIndex d m k ∧
      principalFiveTermCharacteristicResidue d x.1 x.2 =
        principalFiveTermCharacteristicResidue d m k := by
  let c : ℤ := (d : ℤ) * ((d : ℤ) - 2)
  have hc : 0 < c := by
    have hdI : (3 : ℤ) < d := by exact_mod_cast hd
    dsimp [c]
    nlinarith
  let t := m / c
  have hm : m - c * t = m % c := by
    have := Int.emod_add_mul_ediv m c
    dsimp [t]
    omega
  have hS : principalFiveTermLatticeIndex d (m - c * t) (k + (d : ℤ) * t) =
      principalFiveTermLatticeIndex d m k := by
    dsimp [principalFiveTermLatticeIndex, c]
    ring
  refine ⟨(m - c * t, k + (d : ℤ) * t), ?_, hS, ?_⟩
  · apply (mem_principalFiveTermWindow d hd a _).2
    rw [hS, hm]
    exact ⟨Int.emod_nonneg _ hc.ne', Int.emod_lt_of_pos _ hc, hlo, hhi⟩
  · change principalFiveTermCharacteristicResidue d (m - c * t) (k + (d : ℤ) * t) = _
    calc
      _ = principalFiveTermCharacteristicResidue d m k -
          principalFiveTermCharacteristicResidue d (c * t) (-(d : ℤ) * t) := by
            simpa only [neg_mul, sub_neg_eq_add] using
              (principalFiveTermCharacteristicResidue_sub d m k (c * t) (-(d : ℤ) * t))
      _ = _ := by rw [show principalFiveTermCharacteristicResidue d (c * t)
        (-(d : ℤ) * t) = 0 from principalFiveTermCharacteristicResidue_mul_neg_mul d hd t,
        sub_zero]

/-- Division by `H` selects the lattice transport whose index lies in `[a,a+H)`. -/
private theorem principalFiveTermLatticeIndex_normalize (d : ℕ) (m k a q : ℤ)
    (hq : q = -((principalFiveTermLatticeIndex d m k - a) /
      principalFiveTermUpperIndexBound d)) :
    principalFiveTermLatticeIndex d (m - (d : ℤ) * q) (k + (d : ℤ) * q) =
      (principalFiveTermLatticeIndex d m k - a) % principalFiveTermUpperIndexBound d + a := by
  rw [principalFiveTermLatticeIndex_transport, hq]
  calc
    principalFiveTermLatticeIndex d m k + principalFiveTermUpperIndexBound d *
        -((principalFiveTermLatticeIndex d m k - a) / principalFiveTermUpperIndexBound d) =
        principalFiveTermLatticeIndex d m k - principalFiveTermUpperIndexBound d *
          ((principalFiveTermLatticeIndex d m k - a) / principalFiveTermUpperIndexBound d) := by
            ring
    _ = _ := by
      have := Int.emod_add_mul_ediv (principalFiveTermLatticeIndex d m k - a)
        (principalFiveTermUpperIndexBound d)
      omega

/-- Every class of `G_d` is the residue of a window pair: normalize the index by transport, then
the first coordinate by multiples of `(c, -d)`. -/
theorem exists_mem_principalFiveTermWindow_residue_eq (d : ℕ) (hd : 3 < d) (a : ℤ)
    {g : Fin 2 → ZMod (principalDilogOrder d)} (hg : g ∈ principalDilogGroup d) :
    ∃ x ∈ principalFiveTermWindow d a,
      principalFiveTermCharacteristicResidue d x.1 x.2 = g := by
  obtain ⟨m, k, hr⟩ := exists_characteristicResidue_eq d hd hg
  let H := principalFiveTermUpperIndexBound d
  have hH : 0 < H := by
    have hdI : (3 : ℤ) < d := by exact_mod_cast hd
    dsimp [H, principalFiveTermUpperIndexBound]
    nlinarith
  let q := -((principalFiveTermLatticeIndex d m k - a) / H)
  let m' := m - (d : ℤ) * q
  let k' := k + (d : ℤ) * q
  have hr' : principalFiveTermCharacteristicResidue d m' k' = g :=
    (principalFiveTermCharacteristicResidue_transport d hd m k q).trans hr
  have hS' : principalFiveTermLatticeIndex d m' k' =
      (principalFiveTermLatticeIndex d m k - a) % H + a := by
    exact principalFiveTermLatticeIndex_normalize d m k a q rfl
  have hlo : a ≤ principalFiveTermLatticeIndex d m' k' := by
    rw [hS']
    have := Int.emod_nonneg (principalFiveTermLatticeIndex d m k - a) hH.ne'
    omega
  have hhi : principalFiveTermLatticeIndex d m' k' < a + H := by
    rw [hS']
    have := Int.emod_lt_of_pos (principalFiveTermLatticeIndex d m k - a) hH
    omega
  obtain ⟨x, hx, _, hres⟩ := principalFiveTermWindow_of_index_interval d hd a m' k' hlo hhi
  exact ⟨x, hx, hres.trans hr'⟩

/-- **Sums over the window are sums over `G_d`.** For every function on residue vectors,
`∑_{x ∈ window} f(x̄) = ∑_{g ∈ G_d} f(g)`: the residue map is a bijection from the window onto
`G_d`. This is the counting behind the residue sum in
[RW26, Radchenko, Wheeler (2026), Section 3.2]. -/
theorem sum_principalFiveTermWindow (d : ℕ) (hd : 3 < d) [NeZero (principalDilogOrder d)]
    (a : ℤ) (f : (Fin 2 → ZMod (principalDilogOrder d)) → ℂ) :
    (∑ x ∈ principalFiveTermWindow d a, f (principalFiveTermCharacteristicResidue d x.1 x.2)) =
      ∑ g : principalDilogGroup d, f g := by
  let F : ℤ × ℤ → principalDilogGroup d := fun x =>
    ⟨principalFiveTermCharacteristicResidue d x.1 x.2,
      principalFiveTermCharacteristicResidue_mem d hd x.1 x.2⟩
  change (∑ x ∈ principalFiveTermWindow d a, f (F x).1) =
    ∑ g ∈ (Finset.univ : Finset (principalDilogGroup d)), f g.1
  apply Finset.sum_bij (fun x _ => F x)
  · intro x hx
    exact Finset.mem_univ _
  · intro x hx y hy hxy
    apply principalFiveTermCharacteristicResidue_injOn d hd a hx hy
    exact congrArg Subtype.val hxy
  · intro g _
    obtain ⟨x, hx, hres⟩ := exists_mem_principalFiveTermWindow_residue_eq d hd a g.2
    exact ⟨x, hx, Subtype.ext hres⟩
  · intro x hx
    rfl

/-- Normalizing the first coordinate after source transport preserves the residue and gives
a window representative with the transported exact index. Used by
`sum_principalFiveTermWindow_index_sub_bound`. -/
private theorem principalFiveTermWindow_index_transport (d : ℕ) (hd : 3 < d)
    (m k s q : ℤ) (hS : principalFiveTermLatticeIndex d m k = s) :
    ∃ x ∈ principalFiveTermWindow d (s + principalFiveTermUpperIndexBound d * q),
      principalFiveTermLatticeIndex d x.1 x.2 =
        s + principalFiveTermUpperIndexBound d * q ∧
      principalFiveTermCharacteristicResidue d x.1 x.2 =
        principalFiveTermCharacteristicResidue d m k := by
  let m' := m - (d : ℤ) * q
  let k' := k + (d : ℤ) * q
  have hS' : principalFiveTermLatticeIndex d m' k' =
      s + principalFiveTermUpperIndexBound d * q := by
    simpa only [m', k', hS] using principalFiveTermLatticeIndex_transport d m k q
  obtain ⟨x, hx, hxS, hxR⟩ := principalFiveTermWindow_of_index_interval d hd
    (s + principalFiveTermUpperIndexBound d * q) m' k' (by omega) (by
      have hH := principalFiveTermUpperIndexBound_pos d hd
      omega)
  exact ⟨x, hx, hxS.trans hS',
    hxR.trans (principalFiveTermCharacteristicResidue_transport d hd m k q)⟩

/-- Exact index fibers in windows are carried to the fiber shifted by `H*q`, preserving
residue. Used by `sum_principalFiveTermWindow_index_sub_bound`. -/
private theorem principalFiveTermWindow_index_fiber_transport (d : ℕ) (hd : 3 < d)
    (a q : ℤ) (x : ℤ × ℤ)
    (hx : x ∈ (principalFiveTermWindow d a).filter
      (fun y => principalFiveTermLatticeIndex d y.1 y.2 = a)) :
    ∃ y ∈ (principalFiveTermWindow d (a + principalFiveTermUpperIndexBound d * q)).filter
        (fun z => principalFiveTermLatticeIndex d z.1 z.2 =
          a + principalFiveTermUpperIndexBound d * q),
      principalFiveTermCharacteristicResidue d y.1 y.2 =
        principalFiveTermCharacteristicResidue d x.1 x.2 := by
  obtain ⟨_, hxS⟩ := Finset.mem_filter.mp hx
  obtain ⟨y, hy, hyS, hyR⟩ :=
    principalFiveTermWindow_index_transport d hd x.1 x.2 a q hxS
  exact ⟨y, Finset.mem_filter.mpr ⟨hy, hyS⟩, hyR⟩

/-- Translation by the source lattice identifies the index fibers `S=s` and `S=s-H`,
with first coordinates normalized to `[0,c)`. Their sums of any function of the residue
class agree. This transports the two zero-pole fibers in the residue argument of
[RW26, Radchenko, Wheeler (2026), Section 3.2, proof of Theorem 2, `thm:fg.equs`]. -/
theorem sum_principalFiveTermWindow_index_sub_bound (d : ℕ) (hd : 3 < d)
    (s : ℤ) (f : (Fin 2 → ZMod (principalDilogOrder d)) → ℂ) :
    (∑ x ∈ principalFiveTermWindow d s with
        principalFiveTermLatticeIndex d x.1 x.2 = s,
      f (principalFiveTermCharacteristicResidue d x.1 x.2)) =
    ∑ x ∈ principalFiveTermWindow d (s - principalFiveTermUpperIndexBound d) with
        principalFiveTermLatticeIndex d x.1 x.2 = s - principalFiveTermUpperIndexBound d,
      f (principalFiveTermCharacteristicResidue d x.1 x.2) := by
  let R : ℤ × ℤ → Fin 2 → ZMod (principalDilogOrder d) :=
    fun x => principalFiveTermCharacteristicResidue d x.1 x.2
  let A := (principalFiveTermWindow d s).filter
    (fun x => principalFiveTermLatticeIndex d x.1 x.2 = s)
  let B := (principalFiveTermWindow d (s - principalFiveTermUpperIndexBound d)).filter
    (fun x => principalFiveTermLatticeIndex d x.1 x.2 =
      s - principalFiveTermUpperIndexBound d)
  have hforward : ∀ x ∈ A, ∃ y ∈ B, R y = R x := by
    intro x hx
    simpa only [A, B, R, mul_neg_one, sub_eq_add_neg] using
      principalFiveTermWindow_index_fiber_transport d hd s (-1) x hx
  have hback : ∀ y ∈ B, ∃ x ∈ A, R x = R y := by
    intro y hy
    simpa only [A, B, R, mul_one, sub_add_cancel] using
      principalFiveTermWindow_index_fiber_transport d hd
        (s - principalFiveTermUpperIndexBound d) 1 y hy
  have himage : A.image R = B.image R := by
    ext r
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hR⟩ := hforward x hx
      exact ⟨y, hy, hR⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hR⟩ := hback y hy
      exact ⟨x, hx, hR⟩
  change (∑ x ∈ A, f (R x)) = ∑ x ∈ B, f (R x)
  calc
    _ = ∑ r ∈ A.image R, f r := (Finset.sum_image (by
      intro x hx y hy hxy
      exact principalFiveTermCharacteristicResidue_injOn d hd s
        (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy)).symm
    _ = ∑ r ∈ B.image R, f r := by rw [himage]
    _ = _ := Finset.sum_image (by
      intro x hx y hy hxy
      exact principalFiveTermCharacteristicResidue_injOn d hd
        (s - principalFiveTermUpperIndexBound d)
        (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy)

/-! ### Positive representatives and the removable-origin sum

Choose `v` in the window `1 ≤ S_d(v) ≤ H` and `u` in `0 ≤ S_d(u) < H`. For a zero left
class use the literal origin. When the sum of the classes is zero, take
`u=(a-1,b)-v`; the integral pair `(a-1,b)` has residue zero, index `H`, and argument
`-aρ_d-b`, so the shifted closed form has its removable numerator at zero.
-/

/-- The source pair `(a-1,b)` has lattice index `H`; used by
`exists_principalFiveTerm_positive_representatives`. -/
private theorem principalFiveTermLatticeIndex_source_sum (d : ℕ) :
    principalFiveTermLatticeIndex d ((principalA d) 0 0 - 1) ((principalA d) 0 1) =
      principalFiveTermUpperIndexBound d := by
  simp [principalFiveTermLatticeIndex, principalFiveTermUpperIndexBound, coe_principalA]
  ring

/-- The source pair `(a-1,b)` has zero residue; used by
`exists_principalFiveTerm_positive_representatives`. -/
private theorem characteristicResidue_source_sum_eq_zero (d : ℕ) (hd : 3 < d) :
    principalFiveTermCharacteristicResidue d ((principalA d) 0 0 - 1)
      ((principalA d) 0 1) = 0 := by
  apply (principalFiveTermCharacteristicResidue_eq_zero_iff d hd _ _).2
  constructor
  · refine ⟨(d : ℤ) * ((d : ℤ) - 2), ?_⟩
    simp [principalFiveTermUpperIndexBound, coe_principalA]
    ring
  · refine ⟨((d : ℤ) - 1) * ((d : ℤ) ^ 2 - 2 * d - 1), ?_⟩
    simp [principalFiveTermUpperIndexBound, coe_principalA]
    ring

/-- Subtracting a source pair from `(a-1,b)` negates its residue and complements its index
within `H`; used by `exists_principalFiveTerm_positive_representatives`. -/
private theorem principalFiveTerm_source_sum_sub (d : ℕ) (hd : 3 < d) (v₁ v₂ : ℤ) :
    principalFiveTermCharacteristicResidue d ((principalA d) 0 0 - 1 - v₁)
        ((principalA d) 0 1 - v₂) = -principalFiveTermCharacteristicResidue d v₁ v₂ ∧
      principalFiveTermLatticeIndex d ((principalA d) 0 0 - 1 - v₁)
        ((principalA d) 0 1 - v₂) = principalFiveTermUpperIndexBound d -
          principalFiveTermLatticeIndex d v₁ v₂ := by
  constructor
  · rw [principalFiveTermCharacteristicResidue_sub,
      characteristicResidue_source_sum_eq_zero d hd, zero_sub]
  · have hsub : principalFiveTermLatticeIndex d ((principalA d) 0 0 - 1 - v₁)
        ((principalA d) 0 1 - v₂) =
          principalFiveTermLatticeIndex d ((principalA d) 0 0 - 1) ((principalA d) 0 1) -
            principalFiveTermLatticeIndex d v₁ v₂ := by
      simp only [principalFiveTermLatticeIndex]
      ring
    simpa only [principalFiveTermLatticeIndex_source_sum] using hsub

/-- Positive representatives for the deformed-contour argument of
[RW26, Radchenko, Wheeler (2026), Section 3.2, proof of Theorem 2, `thm:fg.equs`].
They satisfy `0 ≤ S_d(u) < H`, `1 ≤ S_d(v) ≤ H`; a zero left class is represented by
`(0,0)`, and a zero sum of classes by the source sum `(a-1,b)`. -/
theorem exists_principalFiveTerm_positive_representatives
    (d : ℕ) (hd : 3 < d)
    {u v : Fin 2 → ZMod (principalDilogOrder d)}
    (hu : u ∈ principalDilogGroup d) (hv : v ∈ principalDilogGroup d) (hv0 : v ≠ 0) :
    ∃ u₁ u₂ v₁ v₂ : ℤ,
      principalFiveTermCharacteristicResidue d u₁ u₂ = u ∧
      principalFiveTermCharacteristicResidue d v₁ v₂ = v ∧
      (0 ≤ principalFiveTermLatticeIndex d u₁ u₂ ∧
        principalFiveTermLatticeIndex d u₁ u₂ < principalFiveTermUpperIndexBound d) ∧
      (1 ≤ principalFiveTermLatticeIndex d v₁ v₂ ∧
        principalFiveTermLatticeIndex d v₁ v₂ ≤ principalFiveTermUpperIndexBound d) ∧
      (u = 0 → u₁ = 0 ∧ u₂ = 0) ∧
      (u + v = 0 → u₁ + v₁ = (principalA d) 0 0 - 1 ∧
        u₂ + v₂ = (principalA d) 0 1) := by
  obtain ⟨⟨v₁, v₂⟩, hvWindow, hvRes⟩ :=
    exists_mem_principalFiveTermWindow_residue_eq d hd 1 hv
  obtain ⟨_, _, hvLo, hvHi⟩ :=
    (mem_principalFiveTermWindow d hd 1 (v₁, v₂)).1 hvWindow
  simp only at hvLo hvHi
  have hH := principalFiveTermUpperIndexBound_pos d hd
  have hvBound : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂ ∧
      principalFiveTermLatticeIndex d v₁ v₂ ≤ principalFiveTermUpperIndexBound d := by
    omega
  by_cases hu0 : u = 0
  · refine ⟨0, 0, v₁, v₂, ?_, hvRes, ?_, hvBound, ?_, ?_⟩
    · simpa [hu0] using
        (principalFiveTermCharacteristicResidue_eq_zero_iff d hd 0 0).2 (by simp)
    · simp only [principalFiveTermLatticeIndex, zero_add, mul_zero]
      exact ⟨le_refl 0, hH⟩
    · exact fun _ => ⟨rfl, rfl⟩
    · intro huv0
      exact (hv0 (by simpa [hu0] using huv0)).elim
  · by_cases huv0 : u + v = 0
    · let a : ℤ := (principalA d) 0 0 - 1
      let b : ℤ := (principalA d) 0 1
      obtain ⟨hResComp, hIndex⟩ := principalFiveTerm_source_sum_sub d hd v₁ v₂
      refine ⟨a - v₁, b - v₂, v₁, v₂, ?_, hvRes, ?_, hvBound, ?_, ?_⟩
      · rw [hResComp, hvRes]
        simpa only [zero_sub] using (eq_neg_of_add_eq_zero_left huv0).symm
      · rw [hIndex]
        constructor <;> omega
      · exact fun h => (hu0 h).elim
      · intro _
        dsimp [a, b]
        constructor <;> omega
    · obtain ⟨⟨u₁, u₂⟩, huWindow, huRes⟩ :=
        exists_mem_principalFiveTermWindow_residue_eq d hd 0 hu
      obtain ⟨_, _, huLo, huHi⟩ :=
        (mem_principalFiveTermWindow d hd 0 (u₁, u₂)).1 huWindow
      simp only at huLo huHi
      refine ⟨u₁, u₂, v₁, v₂, huRes, hvRes, ?_, hvBound, ?_, ?_⟩
      · constructor <;> omega
      · exact fun h => (hu0 h).elim
      · exact fun h => (huv0 h).elim

end SIC

end
