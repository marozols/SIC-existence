/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Pentagon

/-!
# Convolution on the principal torsion subgroup

Averaging the pentagon relation over characters of `G_d/H` gives the scalar convolution
identity of Theorem 7 on the `d`-torsion, with the conjugate unit character.

This module follows [RW26, Radchenko, Wheeler (2026), proof of Theorem 7, `thm:ghostsic`,
with equation (40), `eq:sicmaintrick`] at `γ = A_d`, `M = d`, `N = d²(d - 3)`.
The values are `E = F⁺` and `F⁻` on `G_d`. Its input is `principalDilogPentagon` in
`SICs.Principal.Dilogarithm.Pentagon`.

## The argument

**From (36) to Theorem 7.** Fix `v = d(d - 3)p ∈ H`, `v ≠ 0`, and `w ∈ G_d`. Averaging over
the `d - 3` characters `⟨w + jg; ·⟩` of the coset `w + ⟨g⟩` projects the sum over `G_d` onto
`H`, the kernel of `⟨g; ·⟩` (`sum_sum_mul_principalDilogBicharacter_pow`):
`(1/d) ∑_{u ∈ H} E(u)⟨u⟩E(v - u)⟨w; u⟩
  = (1/(d(d - 3))) ∑_{j < d-3} ∑_{x ∈ G_d} E(x)⟨x⟩E(v - x)⟨x; w + jg⟩`.
Each inner sum is (36) at `(w + jg, v)`, whose delta term vanishes since `v ≠ 0`:
`√N ⟨v + w + jg⟩ E(-(v + w + jg)) E(w + jg) E(v)`. Under the claim `E(w + jg) = E(v + w + jg)`
and `v + w + jg ≠ 0`, the reflection law (ii) reduces each term to `√N E(v)`, and
`√N (d - 3)/(d(d - 3)) = √(d - 3)` (`sqrt_principalDilogOrder`). This is equation (40) and the
end of the proof of Theorem 7, formalized as
`principalDilogTorsionConvolution_of_E_eq`; for
`v = 0` the identity is the direct count `(1/d)(E(0)² + d² - 1) = √(d - 3) E(0) + d`
(`principalDilogTorsionConvolution_zero`).

**The conjugate character.** Radchenko and Wheeler take `w = v/(ε - 1)`, which satisfies the
claim through (38) at `ε` and has character `e_M(i(-r) + j(r - s))` on `H`. The conjugate vector
`w' = v/(ε⁻¹ - 1)` satisfies the same claim through (38) at `ε⁻¹`, and its character
`ω_d^{-(p₁q₁ + p₂q₂ + p₁q₂)}` is the one the finite Twisted Convolution sum produces:
`principalDilogConvolutionConj`, which `SICs.Principal.Dilogarithm.TwistedConvolution` consumes.
It is the same theorem of [RW26, Radchenko, Wheeler (2026)] read with the root `ε⁻¹` of
`x² - (M - 1)x + 1` in place of `ε`.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The convolution identity on `H`

Averaging (36) over the characters of `G_d/H`: equation (40) and the end of the proof of
Theorem 7, for an arbitrary `w ∈ G_d` satisfying the claim. -/

/-- **The convolution sum over `H`** of the proof of [RW26, Radchenko, Wheeler (2026), Theorem 7,
`thm:ghostsic`]: `(1/M) ∑_{u ∈ H} F_γ(u)⟨u⟩F_γ(v - u)⟨w; u⟩` for `v = d(d - 3)p ∈ H` and
`w ∈ G_d`, the sum indexed by `(ℤ/dℤ)²` through `principalDilogTorsionMod`. -/
def principalDilogTorsionConvolution (d : ℕ) [NeZero d] (p : IntPhaseSpace)
    (w : Fin 2 → ZMod (principalDilogOrder d)) : ℂ :=
  (1 / (d : ℂ)) * ∑ c : PhaseSpaceMod d,
    principalDilogE d (principalDilogTorsionMod d c) *
      principalDilogGaussian d (principalDilogTorsionMod d c) *
      principalDilogE d (principalDilogTorsion d p - principalDilogTorsionMod d c) *
      principalDilogBicharacter d w (principalDilogTorsionMod d c)

/-- A character shifted by `j g` is the product of its two characters. -/
private lemma principalDilogTorsionConvolution_character (d : ℕ) (hd : 3 < d)
    {w x : Fin 2 → ZMod (principalDilogOrder d)}
    (hw : w ∈ principalDilogGroup d) (hx : x ∈ principalDilogGroup d) (j : ℕ) :
    principalDilogBicharacter d w x *
        principalDilogBicharacter d (principalDilogGenerator d) x ^ j =
      principalDilogBicharacter d x (w + j • principalDilogGenerator d) := by
  have : NeZero (principalDilogOrder d) := principalDilogOrder_neZero d hd
  have hg := principalDilogGenerator_mem d hd
  calc
    _ = principalDilogBicharacter d w x *
          principalDilogBicharacter d (j • principalDilogGenerator d) x := by
            exact congrArg (fun z => principalDilogBicharacter d w x * z)
              (fixedBicharacter_nsmul_left (principalA d) (principalDilogOrder d)
                hg hx j).symm
    _ = principalDilogBicharacter d (w + j • principalDilogGenerator d) x := by
      exact (fixedBicharacter_add_left (principalA d) (principalDilogOrder d)
        hw (AddSubgroup.nsmul_mem _ hg j) hx).symm
    _ = _ := fixedBicharacter_comm (principalA d) (principalDilogOrder d) _ _

/-- Reflection turns the product in the pentagon value into one. -/
private lemma principalDilogTorsionConvolution_reflection (d : ℕ) (hd : 3 < d)
    {u y : Fin 2 → ZMod (principalDilogOrder d)}
    (hy : y ∈ principalDilogGroup d) (hy0 : y ≠ 0)
    (hE : principalDilogE d u = principalDilogE d y) :
    principalDilogGaussian d y * principalDilogE d (-y) * principalDilogE d u = 1 := by
  rw [hE]
  convert principalDilogE_mul_gaussian_mul_E_neg
    d hd hy hy0 using 1
  ring

/-- Multiplying by the generator character shifts the pentagon parameter. -/
private lemma sum_mul_bicharacter_generator_pow
    (d : ℕ) (hd : 3 < d) [NeZero (principalDilogOrder d)]
    {v w : Fin 2 → ZMod (principalDilogOrder d)} (hw : w ∈ principalDilogGroup d)
    (j : ℕ) :
    (∑ x : principalDilogGroup d,
      (principalDilogE d x * principalDilogGaussian d x * principalDilogE d (v - x) *
        principalDilogBicharacter d w x) *
        principalDilogBicharacter d (principalDilogGenerator d) x ^ j) =
      ∑ x : principalDilogGroup d,
        principalDilogE d x * principalDilogGaussian d x * principalDilogE d (v - x) *
          principalDilogBicharacter d x (w + j • principalDilogGenerator d) := by
  apply Finset.sum_congr rfl
  intro x _
  rw [← principalDilogTorsionConvolution_character d hd hw x.property j]
  ring

/-- The pentagon relation evaluates each normalized character sum. -/
private lemma principalDilogTorsionConvolution_normalized_sum (d : ℕ) (hd : 3 < d)
    [NeZero (principalDilogOrder d)] (p : IntPhaseSpace)
    (hp : intPhaseSpaceMod d p ≠ 0)
    {w : Fin 2 → ZMod (principalDilogOrder d)} (hw : w ∈ principalDilogGroup d)
    (hinv : ∀ j : ℕ, principalDilogE d (w + j • principalDilogGenerator d) =
      principalDilogE d (principalDilogTorsion d p + w + j • principalDilogGenerator d))
    (hne : ∀ j : ℕ, principalDilogTorsion d p + w + j • principalDilogGenerator d ≠ 0)
    (j : ℕ) :
    (1 / (Real.sqrt (principalDilogOrder d) : ℂ)) *
      ∑ x : principalDilogGroup d,
        principalDilogE d x * principalDilogGaussian d x *
          principalDilogE d (principalDilogTorsion d p - x) *
          principalDilogBicharacter d x (w + j • principalDilogGenerator d) =
      principalDilogE d (principalDilogTorsion d p) := by
  let v := principalDilogTorsion d p
  let u := w + j • principalDilogGenerator d
  have hv : v ∈ principalDilogGroup d := principalDilogTorsion_mem d hd p
  have hu : u ∈ principalDilogGroup d :=
    AddSubgroup.add_mem _ hw (AddSubgroup.nsmul_mem _ (principalDilogGenerator_mem d hd) j)
  have hv0 : v ≠ 0 := (principalDilogTorsion_eq_zero_iff d hd p).not.mpr hp
  have h := principalDilogPentagon d hd hu hv
  have harg : u + v = v + w + j • principalDilogGenerator d := by dsimp [u, v]; abel
  have hneg : -u - v = -(v + w + j • principalDilogGenerator d) := by dsimp [u, v]; abel
  rw [harg, hneg] at h
  have hprod : principalDilogGaussian d (v + w + j • principalDilogGenerator d) *
      principalDilogE d (-(v + w + j • principalDilogGenerator d)) *
      principalDilogE d u = 1 := by
    exact principalDilogTorsionConvolution_reflection d hd
      (by simpa only [u, add_assoc] using AddSubgroup.add_mem _ hv hu) (hne j) (hinv j)
  simp only [hv0, ↓reduceIte, mul_zero, sub_zero, hprod, one_mul] at h
  exact h

/-- Every character sum in equation (40) has the same value under the claim. -/
private lemma principalDilogTorsionConvolution_character_sum (d : ℕ) (hd : 3 < d)
    [NeZero (principalDilogOrder d)] (p : IntPhaseSpace)
    (hp : intPhaseSpaceMod d p ≠ 0)
    {w : Fin 2 → ZMod (principalDilogOrder d)} (hw : w ∈ principalDilogGroup d)
    (hinv : ∀ j : ℕ, principalDilogE d (w + j • principalDilogGenerator d) =
      principalDilogE d (principalDilogTorsion d p + w + j • principalDilogGenerator d))
    (hne : ∀ j : ℕ, principalDilogTorsion d p + w + j • principalDilogGenerator d ≠ 0)
    (j : ℕ) :
    (∑ x : principalDilogGroup d,
      (principalDilogE d x * principalDilogGaussian d x *
        principalDilogE d (principalDilogTorsion d p - x) *
        principalDilogBicharacter d w x) *
        principalDilogBicharacter d (principalDilogGenerator d) x ^ j) =
      (Real.sqrt (principalDilogOrder d) : ℂ) *
        principalDilogE d (principalDilogTorsion d p) := by
  rw [sum_mul_bicharacter_generator_pow d hd hw j]
  have hs : (Real.sqrt (principalDilogOrder d) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.2 (by exact_mod_cast principalDilogOrder_pos d hd))
  calc
    _ = (Real.sqrt (principalDilogOrder d) : ℂ) *
        ((1 / (Real.sqrt (principalDilogOrder d) : ℂ)) *
          ∑ x : principalDilogGroup d,
            principalDilogE d x * principalDilogGaussian d x *
              principalDilogE d (principalDilogTorsion d p - x) *
                principalDilogBicharacter d x
                  (w + j • principalDilogGenerator d)) := by
                field_simp
    _ = _ := by rw [principalDilogTorsionConvolution_normalized_sum
      d hd p hp hw hinv hne j]

/-- Averaging the equal character sums projects onto the torsion subgroup. -/
private lemma principalDilogTorsionConvolution_average (d : RankOneDimension) (p : IntPhaseSpace)
    (hp : intPhaseSpaceMod d p ≠ 0)
    {w : Fin 2 → ZMod (principalDilogOrder d)} (hw : w ∈ principalDilogGroup d)
    (hinv : ∀ j : ℕ, principalDilogE d (w + j • principalDilogGenerator d) =
      principalDilogE d (principalDilogTorsion d p + w + j • principalDilogGenerator d))
    (hne : ∀ j : ℕ, principalDilogTorsion d p + w + j • principalDilogGenerator d ≠ 0) :
    (∑ c : PhaseSpaceMod d,
      principalDilogE d (principalDilogTorsionMod d c) *
        principalDilogGaussian d (principalDilogTorsionMod d c) *
        principalDilogE d (principalDilogTorsion d p - principalDilogTorsionMod d c) *
        principalDilogBicharacter d w (principalDilogTorsionMod d c)) =
      (Real.sqrt (principalDilogOrder d) : ℂ) *
        principalDilogE d (principalDilogTorsion d p) := by
  have : NeZero (principalDilogOrder d) := principalDilogOrder_neZero d d.property
  let f : (Fin 2 → ZMod (principalDilogOrder d)) → ℂ := fun x =>
    principalDilogE d x * principalDilogGaussian d x *
      principalDilogE d (principalDilogTorsion d p - x) * principalDilogBicharacter d w x
  have havg := sum_sum_mul_principalDilogBicharacter_pow d f
  have hsumj : (∑ j ∈ Finset.range (d - 3), ∑ x : principalDilogGroup d,
      f x * principalDilogBicharacter d (principalDilogGenerator d) x ^ j) =
      (d - 3 : ℕ) * ((Real.sqrt (principalDilogOrder d) : ℂ) *
        principalDilogE d (principalDilogTorsion d p)) := by
    calc
      _ = ∑ j ∈ Finset.range (d - 3),
          (Real.sqrt (principalDilogOrder d) : ℂ) *
            principalDilogE d (principalDilogTorsion d p) := by
            apply Finset.sum_congr rfl
            intro j _
            exact principalDilogTorsionConvolution_character_sum d d.property p hp hw hinv hne j
      _ = _ := by simp
  rw [hsumj] at havg
  have hfactor : ((d - 3 : ℕ) : ℂ) = (d : ℂ) - 3 := by
    exact Nat.cast_sub (R := ℂ) (by omega : 3 ≤ (d : ℕ))
  rw [hfactor] at havg
  have hfactor0 : (d : ℂ) - 3 ≠ 0 := by
    exact_mod_cast (by omega : (d : ℤ) - 3 ≠ 0)
  change (∑ c, f (principalDilogTorsionMod d c)) = _
  exact mul_left_cancel₀ hfactor0 havg.symm

/-- **[RW26, Radchenko, Wheeler (2026), equation (40), `eq:sicmaintrick`, in the proof of
Theorem 7, `thm:ghostsic`] and its conclusion**: for `v = d(d - 3)p ≠ 0` and `w ∈ G_d` with
`F_γ(w + jg) = F_γ(v + w + jg)` and `v + w + jg ≠ 0` for all `j`,
`(1/M) ∑_{u ∈ H} F_γ(u)⟨u⟩F_γ(v - u)⟨w; u⟩ = √(M - 3) F_γ(v)`. The sum over `H` is `1/(M - 3)`
of the sum over `j < M - 3` of the sums over `G` against `⟨w + jg; ·⟩`, each of which (36)
evaluates to `√N F_γ(v) F_γ(w + jg) ⟨v + w + jg⟩ F_γ(-(v + w + jg))`; the claim and the
reflection law (ii) reduce every term to `√N F_γ(v)`. The last line of display (40) is
`principalDilogTorsionConvolution_character_sum`; this theorem evaluates it under the claim. -/
@[source "RW26, equation (40), p. 21, eq:sicmaintrick (γ = A_d)"]
theorem principalDilogTorsionConvolution_of_E_eq (d : RankOneDimension)
    (p : IntPhaseSpace) (hp : intPhaseSpaceMod d p ≠ 0)
    {w : Fin 2 → ZMod (principalDilogOrder d)} (hw : w ∈ principalDilogGroup d)
    (hinv : ∀ j : ℕ, principalDilogE d (w + j • principalDilogGenerator d) =
      principalDilogE d (principalDilogTorsion d p + w + j • principalDilogGenerator d))
    (hne : ∀ j : ℕ, principalDilogTorsion d p + w + j • principalDilogGenerator d ≠ 0) :
    principalDilogTorsionConvolution d p w =
      (Real.sqrt ((d : ℝ) - 3) : ℂ) * principalDilogE d (principalDilogTorsion d p) := by
  have : NeZero (principalDilogOrder d) := principalDilogOrder_neZero d d.property
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne (d : ℕ))
  have hsqrt : (Real.sqrt (principalDilogOrder d) : ℂ) =
      (d : ℂ) * (Real.sqrt ((d : ℝ) - 3) : ℂ) :=
    ofReal_sqrt_principalDilogOrder d d.property
  unfold principalDilogTorsionConvolution
  rw [principalDilogTorsionConvolution_average d p hp hw hinv hne, hsqrt]
  field_simp

/-- The torsion summand at zero is `E(0)²`, and every other summand is one. -/
private lemma principalDilogTorsionConvolution_zero_term (d : RankOneDimension)
    {w : Fin 2 → ZMod (principalDilogOrder d)}
    (hw : ∀ c : PhaseSpaceMod d,
      principalDilogBicharacter d w (principalDilogTorsionMod d c) = 1)
    (c : PhaseSpaceMod d) :
    principalDilogE d (principalDilogTorsionMod d c) *
      principalDilogGaussian d (principalDilogTorsionMod d c) *
      principalDilogE d (-principalDilogTorsionMod d c) *
      principalDilogBicharacter d w (principalDilogTorsionMod d c) =
        if c = 0 then principalDilogE d 0 ^ 2 else 1 := by
  by_cases hc : c = 0
  · subst c
    have hG : principalDilogGaussian d 0 = 1 :=
      fixedGaussian_zero (principalA d) (principalDilogOrder d)
    have hB : principalDilogBicharacter d w 0 = 1 := by
      change fixedBicharacter (principalA d) (principalDilogOrder d) w 0 = 1
      rw [fixedBicharacter_comm]
      exact fixedBicharacter_zero_left (principalA d) (principalDilogOrder d) w
    simp only [principalDilogTorsionMod_zero, neg_zero, hG, hB, mul_one, ite_true]
    ring
  · have htor : principalDilogTorsionMod d c ≠ 0 := by
      intro h
      apply hc
      exact principalDilogTorsionMod_injective d
        (h.trans (principalDilogTorsionMod_zero d).symm)
    simp only [hc, ↓reduceIte, hw c, mul_one]
    exact principalDilogE_mul_gaussian_mul_E_neg
      d d.property (principalDilogTorsionMod_mem d c) htor

/-- The zero torsion convolution sum has one exceptional term among `d²` terms. -/
private lemma principalDilogTorsionConvolution_zero_sum (d : RankOneDimension)
    {w : Fin 2 → ZMod (principalDilogOrder d)}
    (hw : ∀ c : PhaseSpaceMod d,
      principalDilogBicharacter d w (principalDilogTorsionMod d c) = 1) :
    (∑ c : PhaseSpaceMod d,
      principalDilogE d (principalDilogTorsionMod d c) *
        principalDilogGaussian d (principalDilogTorsionMod d c) *
        principalDilogE d (-principalDilogTorsionMod d c) *
        principalDilogBicharacter d w (principalDilogTorsionMod d c)) =
      principalDilogE d 0 ^ 2 + (d : ℂ) ^ 2 - 1 := by
  let f : PhaseSpaceMod d → ℂ := fun c =>
    principalDilogE d (principalDilogTorsionMod d c) *
      principalDilogGaussian d (principalDilogTorsionMod d c) *
      principalDilogE d (-principalDilogTorsionMod d c) *
      principalDilogBicharacter d w (principalDilogTorsionMod d c)
  have hcard : Fintype.card (PhaseSpaceMod d) = d ^ 2 := by simp [PhaseSpaceMod]
  have hrest : ∑ c ∈ (Finset.univ : Finset (PhaseSpaceMod d)).erase 0, f c =
      (d : ℂ) ^ 2 - 1 := by
    calc
      _ = ∑ c ∈ (Finset.univ : Finset (PhaseSpaceMod d)).erase 0, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro c hc
        simpa [f, Finset.ne_of_mem_erase hc] using
          principalDilogTorsionConvolution_zero_term d hw c
      _ = ((Finset.univ : Finset (PhaseSpaceMod d)).erase 0).card := by simp
      _ = (d : ℂ) ^ 2 - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard]
        rw [Nat.cast_sub (R := ℂ) (by nlinarith [d.property] : 1 ≤ (d : ℕ) ^ 2)]
        push_cast
        ring
  change (∑ c, f c) = _
  rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ (0 : PhaseSpaceMod d)), hrest]
  have hterm : f 0 = principalDilogE d 0 ^ 2 := by
    simpa [f] using principalDilogTorsionConvolution_zero_term d hw 0
  rw [hterm]
  ring

/-- **The case `v = 0` of Theorem 7**, "trivial" in [RW26, Radchenko, Wheeler (2026), proof of
Theorem 7, `thm:ghostsic`]: for `p ≡ 0 (mod d)` and `w` pairing trivially with `H`,
`(1/M) ∑_{u ∈ H} F_γ(u)⟨u⟩F_γ(-u) = (1/M)(F_γ(0)² + M² - 1) = √(M - 3) F_γ(0) + M`, by (ii) off
`u = 0` and `F_γ(0)² = √N F_γ(0) + 1`. -/
theorem principalDilogTorsionConvolution_zero (d : RankOneDimension)
    (p : IntPhaseSpace) (hp : intPhaseSpaceMod d p = 0)
    {w : Fin 2 → ZMod (principalDilogOrder d)}
    (hw : ∀ c : PhaseSpaceMod d, principalDilogBicharacter d w (principalDilogTorsionMod d c) = 1) :
    principalDilogTorsionConvolution d p w =
      (Real.sqrt ((d : ℝ) - 3) : ℂ) * principalDilogE d (principalDilogTorsion d p) + d := by
  have hv0 : principalDilogTorsion d p = 0 :=
    (principalDilogTorsion_eq_zero_iff d d.property p).2 hp
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne (d : ℕ))
  have hsqrt : (Real.sqrt (principalDilogOrder d) : ℂ) =
      (d : ℂ) * (Real.sqrt ((d : ℝ) - 3) : ℂ) :=
    ofReal_sqrt_principalDilogOrder d d.property
  unfold principalDilogTorsionConvolution
  rw [hv0]
  simp only [zero_sub]
  rw [principalDilogTorsionConvolution_zero_sum d hw]
  rw [principalDilogE_zero_sq d d.property, hsqrt]
  field_simp
  ring

/-! ### The scalar identity of Theorem 7

Radchenko and Wheeler's identity in the coordinates `u = q/d`, `v = p/d`, with the character of
the conjugate vector, which the Twisted Convolution sum produces. -/

/-- A lattice vector divisible by `d` pairs trivially with the `d`-torsion. -/
private lemma principalDilogOfLattice_pairing_zero (d : RankOneDimension)
    (k : IntPhaseSpace) (hk : (d : ℤ) ∣ k 0 ∧ (d : ℤ) ∣ k 1)
    (c : PhaseSpaceMod d) :
    principalDilogBicharacter d (principalDilogOfLattice d k)
      (principalDilogTorsionMod d c) = 1 := by
  let q := (canonicalPhaseSpaceTransversal d).repr c
  change principalDilogBicharacter d (principalDilogOfLattice d k)
    (principalDilogTorsion d q) = 1
  rw [principalDilogBicharacter_ofLattice_torsion d k q]
  rcases hk with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  have hdiv : (d : ℤ) ∣ intSymplecticForm q k - 0 := by
    refine ⟨q 1 * a - q 0 * b, ?_⟩
    simp only [intSymplecticForm, sub_zero]
    rw [ha, hb]
    ring
  have hroot := standardRoot_zpow_eq_of_dvd_sub (d := d) hdiv
  simpa using hroot

/-- The zero/nonzero split for a lattice character of Theorem 7; used by
`principalDilogConvolutionConj`. -/
private lemma principalDilogConvolution_of_lattice (d : RankOneDimension)
    (p k : IntPhaseSpace)
    (hk : intPhaseSpaceMod d p = 0 → (d : ℤ) ∣ k 0 ∧ (d : ℤ) ∣ k 1)
    (hinv : ∀ j : ℕ,
      principalDilogE d (principalDilogOfLattice d k + j • principalDilogGenerator d) =
        principalDilogE d (principalDilogTorsion d p + principalDilogOfLattice d k +
          j • principalDilogGenerator d))
    (hne : intPhaseSpaceMod d p ≠ 0 → ∀ j : ℕ,
      principalDilogTorsion d p + principalDilogOfLattice d k +
        j • principalDilogGenerator d ≠ 0) :
    principalDilogTorsionConvolution d p (principalDilogOfLattice d k) =
      (Real.sqrt ((d : ℝ) - 3) : ℂ) *
        principalDilogValue d (shiftRationalPoint d p) +
        if intPhaseSpaceMod d p = 0 then (d : ℂ) else 0 := by
  by_cases hp : intPhaseSpaceMod d p = 0
  · have hw : ∀ c : PhaseSpaceMod d,
        principalDilogBicharacter d (principalDilogOfLattice d k)
          (principalDilogTorsionMod d c) = 1 :=
      principalDilogOfLattice_pairing_zero d k (hk hp)
    rw [principalDilogTorsionConvolution_zero d p hp hw,
      principalDilogE_principalDilogTorsion d d.property p]
    simp [hp]
  · rw [principalDilogTorsionConvolution_of_E_eq d p hp
      (principalDilogOfLattice_mem d d.property k) hinv (hne hp),
      principalDilogE_principalDilogTorsion d d.property p]
    simp [hp]

/-- The convolution sum over `H` in the coordinates `u = q/d`, `v = p/d`, `w = -adj(A_d - I)k`:
`E(u) = F(q/d)` (`principalDilogE_principalDilogTorsion`), `⟨u⟩ = χ_{q/d}(A_d)`
(`principalDilogGaussian_principalDilogTorsion`), `E(v - u) = F((p - q)/d)`
(`principalDilogTorsion_sub`), and `⟨w; u⟩ = ω_d^{⟨q, k⟩}`
(`principalDilogBicharacter_ofLattice_torsion`), summed over the
canonical representatives `q` of `(ℤ/dℤ)²`. -/
theorem principalDilogTorsionConvolution_ofLattice (d : RankOneDimension)
    (p k : IntPhaseSpace) :
    principalDilogTorsionConvolution d p (principalDilogOfLattice d k) =
      (1 / (d : ℂ)) * ∑ c : PhaseSpaceMod d,
        principalDilogValue d (shiftRationalPoint d ((canonicalPhaseSpaceTransversal d).repr c)) *
          principalDilogValue d
            (shiftRationalPoint d (p - (canonicalPhaseSpaceTransversal d).repr c)) *
          thetaCharacter (shiftRationalPoint d ((canonicalPhaseSpaceTransversal d).repr c))
            (principalA d : Mat(2, ℤ)) *
          standardRoot d ^ intSymplecticForm ((canonicalPhaseSpaceTransversal d).repr c) k := by
  unfold principalDilogTorsionConvolution
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  let q := (canonicalPhaseSpaceTransversal d).repr c
  change principalDilogE d (principalDilogTorsion d q) *
      principalDilogGaussian d (principalDilogTorsion d q) *
      principalDilogE d (principalDilogTorsion d p - principalDilogTorsion d q) *
      principalDilogBicharacter d (principalDilogOfLattice d k)
        (principalDilogTorsion d q) = _
  rw [← principalDilogTorsion_sub d p q,
    principalDilogE_principalDilogTorsion d d.property q,
    principalDilogE_principalDilogTorsion d d.property (p - q),
    principalDilogGaussian_principalDilogTorsion d d.property q,
    principalDilogBicharacter_ofLattice_torsion d k q]
  ring

/-- **The scalar identity of Theorem 7 at the conjugate unit**: the scalar identity of Theorem 7
with the character `ω_d^{-(p₁q₁ + p₂q₂ + p₁q₂)}` of the conjugate vector `w' = v/(ε⁻¹ - 1)` in
place of `e_M(i(-r) + j(r - s))`, the character of `w = v/(ε - 1)`. It is
Radchenko and Wheeler's argument for [RW26, Radchenko, Wheeler (2026), Theorem 7, `thm:ghostsic`]
run with `ε⁻¹` in place of `ε`, and its character is the one the finite Twisted Convolution sum
produces (`SICs.Principal.Dilogarithm.TwistedConvolution`). Proved from
`principalDilogTorsionConvolution_of_E_eq` at
`w = principalDilogDualVectorConj d p` for `v ≠ 0`
and from `principalDilogTorsionConvolution_zero` for `v = 0`. -/
theorem principalDilogConvolutionConj (d : RankOneDimension) (p : IntPhaseSpace) :
    (1 / (d : ℂ)) * ∑ c : PhaseSpaceMod d,
        principalDilogValue d (shiftRationalPoint d ((canonicalPhaseSpaceTransversal d).repr c)) *
          principalDilogValue d
            (shiftRationalPoint d (p - (canonicalPhaseSpaceTransversal d).repr c)) *
          thetaCharacter (shiftRationalPoint d ((canonicalPhaseSpaceTransversal d).repr c))
            (principalA d : Mat(2, ℤ)) *
          standardRoot d ^
            (-(p 0 * (canonicalPhaseSpaceTransversal d).repr c 0 +
              p 1 * (canonicalPhaseSpaceTransversal d).repr c 1 +
              p 0 * (canonicalPhaseSpaceTransversal d).repr c 1)) =
      (Real.sqrt ((d : ℝ) - 3) : ℂ) * principalDilogValue d (shiftRationalPoint d p) +
        if intPhaseSpaceMod d p = 0 then (d : ℂ) else 0 := by
  let k : IntPhaseSpace := ![-(p 0 + p 1), p 0]
  have hk : intPhaseSpaceMod d p = 0 → (d : ℤ) ∣ k 0 ∧ (d : ℤ) ∣ k 1 := by
    intro hp
    obtain ⟨h₀, h₁⟩ := (intPhaseSpaceMod_eq_zero_iff_dvd d p).mp hp
    simpa [k] using (And.intro (dvd_neg.mpr (dvd_add h₀ h₁)) h₀)
  have hinv : ∀ j : ℕ,
      principalDilogE d (principalDilogOfLattice d k + j • principalDilogGenerator d) =
        principalDilogE d (principalDilogTorsion d p + principalDilogOfLattice d k +
          j • principalDilogGenerator d) :=
    fun j => principalDilogE_dualVectorConj_add_nsmul d d.property p j
  have hne : intPhaseSpaceMod d p ≠ 0 → ∀ j : ℕ,
      principalDilogTorsion d p + principalDilogOfLattice d k +
        j • principalDilogGenerator d ≠ 0 :=
    fun hp j => principalDilogTorsion_add_dualVectorConj_add_nsmul_ne_zero
      d d.property p hp j
  calc
    _ = principalDilogTorsionConvolution d p (principalDilogOfLattice d k) := by
      rw [principalDilogTorsionConvolution_ofLattice d p k]
      congr 1
      apply Finset.sum_congr rfl
      intro c _
      congr 1
      simp only [k, intSymplecticForm, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      ring_nf
    _ = _ := principalDilogConvolution_of_lattice d p k hk hinv hne

end SIC

end
