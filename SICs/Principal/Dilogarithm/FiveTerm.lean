/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.CrossedStrip
import SICs.Principal.Dilogarithm.Faddeev.FiveTerm.CrossedIdentity

/-!
# The principal finite five-term relation from the residue strip

The finite five-term relation (7) at `A_d` for every pair with nonzero right class, by the
corrected crossed-pole strip.

This module follows [RW26, Radchenko, Wheeler (2026), Section 3.2, the proof of Theorem 2,
`thm:fg.equs`, equation (7), `eq:Fgpm.5term`] at `γ = A_d`, `τ = ρ_d`, `ε = ρ_d³ > 1`,
`H = d(d-3)`, `N = d²(d-3)`.

## The argument

For source pairs `u`, `v`, take `ℓ = u₁ + 1`, `p = v₁`, `w = z_u`, `y = z_v`. The residue strip
of `SICs.Principal.Dilogarithm.Faddeev.FiveTerm.ResidueStrip` relates the integrals of the residue
sum `L` along two lines at distance `(ε-1)/c` to the residues at the window of kernel poles
between them, the telescoping identity of `Telescoping` turns the difference of the two line
integrals into the integral of the difference kernels `J`, and `ShiftedIdentity` evaluates the
latter as `ε^{1/2} E(u+v)/(E(u)E(v))`. The window represents each class of `G_d` once
(`sum_principalFiveTermWindow`), and `ε - 1 = √(Nε)` gives the normalization of equation (7).

For an arbitrary nonzero right class, choose positive source representatives and a line just
right of the kernel pole `β_v`. The corrected strip and shifted identity have the same square
integrals around crossed poles. On a line regular at both boundaries, telescoping identifies
their remaining integrals; subtraction cancels the squares. Irrationality of `β_v` makes the
crossed integer positions constant on a small interval to its right, and `ε-1=√(Nε)` supplies
the normalization, including the continued values at zero left and zero sum classes.
-/

noncomputable section

open Complex MeasureTheory

namespace SIC

/-! ### Regular crossings for the strip

A crossing in a nonempty open interval avoiding countably many lattice-related points serves
both the residue strip and the shifted five-term identity. -/

/-- The four countable families of forbidden real crossings: the lattice on each of the two
shifted lines, the lattice at the shifted parameter, and the residue kernel poles. -/
private def principalFiveTermBadPoint (d : ℕ) (y y' : ℝ)
    (q : FiveTermIndex (principalA d) × (Fin 4 × (ℤ × ℤ))) : ℝ :=
  let s := ((q.1 : ℕ) : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ)
  let z := (q.2.2.1 : ℝ) + (q.2.2.2 : ℝ) * principalRoot d
  if q.2.1 = 0 then s + z else
    if q.2.1 = 1 then s + z - y else
      if q.2.1 = 2 then s + z - y' else
        s + principalFiveTermLatticeArgument d ((q.1 : ℕ) : ℤ) q.2.2.1

/-- A real crossing avoids the period lattices at `y` and `y'` and all residue kernel poles. -/
private def principalFiveTermCrossingAvoids (d : ℕ) (y y' x : ℝ) : Prop :=
  ∀ m : FiveTermIndex (principalA d),
    (∀ n k : ℤ, x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 /
      ((principalA d) 1 0 : ℝ) ≠ (n : ℝ) + (k : ℝ) * principalRoot d) ∧
    (∀ n k : ℤ, x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 /
      ((principalA d) 1 0 : ℝ) + y ≠ (n : ℝ) + (k : ℝ) * principalRoot d) ∧
    (∀ n k : ℤ, x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 /
      ((principalA d) 1 0 : ℝ) + y' ≠ (n : ℝ) + (k : ℝ) * principalRoot d) ∧
    (∀ k : ℤ, x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 /
      ((principalA d) 1 0 : ℝ) ≠
        principalFiveTermLatticeArgument d ((m : ℕ) : ℤ) k)

/-- Avoiding the countable range of `principalFiveTermBadPoint` gives all regularity conditions. -/
private theorem principalFiveTermCrossingAvoids_of_not_mem (d : ℕ) (y y' x : ℝ)
    (hx : x ∉ Set.range (principalFiveTermBadPoint d y y')) :
    principalFiveTermCrossingAvoids d y y' x := by
  intro m
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n k h
    apply hx
    refine ⟨(m, (0, (n, k))), ?_⟩
    dsimp [principalFiveTermBadPoint]
    linarith
  · intro n k h
    apply hx
    refine ⟨(m, (1, (n, k))), ?_⟩
    dsimp [principalFiveTermBadPoint]
    linarith
  · intro n k h
    apply hx
    refine ⟨(m, (2, (n, k))), ?_⟩
    dsimp [principalFiveTermBadPoint]
    linarith
  · intro k h
    apply hx
    refine ⟨(m, (3, (k, 0))), ?_⟩
    dsimp [principalFiveTermBadPoint]
    linarith

/-- Every nonempty open interval contains a crossing avoiding all four forbidden families on
both boundaries of the translated strip. Used by `principalDilogFiveTerm_of_ne_zero_right`. -/
private theorem exists_principalFiveTerm_avoiding_between (d : ℕ) (y y' a b : ℝ)
    (hab : a < b) :
    ∃ x : ℝ, a < x ∧ x < b ∧
      principalFiveTermCrossingAvoids d y y' x ∧
        principalFiveTermCrossingAvoids d y y'
          (x + (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ)) := by
  have hne : (Set.Ioo a b).Nonempty := ⟨(a + b) / 2, by constructor <;> linarith⟩
  let bad := Set.range (principalFiveTermBadPoint d y y')
  let bad' := Set.range (fun q => principalFiveTermBadPoint d y y' q -
    (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ))
  have hcount : (bad ∪ bad').Countable :=
    (Set.countable_range _).union (Set.countable_range _)
  obtain ⟨x, hxBad, hxI⟩ := (hcount.dense_compl ℝ).exists_mem_open isOpen_Ioo hne
  have hxBad₁ : x ∉ bad := fun h => hxBad (Set.mem_union_left _ h)
  have hxBad₂ : x + (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) ∉ bad := by
    intro ⟨q, hq⟩
    apply hxBad (Set.mem_union_right _ _)
    refine ⟨q, ?_⟩
    dsimp [bad']
    linarith
  exact ⟨x, hxI.1, hxI.2,
    principalFiveTermCrossingAvoids_of_not_mem d y y' x hxBad₁,
    principalFiveTermCrossingAvoids_of_not_mem d y y' _ hxBad₂⟩

/-- The four real exclusions give the two regular-crossing predicates used by the integrals. -/
private theorem principalFiveTermCrossingAvoids_regular (d : ℕ) (y y' x : ℝ)
    (havoid : principalFiveTermCrossingAvoids d y y' x) :
    (∀ m : FiveTermIndex (principalA d),
      IsPrincipalFiveTermResidueCrossing d ((m : ℕ) : ℤ) y
        (x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ))) ∧
    (∀ m : FiveTermIndex (principalA d),
      IsRegularPeriodLatticeCrossing (principalRoot d) y'
        (x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ))) := by
  constructor
  · intro m
    obtain ⟨hbase, hshift, _, hpole⟩ := havoid m
    refine ⟨⟨?_, ?_⟩, hpole⟩
    · rintro ⟨n, k, h⟩
      apply hbase n k
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast] using h
    · rintro ⟨n, k, h⟩
      apply hshift n k
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast] using h
  · intro m
    obtain ⟨hbase, _, hshift, _⟩ := havoid m
    refine ⟨?_, ?_⟩
    · rintro ⟨n, k, h⟩
      apply hbase n k
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast] using h
    · rintro ⟨n, k, h⟩
      apply hshift n k
      apply Complex.ofReal_injective
      simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast] using h

/-! ### Rates, telescoping, and normalization

The source parameters satisfy the convergence-rate hypotheses, the telescoping identity
integrates to the difference of two line integrals, and `ε-1=√(Nε)` normalizes the residue
prefactor. -/

/-- The two convergence rates of the residue integral at the source parameters. -/
private theorem principalFiveTerm_source_rates (d : ℕ) (hd : 3 < d)
    (u₁ u₂ v₁ v₂ : ℤ)
    (hu : principalFiveTermLatticeIndex d u₁ u₂ < principalFiveTermUpperIndexBound d)
    (huv : 0 < principalFiveTermLatticeIndex d u₁ u₂ + principalFiveTermLatticeIndex d v₁ v₂) :
    (principalRoot d ^ 3)⁻¹ <
        principalFiveTermUpperRate d (u₁ + 1) (principalFiveTermLatticeArgument d u₁ u₂) ∧
      0 < principalFiveTermUpperRate d (u₁ + 1)
        (principalFiveTermLatticeArgument d u₁ u₂) ∧
      principalFiveTermLowerRate d (u₁ + 1) v₁
        (principalFiveTermLatticeArgument d u₁ u₂)
        (principalFiveTermLatticeArgument d v₁ v₂) < 0 := by
  have hstrong : (principalRoot d ^ 3)⁻¹ <
      principalFiveTermUpperRate d (u₁ + 1) (principalFiveTermLatticeArgument d u₁ u₂) := by
    rw [principalFiveTermUpperRate_latticeArgument d hd]
    have h := (principalFiveTermLatticeRate_lt_one_sub_inv_iff d hd u₁ u₂).mpr hu
    linarith
  refine ⟨hstrong, ?_, ?_⟩
  · have hε : 0 < (principalRoot d ^ 3)⁻¹ := by
      apply inv_pos.mpr
      exact pow_pos (lt_trans zero_lt_one (one_lt_principalRoot d hd)) _
    exact lt_trans hε hstrong
  · rw [principalFiveTermLowerRate_latticeArgument d hd]
    have h := (principalFiveTermLatticeRates_add_pos_iff d hd u₁ u₂ v₁ v₂).mpr huv
    linarith

/-- The residue prefactor becomes `√ε/√N`, since `ε - 1 = √(Nε)`. -/
private theorem principalFiveTermResidue_prefactor_eq (d : ℕ) (hd : 3 < d) :
    -(2 * Real.pi * I) *
        ((principalRoot d : ℂ) ^ 3 /
          (2 * Real.pi * I * (1 - (principalRoot d : ℂ) ^ 3))) =
      (Real.sqrt (principalRoot d ^ 3) : ℂ) /
        (Real.sqrt (principalDilogOrder d) : ℂ) := by
  let ε : ℝ := principalRoot d ^ 3
  let s : ℝ := Real.sqrt ε
  let n : ℝ := Real.sqrt (principalDilogOrder d)
  have hε : 1 < ε := one_lt_principalRoot_pow_three d hd
  have hn0 : n ≠ 0 := (Real.sqrt_ne_zero').mpr (by exact_mod_cast principalDilogOrder_pos d hd)
  have hsq : s ^ 2 = ε := Real.sq_sqrt (by linarith)
  have hrel : ε - 1 = n * s := principalRoot_pow_three_sub_one_eq_sqrt_mul d hd
  have hA : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  have hε0 : ((ε : ℂ) - 1) ≠ 0 := by exact_mod_cast (ne_of_gt (by linarith : 0 < ε - 1))
  have hOne : 1 - (ε : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (sub_ne_zero.mp hε0).symm
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  suffices h : -(2 * Real.pi * I) * ((ε : ℂ) / (2 * Real.pi * I * (1 - (ε : ℂ)))) =
      (s : ℂ) / (n : ℂ) by
    simpa only [ε, s, n, Complex.ofReal_pow] using h
  calc
    _ = (ε : ℂ) / ((ε : ℂ) - 1) := by field_simp [hA, hOne, hε0]; ring
    _ = (s : ℂ) / (n : ℂ) := by
      apply (div_eq_div_iff hε0 hnC).mpr
      have hsqC : (s : ℂ) ^ 2 = (ε : ℂ) := by exact_mod_cast hsq
      have hrelC : (ε : ℂ) - 1 = (n : ℂ) * s := by exact_mod_cast hrel
      calc
        (ε : ℂ) * n = (s : ℂ) ^ 2 * n := by rw [hsqC]
        _ = (s : ℂ) * ((ε : ℂ) - 1) := by rw [hrelC]; ring

/-- The complex shift of a vertical line is the real shift of its crossing. -/
private theorem principalFiveTerm_line_shift (d : ℕ) (x t : ℝ) :
    ((x : ℂ) + t * I) +
        ((principalRoot d : ℂ) ^ 3 - 1) / ((principalA d) 1 0 : ℂ) =
      ((x + (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) : ℝ) : ℂ) + t * I := by
  push_cast
  ring

/-- Integrating the almost everywhere telescoping identity gives the difference of the two
strip-boundary integrals. -/
private theorem principalFiveTerm_integral_telescope (d : ℕ) (hd : 3 < d)
    (ℓ p : ℤ) (w y x : ℝ)
    (hreg : ∀ m : FiveTermIndex (principalA d),
      IsPrincipalFiveTermResidueCrossing d ((m : ℕ) : ℤ) y
        (x - ((m : ℕ) : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ)))
    (hregRight : ∀ m : FiveTermIndex (principalA d),
      IsPrincipalFiveTermResidueCrossing d ((m : ℕ) : ℤ) y
        (x + (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) -
          ((m : ℕ) : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ)))
    (hupper : (principalRoot d ^ 3)⁻¹ < principalFiveTermUpperRate d ℓ w)
    (hlower : principalFiveTermLowerRate d ℓ p w y < 0)
    (hw : Complex.exp (2 * Real.pi * I * ((w : ℂ) / (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I * ((w : ℂ) + ((ℓ : ℂ) - 1) * (principalRoot d : ℂ))))
    (hy : Complex.exp (2 * Real.pi * I * ((y : ℂ) / (principalRoot d : ℂ) ^ 3)) =
      Complex.exp (2 * Real.pi * I * ((y : ℂ) + (p : ℂ) * (principalRoot d : ℂ)))) :
    (∫ t : ℝ, principalFiveTermDifferenceSum d ℓ p w y ((x : ℂ) + t * I) * I) =
      (∫ t : ℝ, principalFiveTermResidueSum d ℓ p w y ((x : ℂ) + t * I) * I) -
        (∫ t : ℝ, principalFiveTermResidueSum d ℓ p w y
          (((x + (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) : ℝ) : ℂ) + t * I) * I) := by
  let L := principalFiveTermResidueSum d ℓ p w y
  have hleft := integrable_principalFiveTermResidueSum d hd ℓ p w y x hreg hupper hlower
  have hright := integrable_principalFiveTermResidueSum d hd ℓ p w y
    (x + (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ)) hregRight hupper hlower
  have hrightShift : Integrable (fun t : ℝ => L (((x : ℂ) + t * I) +
      ((principalRoot d : ℂ) ^ 3 - 1) / ((principalA d) 1 0 : ℂ))) volume := by
    convert hright using 1
    funext t
    exact congrArg L (principalFiveTerm_line_shift d x t)
  have hae := ae_principalFiveTermResidueSum_sub_shift_eq d hd ℓ p w y hw hy x
  calc
    _ = ∫ t : ℝ, (L ((x : ℂ) + t * I) -
        L (((x : ℂ) + t * I) +
          ((principalRoot d : ℂ) ^ 3 - 1) / ((principalA d) 1 0 : ℂ))) * I := by
      apply integral_congr_ae
      filter_upwards [hae] with t ht
      rw [ht]
    _ = _ := by
      simp_rw [sub_mul]
      rw [integral_sub (hleft.mul_const I) (hrightShift.mul_const I)]
      have heq : (∫ t : ℝ, L (((x : ℂ) + t * I) +
          ((principalRoot d : ℂ) ^ 3 - 1) / ((principalA d) 1 0 : ℂ)) * I) =
          (∫ t : ℝ, L
            (((x + (principalRoot d ^ 3 - 1) / ((principalA d) 1 0 : ℝ) : ℝ) : ℂ) +
              t * I) * I) := by
        apply integral_congr_ae
        filter_upwards [] with t
        rw [principalFiveTerm_line_shift d x t]
      exact congrArg₂ (· - ·) rfl heq

/-- The source lattice arguments satisfy the two exponential relations for telescoping. -/
private theorem principalFiveTerm_exponential_parameters (d : ℕ) (hd : 3 < d)
    (u₁ u₂ v₁ v₂ : ℤ) :
    Complex.exp (2 * Real.pi * I *
        ((principalFiveTermLatticeArgument d u₁ u₂ : ℂ) / (principalRoot d : ℂ) ^ 3)) =
        Complex.exp (2 * Real.pi * I *
          ((principalFiveTermLatticeArgument d u₁ u₂ : ℂ) +
            (((u₁ + 1 : ℤ) : ℂ) - 1) * (principalRoot d : ℂ))) ∧
      Complex.exp (2 * Real.pi * I *
        ((principalFiveTermLatticeArgument d v₁ v₂ : ℂ) / (principalRoot d : ℂ) ^ 3)) =
        Complex.exp (2 * Real.pi * I *
          ((principalFiveTermLatticeArgument d v₁ v₂ : ℂ) +
            (v₁ : ℂ) * (principalRoot d : ℂ))) := by
  constructor
  · convert (principalFiveTermLatticeArgument_exp_lower d hd u₁ u₂).symm using 1
    push_cast
    ring_nf
  · convert (principalFiveTermLatticeArgument_exp_lower d hd v₁ v₂).symm using 1
    ring_nf

/-- Cancel `√ε` from the residue integral after its prefactor has become `√ε/√N`. -/
private theorem principalFiveTerm_normalize (d : ℕ) (hd : 3 < d) (A B S : ℂ)
    (h : (Real.sqrt (principalRoot d ^ 3) : ℂ) * A / B =
      ((Real.sqrt (principalRoot d ^ 3) : ℂ) /
        (Real.sqrt (principalDilogOrder d) : ℂ)) * S) :
    (1 / (Real.sqrt (principalDilogOrder d) : ℂ)) * S = A / B := by
  have hs0 : (Real.sqrt (principalRoot d ^ 3) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (pow_pos (principalRoot_pos d hd) 3))
  have hcancel : (Real.sqrt (principalRoot d ^ 3) : ℂ) * (A / B) =
      (Real.sqrt (principalRoot d ^ 3) : ℂ) *
        ((1 / (Real.sqrt (principalDilogOrder d) : ℂ)) * S) := by
    calc
      _ = (Real.sqrt (principalRoot d ^ 3) : ℂ) * A / B := by ring
      _ = ((Real.sqrt (principalRoot d ^ 3) : ℂ) /
        (Real.sqrt (principalDilogOrder d) : ℂ)) * S := h
      _ = _ := by ring
  exact (mul_left_cancel₀ hs0 hcancel).symm

/-! ### All nonzero right classes

Positive source representatives, with the two zero-class choices of `ClassWindow`, give the
crossed residue strip and the shifted integral on the same common line. Subtracting their
identical square corrections gives the finite relation, after `ε-1=√(Nε)`.
-/

/-- The right source pole satisfies `β_v=(ε-1)S_d(v)/(cH)` on the common line. Used by
`principalFiveTerm_crossed_beta_data`. -/
private theorem principalFiveTerm_crossed_beta_eq (d : ℕ) (hd : 3 < d) (v₁ v₂ : ℤ) :
    -((v₁ : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) +
        principalFiveTermLatticeArgument d v₁ v₂) =
      (principalRoot d ^ 3 - 1) * (principalFiveTermLatticeIndex d v₁ v₂ : ℝ) /
        (((principalA d) 1 0 : ℝ) * (principalFiveTermUpperIndexBound d : ℝ)) := by
  linear_combination -(principalFiveTermLatticeArgument_add_mul_eq d hd v₁ v₂)

/-- A positive right source pole cannot lie on the integer grid `j/c`. Used by
`principalFiveTerm_crossed_beta_data`. -/
private theorem principalFiveTerm_crossed_beta_ne_grid (d : ℕ) (hd : 3 < d)
    (v₁ v₂ : ℤ) (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂) (j : ℤ) :
    -((v₁ : ℝ) * principalRoot d ^ 3 / ((principalA d) 1 0 : ℝ) +
        principalFiveTermLatticeArgument d v₁ v₂) ≠
      (j : ℝ) / ((principalA d) 1 0 : ℝ) := by
  let ε : ℝ := principalRoot d ^ 3
  let c : ℝ := ((principalA d) 1 0 : ℝ)
  let H : ℝ := (principalFiveTermUpperIndexBound d : ℝ)
  let S : ℤ := principalFiveTermLatticeIndex d v₁ v₂
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (principalA_lowerLeft_pos d hd).ne'
  have hH : H ≠ 0 := by
    dsimp [H]
    exact_mod_cast (principalFiveTermUpperIndexBound_pos d hd).ne'
  have hirrε : Irrational (ε - 1) := principalRoot_pow_three_sub_one_irrational d hd
  have hirrS : Irrational ((ε - 1) * (S : ℝ)) :=
    hirrε.mul_intCast (by omega : S ≠ 0)
  intro hj
  rw [principalFiveTerm_crossed_beta_eq d hd] at hj
  have hmul := (div_eq_div_iff (mul_ne_zero hc hH) hc).1 hj
  have hmul' : c * ((ε - 1) * (S : ℝ)) = c * ((j : ℝ) * H) := by
    nlinarith [hmul]
  have hEq : (ε - 1) * (S : ℝ) = ((j * principalFiveTermUpperIndexBound d : ℤ) : ℝ) := by
    have hcancel := mul_left_cancel₀ hc hmul'
    simpa only [H, Int.cast_mul] using hcancel
  exact hirrS.ne_int _ hEq

/-- For a positive right source index, the kernel pole `β_v` lies in `(0,δ]` and misses the
integer grid `j/c`. Used by `principalDilogFiveTerm_of_ne_zero_right`. -/
private theorem principalFiveTerm_crossed_beta_data (d : ℕ) (hd : 3 < d)
    (v₁ v₂ : ℤ)
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂ ∧
      principalFiveTermLatticeIndex d v₁ v₂ ≤ principalFiveTermUpperIndexBound d) :
    let ε := principalRoot d ^ 3
    let c : ℝ := ((principalA d) 1 0 : ℝ)
    let y := principalFiveTermLatticeArgument d v₁ v₂
    let β := -((v₁ : ℝ) * ε / c + y)
    0 < β ∧ β ≤ (ε - 1) / c ∧ ∀ j : ℤ, β ≠ (j : ℝ) / c := by
  let ε : ℝ := principalRoot d ^ 3
  let c : ℝ := ((principalA d) 1 0 : ℝ)
  let H : ℝ := (principalFiveTermUpperIndexBound d : ℝ)
  let S : ℤ := principalFiveTermLatticeIndex d v₁ v₂
  let y := principalFiveTermLatticeArgument d v₁ v₂
  let β := -((v₁ : ℝ) * ε / c + y)
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast principalA_lowerLeft_pos d hd
  have hH : 0 < H := by
    dsimp [H]
    exact_mod_cast principalFiveTermUpperIndexBound_pos d hd
  have hε : 0 < ε - 1 := sub_pos.mpr (one_lt_principalRoot_pow_three d hd)
  have hS : 0 < (S : ℝ) := by exact_mod_cast hv.1
  have hSle : (S : ℝ) ≤ H := by
    dsimp [S, H]
    exact_mod_cast hv.2
  have hβ : β = (ε - 1) * (S : ℝ) / (c * H) :=
    principalFiveTerm_crossed_beta_eq d hd v₁ v₂
  change 0 < β ∧ β ≤ (ε - 1) / c ∧ ∀ j : ℤ, β ≠ (j : ℝ) / c
  refine ⟨?_, ?_, ?_⟩
  · rw [hβ]
    exact div_pos (mul_pos hε hS) (mul_pos hc hH)
  · rw [hβ]
    apply (div_le_div_iff₀ (mul_pos hc hH) hc).2
    nlinarith [mul_nonneg (mul_nonneg hε.le hc.le) (sub_nonneg.mpr hSle)]
  · exact principalFiveTerm_crossed_beta_ne_grid d hd v₁ v₂ hv.1

/-- A sufficiently small positive radius is regular at both vertical edges of the crossed
squares. Used by `principalDilogFiveTerm_of_ne_zero_right`. -/
private theorem exists_principalFiveTerm_regular_radius (d : ℕ) (hd : 3 < d)
    (y b : ℝ) (hb : 0 < b) :
    ∃ r : ℝ, 0 < r ∧ r < b ∧
      IsRegularPeriodLatticeCrossing (principalRoot d) y r ∧
      IsRegularPeriodLatticeCrossing (principalRoot d) y (-r) := by
  let bad := Set.range (principalFiveTermBadPoint d y y)
  let badNeg := Set.range (fun q => -principalFiveTermBadPoint d y y q)
  have hcount : (bad ∪ badNeg).Countable :=
    (Set.countable_range _).union (Set.countable_range _)
  have hne : (Set.Ioo (0 : ℝ) b).Nonempty := ⟨b / 2, by constructor <;> linarith⟩
  obtain ⟨r, hrBad, hrI⟩ := (hcount.dense_compl ℝ).exists_mem_open isOpen_Ioo hne
  have hrPlus : r ∉ bad := fun h => hrBad (Set.mem_union_left _ h)
  have hrMinus : -r ∉ bad := by
    intro ⟨q, hq⟩
    apply hrBad (Set.mem_union_right _ _)
    refine ⟨q, ?_⟩
    dsimp [badNeg] at hq ⊢
    linarith
  have hc : 0 < ((principalA d) 1 0).toNat := by
    have h := principalA_lowerLeft_pos d hd
    omega
  let m : FiveTermIndex (principalA d) := ⟨0, hc⟩
  have hplus := (principalFiveTermCrossingAvoids_regular d y y r
    (principalFiveTermCrossingAvoids_of_not_mem d y y r hrPlus)).2 m
  have hminus := (principalFiveTermCrossingAvoids_regular d y y (-r)
    (principalFiveTermCrossingAvoids_of_not_mem d y y (-r) hrMinus)).2 m
  exact ⟨r, hrI.1, hrI.2, by simpa [m] using hplus, by simpa [m] using hminus⟩

/-- The crossed-strip coefficient `ε/(ε-1)` is the residue prefactor `√ε/√N` of
`principalFiveTermResidue_prefactor_eq`. Used by `principalDilogFiveTerm_of_ne_zero_right`. -/
private theorem principalFiveTerm_crossed_prefactor_eq (d : ℕ) (hd : 3 < d) :
    ((principalRoot d ^ 3 : ℝ) : ℂ) / (((principalRoot d ^ 3 : ℝ) : ℂ) - 1) =
      (Real.sqrt (principalRoot d ^ 3) : ℂ) /
        (Real.sqrt (principalDilogOrder d) : ℂ) := by
  simp only [Complex.ofReal_pow]
  have hA : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  have hε0 : (principalRoot d : ℂ) ^ 3 - 1 ≠ 0 := by
    exact_mod_cast (ne_of_gt (sub_pos.mpr (one_lt_principalRoot_pow_three d hd)))
  have hOne : 1 - (principalRoot d : ℂ) ^ 3 ≠ 0 :=
    sub_ne_zero.mpr (sub_ne_zero.mp hε0).symm
  calc
    _ = -(2 * Real.pi * I) *
        ((principalRoot d : ℂ) ^ 3 /
          (2 * Real.pi * I * (1 - (principalRoot d : ℂ) ^ 3))) := by
        field_simp [hA, hε0, hOne]
        ring
    _ = _ := principalFiveTermResidue_prefactor_eq d hd

/-- The open interval just right of `β_v` has the strip width and no new integer crossing;
it contains a line regular on both boundaries. Used by `exists_principalFiveTerm_crossed_line`. -/
private theorem exists_principalFiveTerm_crossed_interval (d : ℕ) (hd : 3 < d)
    (v₁ v₂ : ℤ)
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂ ∧
      principalFiveTermLatticeIndex d v₁ v₂ ≤ principalFiveTermUpperIndexBound d) :
    let ε := principalRoot d ^ 3
    let c : ℝ := ((principalA d) 1 0 : ℝ)
    let H : ℝ := (principalFiveTermUpperIndexBound d : ℝ)
    let δ := (ε - 1) / c
    let y := principalFiveTermLatticeArgument d v₁ v₂
    let β := -((v₁ : ℝ) * ε / c + y)
    ∃ x : ℝ, β < x ∧ x < β + δ / H ∧ x < ε / c ∧
      x < (⌈c * β⌉ : ℝ) / c ∧
      principalFiveTermCrossingAvoids d y (principalFiveTermShiftedParameter d y) x ∧
      principalFiveTermCrossingAvoids d y (principalFiveTermShiftedParameter d y) (x + δ) := by
  let ε : ℝ := principalRoot d ^ 3
  let c : ℝ := ((principalA d) 1 0 : ℝ)
  let H : ℝ := (principalFiveTermUpperIndexBound d : ℝ)
  let δ : ℝ := (ε - 1) / c
  let y := principalFiveTermLatticeArgument d v₁ v₂
  let β := -((v₁ : ℝ) * ε / c + y)
  have hc : 0 < c := by dsimp [c]; exact_mod_cast principalA_lowerLeft_pos d hd
  have hH : 0 < H := by dsimp [H]; exact_mod_cast principalFiveTermUpperIndexBound_pos d hd
  have hε : 0 < ε - 1 := sub_pos.mpr (one_lt_principalRoot_pow_three d hd)
  obtain ⟨_, hβle, hβgrid⟩ := principalFiveTerm_crossed_beta_data d hd v₁ v₂ hv
  have hβeps : β < ε / c := by
    have hδlt : δ < ε / c := by
      dsimp [δ]
      apply (div_lt_div_iff₀ hc hc).2
      nlinarith [hc]
    exact lt_of_le_of_lt hβle hδlt
  have hβnext : β < (⌈c * β⌉ : ℝ) / c := by
    have hceil : c * β ≤ (⌈c * β⌉ : ℝ) := Int.le_ceil _
    have hne : c * β ≠ (⌈c * β⌉ : ℝ) := by
      intro heq
      apply hβgrid ⌈c * β⌉
      apply (eq_div_iff hc.ne').2
      nlinarith [heq]
    exact (lt_div_iff₀ hc).2 (by nlinarith [lt_of_le_of_ne hceil hne])
  have hδH : 0 < δ / H := div_pos (div_pos hε hc) hH
  let b := min (β + δ / H) (min (ε / c) ((⌈c * β⌉ : ℝ) / c))
  have hβb : β < b := lt_min (by linarith) (lt_min hβeps hβnext)
  obtain ⟨x, hβx, hxb, havoid, havoidRight⟩ :=
    exists_principalFiveTerm_avoiding_between d y (principalFiveTermShiftedParameter d y) β b hβb
  change ∃ x : ℝ, β < x ∧ x < β + δ / H ∧ x < ε / c ∧
    x < (⌈c * β⌉ : ℝ) / c ∧
    principalFiveTermCrossingAvoids d y (principalFiveTermShiftedParameter d y) x ∧
    principalFiveTermCrossingAvoids d y (principalFiveTermShiftedParameter d y) (x + δ)
  exact ⟨x, hβx, lt_of_lt_of_le hxb (min_le_left _ _),
    lt_of_lt_of_le hxb ((min_le_right _ _).trans (min_le_left _ _)),
    lt_of_lt_of_le hxb ((min_le_right _ _).trans (min_le_right _ _)),
    havoid, by simpa [δ, ε, c] using havoidRight⟩

/-- A common line just right of `β_v` satisfies both crossed endpoint domains and is regular
at both strip boundaries. Used by `principalDilogFiveTerm_of_ne_zero_right`. -/
private theorem exists_principalFiveTerm_crossed_line (d : ℕ) (hd : 3 < d)
    (v₁ v₂ : ℤ)
    (hv : 1 ≤ principalFiveTermLatticeIndex d v₁ v₂ ∧
      principalFiveTermLatticeIndex d v₁ v₂ ≤ principalFiveTermUpperIndexBound d) :
    let ε := principalRoot d ^ 3
    let c : ℝ := ((principalA d) 1 0 : ℝ)
    let H : ℝ := (principalFiveTermUpperIndexBound d : ℝ)
    let δ := (ε - 1) / c
    let y := principalFiveTermLatticeArgument d v₁ v₂
    let β := -((v₁ : ℝ) * ε / c + y)
    ∃ (x : ℝ) (F : Finset ℤ),
      β < x ∧ x < β + δ / H ∧ x < ε / c ∧
      (∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧ (j : ℝ) / c < β) ∧
      (∀ j : ℤ, 0 ≤ j → ((j : ℝ) / c < x ↔ (j : ℝ) / c < β)) ∧
      (∀ m : FiveTermIndex (principalA d),
        IsPrincipalFiveTermResidueCrossing d ((m : ℕ) : ℤ) y
          (x - ((m : ℕ) : ℝ) * ε / c)) ∧
      (∀ m : FiveTermIndex (principalA d),
        IsPrincipalFiveTermResidueCrossing d ((m : ℕ) : ℤ) y
          (x + δ - ((m : ℕ) : ℝ) * ε / c)) := by
  let ε : ℝ := principalRoot d ^ 3
  let c : ℝ := ((principalA d) 1 0 : ℝ)
  let H : ℝ := (principalFiveTermUpperIndexBound d : ℝ)
  let δ : ℝ := (ε - 1) / c
  let y := principalFiveTermLatticeArgument d v₁ v₂
  let y' := principalFiveTermShiftedParameter d y
  let β := -((v₁ : ℝ) * ε / c + y)
  have hc : 0 < c := by dsimp [c]; exact_mod_cast principalA_lowerLeft_pos d hd
  obtain ⟨x, hβx, hxδ, hxε, hxnext, havoid, havoidRight⟩ :=
    exists_principalFiveTerm_crossed_interval d hd v₁ v₂ hv
  let F : Finset ℤ := Finset.Ico 0 ⌈c * β⌉
  have hF : ∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧ (j : ℝ) / c < β := by
    intro j
    change j ∈ Finset.Ico 0 ⌈c * β⌉ ↔ 0 ≤ j ∧ (j : ℝ) / c < β
    rw [Finset.mem_Ico, Int.lt_ceil]
    constructor
    · rintro ⟨hj0, hj⟩
      exact ⟨hj0, (div_lt_iff₀ hc).2 (by nlinarith [hj])⟩
    · rintro ⟨hj0, hj⟩
      exact ⟨hj0, (div_lt_iff₀ hc).1 hj |>.trans_eq (mul_comm β c)⟩
  have hstable : ∀ j : ℤ, 0 ≤ j → ((j : ℝ) / c < x ↔ (j : ℝ) / c < β) := by
    intro j _
    constructor
    · intro hjx
      have hjcx : (j : ℝ) < x * c := (div_lt_iff₀ hc).1 hjx
      have hxceil : x * c < (⌈c * β⌉ : ℝ) := (lt_div_iff₀ hc).1 hxnext
      have hjceil : j < ⌈c * β⌉ := by exact_mod_cast lt_trans hjcx hxceil
      exact (div_lt_iff₀ hc).2 ((Int.lt_ceil.1 hjceil).trans_eq (mul_comm c β))
    · intro hjβ
      exact lt_trans hjβ hβx
  have hreg := (principalFiveTermCrossingAvoids_regular d y y' x havoid).1
  have hregRight := (principalFiveTermCrossingAvoids_regular d y y' (x + δ) havoidRight).1
  change ∃ (x : ℝ) (F : Finset ℤ), β < x ∧ x < β + δ / H ∧ x < ε / c ∧
    (∀ j : ℤ, j ∈ F ↔ 0 ≤ j ∧ (j : ℝ) / c < β) ∧
    (∀ j : ℤ, 0 ≤ j → ((j : ℝ) / c < x ↔ (j : ℝ) / c < β)) ∧
    (∀ m : FiveTermIndex (principalA d),
      IsPrincipalFiveTermResidueCrossing d ((m : ℕ) : ℤ) y
        (x - ((m : ℕ) : ℝ) * ε / c)) ∧
    (∀ m : FiveTermIndex (principalA d),
      IsPrincipalFiveTermResidueCrossing d ((m : ℕ) : ℤ) y
        (x + δ - ((m : ℕ) : ℝ) * ε / c))
  exact ⟨x, F, hβx, hxδ, hxε, hF, hstable, hreg, hregRight⟩

/-- The nonzero-right case of [RW26, Radchenko, Wheeler (2026), Theorem 2, `thm:fg.equs`,
equation (7), `eq:Fgpm.5term`] at `A_d`. The corrected residue strip and crossed integral
identity have the same square terms, which cancel; positive source representatives include
the continued zero left and zero sum cases. -/
theorem principalDilogFiveTerm_of_ne_zero_right (d : ℕ) (hd : 3 < d)
    [NeZero (principalDilogOrder d)]
    {u v : Fin 2 → ZMod (principalDilogOrder d)}
    (hu : u ∈ principalDilogGroup d) (hv : v ∈ principalDilogGroup d) (hv0 : v ≠ 0) :
    (1 / (Real.sqrt (principalDilogOrder d) : ℂ)) *
        ∑ x : principalDilogGroup d,
          principalDilogBicharacter d x u *
            (principalDilogE d x / principalDilogEMinus d (x + v)) =
      principalDilogE d (u + v) / (principalDilogEMinus d u * principalDilogEMinus d v) := by
  obtain ⟨u₁, u₂, v₁, v₂, huEq, hvEq, huBound, hvBound, huZero, huvZero⟩ :=
    exists_principalFiveTerm_positive_representatives d hd hu hv hv0
  have hvNonzero : principalFiveTermCharacteristicResidue d v₁ v₂ ≠ 0 := by
    simpa only [hvEq] using hv0
  have huZero' : principalFiveTermCharacteristicResidue d u₁ u₂ = 0 →
      u₁ = 0 ∧ u₂ = 0 := by
    intro h
    exact huZero (by simpa only [huEq] using h)
  have huvZero' : principalFiveTermCharacteristicResidue d (u₁ + v₁) (u₂ + v₂) = 0 →
      u₁ + v₁ = (principalA d) 0 0 - 1 ∧ u₂ + v₂ = (principalA d) 0 1 := by
    intro h
    apply huvZero
    simpa only [principalFiveTermCharacteristicResidue_add, huEq, hvEq] using h
  have huvPos : 0 < principalFiveTermLatticeIndex d u₁ u₂ +
      principalFiveTermLatticeIndex d v₁ v₂ := by omega
  obtain ⟨hupper, _, hlower⟩ :=
    principalFiveTerm_source_rates d hd u₁ u₂ v₁ v₂ huBound.2 huvPos
  let w := principalFiveTermLatticeArgument d u₁ u₂
  let y := principalFiveTermLatticeArgument d v₁ v₂
  let y' := principalFiveTermShiftedParameter d y
  obtain ⟨x, F, hβx, hxδ, hxε, hF, hstable, hreg, hregRight⟩ :=
    exists_principalFiveTerm_crossed_line d hd v₁ v₂ hvBound
  obtain ⟨hw, hy⟩ := principalFiveTerm_exponential_parameters d hd u₁ u₂ v₁ v₂
  have hbridge := principalFiveTerm_integral_telescope d hd (u₁ + 1) v₁ w y x
    hreg hregRight hupper hlower hw hy
  have hstrip := integral_principalFiveTermResidueSum_of_crossed
    d hd u₁ u₂ v₁ v₂ huBound hvBound hvNonzero x F hβx hxδ hxε hF hstable hreg
  have hshift := integral_principalFiveTermDifferenceSum_of_crossed
    d hd u₁ u₂ v₁ v₂ huBound hvBound hvNonzero huZero' huvZero'
      x F hβx hxε hF hstable hreg
  obtain ⟨b, hb, hbsub⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset).1 (hstrip.and hshift)
  obtain ⟨r, hr0, hrb, hrplus, hrminus⟩ :=
    exists_principalFiveTerm_regular_radius d hd y' b hb
  obtain ⟨hstripR, hshiftR⟩ := hbsub ⟨hr0, hrb⟩
  have hshiftR := hshiftR hrplus hrminus
  rw [← hbridge] at hstripR
  have hmain := hshiftR.symm.trans hstripR
  rw [principalFiveTerm_crossed_prefactor_eq d hd] at hmain
  have hresult := principalFiveTerm_normalize d hd _ _ _ hmain
  rw [principalFiveTermCharacteristicResidue_add, huEq, hvEq] at hresult
  exact hresult

end SIC

end
