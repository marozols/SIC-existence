/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Principal.Dilogarithm.Faddeev.Basic

/-!
# Reflection of the principal Faddeev product

The reflection law of the principal Faddeev product with its quadratic and constant phases.

This module follows [RW26, Radchenko, Wheeler (2026), Proposition 1, `prop:reflection`]
at `γ = A_d` and `τ = ρ_d`, using the three-factor formula of Proposition 2(ii),
`prop:prod.id.mod,fad`, equation (20), `eq:modulartofaddeevCF`.

## The argument

Choose internal indices `(1,1)` in `Φ_{A_d,m+1,n+1}(z)`. Its arguments pair with those
of `Φ_{A_d,-m,-n}(-z)` as `w+ρ_d-1` and `-w`, where
`w = z/ρ_d²-n, z/ρ_d, z+mρ_d`. Apply the generator reflection law to each pair.
The identity `ρ_d+ρ_d⁻¹=d-1` reduces the sum of the three quadratic exponents to
`Q_{A_d,m,n}(z,ρ_d)`, the sign `(-1)^{m+n}`, and the constant `exp(-πid/2)`.
The remaining integer multiple is even because `n(n+1)` is even.

Proposition 1 includes the multiplier `μ_γ⁻²`. For the principal word its value is
`exp(-πid/2)`, the constant obtained here from the generator identity (13),
`eq:PhiS.reflection`. The polynomial `Q` is the one in the source.

The pointwise law requires the gamma denominators along the intermediate-index paths of its
two three-factor products to be nonzero. For nonreal `z` these conditions hold
automatically, since every argument has nonzero imaginary part and `ρ_d > 0`.
-/

noncomputable section

namespace SIC

/-! ### The quadratic exponent

At the principal fixed point, `c=d(d-2)`, `cρ_d+1-d=ρ_d³`, and `A_d·ρ_d=ρ_d`.
Thus the two Bernoulli terms in Proposition 1 combine to
`(m²+m-n²-n)ρ_d`; the constants `1/6` cancel.
-/

/-- The polynomial `Q_{A_d,m,n}(z,ρ_d)` of
[RW26, Radchenko, Wheeler (2026), Proposition 1, `prop:reflection`]. Here
`B₂(m+1)-B₂(n+1)=m²+m-n²-n`, `c=d(d-2)`, and `cρ_d+1-d=ρ_d³`. -/
def principalFaddeevReflectionExponent (d : ℕ) (m n : ℤ) (z : ℂ) : ℂ :=
  -(1 / 2 : ℂ) *
    ((d : ℂ) * ((d : ℂ) - 2) * z ^ 2 / (principalRoot d : ℂ) ^ 3 +
      (2 * (m : ℂ) + 1 - (2 * (n : ℂ) + 1) / (principalRoot d : ℂ) ^ 3) * z +
      ((m : ℂ) ^ 2 + m - (n : ℂ) ^ 2 - n) * (principalRoot d : ℂ))

section PrincipalReflection

variable (d : ℕ)

/-- The complex principal period used in the reflection formula. -/
local notation "ρ" => (principalRoot d : ℂ)

/-! ### Reflection on the pointwise domain

Intermediate-index transport supplies the three matching pairs. The path endpoints
also give the denominator conditions for their first factors.
-/

/-- The bracket in the exponent of `faddeevS_mul_neg`, used by
`principalFaddeev_mul_neg_of_paths` at the principal period. -/
private def principalFaddeevReflectionTerm (d : ℕ) (w : ℂ) : ℂ :=
  w ^ 2 / (principalRoot d : ℂ) +
    (1 - (principalRoot d : ℂ)⁻¹) * w +
    ((principalRoot d : ℂ) + (principalRoot d : ℂ)⁻¹) / 6 - 1 / 2

/-- The three generator exponents combine into the principal quadratic exponent,
sign, and constant terms. Used by `principalFaddeev_mul_neg_of_paths`. -/
private lemma principalFaddeevReflectionTerm_sum (hd : 3 < d) (m n : ℤ) (z : ℂ) :
    principalFaddeevReflectionTerm d (z / ρ ^ 2 - n) +
      principalFaddeevReflectionTerm d (z / ρ) +
      principalFaddeevReflectionTerm d (z + m * ρ) =
    -2 * principalFaddeevReflectionExponent d m n z +
      ((n : ℂ) ^ 2 + n) * ((d : ℂ) - 1) - m - n + (d : ℂ) / 2 - 2 := by
  dsimp only [principalFaddeevReflectionTerm, principalFaddeevReflectionExponent]
  set ρ' : ℂ := ρ with hρdef
  have hρ : ρ' ≠ 0 := ofReal_principalRoot_ne_zero d hd
  have hsum : ρ' + ρ'⁻¹ = (d : ℂ) - 1 := by
    dsimp only [ρ']
    exact ofReal_principalRoot_add_inv d hd
  have hdval : (d : ℂ) = ρ' + ρ'⁻¹ + 1 := by linear_combination -hsum
  rw [hdval]
  field_simp [hρ]
  ring_nf

/-- Removes the even integer from the sum of the three generator exponents.
Used by `principalFaddeev_mul_neg_of_paths`. -/
private lemma principalFaddeevReflection_exp (hd : 3 < d) (m n : ℤ) (z : ℂ) :
    Complex.exp (-Real.pi * Complex.I *
      (principalFaddeevReflectionTerm d (z / ρ ^ 2 - n) +
        principalFaddeevReflectionTerm d (z / ρ) +
        principalFaddeevReflectionTerm d (z + m * ρ))) =
    (-1 : ℂ) ^ (m + n) * Complex.exp (-Real.pi * Complex.I * (d : ℂ) / 2) *
      Complex.exp (2 * Real.pi * Complex.I * principalFaddeevReflectionExponent d m n z) := by
  obtain ⟨k, hk⟩ := Int.even_mul_succ_self n
  have hkC : (n : ℂ) ^ 2 + n = (k : ℂ) + k := by
    calc
      _ = (n : ℂ) * (n + 1) := by ring_nf
      _ = (k : ℂ) + k := by exact_mod_cast hk
  let F : ℂ := principalFaddeevReflectionTerm d (z / ρ ^ 2 - n) +
    principalFaddeevReflectionTerm d (z / ρ) +
    principalFaddeevReflectionTerm d (z + m * ρ)
  let Q : ℂ := principalFaddeevReflectionExponent d m n z
  have hF : F = -2 * Q + ((n : ℂ) ^ 2 + n) * ((d : ℂ) - 1) - m - n +
      (d : ℂ) / 2 - 2 := principalFaddeevReflectionTerm_sum d hd m n z
  have hshift : -F / 2 - (Q - (d : ℂ) / 4 + ((m + n : ℤ) : ℂ) / 2) =
      ((1 - k * ((d : ℤ) - 1) : ℤ) : ℂ) := by
    rw [hF, hkC]; push_cast; ring_nf
  have hperiod := exp_two_pi_I_eq_of_sub_intCast
    (-F / 2) (Q - (d : ℂ) / 4 + ((m + n : ℤ) : ℂ) / 2)
    (1 - k * ((d : ℤ) - 1)) hshift
  have hsign : Complex.exp (((m + n : ℤ) : ℂ) * (Real.pi * Complex.I)) =
      (-1 : ℂ) ^ (m + n) := by
    rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]
  change Complex.exp (-Real.pi * Complex.I * F) = _
  calc
    _ = Complex.exp (2 * Real.pi * Complex.I * (-F / 2)) := by congr 1; ring_nf
    _ = Complex.exp (2 * Real.pi * Complex.I *
      (Q - (d : ℂ) / 4 + ((m + n : ℤ) : ℂ) / 2)) := hperiod
    _ = Complex.exp ((((m + n : ℤ) : ℂ) * (Real.pi * Complex.I) +
        (-Real.pi * Complex.I * (d : ℂ) / 2)) +
        2 * Real.pi * Complex.I * Q) := by congr 1; ring_nf
    _ = _ := by rw [Complex.exp_add, Complex.exp_add, hsign]

/-- Applies `faddeevS_mul_neg` at the principal period in the form used by
`principalFaddeev_mul_neg_of_paths`. -/
private lemma principalFaddeevReflection_generator (hd : 3 < d) (w : ℂ)
    (hfirst : barnesDoubleGammaInv (1 - w) 1 ρ ≠ 0)
    (hsecond : barnesDoubleGammaInv (ρ + w) 1 ρ ≠ 0) :
    faddeevS (w + ρ - 1) ρ * faddeevS (-w) ρ =
      Complex.exp (-Real.pi * Complex.I * principalFaddeevReflectionTerm d w) := by
  have hρ : ρ ≠ 0 := ofReal_principalRoot_ne_zero d hd
  have hsecond' : barnesDoubleGammaInv (w + ρ) 1 ρ ≠ 0 := by
    convert hsecond using 1; ring_nf
  simpa only [principalFaddeevReflectionTerm] using
    faddeevS_mul_neg w ρ hρ hfirst hsecond'

/-- Equation (20) at internal indices `(1,1)`, arranged as three reflected
generator pairs for `principalFaddeev_mul_neg_of_paths`. -/
private lemma principalFaddeevReflection_factor_pairs (hd : 3 < d) (m n : ℤ) (z : ℂ)
    (h₂ : FaddeevSRegularPath ρ 1
      (fun j => z / ρ ^ 2 + j * ρ - (n + 1 : ℤ)))
    (h₁ : FaddeevSRegularPath ρ 1 (fun j => z / ρ - j))
    (h₁' : FaddeevSRegularPath ρ 1 (fun j => z / ρ + j * ρ - 1))
    (h₀ : FaddeevSRegularPath ρ 1 (fun j => z + (m + 1 : ℤ) * ρ - j)) :
    principalFaddeev d (m + 1) (n + 1) z *
        principalFaddeev d (-m) (-n) (-z) =
      (faddeevS (z / ρ ^ 2 - n + ρ - 1) ρ * faddeevS (-(z / ρ ^ 2 - n)) ρ) *
        (faddeevS (z / ρ + ρ - 1) ρ * faddeevS (-(z / ρ)) ρ) *
        (faddeevS (z + m * ρ + ρ - 1) ρ * faddeevS (-(z + m * ρ)) ρ) := by
  have hpos : principalFaddeev d (m + 1) (n + 1) z =
      faddeevS (z / ρ ^ 2 - n + ρ - 1) ρ *
        faddeevS (z / ρ + ρ - 1) ρ *
        faddeevS (z + m * ρ + ρ - 1) ρ := by
    have hstart : (0 : ℤ) ∈ Set.uIcc (0 : ℤ) 1 := by simp
    have hend : (1 : ℤ) ∈ Set.uIcc (0 : ℤ) 1 := by simp
    rw [principalFaddeev_eq_indices d hd (m + 1) (n + 1) 1 1 z
      (by simpa using h₂.denominator_ne_zero 1 hend)
      (by simpa using h₁.denominator_ne_zero 0 hstart)
      (by simpa using h₁'.denominator_ne_zero 1 hend)
      (by simpa using h₀.denominator_ne_zero 0 hstart)]
    congr 1 <;> push_cast <;> ring_nf
  have hneg : principalFaddeev d (-m) (-n) (-z) =
      faddeevS (-(z / ρ ^ 2 - n)) ρ * faddeevS (-(z / ρ)) ρ *
        faddeevS (-(z + m * ρ)) ρ := by
    simp only [principalFaddeev]
    congr 1 <;> push_cast <;> ring_nf
  rw [hpos, hneg]
  ring_nf

/-- The principal reflection law on the intermediate finite paths
`Φ_{A_d,m+1,n+1}(z) Φ_{A_d,-m,-n}(-z) =
(-1)^{m+n} exp(-πid/2) e(Q_{A_d,m,n}(z,ρ_d))`, where all displayed gamma quotients
are finite. This is [RW26, Radchenko, Wheeler (2026), Proposition 1, `prop:reflection`]
at the principal word, with `μ_{A_d}⁻² = exp(-πid/2)` expanded using equation (13),
`eq:PhiS.reflection`.
Specializes `faddeevS_mul_neg` at the three principal arguments. -/
private theorem principalFaddeev_mul_neg_of_paths (hd : 3 < d) (m n : ℤ) (z : ℂ)
    (h₂ : FaddeevSRegularPath ρ 1
      (fun j => z / ρ ^ 2 + j * ρ - (n + 1 : ℤ)))
    (h₁ : FaddeevSRegularPath ρ 1 (fun j => z / ρ - j))
    (h₁' : FaddeevSRegularPath ρ 1 (fun j => z / ρ + j * ρ - 1))
    (h₀ : FaddeevSRegularPath ρ 1 (fun j => z + (m + 1 : ℤ) * ρ - j))
    (hneg₂ : barnesDoubleGammaInv (ρ + (z / ρ ^ 2 - n)) 1 ρ ≠ 0)
    (hneg₁ : barnesDoubleGammaInv (ρ + z / ρ) 1 ρ ≠ 0)
    (hneg₀ : barnesDoubleGammaInv (ρ + (z + m * ρ)) 1 ρ ≠ 0) :
    principalFaddeev d (m + 1) (n + 1) z *
        principalFaddeev d (-m) (-n) (-z) =
      (-1 : ℂ) ^ (m + n) * Complex.exp (-Real.pi * Complex.I * (d : ℂ) / 2) *
        Complex.exp (2 * Real.pi * Complex.I * principalFaddeevReflectionExponent d m n z) := by
  have hend : (1 : ℤ) ∈ Set.uIcc (0 : ℤ) 1 := by simp
  have hfirst₂ : barnesDoubleGammaInv (1 - (z / ρ ^ 2 - n)) 1 ρ ≠ 0 := by
    convert h₂.denominator_ne_zero 1 hend using 1; push_cast; ring_nf
  have hfirst₁ : barnesDoubleGammaInv (1 - z / ρ) 1 ρ ≠ 0 := by
    convert h₁'.denominator_ne_zero 1 hend using 1; push_cast; ring_nf
  have hfirst₀ : barnesDoubleGammaInv (1 - (z + m * ρ)) 1 ρ ≠ 0 := by
    convert h₀.denominator_ne_zero 1 hend using 1; push_cast; ring_nf
  have hpair₂ := principalFaddeevReflection_generator d hd (z / ρ ^ 2 - n) hfirst₂ hneg₂
  have hpair₁ := principalFaddeevReflection_generator d hd (z / ρ) hfirst₁ hneg₁
  have hpair₀ := principalFaddeevReflection_generator d hd (z + m * ρ) hfirst₀ hneg₀
  rw [principalFaddeevReflection_factor_pairs d hd m n z h₂ h₁ h₁' h₀]
  calc
    _ = Complex.exp (-Real.pi * Complex.I *
          principalFaddeevReflectionTerm d (z / ρ ^ 2 - n)) *
        Complex.exp (-Real.pi * Complex.I *
          principalFaddeevReflectionTerm d (z / ρ)) *
        Complex.exp (-Real.pi * Complex.I *
          principalFaddeevReflectionTerm d (z + m * ρ)) := by
          rw [hpair₂, hpair₁, hpair₀]
    _ = Complex.exp (-Real.pi * Complex.I *
          (principalFaddeevReflectionTerm d (z / ρ ^ 2 - n) +
            principalFaddeevReflectionTerm d (z / ρ) +
            principalFaddeevReflectionTerm d (z + m * ρ))) := by
          rw [← Complex.exp_add, ← Complex.exp_add]
          congr 1
          ring_nf
    _ = _ := principalFaddeevReflection_exp d hd m n z

/-- The principal reflection law for every nonreal `z`, with the path and gamma-denominator
conditions of the pointwise law discharged by the gamma divisor.
Specializes `faddeevS_mul_neg` at the nonreal principal arguments. -/
theorem principalFaddeev_mul_neg_of_im_ne_zero (hd : 3 < d)
    (m n : ℤ) (z : ℂ) (hz : z.im ≠ 0) :
    principalFaddeev d (m + 1) (n + 1) z *
        principalFaddeev d (-m) (-n) (-z) =
      (-1 : ℂ) ^ (m + n) * Complex.exp (-Real.pi * Complex.I * (d : ℂ) / 2) *
        Complex.exp (2 * Real.pi * Complex.I * principalFaddeevReflectionExponent d m n z) := by
  have hρpos : 0 < principalRoot d := principalRoot_pos d hd
  have hz₂ : (z / ρ ^ 2).im ≠ 0 := by
    simpa only [← Complex.ofReal_pow, Complex.div_ofReal_im] using
      div_ne_zero hz (pow_ne_zero 2 (ne_of_gt hρpos))
  have hz₁ : (z / ρ).im ≠ 0 := by
    simpa only [Complex.div_ofReal_im] using div_ne_zero hz (ne_of_gt hρpos)
  refine principalFaddeev_mul_neg_of_paths d hd m n z ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact FaddeevSRegularPath.of_im_ne_zero hρpos (fun j hj => by
      simpa [Complex.mul_im] using hz₂)
  · exact FaddeevSRegularPath.of_im_ne_zero hρpos (fun j hj => by
      simpa using hz₁)
  · exact FaddeevSRegularPath.of_im_ne_zero hρpos (fun j hj => by
      simpa [Complex.mul_im] using hz₁)
  · exact FaddeevSRegularPath.of_im_ne_zero hρpos (fun j hj => by
      simpa [Complex.mul_im] using hz)
  · convert faddeevS_denominator_ne_zero_of_im_ne_zero
      (-(z / ρ ^ 2 - n)) (principalRoot d) hρpos (by simpa using hz₂) using 1; ring_nf
  · convert faddeevS_denominator_ne_zero_of_im_ne_zero
      (-(z / ρ)) (principalRoot d) hρpos (by simpa using hz₁) using 1; ring_nf
  · convert faddeevS_denominator_ne_zero_of_im_ne_zero
      (-(z + m * ρ)) (principalRoot d) hρpos
      (by simpa [Complex.mul_im] using hz) using 1; ring_nf

end PrincipalReflection

end SIC

end
