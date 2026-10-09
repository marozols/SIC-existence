/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SpecialFunctions.Faddeev.Divisor
import SICs.SpecialFunctions.DoubleSine.Comparison
import SICs.SpecialFunctions.Faddeev.Modular
import SICs.SL2Z.WordPeriods
import SICs.Analysis.IdentityTheorem

/-!
# The Faddeev q-product and its modular product along a word

The generator as a q-product quotient and the modular cocycle factorization along a word of
letters `T^bS`.

This module follows [RW26, Radchenko, Wheeler (2026), equation (17), `eq:g2r`] and
Proposition 2(ii), `prop:prod.id.mod,fad`. Put `ϖ(z,τ)` for the q-product,
`j_B(τ)=cτ+d`, and `B·τ=(aτ+b)/(cτ+d)`.

## The argument

In the quotient defining `Φ_{AB,m,n}`, the q-product at the transported point `B(z;τ)` is
inserted once in the numerator and once in the denominator; it cancels when nonzero. For a
letter `T^b S`, its denominator is `τ` and its transported period is `b-1/τ`. Integer
periodicity in both arguments of `ϖ` identifies that letter's quotient with
`Φ_{S,0,0}(z+mτ-n;τ)`.

For a word `γ=(T^{b₁}S)γ'` with `γ'=∏_{j≥2}T^{b_j}S`, the cocycle with intermediate index
zero peels the first letter: `Φ_{γ,m,n}(z;τ)=Φ_{S,0,0}(z/j_{γ'}(τ)-n;γ'·τ)Φ_{γ',m,0}(z;τ)`.
Induction on the word gives equation (20) with every intermediate index zero. The q-product
cancelled at each step is the next letter's q-denominator, since `γ·τ=b₂-1/(γ''·τ)` for
`γ'=(T^{b₂}S)γ''`. At zeros of these denominators the raw quotients use Lean's totalized
division; the factorization holds as meromorphic germs at every base point, and along every
nonconstant affine real line almost everywhere.
-/

noncomputable section

open ModularGroup MatrixGroups Filter
open scoped MatrixGroups Topology

namespace SIC

/-! ### The generator as a q-product quotient

Shintani's product expression at `z+1` has exactly the normalization exponent used by the
Faddeev generator, so the exponentials cancel. Integer periodicity turns its first product into
`ϖ(z,τ)`, and its second is `ϖ(z/τ,-1/τ)`. Nonvanishing of the latter also excludes zeros of
the gamma denominator. This is [RW26, Radchenko, Wheeler (2026), equation (9),
`eq:prod.fadeev`] at `m=n=0`.
-/

/-- Nonvanishing of the second q-product excludes a zero of the Barnes denominator
used by `faddeevS_eq_qPochhammer_div`. -/
private theorem denominator_ne_zero_of_qPochhammer_ne_zero
    (z τ : ℂ) (hτ : 0 < τ.im)
    (hz : qPochhammer (z / τ) (-1 / τ) ≠ 0) :
    barnesDoubleGammaInv (1 + τ - (z + 1)) 1 τ ≠ 0 := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have hslit : τ ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hτ))
  intro hzero
  have hden : barnesDoubleGammaInv (τ - z) 1 τ = 0 := by
    simpa only [show 1 + τ - (z + 1) = τ - z by ring] using hzero
  obtain ⟨a, b, hzab⟩ := (faddeevS_denominator_eq_zero_iff z τ hslit).mp hden
  apply hz
  apply (qPochhammer_eq_zero_iff (z / τ) (-1 / τ)
    (neg_one_div_im_pos τ hτ)).mpr
  refine ⟨a, (b : ℤ) + 1, ?_⟩
  rw [hzab]
  push_cast
  field_simp [hτ0]
  ring

/-- For `Im τ > 0`, `Φ_{S,0,0}(z;τ) = ϖ(z,τ)/ϖ(z/τ,-1/τ)` wherever the
displayed denominator is nonzero. This is [RW26, Radchenko, Wheeler (2026),
equation (9), `eq:prod.fadeev`] at `m=n=0`, with the existing gamma normalization. -/
@[source "RW26, equation (9), p. 5, eq:prod.fadeev (m=n=0; nonzero denominator)"]
theorem faddeevS_eq_qPochhammer_div (z τ : ℂ) (hτ : 0 < τ.im)
    (hz : qPochhammer (z / τ) (-1 / τ) ≠ 0) :
    faddeevS z τ = qPochhammer z τ / qPochhammer (z / τ) (-1 / τ) := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have hf₂ : shintaniF2 (z + 1) τ ≠ 0 := by simpa [shintaniF2] using hz
  have hΓ : barnesDoubleGammaInv (1 + τ - (z + 1)) 1 τ ≠ 0 :=
    denominator_ne_zero_of_qPochhammer_ne_zero z τ hτ hz
  have hexp : sigmaSKoppExpArg (z + 1) τ = faddeevSExpArg z τ := by
    unfold sigmaSKoppExpArg
    rw [add_sub_cancel_right]
  rw [faddeevS,
    shintaniDoubleSineGamma_eq_product (z + 1) τ hτ hf₂ hΓ,
    shintaniDoubleSineProduct_eq_exp_sigmaSKoppExpArg (z + 1) τ hτ0,
    hexp, shintaniF1_add_one z τ]
  simp only [shintaniF1, shintaniF2]
  rw [show (z + 1 - 1) / τ = z / τ by ring]
  calc
    _ = (Complex.exp (faddeevSExpArg z τ) *
          Complex.exp (-faddeevSExpArg z τ)) *
          (qPochhammer z τ / qPochhammer (z / τ) (-1 / τ)) := by ring
    _ = _ := by rw [← Complex.exp_add]; simp

/-! ### The cocycle and one letter

The cocycle telescopes the middle q-product. A single `T^b S` letter changes the modulus by an
integer after inversion, and all of its integer index shifts can be moved through the product's
periodicity. -/

/-- The pointwise cocycle `Φ_{AB,m,n}(z;τ) = Φ_{A,k,n}(B(z;τ)) Φ_{B,m,k}(z;τ)`
on the domain where the inserted intermediate q-product is nonzero.
[RW26, Radchenko, Wheeler (2026), equation (17), `eq:g2r`]. -/
theorem faddeevModularUHP_mul (A B : SL(2, ℤ)) (m k n : ℤ) (z τ : ℂ)
    (hτ : 0 < τ.im)
    (hq : qPochhammer (z / fltDenominator (B : Mat(2, ℤ)) τ + k * flt (B : Mat(2, ℤ)) τ)
      (flt (B : Mat(2, ℤ)) τ) ≠ 0) :
    faddeevModularUHP (A * B) m n z τ =
      faddeevModularUHP A k n (z / fltDenominator (B : Mat(2, ℤ)) τ)
        (flt (B : Mat(2, ℤ)) τ) * faddeevModularUHP B m k z τ := by
  have hB := fltDenominator_ne_zero_of_im_ne_zero B hτ.ne'
  have harg : z / fltDenominator ((A * B : SL(2, ℤ)) : Mat(2, ℤ)) τ =
      (z / fltDenominator (B : Mat(2, ℤ)) τ) /
        fltDenominator (A : Mat(2, ℤ)) (flt (B : Mat(2, ℤ)) τ) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, fltDenominator_mul _ _ τ hB,
      div_eq_mul_inv, mul_inv_rev]
    ring
  unfold faddeevModularUHP
  rw [harg, Matrix.SpecialLinearGroup.coe_mul, flt_mul _ _ τ hB]
  conv_rhs => rw [mul_comm]
  exact (div_mul_div_cancel₀ hq).symm

/-- Integer periods identify the denominator of `Φ_{T^bS,m,n}(z;τ)` with that of
`Φ_{S,0,0}(z+mτ-n;τ)`; used by `faddeevModularUHP_letter`. -/
private theorem faddeevLetter_qPochhammer (b m n : ℤ) (z τ : ℂ) (hτ : τ ≠ 0) :
    qPochhammer
        (z / fltDenominator ((T ^ b * S : SL(2, ℤ)) : Mat(2, ℤ)) τ +
          n * flt ((T ^ b * S : SL(2, ℤ)) : Mat(2, ℤ)) τ)
        (flt ((T ^ b * S : SL(2, ℤ)) : Mat(2, ℤ)) τ) =
      qPochhammer ((z + m * τ - n) / τ) (-1 / τ) := by
  rw [fltDenominator_T_zpow_mul_S, flt_T_zpow_mul_S b hτ]
  rw [show (b : ℂ) - 1 / τ = -1 / τ + b by ring]
  have harg : z / τ + (n : ℂ) * (-1 / τ + b) =
      (z + m * τ - n) / τ + ((n * b - m : ℤ) : ℂ) := by
    push_cast
    field_simp
    ring
  rw [harg, qPochhammer_tau_add_intCast _ _ b,
    qPochhammer_add_intCast]

/-- For every integer `b`, the letter `T^bS` contributes
`Φ_{T^bS,m,n}(z;τ)=Φ_{S,0,0}(z+mτ-n;τ)` on the nonzero q-denominator domain.
This is the one-letter case of [RW26, Radchenko, Wheeler (2026), Proposition 2(ii),
`prop:prod.id.mod,fad`], with arbitrary `b` in place of the source's `b ≥ 2`. -/
theorem faddeevModularUHP_letter (b m n : ℤ) (z τ : ℂ) (hτ : 0 < τ.im)
    (hq : qPochhammer ((z + m * τ - n) / τ) (-1 / τ) ≠ 0) :
    faddeevModularUHP (T ^ b * S) m n z τ = faddeevS (z + m * τ - n) τ := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  rw [faddeevS_eq_qPochhammer_div _ _ hτ hq]
  unfold faddeevModularUHP
  rw [faddeevLetter_qPochhammer b m n z τ hτ0]
  have hnum : qPochhammer (z + m * τ - n) τ = qPochhammer (z + m * τ) τ := by
    calc
      _ = qPochhammer ((z + m * τ - n) + n) τ :=
        (qPochhammer_add_intCast _ _ n).symm
      _ = _ := by congr 1; ring
  rw [hnum]

/-! ### Words

The word product peels the first letter by the cocycle with intermediate index zero. Its
first letter never enters: the factor it contributes is `Φ_{S,0,0}(z₁-n;τ₁)`, with `τ₁` and
`z₁` determined by the remaining letters. -/

/-- The product `∏_{j=1}^r Φ_{S,0,0}(z_j+m_jτ_j-m_{j-1};τ_j)` of [RW26, Radchenko, Wheeler
(2026), Proposition 2(ii), `prop:prod.id.mod,fad`, equation (20), `eq:modulartofaddeevCF`] for
the letters `[b₁,…,b_r]`, with outer indices `m_r=m`, `m_0=n`, and every intermediate index
zero. With `γ'=∏_{j≥2}T^{b_j}S`, the first factor is `Φ_{S,0,0}(z/j_{γ'}(τ)-n;γ'·τ)`, since
`τ₁=γ'·τ` and `z₁=z/j_{γ'}(τ)`; the empty word takes the junk value `1`. Each factor is
`faddeevS`, defined at every complex period, so this is also the source's product at real
periods. -/
@[source "RW26, Proposition 2, p. 6, prop:prod.id.mod,fad (ii, intermediate indices zero)"
  (symbol := "Φ_{γ,m,n}(z;τ)")]
def faddeevWord : List ℤ → ℤ → ℤ → ℂ → ℂ → ℂ
  | [], _, _, _, _ => 1
  | [_], m, n, z, τ => faddeevS (z + m * τ - n) τ
  | _ :: b :: bs, m, n, z, τ =>
      faddeevS (z / fltDenominator (letterWord (b :: bs) : Mat(2, ℤ)) τ - n)
          (flt (letterWord (b :: bs) : Mat(2, ℤ)) τ) *
        faddeevWord (b :: bs) m 0 z τ

/-- A one-letter word contributes a single Faddeev factor. -/
@[simp]
theorem faddeevWord_singleton (b m n : ℤ) (z τ : ℂ) :
    faddeevWord [b] m n z τ = faddeevS (z + m * τ - n) τ := rfl

/-- Peeling the first letter of `faddeevWord`; see that declaration for the source. -/
theorem faddeevWord_cons_cons (a b : ℤ) (bs : List ℤ) (m n : ℤ) (z τ : ℂ) :
    faddeevWord (a :: b :: bs) m n z τ =
      faddeevS (z / fltDenominator (letterWord (b :: bs) : Mat(2, ℤ)) τ - n)
          (flt (letterWord (b :: bs) : Mat(2, ℤ)) τ) *
        faddeevWord (b :: bs) m 0 z τ := rfl

/-- For a nonempty word and `τ∈ℍ`, the modular product `Φ_{γ,m,n}(·;τ)` at
`γ=∏_j T^{b_j}S` and the word product `faddeevWord` have the same meromorphic germ at every
complex `z`. This is [RW26, Radchenko, Wheeler (2026), Proposition 2(ii),
`prop:prod.id.mod,fad`, equation (20), `eq:modulartofaddeevCF`] with every intermediate index
zero, for arbitrary integer letters, although the source assumes `b_j ≥ 2`. Common zeros of
the cancelled q-products do not affect the germ. -/
@[source "RW26, equation (20), p. 7, eq:modulartofaddeevCF (intermediate indices zero, Im τ > 0)"]
theorem faddeevModularUHP_eventuallyEq_faddeevWord (bs : List ℤ) (hbs : bs ≠ [])
    (m n : ℤ) (z τ : ℂ) (hτ : 0 < τ.im) :
    (fun w => faddeevModularUHP (letterWord bs) m n w τ) =ᶠ[𝓝[≠] z]
      (fun w => faddeevWord bs m n w τ) := by
  induction bs generalizing n with
  | nil => exact (hbs rfl).elim
  | cons a bs ih =>
    cases bs with
    | nil =>
      have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
      have harg (w : ℂ) : (w + m * τ - n) / τ = w / τ + (m - n / τ) := by
        field_simp [hτ0]
        ring
      have hq := eventually_qPochhammer_div_add_ne_zero τ (m - n / τ)
        (-1 / τ) z hτ0 (neg_one_div_im_pos τ hτ)
      filter_upwards [hq] with w hw
      rw [letterWord_singleton, faddeevWord_singleton]
      exact faddeevModularUHP_letter a m n w τ hτ (harg w ▸ hw)
    | cons b bs =>
      let B : SL(2, ℤ) := letterWord (b :: bs)
      let ε : ℂ := fltDenominator (B : Mat(2, ℤ)) τ
      let σ : ℂ := flt (B : Mat(2, ℤ)) τ
      have hε : ε ≠ 0 := fltDenominator_ne_zero_of_im_ne_zero B hτ.ne'
      have hσ : 0 < σ.im := flt_im_pos B hτ
      have hσ0 : σ ≠ 0 := fun h => by simp [h] at hσ
      have harg (w : ℂ) : (w / ε - n) / σ =
          w / (ε * σ) + (-n / σ) := by
        field_simp [hε, hσ0]
        ring
      have hmid := eventually_qPochhammer_div_add_ne_zero ε 0 σ z hε hσ
      have hletter := eventually_qPochhammer_div_add_ne_zero (ε * σ) (-n / σ)
        (-1 / σ) z (mul_ne_zero hε hσ0) (neg_one_div_im_pos σ hσ)
      have htail := ih (by simp) 0
      filter_upwards [hmid, hletter, htail] with w hw₁ hw₂ hw₃
      rw [letterWord_cons, faddeevWord_cons_cons]
      rw [faddeevModularUHP_mul (T ^ a * S) B m 0 n w τ hτ (by
        simpa only [B, ε, σ, Int.cast_zero, zero_mul, add_zero] using hw₁)]
      rw [faddeevModularUHP_letter a 0 n (w / ε) σ hσ (by
        simpa only [Int.cast_zero, zero_mul, add_zero, harg] using hw₂)]
      simpa only [B, ε, σ, Int.cast_zero, zero_mul, add_zero] using
        congrArg (fun v => faddeevS (w / ε - n) σ * v) hw₃

/-- Along `z=a t+b`, `a≠0`, the modular product at a nonempty word equals the word product
for almost every real `t`, at each fixed `τ∈ℍ`. This is the contour form of
`faddeevModularUHP_eventuallyEq_faddeevWord`: the two sides differ only on a countable set. -/
theorem ae_faddeevModularUHP_eq_faddeevWord (bs : List ℤ) (hbs : bs ≠ []) (m n : ℤ)
    (τ a b : ℂ) (hτ : 0 < τ.im) (ha : a ≠ 0) :
    ∀ᵐ t : ℝ, faddeevModularUHP (letterWord bs) m n (a * (t : ℂ) + b) τ =
      faddeevWord bs m n (a * (t : ℂ) + b) τ := by
  exact ae_eq_comp_affine_of_forall_eventuallyEq_nhdsNE
    (fun z => faddeevModularUHP_eventuallyEq_faddeevWord bs hbs m n z τ hτ) a b ha

end SIC
