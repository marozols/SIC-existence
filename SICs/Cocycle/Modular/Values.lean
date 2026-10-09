/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Cocycle.Word.Basic

/-!
# Real Shintani--Faddeev modular values

Real modular cocycle values, orientation, inverse APIs, and finite-factor nonvanishing.

This is [AFK25, Definition 1.18, `def:shin`, equation (1.26), `eq:shindf`], using the
finite canonical word at real arguments. The membership `M ∈ Γ_r` makes the finite-product
index integral. Inverse orientation extends evaluation to arbitrary matrices; it uses
the reciprocal value at the inverse image, as in Lemma 2.13, `lm:sfam1sfaeq1`.

The source's real domain requires a positive Jacobi denominator. At an irrational point,
a nonintegral characteristic avoids the lattice and the zeros of the finite denominator.
For an integral characteristic, the raw quotient may instead evaluate an identically vanishing
factor. The shift identities in [72, Kopp (2024), Proposition 4.35, `prop:invariance`] express
the regularized value using the zero-characteristic word and finite products with that factor
removed. Crossing from second coordinate $0$ to $1$ contributes the Jacobi denominator;
the remaining shifts contribute finite-product ratios. At a fixed point equal finite factors
are cancelled before evaluation, leaving just that Jacobi factor when the second coordinate
is positive. This agrees with the source's zero-characteristic convention and makes the
identity value $1$ at every input. No agreement with meromorphic continuation at other rational
removable singularities is asserted here.
The real word formula does not itself construct the source's meromorphic continuation.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### The cocycle

The real modular-cocycle value combines the word-chained Jacobi factor with the finite
`q`-Pochhammer correction of [AFK25, equation (1.26), `eq:shindf`], regularized for integral
characteristics by the shift identities of [72, Kopp (2024), Proposition 4.35, `prop:invariance`].
Membership in `Γ_r` remains explicit so every term has its source interpretation. -/

/-- The finite correction from the zero characteristic to an integral characteristic with
second coordinate $k$, obtained by iterating the shift identities in
[72, Kopp (2024), Proposition 4.35, `prop:invariance`]. With $\tau'=M\tau$ and $j=j_M(\tau)$,
it is $j\,\varpi_{k-1}(\tau,\tau)/\varpi_{k-1}(\tau',\tau')$ for $k>0$, and
$\varpi_{-k}(k\tau',\tau')/\varpi_{-k}(k\tau,\tau)$ otherwise. The factor that vanishes
identically at the shift from $0$ to $1$ has already been cancelled, leaving $j$.
On the diagonal $\tau'=\tau$, equal finite factors are cancelled before evaluation. This
also preserves the identity-matrix value at rational inputs; it asserts no comparison with
meromorphic continuation at other rational removable singularities. The shift factors use
$1-e(x)$ as in the source's displayed cocycle ratio; the preceding sentence of its proof
incorrectly prints $1+e(x)$. -/
def sfIntegralCorrection (k : ℤ) (τ τ' j : ℝ) : ℂ :=
  if τ' = τ then (if 0 < k then (j : ℂ) else 1)
  else if 0 < k then
    (j : ℂ) * qPochhammerFin (k - 1) τ τ / qPochhammerFin (k - 1) τ' τ'
  else
    qPochhammerFin (-k) ((k : ℂ) * τ') τ' /
      qPochhammerFin (-k) ((k : ℂ) * τ) τ

/-- At zero shift, the integral correction is $1$. -/
@[simp] theorem sfIntegralCorrection_zero (τ τ' j : ℝ) :
    sfIntegralCorrection 0 τ τ' j = 1 := by
  simp [sfIntegralCorrection, qPochhammerFin]

/-- At a fixed point the finite correction is $j$ for $k>0$ and $1$ otherwise. -/
@[simp] theorem sfIntegralCorrection_self (k : ℤ) (τ j : ℝ) :
    sfIntegralCorrection k τ τ j = if 0 < k then (j : ℂ) else 1 := by
  simp [sfIntegralCorrection]

open scoped Classical in
/-- **The Shintani--Faddeev modular cocycle at a real argument**, [AFK25, Definition 1.18,
`def:shin`, equation (1.26), `eq:shindf`]:
```
ש^r_M(τ) = σ_M(⟨⟨r,τ⟩⟩, τ) / ϖ_{n_QP(r,M)}(⟨⟨r,τ⟩⟩ / j_M(τ), M·τ).
```
For $r\notin\mathbb Z^2$ this is the raw word quotient displayed above. For integral $r$,
the zero-characteristic word is multiplied by `sfIntegralCorrection` with $k=r_1$ (the
paper's $r_2$). This cancels the identically vanishing factor before evaluating the integral
characteristic, following [72, Kopp (2024), Proposition 4.35, `prop:invariance`]. In particular,
the zero characteristic remains `wordSigmaS 0 τ M h0`.

`hM` carries the source hypothesis $M\in\Gamma_r$; `h0` is the word algorithm's hypothesis.
The source domain on the real line is described by `mem_sfDomain_ofReal_iff`. -/
@[source "AFK25, Definition 1.18, p. 11, def:shin" (symbol := "ש^r_M(τ)")]
def sfModularCocycleReal (r : Fin 2 → ℚ) (M : SL(2, ℤ))
    (_hM : M ∈ gammaSubgroup r) (h0 : 0 ≤ M 1 0) (τ : ℝ) : ℂ :=
  if IsIntegralIndex r then
    wordSigmaS 0 τ M h0 * sfIntegralCorrection (r 1).num τ
      (flt (M : Mat(2, ℤ)) τ)
      (fltDenominator (M : Mat(2, ℤ)) τ)
  else
    wordSigmaS (fracSymplecticFormRat r τ) τ M h0 /
      qPochhammerFin (nQPInt r (M : Mat(2, ℤ)))
        (((fracSymplecticFormRat r τ : ℝ) : ℂ) /
          ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ))
        (((flt (M : Mat(2, ℤ)) τ : ℝ) : ℂ))

/-- For a nonintegral characteristic the real cocycle is the raw word quotient in
`sfModularCocycleReal`. -/
theorem sfModularCocycleReal_eq_of_not_isIntegralIndex {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hr : ¬ IsIntegralIndex r)
    (hM : M ∈ gammaSubgroup r) (h0 : 0 ≤ M 1 0) (τ : ℝ) :
    sfModularCocycleReal r M hM h0 τ =
      wordSigmaS (fracSymplecticFormRat r τ) τ M h0 /
        qPochhammerFin (nQPInt r (M : Mat(2, ℤ)))
          (((fracSymplecticFormRat r τ : ℝ) : ℂ) /
            ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ))
          (((flt (M : Mat(2, ℤ)) τ : ℝ) : ℂ)) := by
  rw [sfModularCocycleReal, ite_eq_right hr]

/-- At an integral characteristic the real cocycle is the zero word times the regularized
finite correction of `sfIntegralCorrection`. -/
theorem sfModularCocycleReal_of_isIntegralIndex {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hr : IsIntegralIndex r)
    (hM : M ∈ gammaSubgroup r) (h0 : 0 ≤ M 1 0) (τ : ℝ) :
    sfModularCocycleReal r M hM h0 τ = wordSigmaS 0 τ M h0 *
      sfIntegralCorrection (r 1).num τ (flt (M : Mat(2, ℤ)) τ)
        (fltDenominator (M : Mat(2, ℤ)) τ) := by
  rw [sfModularCocycleReal, ite_eq_left hr]

/-- The zero characteristic is the uncorrected zero word value. -/
@[simp] theorem sfModularCocycleReal_zero {M : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup 0) (h0 : 0 ≤ M 1 0) (τ : ℝ) :
    sfModularCocycleReal 0 M hM h0 τ = wordSigmaS 0 τ M h0 := by
  have hr : IsIntegralIndex 0 := fun _ => ⟨0, rfl⟩
  simp [sfModularCocycleReal_of_isIntegralIndex hr]

/-- At an integral characteristic and a fixed point, the shift correction multiplies the zero
word by $j_M(\tau)$ exactly when $r_1>0$ (the paper's $r_2>0$). This is the regularized
shift relation of [72, Kopp (2024), Proposition 4.35, `prop:invariance`]. -/
theorem sfModularCocycleReal_integral_of_flt_eq_self
    {r : Fin 2 → ℚ} {M : SL(2, ℤ)} (hr : IsIntegralIndex r)
    (hM : M ∈ gammaSubgroup r) (h0 : 0 ≤ M 1 0) {τ : ℝ}
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) :
    sfModularCocycleReal r M hM h0 τ = wordSigmaS 0 τ M h0 *
      (if 0 < r 1 then (fltDenominator (M : Mat(2, ℤ)) τ : ℂ) else 1) := by
  simp [sfModularCocycleReal_of_isIntegralIndex hr, hfix, Rat.num_pos]

/-- The identity matrix has value $1$ for every characteristic and real argument, including
integral characteristics where equal finite factors are cancelled in `sfIntegralCorrection`. -/
@[simp] theorem sfModularCocycleReal_one (r : Fin 2 → ℚ)
    (hM : (1 : SL(2, ℤ)) ∈ gammaSubgroup r)
    (h0 : 0 ≤ (1 : SL(2, ℤ)) 1 0) (τ : ℝ) :
    sfModularCocycleReal r 1 hM h0 τ = 1 := by
  have hz : (1 : SL(2, ℤ)) 1 0 = 0 := by simp
  simp [sfModularCocycleReal, wordSigmaS_of_lowerLeft_eq_zero _ _ _ _ hz,
    flt_one, fltDenominator_one, nQPInt, nQP, qPochhammerFin]

/-- **The nonintegral defining equation with a caller-supplied index.** Consumers identifying
`n_QP(r,M)` in closed form (the principal family's `-ℓ = q - (d-2)p`, say) can rewrite with their
own integer, without unfolding `nQPInt`: any `n` casting to `n_QP(r,M)` *is* `nQPInt r M`, since
`Rat.num` is determined by the value. -/
theorem sfModularCocycleReal_eq_of_nQP {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hr : ¬ IsIntegralIndex r)
    (hM : M ∈ gammaSubgroup r) (h0 : 0 ≤ M 1 0) (τ : ℝ) {n : ℤ}
    (hn : (n : ℚ) = nQP r (M : Mat(2, ℤ))) :
    sfModularCocycleReal r M hM h0 τ =
      wordSigmaS (fracSymplecticFormRat r τ) τ M h0 /
        qPochhammerFin n
          (((fracSymplecticFormRat r τ : ℝ) : ℂ) /
            ((fltDenominator (M : Mat(2, ℤ)) τ : ℝ) : ℂ))
          (((flt (M : Mat(2, ℤ)) τ : ℝ) : ℂ)) := by
  have : nQPInt r (M : Mat(2, ℤ)) = n := by
    rw [nQPInt, ← hn, Rat.num_intCast]
  rw [sfModularCocycleReal_eq_of_not_isIntegralIndex hr, this]

/-! ### The value at an inverse matrix

The inverse value is defined by the reciprocal relation of [AFK25, Lemma 2.13,
`lm:sfam1sfaeq1`]. The total cocycle chooses between a matrix and its inverse according to the
sign of its lower-left entry. -/

/-- **The Shintani--Faddeev modular cocycle at an inverse matrix**, `ש^r_{M⁻¹}(τ)`, on the real
line:
```
ש^r_{M⁻¹}(τ) = (ש^r_M(M⁻¹·τ))⁻¹,
```
which is [AFK25, Lemma 2.13, `lm:sfam1sfaeq1`, equation (2.40), `eq:cocyclerelinv`] read as a
definition. Indexed by `M`, not by `M⁻¹`, since `M` is the matrix carrying the hypotheses.

The recursive product `wordSigmaS` requires `0 ≤ M 1 0`. By `SL2Z.lowerLeft_inv`,
`M⁻¹` has negative lower-left entry when `M` has positive lower-left entry. The reciprocal
formula therefore defines the value for the opposite orientation. At irrational fixed points
with nonintegral characteristic and positive Jacobi denominator,
`tendsto_sfPeriodProduct_div_total` in `SICs.Cocycle.Conjugation` identifies this value with the
boundary limit of the period-product quotient.

`hM` is `sfModularCocycleReal`'s hypothesis for `M`; it also gives the hypothesis for
`M⁻¹`, since `Γ_r` is closed under inversion
(`SICs.SL2Z.Characteristics.inv_mem_gammaSubgroup`). As in `sfModularCocycleReal`, definedness
at `τ` is not built in. -/
def sfModularCocycleRealInv (r : Fin 2 → ℚ) (M : SL(2, ℤ))
    (hM : M ∈ gammaSubgroup r) (h0 : 0 ≤ M 1 0) (τ : ℝ) : ℂ :=
  (sfModularCocycleReal r M hM h0
    (flt ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) τ))⁻¹

/-- **At a fixed point of `M`, the inverse value is the plain reciprocal.** `M⁻¹` fixes whatever
`M` fixes (`SICs.SL2Z.FractionalLinear.flt_inv_of_flt_eq_self`), so the transported
argument `M⁻¹·τ` collapses to `τ`. This is the form [AFK25, Corollary 2.12, `cor:funchar`]'s
hypothesis puts one in, and the form `AdmissibleTuple.shiftConvolutionSum` needs, since it
evaluates both matrices at the real quadratic fixed point `ρ_t`. -/
theorem sfModularCocycleRealInv_of_flt_eq_self {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup r) (h0 : 0 ≤ M 1 0) {τ : ℝ}
    (hτ : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) :
    sfModularCocycleRealInv r M hM h0 τ = (sfModularCocycleReal r M hM h0 τ)⁻¹ := by
  rw [sfModularCocycleRealInv, flt_inv_of_flt_eq_self hτ hfix]

/-! ### The cocycle at an arbitrary `M ∈ Γ_r`

`0 ≤ M 1 0` is not a hypothesis of [AFK25, Definition 1.18, `def:shin`] — it is an artefact of the
Hirzebruch--Jung decomposition, and by `SL2Z.lowerLeft_inv` it fails for exactly one of `M`, `M⁻¹`
whenever it holds strictly for the other. Since `sfModularCocycleRealInv` already supplies the value
on the failing side, the two branches assemble into a definition with no sign hypothesis. This
is what [AFK25, Definition 1.34, `dfn:shift`]'s convolution sum needs: it evaluates `ש` at both
`A_t` and `A_t⁻¹`, and for an arbitrary admissible tuple the sign of `A_t 1 0` is the sign of the
form's
leading coefficient `a`, which [AFK25, §1.3] does not normalize. -/

/-- **Transporting the value along an equality of matrices.** The hypotheses of
`sfModularCocycleReal` are `Prop`s, so once the matrices are identified proof irrelevance closes
the goal; without this the `(M⁻¹)⁻¹ = M` rewrite below hits a motive that does not typecheck. -/
lemma sfModularCocycleReal_congr {r : Fin 2 → ℚ} {M N : SL(2, ℤ)} (hMN : M = N)
    (hM : M ∈ gammaSubgroup r) (h0 : 0 ≤ M 1 0)
    (hN : N ∈ gammaSubgroup r) (h0' : 0 ≤ N 1 0) (τ : ℝ) :
    sfModularCocycleReal r M hM h0 τ = sfModularCocycleReal r N hN h0' τ := by
  subst hMN; rfl

/-- **`ש^r_M(τ)` on the real line for *every* `M ∈ Γ_r`**, `sfModularCocycleReal` with no sign
restriction: the word value where the word walk applies, and the
`sfModularCocycleRealInv` value at `M⁻¹`'s walk where it does not. The two branches are the same
mathematical object — the second is `sfModularCocycleRealInv` read at
`M⁻¹` — so this adds no hypothesis to the source's definition.

At `M 1 0 = 0`, both `M` and `M⁻¹` admit a word decomposition, and the definition chooses
`M` directly. The reciprocal identity is stated for `M 1 0 ≠ 0` in
`sfModularCocycleRealTotal_inv_of_lowerLeft_ne_zero`, corresponding to [AFK25, Lemma 2.13,
`lm:sfam1sfaeq1`]. This nonzero condition holds for associated stabilizers by
`IsAssociatedStabilizerPair.lowerLeft_A_ne_zero` in `SICs.Admissible.StabilizerDomain`.
-/
def sfModularCocycleRealTotal (r : Fin 2 → ℚ) (M : SL(2, ℤ))
    (hM : M ∈ gammaSubgroup r) (τ : ℝ) : ℂ :=
  if h : 0 ≤ M 1 0 then
    sfModularCocycleReal r M hM h τ
  else
    (sfModularCocycleReal r M⁻¹ (inv_mem_gammaSubgroup hM)
      (by rw [SL2Z.lowerLeft_inv]; omega) (flt (M : Mat(2, ℤ)) τ))⁻¹

/-- Where the lower-left entry is nonnegative, the total cocycle equals the direct
word-product value. -/
theorem sfModularCocycleRealTotal_of_nonneg {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup r) (h0 : 0 ≤ M 1 0) (τ : ℝ) :
    sfModularCocycleRealTotal r M hM τ = sfModularCocycleReal r M hM h0 τ :=
  dite_eq_left h0

/-- **And at `M⁻¹` it is `sfModularCocycleRealInv`.** Indexed by `M`, matching this section's
convention that `M` carries the hypotheses. `0 < M 1 0` is strict: at `M 1 0 = 0` the total
cocycle takes the direct word product for `M⁻¹`, so this branch identity does not apply. -/
theorem sfModularCocycleRealTotal_inv {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup r) (h0 : 0 < M 1 0) (τ : ℝ) :
    sfModularCocycleRealTotal r M⁻¹ (inv_mem_gammaSubgroup hM) τ =
      sfModularCocycleRealInv r M hM h0.le τ := by
  rw [sfModularCocycleRealTotal, dite_eq_right (by rw [SL2Z.lowerLeft_inv]; omega),
    sfModularCocycleRealInv]
  congr 1
  exact sfModularCocycleReal_congr (inv_inv M) _ _ _ _ _

/-- **At a fixed point of `M` the two values are reciprocal.** The form
`AdmissibleTuple.shiftConvolutionSum` needs at `τ = ρ_t`, stated for the total cocycle. -/
theorem sfModularCocycleRealTotal_inv_of_flt_eq_self {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup r) (h0 : 0 < M 1 0) {τ : ℝ}
    (hden : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) :
    sfModularCocycleRealTotal r M⁻¹ (inv_mem_gammaSubgroup hM) τ =
      (sfModularCocycleRealTotal r M hM τ)⁻¹ := by
  rw [sfModularCocycleRealTotal_inv hM h0,
    sfModularCocycleRealInv_of_flt_eq_self hM h0.le hden hfix,
    sfModularCocycleRealTotal_of_nonneg hM h0.le]

/-- **Transporting the total value along an equality of matrices**, the `sfModularCocycleRealTotal`
counterpart of `sfModularCocycleReal_congr` and needed for the same `(M⁻¹)⁻¹ = M` rewrite. -/
lemma sfModularCocycleRealTotal_congr {r : Fin 2 → ℚ} {M N : SL(2, ℤ)} (hMN : M = N)
    (hM : M ∈ gammaSubgroup r)
    (hN : N ∈ gammaSubgroup r) (τ : ℝ) :
    sfModularCocycleRealTotal r M hM τ = sfModularCocycleRealTotal r N hN τ := by
  subst hMN; rfl

/-- **Transporting the total value along an equality of characteristics**, the counterpart of
`sfModularCocycleRealTotal_congr` in `r`: the membership proof is a dependent argument, so a
characteristic rewrite such as `R(-r) = -(Rr)` goes through this lemma. -/
lemma sfModularCocycleRealTotal_congr_index {r s : Fin 2 → ℚ} (hrs : r = s)
    {M : SL(2, ℤ)} (hM : M ∈ gammaSubgroup r)
    (hM' : M ∈ gammaSubgroup s) (τ : ℝ) :
    sfModularCocycleRealTotal r M hM τ = sfModularCocycleRealTotal s M hM' τ := by
  subst s; rfl

/-- **The inverse relation for the total cocycle at a fixed point**, for `M 1 0 ≠ 0`:
`ש^r_{M⁻¹}(τ) = (ש^r_M(τ))⁻¹`. For `0 < M 1 0` it is `sfModularCocycleRealTotal_inv_of_flt_eq_self`;
the negative case is the positive one applied at `M⁻¹`, whose Jacobi denominator is nonzero
because at a fixed point the two denominators multiply to `1`.

The condition `M 1 0 ≠ 0` excludes exactly `M = ±T^k`, where `M` and `M⁻¹` both have a word
walk and the identity becomes the inverse relation used to define `sfModularCocycleRealInv`, which
this theorem does not cover. For associated stabilizers the hypothesis is automatic:
`SICs.Admissible.StabilizerDomain`'s `IsAssociatedStabilizerPair.lowerLeft_A_ne_zero`. -/
theorem sfModularCocycleRealTotal_inv_of_lowerLeft_ne_zero {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup r)
    (h0 : (M : Mat(2, ℤ)) 1 0 ≠ 0) {τ : ℝ}
    (hden : fltDenominator (M : Mat(2, ℤ)) τ ≠ 0)
    (hfix : flt (M : Mat(2, ℤ)) τ = τ) :
    sfModularCocycleRealTotal r M⁻¹ (inv_mem_gammaSubgroup hM) τ =
      (sfModularCocycleRealTotal r M hM τ)⁻¹ := by
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · have hinvpos : 0 < ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) 1 0 := by
      rw [SL2Z.lowerLeft_inv]; omega
    have hfix' : flt ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) τ = τ :=
      flt_inv_of_flt_eq_self hden hfix
    have hden' : fltDenominator ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) τ ≠ 0 := by
      intro h
      have hmul := fltDenominator_inv_mul_self_of_flt_eq_self hden hfix
      rw [h, zero_mul] at hmul
      exact zero_ne_one hmul
    have h := sfModularCocycleRealTotal_inv_of_flt_eq_self (inv_mem_gammaSubgroup hM)
      hinvpos hden' hfix'
    rw [sfModularCocycleRealTotal_congr (inv_inv M) _ hM] at h
    rw [h, inv_inv]
  · exact sfModularCocycleRealTotal_inv_of_flt_eq_self hM hpos hden hfix

/-! ### A value that is total in the matrix

[AFK25, Definition 1.34, `dfn:shift`]'s convolution sum evaluates `ש^r_M(ρ_t)` once per class of a
transversal of `(ℤ/dℤ)²`, at a different index `r = q/d` for each summand. Every declaration above
takes `M ∈ Γ_r` as an argument, as [AFK25, Definition 1.18, `def:shin`] does, so a sum written
directly against them would have to carry that proof under the summation sign, once per class.

`sfModularCocycleReal'` removes the argument by returning `0` off `Γ_r`. The junk branch is
never a value of the source's cocycle -- outside `Γ_r` the source defines none -- and it is not
a totalization at a pole: it is the same device by which `doubleSine'` from
`SICs.SpecialFunctions.DoubleSine.RealIntegral` and `SICs.Cocycle.SigmaS.Basic.sigmaS` are total
outside their analytic domains. Consumers discharge membership once, for the matrix at hand, and
rewrite with `sfModularCocycleReal'_of_mem`; for the level generator of an admissible tuple that
membership is `IsAssociatedStabilizerPair.A_mem_gammaSubgroup` of
`SICs.Admissible.AssociatedStabilizers`. -/

open scoped Classical in
/-- **`ש^r_M(τ)` as a total function of `M`**: the value of `sfModularCocycleRealTotal` on `Γ_r`,
and `0` off it. See the section comment for why the junk branch is harmless and how consumers
avoid it. -/
noncomputable def sfModularCocycleReal' (r : Fin 2 → ℚ) (M : SL(2, ℤ)) (τ : ℝ) : ℂ :=
  if h : M ∈ gammaSubgroup r then
    sfModularCocycleRealTotal r M h τ
  else 0

/-- **On `Γ_r` the total function is the cocycle.** The rewrite every consumer of
`sfModularCocycleReal'` uses to leave the junk branch behind. -/
theorem sfModularCocycleReal'_of_mem {r : Fin 2 → ℚ} {M : SL(2, ℤ)}
    (hM : M ∈ gammaSubgroup r) (τ : ℝ) :
    sfModularCocycleReal' r M τ = sfModularCocycleRealTotal r M hM τ :=
  dite_eq_left hM

/-! ### The finite factor at an irrational point

At an irrational real point, a nonintegral characteristic keeps the finite `q`-Pochhammer factor
of [AFK25, equation (1.26), `eq:shindf`] away from its zeros, so the raw word quotient of
`sfModularCocycleReal` never divides by zero there. -/

/-- **A nonintegral characteristic keeps the finite factor of [AFK25, equation (1.26),
`eq:shindf`] nonzero at an irrational real point.** For any integer matrix with `j_M(τ) ≠ 0`, an
irrational real `τ`, and `r ∈ ℚ² ∖ ℤ²`,

$$\varpi_{n_{QP}(r,M)}\!\left(\frac{\langle\langle r,\tau\rangle\rangle}{j_M(\tau)},
  M\cdot\tau\right) \ne 0 .$$

A vanishing factor would put the argument `⟨⟨r,τ⟩⟩/j_M(τ)` on the lattice `ℤ(M·τ) + ℤ`, which
`sigmaSLatticeFree_fracSymplecticFormRat_div` excludes. It needs neither `M ∈ Γ_r` nor a
fixed point: the index `n_QP(r,M)` only selects which finitely many lattice points are tested.
It discharges the limit point's hypothesis in `SICs.Cocycle.ModularBoundary`'s boundary
comparison. -/
theorem qPochhammerFin_nQPInt_ne_zero_of_irrational {r : Fin 2 → ℚ} (hr : ¬ IsIntegralIndex r)
    (M : Mat(2, ℤ)) {τ : ℝ} (hτ : Irrational τ)
    (hden : fltDenominator M τ ≠ 0) :
    qPochhammerFin (nQPInt r M)
        (((fracSymplecticFormRat r τ : ℝ) : ℂ) / ((fltDenominator M τ : ℝ) : ℂ))
        (((flt M τ : ℝ) : ℂ)) ≠ 0 := by
  have hlat := sigmaSLatticeFree_fracSymplecticFormRat_div hτ hr M hden
  rw [← Complex.ofReal_div]
  refine qPochhammerFin_ne_zero_of_forall_ne_int _ _ _ fun k _ m hkm => ?_
  exact hlat (-k) m (by push_cast; linarith)

end SIC

end
