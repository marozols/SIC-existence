/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quadratic.FormOrders
import SICs.Quadratic.FundamentalForms

/-!
# The canonical representation of a quadratic order by form stabilizers

The representation `χ_Q` of the order of `disc(Q)` for every primitive form, with `S(Q) ∩ SL₂(ℤ)`
as the image of the norm-one units and the level condition read in the order.

This file formalizes the image statements of [AFK25, Theorem 4.34, `tm:canisointun`] and
[AFK25, Corollary 4.35, `cr:etaqmodn`] for an arbitrary primitive form, generalizing the monic
coordinates of `SICs.Quadratic.FormOrders`.

## Mathematical argument

Let `Q = ⟨a,b,c⟩` be an integral form of discriminant `Δ = b² - 4ac`. The order of discriminant
`Δ` is `ℤ[ω]` with `ω = (Δ + √Δ)/2`; when `Δ = f²Δ₀` with `Δ₀` fundamental it is the order
`𝒪_f = ℤ[f(Δ₀ + √Δ₀)/2]` of [AFK25, Definition 4.11, `df:ofufdef`], because
`ω = fΔ₀(f-1)/2 + f(Δ₀ + √Δ₀)/2` and `f(f-1)/2` is a rational integer.

The canonical representation of [AFK25, Definition 4.32, `df:etaq`] sends `x + y√Δ₀` to
`xI + (2y/f)SQ`. In the coordinates `x + yω` it becomes `χ_Q(x + yω) = xI + yN`, where

```text
N = (ΔI + 2SQ)/2 = [[(Δ-b)/2, -c], [a, (Δ+b)/2]].
```

`N` is integral because `Δ = b² - 4ac ≡ b (mod 2)`. It has trace `Δ` and determinant
`(Δ² - Δ)/4`, so Cayley--Hamilton gives `N² = ΔN - ((Δ²-Δ)/4)I`, which is exactly the relation
satisfied by `ω`. Hence `χ_Q` is a ring homomorphism, and its determinant is the norm.

The three off-diagonal and diagonal-difference entries of `χ_Q(x + yω)` are `ya`, `-yc` and
`yb`, and its lower-right entry is `x + y(Δ+b)/2`. For a primitive form `Q`:

* **Image.** The image of `χ_Q` is exactly the integral matrices commuting with `SQ`. The
  commutant side is already available as `IsPrimitive.commute_twiceSQ_iff`, whose coordinates
  `(t, n)` are `t = 2x + yΔ` and `n = y`.
* **Congruences** [AFK25, Corollary 4.35, `cr:etaqmodn`]. `k ∣ χ_Q(z)` entrywise iff `k ∣ z` in
  the order: primitivity of `Q` turns `k ∣ ya, yb, yc` into `k ∣ y`.
* **Units** [AFK25, Theorem 4.34(2), `tm:canisointun`]. `det χ_Q(z) = Nm(z)`, so the norm-one
  units of the order correspond to the determinant-one stabilizers `S(Q) ∩ SL₂(ℤ)`, and the
  congruence statement cuts this down to the level group `S_d(Q)`.

Because the order and the congruence criterion depend on `Q` only through `Δ`, the resulting
isomorphism `S_d(Q) ≃ S_d(Q')` for two primitive forms of the same discriminant lets a statement
about `S_d` be checked on the principal form `⟨1, -Δ, (Δ²-Δ)/4⟩`, where the monic API of
`SICs.Quadratic.FormOrders` applies.

## References

- [AFK25, Definition 4.32, `df:etaq`] for `χ_Q`
- [AFK25, Theorem 4.34, `tm:canisointun`] for the order and unit isomorphisms
- [AFK25, Corollary 4.35, `cr:etaqmodn`] for the congruence criterion
-/

open scoped MatrixGroups

namespace SIC.BinaryQF

/-! ### The order of the discriminant

The discriminant of an integral form is `0` or `1` modulo `4`, so the principal form
`⟨1, -Δ, (Δ²-Δ)/4⟩` of `SICs.Quadratic.FundamentalForms` has discriminant `Δ` and its monic
coordinate ring is the order of discriminant `Δ`. -/

/-- The discriminant of an integral binary form is `0` or `1` modulo `4`. -/
lemma disc_emod_four (Q : BinaryQF) : Q.disc % 4 = 0 ∨ Q.disc % 4 = 1 := by
  simp [disc, discrim, Int.sub_emod, Int.mul_emod, Int.sq_emod_four]
  omega

/-- The order `ℤ[(Δ + √Δ)/2]` of discriminant `Δ = disc(Q)`, as the monic coordinate ring of the
principal form of that discriminant. When `disc(Q) = f²Δ₀` with `Δ₀` fundamental this is the
order `𝒪_f` of [AFK25, Definition 4.11, `df:ofufdef`], on which
[AFK25, Theorem 4.34, `tm:canisointun`] represents the canonical representation `χ_Q`. -/
abbrev DiscOrder (Q : BinaryQF) := (conductorOneForm Q.disc).MonicOrder

/-- The principal form of `disc(Q)` has discriminant `disc(Q)`. -/
lemma disc_conductorOneForm_disc (Q : BinaryQF) :
    (conductorOneForm Q.disc).disc = Q.disc :=
  disc_conductorOneForm_of_emod_four Q.disc_emod_four

/-- The norm on `DiscOrder Q` is `Nm(x + yω) = x² + Δxy + ((Δ² - Δ)/4)y²`. -/
lemma discOrder_norm (Q : BinaryQF) (z : Q.DiscOrder) :
    z.norm = z.re ^ 2 + Q.disc * z.re * z.im + (Q.disc ^ 2 - Q.disc) / 4 * z.im ^ 2 := by
  simpa [conductorOneForm] using monicOrder_norm (conductorOneForm Q.disc) z

/-- The trace on `DiscOrder Q` is `Tr(x + yω) = 2x + Δy`. -/
lemma discOrder_trace (Q : BinaryQF) (z : Q.DiscOrder) :
    QuadraticAlgebra.trace z = 2 * z.re + Q.disc * z.im := by
  rw [QuadraticAlgebra.trace_def]
  simp [conductorOneForm]


/-! ### The canonical generator and the representation

The canonical representation is `x + yω ↦ xI + yN` for the integral matrix `N = (ΔI + 2SQ)/2`.
Integrality of `N` is the parity `Δ ≡ b (mod 2)`, and the quadratic relation satisfied by `N` is
the Cayley--Hamilton equation of a matrix with trace `Δ` and determinant `(Δ² - Δ)/4`. -/

/-- The discriminant and the middle coefficient have the same parity, `Δ ≡ b (mod 2)`. -/
lemma two_dvd_disc_sub_b (Q : BinaryQF) : (2 : ℤ) ∣ Q.disc - Q.b := by
  obtain ⟨k, hk⟩ : Even ((Q.b - 1) * (Q.b - 1 + 1)) := Int.even_mul_succ_self _
  refine ⟨k - 2 * (Q.a * Q.c), ?_⟩
  simp only [disc, discrim]
  linear_combination hk

/-- The discriminant and the middle coefficient have the same parity, `Δ ≡ -b (mod 2)`. -/
lemma two_dvd_disc_add_b (Q : BinaryQF) : (2 : ℤ) ∣ Q.disc + Q.b := by
  obtain ⟨k, hk⟩ := Q.two_dvd_disc_sub_b
  exact ⟨k + Q.b, by linarith⟩

/-- The canonical generator `N = (ΔI + 2SQ)/2 = [[(Δ-b)/2, -c], [a, (Δ+b)/2]]`, the matrix
representing `ω = (Δ + √Δ)/2` in the canonical representation `χ_Q` of
[AFK25, Definition 4.32, `df:etaq`]. -/
def canonicalGen (Q : BinaryQF) : Mat(2, ℤ) :=
  !![(Q.disc - Q.b) / 2, -Q.c; Q.a, (Q.disc + Q.b) / 2]

/-- The doubled canonical generator is `2N = ΔI + 2SQ`, the defining relation without
denominators. -/
lemma twice_canonicalGen (Q : BinaryQF) :
    (2 : ℤ) • Q.canonicalGen = Q.disc • (1 : Mat(2, ℤ)) + Q.twiceSQ := by
  have hsub := Int.mul_ediv_cancel' Q.two_dvd_disc_sub_b
  have hadd := Int.mul_ediv_cancel' Q.two_dvd_disc_add_b
  have hone : Q.disc • (1 : Mat(2, ℤ)) = !![Q.disc, 0; 0, Q.disc] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hone, canonicalGen, twiceSQ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> omega

/-- The canonical generator has trace `Δ`. -/
@[simp]
lemma trace_canonicalGen (Q : BinaryQF) : Matrix.trace Q.canonicalGen = Q.disc := by
  have hsub := Int.mul_ediv_cancel' Q.two_dvd_disc_sub_b
  have hadd := Int.mul_ediv_cancel' Q.two_dvd_disc_add_b
  simp only [canonicalGen, Matrix.trace_fin_two_of]
  omega

/-- Four divides `Δ² - Δ` for every discriminant `Δ = disc(Q)`, so `(Δ² - Δ)/4`, the norm of
`ω = (Δ + √Δ)/2`, is an integer. -/
lemma four_dvd_disc_sq_sub_disc (Q : BinaryQF) : (4 : ℤ) ∣ Q.disc ^ 2 - Q.disc := by
  rcases Q.disc_emod_four with h | h
  · obtain ⟨k, hk⟩ : (4 : ℤ) ∣ Q.disc := Int.dvd_of_emod_eq_zero h
    exact ⟨k * (Q.disc - 1), by rw [hk]; ring⟩
  · obtain ⟨k, hk⟩ : (4 : ℤ) ∣ Q.disc - 1 := ⟨Q.disc / 4, by omega⟩
    exact ⟨Q.disc * k, by rw [show Q.disc ^ 2 - Q.disc = Q.disc * (Q.disc - 1) by ring, hk]; ring⟩

/-- The canonical generator has determinant `(Δ² - Δ)/4`, the norm of `ω`. -/
@[simp]
lemma det_canonicalGen (Q : BinaryQF) :
    Q.canonicalGen.det = (Q.disc ^ 2 - Q.disc) / 4 := by
  have hsub := Int.mul_ediv_cancel' Q.two_dvd_disc_sub_b
  have hadd := Int.mul_ediv_cancel' Q.two_dvd_disc_add_b
  have hquot := Int.mul_ediv_cancel' Q.four_dvd_disc_sq_sub_disc
  have hdisc : Q.disc = Q.b ^ 2 - 4 * (Q.a * Q.c) := by simp only [disc, discrim]; ring
  simp only [canonicalGen, Matrix.det_fin_two_of]
  have hmul : (2 * ((Q.disc - Q.b) / 2)) * (2 * ((Q.disc + Q.b) / 2)) =
      (Q.disc - Q.b) * (Q.disc + Q.b) := by rw [hsub, hadd]
  have key : 4 * ((Q.disc - Q.b) / 2 * ((Q.disc + Q.b) / 2) - -Q.c * Q.a) =
      Q.disc ^ 2 - Q.disc := by nlinarith [hmul, hdisc]
  omega


/-- The canonical generator satisfies the quadratic equation of `ω = (Δ + √Δ)/2`, namely
`N² = ΔN - ((Δ² - Δ)/4)I`. This specializes Mathlib's `Matrix.aeval_self_charpoly` using
`Matrix.charpoly_fin_two`, `trace_canonicalGen`, and `det_canonicalGen`. -/
lemma canonicalGen_sq (Q : BinaryQF) :
    Q.canonicalGen ^ 2 =
      Q.disc • Q.canonicalGen - ((Q.disc ^ 2 - Q.disc) / 4) • (1 : Mat(2, ℤ)) := by
  have h := Matrix.aeval_self_charpoly Q.canonicalGen
  rw [Matrix.charpoly_fin_two, trace_canonicalGen, det_canonicalGen] at h
  simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
    Matrix.one_mul] at h
  rw [sub_add_eq_add_sub, sub_eq_zero] at h
  exact eq_sub_of_add_eq h

/-- **The canonical representation** `χ_Q(x + yω) = xI + yN` of [AFK25, Definition 4.32,
`df:etaq`], restricted to the order of discriminant `disc(Q)`. Its image is the set of integral
matrices commuting with `SQ` by `commute_twiceSQ_iff_exists_canonicalRep`, the image part of
[AFK25, Theorem 4.34(1), `tm:canisointun`]. -/
@[source "AFK25, Definition 4.32, p. 62, df:etaq (order restriction)" (symbol := "χ_Q")]
def canonicalRep (Q : BinaryQF) : Q.DiscOrder →+* Mat(2, ℤ) where
  toFun z := z.re • (1 : Mat(2, ℤ)) + z.im • Q.canonicalGen
  map_zero' := by simp
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' z w := by
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, add_smul]
    abel
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, add_smul, mul_smul]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, ← pow_two, canonicalGen_sq, conductorOneForm]
    module

/-! ### Entries, trace, and determinant

The lower-left, upper-right and diagonal-difference entries of `χ_Q(x + yω)` are `ya`, `-yc` and
`yb`. For a primitive form a Bézout combination of the coefficients turns those three into `y`,
which drives the congruence criterion below. -/

/-- The canonical representation in coordinates, `χ_Q(x + yω) = xI + yN`. -/
lemma canonicalRep_apply (Q : BinaryQF) (z : Q.DiscOrder) :
    Q.canonicalRep z = z.re • (1 : Mat(2, ℤ)) + z.im • Q.canonicalGen := rfl


/-- The lower-left entry of `χ_Q(x + yω)` is `ya`. -/
@[simp]
lemma canonicalRep_lowerLeft (Q : BinaryQF) (z : Q.DiscOrder) :
    Q.canonicalRep z 1 0 = z.im * Q.a := by
  rw [canonicalRep_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
    Matrix.one_apply_ne (by decide)]
  simp [canonicalGen]

/-- The sign of a canonical representation with nonzero root coordinate is `sgn(y)·sgn(Q)`, where
`sgn(Q) = sgn(a)` is [AFK25, Definition 1.19, `dfn:sign`] read on the form. This is what fixes
the orientation of the associated level generator in
[AFK25, Definition 1.28, `dfn:AssociatedStabilizers`]. -/
lemma signMatrix_canonicalRep {Q : BinaryQF} (hQa : Q.a ≠ 0) {z : Q.DiscOrder} (hz : z.im ≠ 0) :
    signMatrix (Q.canonicalRep z) = Int.sign z.im * Q.sign := by
  rw [signMatrix_of_lowerLeft_ne, canonicalRep_lowerLeft, Int.sign_mul]
  · rfl
  · simpa only [canonicalRep_lowerLeft] using mul_ne_zero hz hQa

/-- The upper-right entry of `χ_Q(x + yω)` is `-yc`. -/
@[simp]
lemma canonicalRep_upperRight (Q : BinaryQF) (z : Q.DiscOrder) :
    Q.canonicalRep z 0 1 = -(z.im * Q.c) := by
  rw [canonicalRep_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
    Matrix.one_apply_ne (by decide)]
  simp [canonicalGen]

/-- The diagonal difference of `χ_Q(x + yω)` is `yb`. -/
lemma canonicalRep_diag_sub (Q : BinaryQF) (z : Q.DiscOrder) :
    Q.canonicalRep z 1 1 - Q.canonicalRep z 0 0 = z.im * Q.b := by
  have hsub := Int.mul_ediv_cancel' Q.two_dvd_disc_sub_b
  have hadd := Int.mul_ediv_cancel' Q.two_dvd_disc_add_b
  rw [canonicalRep_apply]
  simp only [canonicalGen, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.of_apply]
  have hhalf : (Q.disc + Q.b) / 2 - (Q.disc - Q.b) / 2 = Q.b := by omega
  linear_combination z.im * hhalf

/-- The canonical representation preserves traces: `Tr χ_Q(x + yω) = 2x + Δy`, the field trace
of `x + yω`. -/
lemma trace_canonicalRep (Q : BinaryQF) (z : Q.DiscOrder) :
    Matrix.trace (Q.canonicalRep z) = 2 * z.re + Q.disc * z.im := by
  rw [canonicalRep_apply]
  simp only [Matrix.trace_fin_two, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one]
  have htrace : Q.canonicalGen 0 0 + Q.canonicalGen 1 1 = Q.disc := by
    simpa only [Matrix.trace_fin_two] using Q.trace_canonicalGen
  linear_combination z.im * htrace

/-- The doubled canonical representation in the coordinates of
`IsPrimitive.commute_twiceSQ_iff`: `2χ_Q(z) = (2x + Δy)I + y(2SQ)`. -/
lemma twice_canonicalRep (Q : BinaryQF) (z : Q.DiscOrder) :
    (2 : ℤ) • Q.canonicalRep z =
      (2 * z.re + Q.disc * z.im) • (1 : Mat(2, ℤ)) + z.im • Q.twiceSQ := by
  rw [canonicalRep_apply, smul_add, smul_smul, smul_smul]
  rw [show (2 * z.im) • Q.canonicalGen = z.im • ((2 : ℤ) • Q.canonicalGen) by
    rw [smul_smul]; ring_nf, Q.twice_canonicalGen, smul_add, smul_smul]
  module

/-- The canonical representation turns norms into determinants,
`det χ_Q(z) = Nm(z)`. This is [AFK25, Proposition 4.31(2)], the unlabelled proposition following
[AFK25, Definition 4.30, `dfn:canonicalRepresentation`]. -/
lemma det_canonicalRep (Q : BinaryQF) (z : Q.DiscOrder) :
    (Q.canonicalRep z).det = z.norm := by
  rw [Q.discOrder_norm, canonicalRep_apply, Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have htrace := Q.trace_canonicalGen
  have hdet := Q.det_canonicalGen
  rw [Matrix.trace_fin_two] at htrace
  rw [Matrix.det_fin_two] at hdet
  simp at htrace hdet ⊢
  linear_combination z.im ^ 2 * hdet + z.re * z.im * htrace

/-! ### The image of the representation

`SICs.Quadratic.FormStabilizers` writes a matrix `M` commuting with `SQ` as
`2M = tI + n(2SQ)` with `t = Tr M`. Since `t ≡ nΔ (mod 2)`, the element `x + yω` with `y = n` and
`x = (t - nΔ)/2` lies in the order and has `χ_Q(x + yω) = M`; conversely every `χ_Q(z)` commutes
with `SQ`. This is the image part of [AFK25, Theorem 4.34(1), `tm:canisointun`]. -/

/-- **The image of the canonical representation of a primitive form is the integral commutant of
`SQ`**, the image part of [AFK25, Theorem 4.34(1), `tm:canisointun`]. -/
@[source "AFK25, Theorem 4.34, p. 63, tm:canisointun (1)"]
theorem commute_twiceSQ_iff_exists_canonicalRep {Q : BinaryQF} (hQ : Q.IsPrimitive)
    {M : Mat(2, ℤ)} :
    Commute Q.twiceSQ M ↔ ∃ z : Q.DiscOrder, Q.canonicalRep z = M := by
  constructor
  · intro hM
    obtain ⟨n, hn⟩ := hQ.commute_twiceSQ_iff.mp hM
    have h00 := congrArg (fun A : Mat(2, ℤ) ↦ A 0 0) hn
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq, mul_one,
      twiceSQ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one] at h00
    obtain ⟨p, hp⟩ := Q.two_dvd_disc_sub_b
    have hdvd : (2 : ℤ) ∣ Matrix.trace M - n * Q.disc := by
      refine ⟨M 0 0 - n * p, ?_⟩
      linear_combination -h00 - n * hp
    let z : Q.DiscOrder := ⟨(Matrix.trace M - n * Q.disc) / 2, n⟩
    refine ⟨z, ?_⟩
    apply smul_right_injective _ (two_ne_zero : (2 : ℤ) ≠ 0)
    change (2 : ℤ) • Q.canonicalRep z = (2 : ℤ) • M
    rw [Q.twice_canonicalRep, hn]
    have hquot := Int.mul_ediv_cancel' hdvd
    have hcoef : 2 * z.re + Q.disc * z.im = Matrix.trace M := by
      dsimp only [z]
      nlinarith
    rw [hcoef]
  · rintro ⟨z, rfl⟩
    rw [hQ.commute_twiceSQ_iff]
    exact ⟨z.im, by rw [Q.trace_canonicalRep]; exact Q.twice_canonicalRep z⟩

/-! ### Congruences

Primitivity makes `y` recoverable from `ya`, `yb` and `yc`: a Bézout relation among the
coefficients turns divisibility of the three products by an integer `k` into `k ∣ y`. This gives
[AFK25, Corollary 4.35, `cr:etaqmodn`]: divisibility of an order element by an integer and
entrywise divisibility of its canonical representation are the same condition. Applied to `u - 1`
this is the level condition below. -/

/-- **[AFK25, Corollary 4.35, `cr:etaqmodn`]**: an element of the order is divisible by an
integer `k` exactly when its canonical representation is divisible by `k` entrywise. -/
@[source "AFK25, Corollary 4.35, p. 64, cr:etaqmodn"]
theorem dvd_canonicalRep_iff {Q : BinaryQF} (hQ : Q.IsPrimitive) (k : ℤ) (z : Q.DiscOrder) :
    (k ∣ z.re ∧ k ∣ z.im) ↔ ∀ i j, k ∣ Q.canonicalRep z i j := by
  constructor
  · rintro ⟨⟨r, hr⟩, ⟨s, hs⟩⟩ i j
    rw [canonicalRep_apply]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine ⟨r * (1 : Mat(2, ℤ)) i j + s * Q.canonicalGen i j, ?_⟩
    rw [hr, hs]
    ring
  · intro h
    have ha : k ∣ z.im * Q.a := by
      simpa only [canonicalRep_lowerLeft] using h 1 0
    have hb : k ∣ z.im * Q.b := by
      have hd := dvd_sub (h 1 1) (h 0 0)
      rw [Q.canonicalRep_diag_sub] at hd
      exact hd
    have hc : k ∣ z.im * Q.c := by
      have hc' := h 0 1
      rw [Q.canonicalRep_upperRight, dvd_neg] at hc'
      exact hc'
    obtain ⟨x, y, u, hxyz⟩ := hQ.exists_linear_combination
    obtain ⟨ra, hra⟩ := ha
    obtain ⟨rb, hrb⟩ := hb
    obtain ⟨rc, hrc⟩ := hc
    have him : k ∣ z.im := by
      refine ⟨x * ra + y * rb + u * rc, ?_⟩
      linear_combination -z.im * hxyz + x * hra + y * hrb + u * hrc
    have hdiag : Q.canonicalRep z 1 1 =
        z.re + z.im * ((Q.disc + Q.b) / 2) := by
      rw [canonicalRep_apply]
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
        mul_one, canonicalGen, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.of_apply]
    have h11 := h 1 1
    rw [hdiag] at h11
    have hterm : k ∣ z.im * ((Q.disc + Q.b) / 2) :=
      dvd_mul_of_dvd_left him _
    exact ⟨by simpa using dvd_sub h11 hterm, him⟩

/-! ### Units and stability groups

`det χ_Q(z) = Nm(z)` turns the determinant-one stabilizers of a primitive form into the norm-one
elements of its order, and the congruence criterion cuts that down to the level group. Both
conditions mention `Q` only through `Δ = disc(Q)`, so `S(Q)` and `S_d(Q)` are the same condition
for every primitive form of a given discriminant;
`canonicalRepUnit_mem_stabilityGroupLevel_iff_dvd` expresses the level condition by divisibility. -/

/-- The canonical representation of the norm-one units of the order, as a homomorphism into
`SL₂(ℤ)`. Its range is `S(Q) ∩ SL₂(ℤ)` by `range_canonicalRepUnit`, which is
[AFK25, Theorem 4.34(2), `tm:canisointun`]. -/
def canonicalRepUnit (Q : BinaryQF) :
    (conductorOneForm Q.disc).monicNormOneUnits →* SL(2, ℤ) where
  toFun u := ⟨Q.canonicalRep (u : (conductorOneForm Q.disc).MonicOrderˣ), by
    rw [det_canonicalRep]; exact u.property⟩
  map_one' := by
    apply Subtype.ext
    exact Q.canonicalRep.map_one
  map_mul' u v := by
    apply Subtype.ext
    exact Q.canonicalRep.map_mul _ _

/-- The matrix of `canonicalRepUnit` is the canonical representation of the underlying element. -/
@[simp]
lemma coe_canonicalRepUnit (Q : BinaryQF) (u : (conductorOneForm Q.disc).monicNormOneUnits) :
    (Q.canonicalRepUnit u : Mat(2, ℤ)) =
      Q.canonicalRep (u : (conductorOneForm Q.disc).MonicOrderˣ) := rfl

/-- **The determinant-one stabilizers of a primitive form are exactly the canonical
representations of the norm-one elements of its order**: [AFK25, Theorem 4.34(2),
`tm:canisointun`], in the range form. -/
@[source "AFK25, Theorem 4.34, p. 63, tm:canisointun (2, norm one)"]
theorem range_canonicalRepUnit {Q : BinaryQF} (hQ : Q.IsPrimitive) :
    Q.canonicalRepUnit.range = Q.stabilityGroupSL := by
  ext M
  constructor
  · rintro ⟨u, rfl⟩
    change Matrix.SpecialLinearGroup.toGL (Q.canonicalRepUnit u) ∈ Q.stabilityGroup
    rw [mem_stabilityGroup_iff_commute_twiceSQ]
    exact (commute_twiceSQ_iff_exists_canonicalRep hQ).2
      ⟨(u : (conductorOneForm Q.disc).MonicOrderˣ), rfl⟩
  · intro hM
    change Matrix.SpecialLinearGroup.toGL M ∈ Q.stabilityGroup at hM
    have hcomm : Commute Q.twiceSQ (M : Mat(2, ℤ)) :=
      mem_stabilityGroup_iff_commute_twiceSQ.mp hM
    obtain ⟨z, hz⟩ := (commute_twiceSQ_iff_exists_canonicalRep hQ).mp hcomm
    have hn : z.norm = 1 := by
      rw [← Q.det_canonicalRep z, hz]
      exact M.property
    let u : (conductorOneForm Q.disc).monicNormOneUnits :=
      ⟨Unitary.toUnits ⟨z, QuadraticAlgebra.mem_unitary hn⟩, hn⟩
    refine ⟨u, ?_⟩
    apply Subtype.ext
    exact hz

/-- **The level condition is a condition on the order alone**: `χ_Q(u) ∈ S_d(Q)` exactly when
`u ≡ 1` modulo `d` in the order. This is [AFK25, Corollary 4.35, `cr:etaqmodn`] applied to
`u - 1`; since neither side mentions `Q` beyond `disc(Q)`, it is what makes `S_d(Q)` depend on
the form only through its discriminant. -/
theorem canonicalRepUnit_mem_stabilityGroupLevel_iff {Q : BinaryQF} (hQ : Q.IsPrimitive)
    (d : ℕ) (u : (conductorOneForm Q.disc).monicNormOneUnits) :
    Q.canonicalRepUnit u ∈ Q.stabilityGroupLevel d ↔
      (d : ℤ) ∣ ((u : (conductorOneForm Q.disc).MonicOrderˣ) :
          (conductorOneForm Q.disc).MonicOrder).re - 1 ∧
      (d : ℤ) ∣ ((u : (conductorOneForm Q.disc).MonicOrderˣ) :
          (conductorOneForm Q.disc).MonicOrder).im := by
  change (Q.canonicalRepUnit u ∈ Q.stabilityGroupSL ∧
    Q.canonicalRepUnit u ∈ CongruenceSubgroup.Gamma d) ↔ _
  have hstab : Q.canonicalRepUnit u ∈ Q.stabilityGroupSL := by
    rw [← range_canonicalRepUnit hQ]
    exact ⟨u, rfl⟩
  simp only [hstab, true_and]
  rw [SL2Z.gamma_mem_iff_modEq]
  let z : Q.DiscOrder :=
    ((u : (conductorOneForm Q.disc).MonicOrderˣ) :
      (conductorOneForm Q.disc).MonicOrder)
  constructor
  · intro hlevel
    have hentries : ∀ i j, (d : ℤ) ∣ Q.canonicalRep (z - 1) i j := by
      intro i j
      rw [map_sub, map_one, Matrix.sub_apply]
      exact dvd_sub_comm.mp (Int.modEq_iff_dvd.mp (hlevel i j))
    have hz := (dvd_canonicalRep_iff hQ (d : ℤ) (z - 1)).mpr hentries
    simpa only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, sub_zero] using hz
  · intro hz
    have hentries := (dvd_canonicalRep_iff hQ (d : ℤ) (z - 1)).mp (by
      simpa only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, sub_zero] using hz)
    intro i j
    rw [Int.modEq_iff_dvd]
    have hij := hentries i j
    rw [map_sub, map_one, Matrix.sub_apply] at hij
    exact dvd_sub_comm.mp hij

/-- The level condition for a canonical unit, in the order: `χ_Q(u) ∈ S_d(Q) ↔ u ≡ 1 (mod d)`.
This is `canonicalRepUnit_mem_stabilityGroupLevel_iff` with the coordinatewise divisibility
recombined by `monicOrder_intCast_dvd_iff`. -/
lemma canonicalRepUnit_mem_stabilityGroupLevel_iff_dvd {Q : BinaryQF} (hQ : Q.IsPrimitive)
    (d : ℕ) (u : (conductorOneForm Q.disc).monicNormOneUnits) :
    Q.canonicalRepUnit u ∈ Q.stabilityGroupLevel d ↔
      (d : Q.DiscOrder) ∣ ((u : (conductorOneForm Q.disc).MonicOrderˣ) : Q.DiscOrder) - 1 := by
  rw [canonicalRepUnit_mem_stabilityGroupLevel_iff hQ]
  have := monicOrder_intCast_dvd_iff (conductorOneForm Q.disc) (d : ℤ)
    (((u : (conductorOneForm Q.disc).MonicOrderˣ) : Q.DiscOrder) - 1)
  simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_one,
    QuadraticAlgebra.im_one, sub_zero, Int.cast_natCast] at this
  exact this.symm

end SIC.BinaryQF
