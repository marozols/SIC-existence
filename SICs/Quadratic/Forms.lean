/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.NumberTheory.Real.Irrational
import SICs.MatrixNotation
import SICs.Quadratic.FundamentalDiscriminants
import SICs.Source

/-!
# Binary Quadratic Forms and Their Real Roots

Binary quadratic forms, their discriminants and conductors, and the real roots and their signs.

This file begins the number-theoretic infrastructure needed for the SIC construction.
The key objects are:

- Binary quadratic forms Q = ⟨a,b,c⟩ and their discriminants
- Form conductors and real roots associated to forms
- The two real roots, the irrationality of `ρ_{Q,+}`, and the Vieta relations

## Main definitions

- `BinaryQF`: binary quadratic form ⟨a,b,c⟩
- `BinaryQF.toQuadraticForm`: the associated Mathlib quadratic form on `ℤ²`
- `BinaryQF.disc`: discriminant Δ = b²-4ac
- `BinaryQF.IsConductor`: the exact factorization `disc(Q) = f²Δ₀` by a positive
  fundamental discriminant
- `BinaryQF.twiceSQ`: the integral matrix `2SQ` controlling the stability group
- `BinaryQF.rootPlus`, `BinaryQF.rootMinus`: roots ρ = (-b ± √Δ)/(2a)
- `BinaryQF.IsAdmissible.rootPlus_irrational`: irrationality of `ρ_{Q,+}`
- `BinaryQF.sign`: sign of a quadratic form (sign of leading coefficient)

The matrix action and stability subgroups are in `SICs.Quadratic.FormActions`.

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Sections 1.3, 4.4, and 4.5
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### Binary quadratic forms

Coefficient triples are connected to Mathlib's quadratic forms, their discriminants, and the
integral matrix `2SQ`.  The latter packages the form in the normalization used by the stability
calculations of [AFK25, Section 4.4]. -/

/-- The coefficients of an integral binary quadratic form `Q(x,y) = ax² + bxy + cy²`,
written `Q = ⟨a,b,c⟩` in [AFK25, §1.3]. The predicate `BinaryQF.IsAdmissible` records the additional
primitive, irreducible, and indefinite conditions imposed by the paper's convention
for the unqualified word "form." -/
@[ext]
structure BinaryQF where
  /-- The coefficient of `x²`. -/
  a : ℤ
  /-- The coefficient of `xy`. -/
  b : ℤ
  /-- The coefficient of `y²`. -/
  c : ℤ
  deriving DecidableEq

namespace BinaryQF

/-- Evaluate the form `Q = ⟨a,b,c⟩` at (x,y): Q(x,y) = ax² + bxy + cy². -/
def eval (Q : BinaryQF) (x y : ℤ) : ℤ := Q.a * x ^ 2 + Q.b * x * y + Q.c * y ^ 2

/-- A binary quadratic form is even: `Q(-x,-y) = Q(x,y)`. Every term of `eval` is of total
degree two. -/
@[simp]
lemma eval_neg (Q : BinaryQF) (x y : ℤ) : Q.eval (-x) (-y) = Q.eval x y := by
  simp only [eval]
  ring

/-- The Mathlib quadratic form on `ℤ²` associated with the coefficient triple `Q`.
The use of `QuadraticMap.proj 0 1` represents the middle term integrally, including when `Q.b`
is odd. -/
def toQuadraticForm (Q : BinaryQF) : QuadraticForm ℤ (Fin 2 → ℤ) :=
  Q.a • QuadraticMap.proj 0 0 + Q.b • QuadraticMap.proj 0 1 +
    Q.c • QuadraticMap.proj 1 1

/-- Evaluating the Mathlib quadratic form associated with `Q` recovers `BinaryQF.eval`. -/
@[simp]
lemma toQuadraticForm_apply (Q : BinaryQF) (v : Fin 2 → ℤ) :
    Q.toQuadraticForm v = Q.eval (v 0) (v 1) := by
  simp [toQuadraticForm, eval, pow_two]
  ring

/-- The associated Mathlib quadratic form determines its integral coefficient triple. -/
lemma toQuadraticForm_injective : Function.Injective toQuadraticForm := by
  intro Q Q' h
  have ha : Q.a = Q'.a := by
    simpa [eval] using DFunLike.congr_fun h ![(1 : ℤ), 0]
  have hc : Q.c = Q'.c := by
    simpa [eval] using DFunLike.congr_fun h ![(0 : ℤ), 1]
  have habc : Q.a + Q.b + Q.c = Q'.a + Q'.b + Q'.c := by
    simpa [eval] using DFunLike.congr_fun h ![(1 : ℤ), 1]
  have hb : Q.b = Q'.b := by omega
  cases Q
  cases Q'
  simp_all

/-- The discriminant Δ = b² - 4ac of a binary quadratic form. -/
def disc (Q : BinaryQF) : ℤ := discrim Q.a Q.b Q.c

/-- The discriminant written out in the coefficients: `Δ = b² - 4ac`. `disc` is defined through
Mathlib's `discrim`, so the polynomial form is not syntactically available. -/
lemma disc_eq_coefficients (Q : BinaryQF) : Q.disc = Q.b ^ 2 - 4 * Q.a * Q.c := by
  simp [disc, discrim]

/-- The discriminant cast to `ℝ`, written out in the cast coefficients: `Δ = b² - 4ac`. This is
`disc_eq_coefficients` pushed through the cast, the form every real computation with the roots
needs. -/
lemma disc_cast_eq_coefficients (Q : BinaryQF) :
    (Q.disc : ℝ) = (Q.b : ℝ) ^ 2 - 4 * Q.a * Q.c := by
  rw [disc_eq_coefficients]; push_cast; ring

/-- The integral matrix `2SQ = [[-b, -2c], [2a, b]]` associated with `Q`, where
`S = [[0, -1], [1, 0]]` and `Q` denotes the paper's half-Hessian matrix
`[[a, b/2], [b/2, c]]`. This normalization avoids denominators when `b` is odd. -/
def twiceSQ (Q : BinaryQF) : Mat(2, ℤ) :=
  !![-Q.b, -2 * Q.c; 2 * Q.a, Q.b]

/-- The integral matrix `2SQ` determines the coefficient triple `Q`. -/
lemma twiceSQ_injective : Function.Injective twiceSQ := by
  intro Q Q' h
  have hb := congrArg (fun M : Mat(2, ℤ) => M 0 0) h
  have hc := congrArg (fun M : Mat(2, ℤ) => M 0 1) h
  have ha := congrArg (fun M : Mat(2, ℤ) => M 1 0) h
  simp [twiceSQ] at ha hb hc
  have ha' : Q.a = Q'.a := by omega
  have hc' : Q.c = Q'.c := by omega
  cases Q
  cases Q'
  simp_all

/-- Equality of the integral matrices `2SQ` is equivalent to equality of coefficient triples. -/
@[simp]
lemma twiceSQ_inj {Q Q' : BinaryQF} : Q.twiceSQ = Q'.twiceSQ ↔ Q = Q' :=
  twiceSQ_injective.eq_iff

/-! ### Form conductors

The imported fundamental-discriminant predicate supplies the arithmetic base, while `IsConductor`
records the exact factorization `disc(Q) = f²Δ₀`. The constructions carry witnesses to this
relation rather than selecting a canonical factorization. -/

/-- `Q` has fundamental discriminant `Δ₀` and form conductor `f` when `Δ₀` is a
positive fundamental discriminant, `f` is positive, and

`disc(Q) = f² · Δ₀`.

This is the exact relational form of [AFK25, equations (1.33) and (1.34), `eq:ConductorOfQ`]. -/
def IsConductor (Q : BinaryQF) (Δ₀ : ℤ) (f : ℕ) : Prop :=
  IsFundamentalDiscriminant Δ₀ ∧ 0 < Δ₀ ∧ 0 < f ∧
    Q.disc = (f : ℤ) ^ 2 * Δ₀

/-- A form-conductor witness gives the discriminant factorization `disc(Q) = f²Δ₀`. -/
lemma IsConductor.disc_eq {Q : BinaryQF} {Δ₀ : ℤ} {f : ℕ}
    (h : Q.IsConductor Δ₀ f) : Q.disc = (f : ℤ) ^ 2 * Δ₀ :=
  h.2.2.2

/-- A quadratic form is primitive if gcd(a,b,c) = 1. -/
def IsPrimitive (Q : BinaryQF) : Prop :=
  Int.gcd (Int.gcd Q.a Q.b) Q.c = 1

/-- A quadratic form is indefinite if its discriminant is positive. -/
def IsIndefinite (Q : BinaryQF) : Prop := 0 < Q.disc

/-- A quadratic form is irreducible (does not split over ℚ).
    Equivalently, the discriminant is not a perfect square. -/
def IsIrreducible (Q : BinaryQF) : Prop := ¬ IsSquare Q.disc

/-- Project-local predicate bundling the primitive, irreducible, and indefinite conditions in
[AFK25, §1.3]. The paper uses the unqualified word "form" for forms satisfying these conditions. -/
def IsAdmissible (Q : BinaryQF) : Prop :=
  Q.IsPrimitive ∧ Q.IsIndefinite ∧ Q.IsIrreducible

/-- An admissible form is primitive. -/
lemma IsAdmissible.isPrimitive {Q : BinaryQF} (hQ : Q.IsAdmissible) : Q.IsPrimitive :=
  hQ.1

/-- An admissible form is indefinite. -/
lemma IsAdmissible.isIndefinite {Q : BinaryQF} (hQ : Q.IsAdmissible) : Q.IsIndefinite :=
  hQ.2.1

/-- An admissible form is irreducible. -/
lemma IsAdmissible.isIrreducible {Q : BinaryQF} (hQ : Q.IsAdmissible) : Q.IsIrreducible :=
  hQ.2.2

/-- A primitive form whose discriminant is positive and not a square is admissible: the
introduction rule matching the projections `IsAdmissible.isPrimitive`, `IsAdmissible.isIndefinite`
and `IsAdmissible.isIrreducible`. -/
lemma isAdmissible_of_disc {Q : BinaryQF} (hprim : Q.IsPrimitive) (hpos : 0 < Q.disc)
    (hnsq : ¬ IsSquare Q.disc) : Q.IsAdmissible :=
  ⟨hprim, hpos, hnsq⟩

/-- An indefinite form has positive discriminant. -/
lemma IsIndefinite.disc_pos {Q : BinaryQF} (hQ : Q.IsIndefinite) : 0 < Q.disc :=
  hQ

/-- An admissible form has positive discriminant. -/
lemma IsAdmissible.disc_pos {Q : BinaryQF} (hQ : Q.IsAdmissible) : 0 < Q.disc :=
  hQ.isIndefinite.disc_pos

/-! ### Roots of a quadratic form

The two real quadratic roots are defined by the usual formula.  Clearing denominators and proving
their quadratic equations supplies the identities used later for fixed points and stabilizers. -/

/-- The root `ρ_{Q,+} = (-b + √Δ)/(2a)` from [AFK25, equation (1.35), `dfn:qrtdf`]. For an
admissible form, it is an irrational real number. -/
noncomputable def rootPlus (Q : BinaryQF) : ℝ :=
  (-Q.b + Real.sqrt Q.disc) / (2 * Q.a)

/-- The root `ρ_{Q,-} = (-b - √Δ)/(2a)` from [AFK25, equation (1.35), `dfn:qrtdf`]. For an
admissible form, it is an irrational real number. -/
noncomputable def rootMinus (Q : BinaryQF) : ℝ :=
  (-Q.b - Real.sqrt Q.disc) / (2 * Q.a)

/-- **Clearing the denominator in `ρ_{Q,+}`**: `2a·ρ_{Q,+} = -b + √Δ`. The form in which the root
enters the associated-stabilizer computations of `SICs.Admissible.StabilizerDomain`, where `a`
always appears multiplied into the root and cancels. -/
lemma two_mul_a_mul_rootPlus (Q : BinaryQF) (ha : Q.a ≠ 0) :
    2 * (Q.a : ℝ) * Q.rootPlus = -(Q.b : ℝ) + Real.sqrt Q.disc := by
  have ha' : (Q.a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
  rw [rootPlus]
  field_simp

/-- The leading coefficient of an irreducible binary quadratic form is nonzero. -/
lemma IsIrreducible.a_ne_zero {Q : BinaryQF} (hQ : Q.IsIrreducible) : Q.a ≠ 0 := by
  intro ha
  apply hQ
  refine ⟨Q.b, ?_⟩
  simp [disc, discrim, ha, pow_two]

/-- The leading coefficient of an admissible binary quadratic form is nonzero. -/
lemma IsAdmissible.a_ne_zero {Q : BinaryQF} (hQ : Q.IsAdmissible) : Q.a ≠ 0 :=
  hQ.isIrreducible.a_ne_zero

/-- The plus branch of the quadratic formula for an irreducible binary quadratic form
with nonnegative discriminant is irrational. This is the irrationality assertion accompanying
`BinaryQF.rootPlus`, stated with
only the two discriminant hypotheses its proof uses. -/
lemma IsIrreducible.rootPlus_irrational {Q : BinaryQF} (hQ : Q.IsIrreducible)
    (hdisc : 0 ≤ Q.disc) : Irrational Q.rootPlus := by
  have hsqrt : Irrational (Real.sqrt Q.disc) :=
    (irrational_sqrt_intCast_iff_of_nonneg hdisc).2 hQ
  have hden : (2 * Q.a : ℤ) ≠ 0 := mul_ne_zero (by norm_num) hQ.a_ne_zero
  rw [rootPlus]
  simpa only [Int.cast_neg, Int.cast_mul, Int.cast_ofNat] using
    (hsqrt.intCast_add (-Q.b)).div_intCast hden

/-- The plus branch `ρ_{Q,+}` of an admissible binary quadratic form is irrational. -/
lemma IsAdmissible.rootPlus_irrational {Q : BinaryQF} (hQ : Q.IsAdmissible) :
    Irrational Q.rootPlus :=
  hQ.isIrreducible.rootPlus_irrational hQ.disc_pos.le

/-- The root `ρ_{Q,+}` satisfies the quadratic equation when the quadratic formula has a
nonzero denominator and a real square root. -/
lemma rootPlus_satisfies_quadratic_of_disc_nonneg (Q : BinaryQF)
    (ha : Q.a ≠ 0) (hdisc : 0 ≤ Q.disc) :
    Q.a * Q.rootPlus ^ 2 + Q.b * Q.rootPlus + Q.c = 0 := by
  have ha' : (Q.a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hdisc' : (0 : ℝ) ≤ Q.disc := by exact_mod_cast hdisc
  have hsqrt : discrim (Q.a : ℝ) Q.b Q.c =
      Real.sqrt Q.disc * Real.sqrt Q.disc := by
    calc
      _ = (Q.disc : ℝ) := by rw [discrim, disc_cast_eq_coefficients]
      _ = Real.sqrt Q.disc ^ 2 := (Real.sq_sqrt hdisc').symm
      _ = _ := pow_two _
  simpa only [pow_two] using
    (quadratic_eq_zero_iff ha' hsqrt Q.rootPlus).2 (Or.inl rfl)

/-- The root `ρ_{Q,-}` satisfies the quadratic equation when the quadratic formula has a
nonzero denominator and a real square root. -/
lemma rootMinus_satisfies_quadratic_of_disc_nonneg (Q : BinaryQF)
    (ha : Q.a ≠ 0) (hdisc : 0 ≤ Q.disc) :
    Q.a * Q.rootMinus ^ 2 + Q.b * Q.rootMinus + Q.c = 0 := by
  have ha' : (Q.a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hdisc' : (0 : ℝ) ≤ Q.disc := by exact_mod_cast hdisc
  have hsqrt : discrim (Q.a : ℝ) Q.b Q.c =
      Real.sqrt Q.disc * Real.sqrt Q.disc := by
    calc
      _ = (Q.disc : ℝ) := by rw [discrim, disc_cast_eq_coefficients]
      _ = Real.sqrt Q.disc ^ 2 := (Real.sq_sqrt hdisc').symm
      _ = _ := pow_two _
  simpa only [pow_two] using
    (quadratic_eq_zero_iff ha' hsqrt Q.rootMinus).2 (Or.inr rfl)

/-- The root ρ_{Q,+} of an admissible form satisfies its quadratic equation. -/
lemma rootPlus_satisfies_quadratic (Q : BinaryQF) (hQ : Q.IsAdmissible) :
    Q.a * Q.rootPlus ^ 2 + Q.b * Q.rootPlus + Q.c = 0 :=
  rootPlus_satisfies_quadratic_of_disc_nonneg Q hQ.a_ne_zero hQ.disc_pos.le

/-- The root ρ_{Q,-} of an admissible form satisfies its quadratic equation. -/
lemma rootMinus_satisfies_quadratic (Q : BinaryQF) (hQ : Q.IsAdmissible) :
    Q.a * Q.rootMinus ^ 2 + Q.b * Q.rootMinus + Q.c = 0 :=
  rootMinus_satisfies_quadratic_of_disc_nonneg Q hQ.a_ne_zero hQ.disc_pos.le

/-- **Clearing the denominator in `ρ_{Q,-}`**: `2a·ρ_{Q,-} = -b - √Δ`, the companion of
`two_mul_a_mul_rootPlus`. -/
lemma two_mul_a_mul_rootMinus (Q : BinaryQF) (ha : Q.a ≠ 0) :
    2 * (Q.a : ℝ) * Q.rootMinus = -(Q.b : ℝ) - Real.sqrt Q.disc := by
  have ha' : (Q.a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
  rw [rootMinus]
  field_simp

/-- **Vieta's sum formula**: `ρ_{Q,+} + ρ_{Q,-} = -b/a`. The two square roots cancel, so no
hypothesis on the discriminant is needed. -/
lemma rootPlus_add_rootMinus {Q : BinaryQF} (ha : Q.a ≠ 0) :
    Q.rootPlus + Q.rootMinus = -(Q.b : ℝ) / Q.a := by
  have ha' : (Q.a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
  simp only [rootPlus, rootMinus]
  field_simp
  ring

/-- **Vieta's product formula**: `ρ_{Q,+}·ρ_{Q,-} = c/a`. Here the square root is squared, so the
discriminant must be nonnegative for `√Δ` to be the actual root. -/
lemma rootPlus_mul_rootMinus {Q : BinaryQF} (ha : Q.a ≠ 0) (hdisc : 0 ≤ Q.disc) :
    Q.rootPlus * Q.rootMinus = (Q.c : ℝ) / Q.a := by
  have ha' : (Q.a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hs2 : Real.sqrt (Q.disc : ℝ) ^ 2 = (Q.disc : ℝ) :=
    Real.sq_sqrt (by exact_mod_cast hdisc)
  simp only [rootPlus, rootMinus]
  field_simp
  nlinarith [hs2, disc_cast_eq_coefficients Q]

/-- **The form factors through its roots**: `ax² + bx + c = a(x - ρ_{Q,+})(x - ρ_{Q,-})` for
every real `x`. This is Vieta's two formulas read as a factorization; it is how the sign of a
value of the form is read off the position of `x` relative to the two roots. -/
lemma quadratic_factorization (Q : BinaryQF) (x : ℝ) (ha : Q.a ≠ 0) (hdisc : 0 ≤ Q.disc) :
    (Q.a : ℝ) * x ^ 2 + Q.b * x + Q.c = Q.a * (x - Q.rootPlus) * (x - Q.rootMinus) := by
  have ha' : (Q.a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hsum := rootPlus_add_rootMinus ha
  have hprod := rootPlus_mul_rootMinus ha hdisc
  rw [eq_div_iff ha'] at hsum hprod
  linear_combination x * hsum - hprod

/-- The factorization `quadratic_factorization` read on the value `Q(x,1)` at an integer `x`:
`Q(x,1) = a(x - ρ_{Q,+})(x - ρ_{Q,-})`. -/
lemma eval_one_factorization (Q : BinaryQF) (x : ℤ) (ha : Q.a ≠ 0) (hdisc : 0 ≤ Q.disc) :
    (Q.eval x 1 : ℝ) = Q.a * ((x : ℝ) - Q.rootPlus) * ((x : ℝ) - Q.rootMinus) := by
  rw [← quadratic_factorization Q x ha hdisc]
  simp [eval]

/-- **A form with positive leading coefficient is determined by its discriminant and its root
`ρ_{Q,+}`** when the discriminant is not a square: equating the two roots and clearing
denominators gives `(a - a')√Δ = ab' - a'b`, so `a = a'` by irrationality of `√Δ`, then `b = b'`,
and the discriminant fixes `c`. -/
lemma eq_of_rootPlus_eq_of_disc_eq {Q Q' : BinaryQF} (hQ : Q.IsIrreducible) (hdisc : 0 ≤ Q.disc)
    (ha : 0 < Q.a) (ha' : 0 < Q'.a) (hd : Q'.disc = Q.disc) (hρ : Q'.rootPlus = Q.rootPlus) :
    Q' = Q := by
  have hsqrt : Irrational (Real.sqrt Q.disc) :=
    (irrational_sqrt_intCast_iff_of_nonneg hdisc).2 hQ
  have h1 := two_mul_a_mul_rootPlus Q ha.ne'
  have h2 := two_mul_a_mul_rootPlus Q' ha'.ne'
  rw [hd, hρ] at h2
  have hlin : ((Q.a - Q'.a : ℤ) : ℝ) * Real.sqrt Q.disc =
      ((Q.a * Q'.b - Q'.a * Q.b : ℤ) : ℝ) := by
    push_cast
    linear_combination (Q'.a : ℝ) * h1 - (Q.a : ℝ) * h2
  have haa : Q.a = Q'.a := by
    by_contra hne
    exact (hsqrt.intCast_mul (sub_ne_zero.mpr hne))
      ⟨(Q.a * Q'.b - Q'.a * Q.b : ℤ), by rw [hlin]; push_cast; ring⟩
  have hbb : Q.b = Q'.b := by
    have h0 : (Q'.a * Q'.b - Q'.a * Q.b : ℤ) = 0 := by
      have := hlin
      rw [haa, sub_self, Int.cast_zero, zero_mul] at this
      exact_mod_cast this.symm
    have : Q'.a * (Q'.b - Q.b) = 0 := by linear_combination h0
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h ha'.ne'
    · linarith
  have hcc : Q.c = Q'.c := by
    rw [disc_eq_coefficients, disc_eq_coefficients, ← haa, ← hbb] at hd
    have : 4 * Q.a * (Q.c - Q'.c) = 0 := by linear_combination hd
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (by positivity)
    · linarith
  exact (BinaryQF.ext haa hbb hcc).symm

/-! ### Sign

The orientation conventions of [AFK25, Definition 1.19, `dfn:sign`] assign signs to both forms and
matrices.  For a matrix the lower-left entry decides the sign unless it vanishes. -/

/-- The sign of a binary quadratic form: the sign of the leading coefficient a.
    See [AFK25, Definition 1.19, `dfn:sign`]. -/
@[source "AFK25, Definition 1.19, p. 12, dfn:sign (1)" (symbol := "sgn(Q)")]
def sign (Q : BinaryQF) : ℤ := Int.sign Q.a

/-- The sign of a 2×2 integer matrix M = [[α,β],[γ,δ]]:
    sgn(M) = sgn(γ) if γ ≠ 0, else sgn(δ). See [AFK25, Definition 1.19, `dfn:sign`]. The paper
    applies this to `GL₂(ℤ)`; the same formula is
    harmlessly defined here for every integer matrix. -/
@[source "AFK25, Definition 1.19, p. 12, dfn:sign (2)" (symbol := "sgn(M)")]
def signMatrix (M : Mat(2, ℤ)) : ℤ :=
  let γ := M 1 0
  let δ := M 1 1
  if γ ≠ 0 then Int.sign γ else Int.sign δ

/-- If the lower-left entry is nonzero, it determines the sign of a matrix. -/
@[simp]
lemma signMatrix_of_lowerLeft_ne {M : Mat(2, ℤ)} (h : M 1 0 ≠ 0) :
    signMatrix M = Int.sign (M 1 0) := by
  simp [signMatrix, h]


end BinaryQF

end SIC

end
