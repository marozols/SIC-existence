/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quantum.RSIC
import SICs.Quantum.DisplacementBasis

/-!
# Weyl--Heisenberg fiducials and overlaps

Weyl–Heisenberg fiducials, their overlaps, and the overlap-norm criterion.

This file formalizes [AFK25, Definition 1.6, `dfn:whcovrsic`, and Theorem 1.8,
`thm:sicfidcond`]. A fiducial generates its family by displacement conjugation. Displacement
orthogonality turns the family's trace correlations into finite Fourier conditions on overlap
norms.
-/

noncomputable section

open Matrix
open scoped MatrixGroups

namespace SIC

variable {d : ℕ} [NeZero d]

/-! ### Fiducials -/

/-- A WH-covariant r-SIC is generated from a single fiducial projector P₀
    via the action of the Weyl-Heisenberg group:
    P_p = D_p · P₀ · D_p†  for each p ∈ (Fin d)².
    See [AFK25, Definition 1.6, `dfn:whcovrsic`]. -/
def WHCovariantFamily (P₀ : Mat(d, ℂ)) :
    Fin d × Fin d → Mat(d, ℂ) :=
  fun p => displacementOperator d p * P₀ * (displacementOperator d p).conjTranspose

/-- A fiducial projector for a WH-covariant r-SIC is an r-rank H-projector P₀ such that
    the WH-covariant family {D_p P₀ D_p†} forms an r-SIC.
    See [AFK25, Definition 1.6, `dfn:whcovrsic`]. -/
@[source "AFK25, Definition 1.6, p. 5, dfn:whcovrsic"]
def IsFiducial (r : ℕ) (P₀ : Mat(d, ℂ)) : Prop :=
  IsRankRHProjector r P₀ ∧ IsRSIC r (WHCovariantFamily P₀)

/-- The Weyl--Heisenberg orbit of a fiducial is an `r`-SIC. -/
theorem IsFiducial.isRSIC {r : ℕ} {P₀ : Mat(d, ℂ)}
    (h : IsFiducial r P₀) : IsRSIC r (WHCovariantFamily P₀) := h.2

/-! ### Overlaps

Displacement-basis coefficients encode a fiducial projector through its overlaps. -/

/-- The overlap μ_p = Tr(P · D_p†) with the displacement operator D_p.

    [AFK25, Definition 1.9, `dfn:sicovlp`] gives this definition for a fiducial projector. This
    total
    project-local extension to arbitrary matrices is useful in stating the fiducial criterion. -/
@[source "AFK25, Definition 1.9, p. 6, dfn:sicovlp (overlaps)" (symbol := "μ_p")]
def overlap (P₀ : Mat(d, ℂ)) (p : Fin d × Fin d) : ℂ :=
  (P₀ * (displacementOperator d p).conjTranspose).trace

/-! ### WHCovariantFamily properties

Unitary displacement conjugation preserves trace, Hermiticity, idempotency, and rank.  These facts
transfer projector data from a fiducial to its entire Weyl--Heisenberg orbit. -/

/-- The WH family at the origin is just P₀ itself. -/
lemma WHCovariantFamily_zero (P₀ : Mat(d, ℂ)) :
    WHCovariantFamily P₀ ((0 : Fin d), (0 : Fin d)) = P₀ := by
  simp [WHCovariantFamily, displacementOperator_zero, conjTranspose_one]

/-- The trace is preserved under WH conjugation. -/
lemma WHCovariantFamily_trace (P₀ : Mat(d, ℂ)) (p : Fin d × Fin d) :
    (WHCovariantFamily P₀ p).trace = P₀.trace := by
  unfold WHCovariantFamily
  rw [show displacementOperator d p * P₀ * (displacementOperator d p).conjTranspose =
        displacementOperator d p * (P₀ * (displacementOperator d p).conjTranspose) from
          (Matrix.mul_assoc _ _ _)]
  rw [Matrix.trace_mul_comm]
  rw [Matrix.mul_assoc, conjTranspose_mul_displacementOperator, Matrix.mul_one]

/-- WH conjugation preserves Hermiticity. -/
lemma WHCovariantFamily_isHermitian (P₀ : Mat(d, ℂ))
    (hP : P₀.IsHermitian) (p : Fin d × Fin d) :
    (WHCovariantFamily P₀ p).IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose (displacementOperator d p) hP

/-- WH conjugation preserves idempotency. -/
lemma WHCovariantFamily_idempotent (P₀ : Mat(d, ℂ))
    (hP : P₀ ^ 2 = P₀) (p : Fin d × Fin d) :
    WHCovariantFamily P₀ p ^ 2 = WHCovariantFamily P₀ p := by
  unfold WHCovariantFamily
  rw [sq, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc (displacementOperator d p).conjTranspose (displacementOperator d p),
      conjTranspose_mul_displacementOperator, Matrix.one_mul,
      ← Matrix.mul_assoc P₀ P₀, ← sq, hP]

/-- For an integer dimension greater than one, `d² - 1` is positive after casting to
the reals. -/
private lemma cast_sq_sub_one_pos (d : ℕ) (hd : 1 < d) :
    0 < (d ^ 2 - 1 : ℝ) := by
  have hdR : (1 : ℝ) < d := by exact_mod_cast hd
  have hp : 0 < ((d : ℝ) - 1) * ((d : ℝ) + 1) := by positivity
  nlinarith

/-- For nonnegative `c`, having norm `√c` is equivalent to having complex norm-square
`c`. -/
private lemma norm_eq_sqrt_iff_normSq_eq (z : ℂ) (c : ℝ) (hc : 0 ≤ c) :
    ‖z‖ = Real.sqrt c ↔ Complex.normSq z = c := by
  rw [← RCLike.sqrt_normSq_eq_norm]
  exact Real.sqrt_inj (Complex.normSq_nonneg z) hc

/-- Rewrites the gap between the projector rank and the off-diagonal `r`-SIC trace as
a positive multiple of the overlap norm-square. -/
private lemma rsic_alpha_gap (d r : ℕ) (hr : 0 < r) (hrd : r < d) :
    (r : ℝ) - (r * (r * d - 1) : ℝ) / (d^2 - 1) =
      (d : ℝ) * ((r * (d - r) : ℝ) / (d^2 - 1)) := by
  have hd1 : 1 < d := by omega
  have hb : 0 < (d^2 - 1 : ℝ) := cast_sq_sub_one_pos d hd1
  field_simp [ne_of_gt hb]
  ring

/-- Arithmetic identity giving the zero-frequency value of the fiducial Fourier
pattern. -/
private lemma fiducial_fourier_value_zero (d r : ℕ) (hr : 0 < r) (hrd : r < d) :
    (r : ℝ)^2 + (d^2 - 1) * ((r * (d - r) : ℝ) / (d^2 - 1)) =
      (d : ℝ) * r := by
  have hd1 : 1 < d := by omega
  have hb : 0 < (d^2 - 1 : ℝ) := cast_sq_sub_one_pos d hd1
  field_simp [ne_of_gt hb]
  ring

/-- Arithmetic identity giving each nonzero-frequency value of the fiducial Fourier
pattern. -/
private lemma fiducial_fourier_value_ne_zero (d r : ℕ) (hr : 0 < r) (hrd : r < d) :
    (r : ℝ)^2 - ((r * (d - r) : ℝ) / (d^2 - 1)) =
      (d : ℝ) * ((r * (r * d - 1) : ℝ) / (d^2 - 1)) := by
  have hd1 : 1 < d := by omega
  have hb : 0 < (d^2 - 1 : ℝ) := cast_sq_sub_one_pos d hd1
  field_simp [ne_of_gt hb]
  ring

/-- The Weyl Fourier transform sends the two-valued displacement-overlap norm pattern
to the corresponding two-valued `r`-SIC correlation pattern. -/
private lemma fiducial_fourier_pattern (d r : ℕ) [NeZero d]
    (hr : 0 < r) (hrd : r < d)
    (s : Fin d × Fin d) :
    whFourierTransform d
        (fun k => if k = 0 then (r : ℂ) ^ 2
          else (((r * (d - r) : ℝ) / (d ^ 2 - 1) : ℝ) : ℂ)) s =
      (d : ℂ) * (if s = 0 then (r : ℂ)
        else (((r * (r * d - 1) : ℝ) / (d ^ 2 - 1) : ℝ) : ℂ)) := by
  rw [whFourierTransform_ite_zero]
  by_cases hs : s = 0
  · simp only [hs, ite_true]
    have h := congrArg (fun x : ℝ => (x : ℂ))
      (fiducial_fourier_value_zero d r hr hrd)
    push_cast at h
    simpa using h
  · simp only [hs, ite_false]
    have h := congrArg (fun x : ℝ => (x : ℂ))
      (fiducial_fourier_value_ne_zero d r hr hrd)
    push_cast at h
    simpa using h

/-- Simultaneously translating both indices of a Weyl--Heisenberg orbit preserves the
trace of the product of the corresponding projectors. -/
private lemma WHCovariantFamily_pair_trace_translate
    (P : Mat(d, ℂ)) (a p q : Fin d × Fin d) :
    (WHCovariantFamily P (a + p) * WHCovariantFamily P (a + q)).trace =
      (WHCovariantFamily P p * WHCovariantFamily P q).trace := by
  let A := WHCovariantFamily P p
  let B := WHCovariantFamily P q
  have hA : WHCovariantFamily P (a + p) =
      displacementOperator d a * A * (displacementOperator d a).conjTranspose := by
    exact (displacementOperator_conjugation_comp d a p P).symm
  have hB : WHCovariantFamily P (a + q) =
      displacementOperator d a * B * (displacementOperator d a).conjTranspose := by
    exact (displacementOperator_conjugation_comp d a q P).symm
  rw [hA, hB]
  have hmul :
      (displacementOperator d a * A * (displacementOperator d a).conjTranspose) *
          (displacementOperator d a * B * (displacementOperator d a).conjTranspose) =
        displacementOperator d a * (A * B) * (displacementOperator d a).conjTranspose := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (displacementOperator d a).conjTranspose (displacementOperator d a),
      conjTranspose_mul_displacementOperator, Matrix.one_mul]
  rw [hmul]
  simpa [WHCovariantFamily, A, B] using WHCovariantFamily_trace (A * B) a

/-- The trace pairing of two members of a Weyl--Heisenberg orbit depends only on their
index difference. -/
private lemma WHCovariantFamily_pair_trace
    (P : Mat(d, ℂ)) (p q : Fin d × Fin d) :
    (WHCovariantFamily P p * WHCovariantFamily P q).trace =
      (WHCovariantFamily P (-p + q) * P).trace := by
  have h := WHCovariantFamily_pair_trace_translate P (-p) p q
  rw [← h, neg_add_cancel]
  change (WHCovariantFamily P ((0 : Fin d), (0 : Fin d)) *
      WHCovariantFamily P (-p + q)).trace = _
  rw [WHCovariantFamily_zero, Matrix.trace_mul_comm]

/-- Weyl--Heisenberg conjugation preserves matrix rank. -/
private lemma WHCovariantFamily_rank
    (P : Mat(d, ℂ)) (hP : P.rank = r) (p : Fin d × Fin d) :
    (WHCovariantFamily P p).rank = r := by
  rw [WHCovariantFamily,
    Matrix.rank_mul_eq_left_of_isUnit_det _ _
      (Matrix.isUnit_det_of_left_inverse (displacementOperator_mul_conjTranspose d p)),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _
      (Matrix.isUnit_det_of_left_inverse (conjTranspose_mul_displacementOperator d p)), hP]

/-- Weyl--Heisenberg conjugation preserves the property of being a rank-`r`
Hermitian projector. -/
lemma WHCovariantFamily_isRankRHProjector (P : Mat(d, ℂ))
    (hP : IsRankRHProjector r P) (p : Fin d × Fin d) :
    IsRankRHProjector r (WHCovariantFamily P p) := {
  isHProjector := {
    hermitian := WHCovariantFamily_isHermitian P hP.isHProjector.hermitian p
    idempotent := WHCovariantFamily_idempotent P hP.isHProjector.idempotent p
  }
  rank_eq := WHCovariantFamily_rank P hP.rank_eq p
}

/-- The autocorrelation of a Hermitian matrix under displacement conjugation is the
Weyl Fourier transform of its overlap norm-squares, scaled by `1 / d`. -/
private lemma conjugation_correlation_eq_fourier
    {M : Mat(d, ℂ)} (hM : M.IsHermitian) (p : Fin d × Fin d) :
    ((displacementOperator d p * M * (displacementOperator d p).conjTranspose) * M).trace =
      (d : ℂ)⁻¹ * whFourierTransform d
        (fun k => (Complex.normSq (overlap M k) : ℂ)) p := by
  simpa [whFourierTransform, overlap, mul_comm] using
    displacementOperator_conjugation_correlation d hM p

/-- The displacement overlap at the origin is the trace of the matrix. -/
private lemma overlap_zero (P : Mat(d, ℂ)) :
    overlap P 0 = P.trace := by
  change overlap P ((0 : Fin d), (0 : Fin d)) = P.trace
  simp [overlap, displacementOperator_zero, conjTranspose_one]

/-- Rearranges the conjugation-correlation formula so that the Fourier transform of
overlap norm-squares equals `d` times the orbit correlation. -/
private lemma normSq_fourier_eq_d_mul_correlation
    (P : Mat(d, ℂ)) (hP : P.IsHermitian) (s : Fin d × Fin d) :
    whFourierTransform d (fun k => (Complex.normSq (overlap P k) : ℂ)) s =
      (d : ℂ) * (WHCovariantFamily P s * P).trace := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hcorrelation := conjugation_correlation_eq_fourier hP s
  change (WHCovariantFamily P s * P).trace =
    (d : ℂ)⁻¹ * whFourierTransform d
      (fun k => (Complex.normSq (overlap P k) : ℂ)) s at hcorrelation
  calc
    whFourierTransform d (fun k => (Complex.normSq (overlap P k) : ℂ)) s =
        (d : ℂ) * ((d : ℂ)⁻¹ * whFourierTransform d
          (fun k => (Complex.normSq (overlap P k) : ℂ)) s) := by field_simp
    _ = (d : ℂ) * (WHCovariantFamily P s * P).trace := by rw [← hcorrelation]

/-- For a rank strictly between zero and `d`, the two-valued `r`-SIC correlation
condition is equivalent to the prescribed two-valued displacement-overlap norm-square
pattern. -/
private lemma fiducial_correlation_iff_normSq_pattern
    (P : Mat(d, ℂ)) (hP : P.IsHermitian)
    (r : ℕ) (hr : 0 < r) (hrd : r < d) :
    (∀ s : Fin d × Fin d,
      (WHCovariantFamily P s * P).trace =
        if s = 0 then (r : ℂ)
        else (((r * (r * d - 1) : ℝ) / (d ^ 2 - 1) : ℝ) : ℂ)) ↔
      ∀ k : Fin d × Fin d,
        (Complex.normSq (overlap P k) : ℂ) =
          if k = 0 then (r : ℂ) ^ 2
          else (((r * (d - r) : ℝ) / (d ^ 2 - 1) : ℝ) : ℂ) := by
  constructor
  · intro hcorrelation
    let f : Fin d × Fin d → ℂ :=
      fun k => (Complex.normSq (overlap P k) : ℂ)
    let g : Fin d × Fin d → ℂ :=
      fun k => if k = 0 then (r : ℂ) ^ 2
        else (((r * (d - r) : ℝ) / (d ^ 2 - 1) : ℝ) : ℂ)
    have hfg : f = g := by
      apply whFourierTransform_injective d
      funext s
      calc
        whFourierTransform d f s =
            (d : ℂ) * (WHCovariantFamily P s * P).trace :=
          normSq_fourier_eq_d_mul_correlation P hP s
        _ = (d : ℂ) * (if s = 0 then (r : ℂ)
            else (((r * (r * d - 1) : ℝ) / (d ^ 2 - 1) : ℝ) : ℂ)) := by
          rw [hcorrelation]
        _ = whFourierTransform d g s := (fiducial_fourier_pattern d r hr hrd s).symm
    exact congrFun hfg
  · intro hpattern s
    change ((displacementOperator d s * P * (displacementOperator d s).conjTranspose) * P).trace = _
    rw [conjugation_correlation_eq_fourier hP]
    rw [show (fun k => (Complex.normSq (overlap P k) : ℂ)) =
        (fun k => if k = 0 then (r : ℂ) ^ 2
          else (((r * (d - r) : ℝ) / (d ^ 2 - 1) : ℝ) : ℂ)) from funext hpattern,
      fiducial_fourier_pattern d r hr hrd]
    have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
    field_simp

/-- A rank-`r` Hermitian projector whose WH orbit has the stated two-valued correlation
pattern, with off-diagonal value different from `r`, generates an `r`-SIC. -/
private lemma WHCovariantFamily_isRSIC_of_correlation
    (P : Mat(d, ℂ)) (hP : IsRankRHProjector r P)
    (β : ℂ) (hβ : β ≠ (r : ℂ))
    (hcorrelation : ∀ s : Fin d × Fin d,
      (WHCovariantFamily P s * P).trace = if s = 0 then (r : ℂ) else β) :
    IsRSIC r (WHCovariantFamily P) := by
  have htraceP : P.trace = (r : ℂ) := hP.trace_eq
  have hequiangular : ∀ p q : Fin d × Fin d, p ≠ q →
      (WHCovariantFamily P p * WHCovariantFamily P q).trace = β := by
    intro p q hpq
    rw [WHCovariantFamily_pair_trace]
    have hdiff : -p + q ≠ 0 := fun hzero => hpq (neg_add_eq_zero.mp hzero)
    rw [hcorrelation, ite_eq_right hdiff]
  refine {
    isRankRHProjector := WHCovariantFamily_isRankRHProjector P hP
    equiangular := ⟨β, hequiangular⟩
    distinct := ?_
  }
  intro p q heq
  by_contra hpq
  have htrace := hequiangular p q hpq
  rw [heq, ← sq, WHCovariantFamily_idempotent P hP.isHProjector.idempotent q,
    WHCovariantFamily_trace, htraceP] at htrace
  exact hβ htrace.symm

/-- The prescribed nonzero overlap norm-square is positive for an interior rank. -/
private lemma fiducial_overlap_normSq_pos (d r : ℕ) (hr : 0 < r) (hrd : r < d) :
    0 < (r * (d - r) : ℝ) / (d ^ 2 - 1) := by
  have hd1 : 1 < d := by omega
  exact div_pos
    (mul_pos (by exact_mod_cast hr) (sub_pos.mpr (by exact_mod_cast hrd)))
    (cast_sq_sub_one_pos d hd1)

/-- For an interior rank, the prescribed off-diagonal correlation is less than the rank. -/
private lemma fiducial_correlation_value_lt_rank (d r : ℕ)
    (hr : 0 < r) (hrd : r < d) :
    (r * (r * d - 1) : ℝ) / (d ^ 2 - 1) < (r : ℝ) := by
  have hgap := rsic_alpha_gap d r hr hrd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast lt_trans hr hrd
  nlinarith [mul_pos hdR (fiducial_overlap_normSq_pos d r hr hrd)]

/-- The total norm-square criterion underlying `fiducial_condition`.

For a rank-`r` H-projector with `0 < r < d`, fiduciality is equivalent to
`|μ₀|² = r²` and `|μ_p|² = r(d-r)/(d²-1)` for `p ≠ 0`. Including the origin, whose value is forced
by the projector trace, makes this form directly compatible with the two-valued WH correlation
pattern; `fiducial_condition` converts it to the source's nonzero-index norm criterion. -/
theorem fiducial_normSq_condition (r : ℕ) (P₀ : Mat(d, ℂ))
    (hproj : IsRankRHProjector r P₀) (hr : 0 < r) (hrd : r < d) :
    IsFiducial r P₀ ↔
      ∀ k : Fin d × Fin d,
        (Complex.normSq (overlap P₀ k) : ℂ) =
          if k = 0 then (r : ℂ) ^ 2
          else (((r * (d - r) : ℝ) / (d ^ 2 - 1) : ℝ) : ℂ) := by
  have hd1 : 1 < d := by omega
  rw [← fiducial_correlation_iff_normSq_pattern P₀ hproj.isHProjector.hermitian
    r hr hrd]
  constructor
  · intro hfid s
    by_cases hs : s = 0
    · subst s
      simp only [ite_true]
      rw [show WHCovariantFamily P₀ (0 : Fin d × Fin d) = P₀ by
        change WHCovariantFamily P₀ ((0, 0) : Fin d × Fin d) = P₀
        exact WHCovariantFamily_zero P₀]
      rw [← sq, hproj.isHProjector.idempotent, hproj.trace_eq]
    · have hsic := rsic_trace_formula r hd1 (WHCovariantFamily P₀) hfid.isRSIC s 0
      rw [ite_eq_right hs] at hsic
      rw [show WHCovariantFamily P₀ (0 : Fin d × Fin d) = P₀ by
        change WHCovariantFamily P₀ ((0, 0) : Fin d × Fin d) = P₀
        exact WHCovariantFamily_zero P₀] at hsic
      simp only [hs, ite_false]
      rw [hsic]
      push_cast
      rfl
  · intro hcorrelation
    exact ⟨hproj, WHCovariantFamily_isRSIC_of_correlation P₀ hproj _
      (by exact_mod_cast (fiducial_correlation_value_lt_rank d r hr hrd).ne) hcorrelation⟩

/-- [AFK25, Theorem 1.8, `thm:sicfidcond`]: a rank-`r` H-projector `Π` is a WH-covariant
`r`-SIC fiducial if and only if
`|μ_p| = √(r(d-r)/(d²-1))` for every `p ≠ 0 mod d`, where `μ_p = Tr(Π D_p†)`.

The assumptions `0 < r` and `r < d` exclude the endpoint cases, where the norm condition
holds for a constant orbit that is not an `r`-SIC. -/
@[source "AFK25, Theorem 1.8, p. 6, thm:sicfidcond"]
theorem fiducial_condition (r : ℕ) (P₀ : Mat(d, ℂ))
    (hproj : IsRankRHProjector r P₀) (hr : 0 < r) (hrd : r < d) :
    IsFiducial r P₀ ↔
      ∀ p : Fin d × Fin d, p ≠ (0, 0) →
        ‖overlap P₀ p‖ = Real.sqrt ((r * (d - r) : ℝ) / (d ^ 2 - 1)) := by
  rw [fiducial_normSq_condition r P₀ hproj hr hrd]
  have hc := fiducial_overlap_normSq_pos d r hr hrd
  constructor
  · intro hpattern p hp
    apply (norm_eq_sqrt_iff_normSq_eq (overlap P₀ p) _ hc.le).2
    have hp0 : p ≠ (0 : Fin d × Fin d) := by
      change p ≠ ((0, 0) : Fin d × Fin d)
      exact hp
    exact Complex.ofReal_injective (by simpa [hp0] using hpattern p)
  · intro hnorm k
    by_cases hk : k = 0
    · subst k
      simp only [ite_true]
      rw [overlap_zero, hproj.trace_eq]
      norm_num [Complex.normSq_eq_norm_sq]
    · simp only [hk, ite_false]
      change k ≠ ((0, 0) : Fin d × Fin d) at hk
      exact congrArg (fun x : ℝ => (x : ℂ))
        ((norm_eq_sqrt_iff_normSq_eq (overlap P₀ k) _ hc.le).mp (hnorm k hk))

/-- The construction form of `fiducial_condition`: a rank-`r` H-projector with `0 < r < d` is an
`r`-SIC fiducial once every nonzero displacement overlap has norm `√(r(d-r)/(d²-1))`.

Candidate constructions use this result to reduce fiduciality to the projector and overlap-norm
checks. -/
theorem isFiducial_of_overlap_norm (r : ℕ) (P₀ : Mat(d, ℂ))
    (hproj : IsRankRHProjector r P₀) (hr : 0 < r) (hrd : r < d)
    (hnorm : ∀ p : Fin d × Fin d, p ≠ (0, 0) →
      ‖overlap P₀ p‖ = Real.sqrt ((r * (d - r) : ℝ) / (d ^ 2 - 1))) :
    IsFiducial r P₀ :=
  (fiducial_condition r P₀ hproj hr hrd).mpr hnorm

end SIC

end
