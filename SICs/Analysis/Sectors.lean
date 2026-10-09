/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# Rays and sectors at infinity

Vertical lines and translated horizontal segments lie in sectors; complex affine maps and
division by nearby periods preserve sectors quantitatively, including uniformly parameterized
affine families.

An *upper sector* is described along a filter by `Im z → +∞` together with an eventual bound
`|Re z| ≤ K Im z`; lower sectors are the reflections under `z ↦ -z`. This is the form in which
`SICs.SpecialFunctions.Faddeev.Asymptotics` states the limits of the Faddeev generator and
`SICs.Principal.Dilogarithm.Faddeev.Asymptotics` those of the principal product, and in which
bounded real translates of vertical rays enter them.

For complex periods near a positive real number, division has an imaginary part bounded below by
a fixed positive multiple of the original height throughout any upper sector. Subtracting
`⌊Re z - a⌋` first puts the real part in `[a, a + 1]`; the same estimate then applies uniformly to
all finite phases indexed between this integer and zero.

## The argument

On the vertical line `z = x + it`, the real part is fixed at `x` while the imaginary part is `t`,
so `|x| ≤ |t|` eventually in either direction. Under `z ↦ cz + b` with
real `c > 0` and `b`, the imaginary part is multiplied by `c` and the real part moves by `|b|`,
which is eventually at most `c Im z`; the slope grows by one.

For `az + b` with `a` near a positive real number and `b` near a fixed complex number, expand
both coordinates. The small imaginary part of `a` is multiplied by `Re z`, so the sector
inequality absorbs it into `Im z`; above a fixed height, the bounded contribution from `b` is
absorbed as well. The imaginary coordinate therefore stays above a positive multiple of `Im z`,
while the real coordinate is bounded by another multiple of it. Continuity makes these coefficient
bounds uniform near a parameter, and reflection gives the corresponding lower-sector statement.

Write `τ = u + iv` and `z = x + iy`. Then `Im(z/τ) = (yu - xv)/‖τ‖²`. If `τ` is sufficiently
close to `τ₀ > 0`, its real part stays above `3τ₀/4`, its imaginary part is small enough that the
sector bound on `x` makes `|xv| ≤ τ₀y/4`, and `‖τ‖² ≤ 4τ₀²`. Hence
`Im(z/τ) ≥ y/(8τ₀)`. For the floor phases, the unit-window bound and an index between the floor
and zero give a new sector bound, so the same division estimate applies to every phase at once.
-/

noncomputable section

open Complex Filter Set
open scoped Topology

namespace SIC

/-! ### Vertical lines

On `z = x + it`, the imaginary part tends to the corresponding infinity while `|x|` is
eventually bounded by `t` above and `-t` below. -/

/-- The vertical line `x + it` eventually lies in the upper sector of slope one:
`Im(x + it) → +∞` and eventually `|Re(x + it)| ≤ Im(x + it)`. -/
theorem upperVerticalLine_sector (x : ℝ) :
    Tendsto (fun t : ℝ => (((x : ℂ) + t * I)).im) atTop atTop ∧
      ∀ᶠ t : ℝ in atTop, |(((x : ℂ) + t * I)).re| ≤
        (1 : ℝ) * (((x : ℂ) + t * I)).im := by
  constructor
  · convert (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop) using 1
    funext t
    simp
  · filter_upwards [eventually_ge_atTop |x|] with t ht
    simpa using ht

/-- The vertical line `x + it` eventually lies in the lower sector of slope one:
`Im(x + it) → -∞` and eventually `|Re(x + it)| ≤ -Im(x + it)`. -/
theorem lowerVerticalLine_sector (x : ℝ) :
    Tendsto (fun t : ℝ => (((x : ℂ) + t * I)).im) atBot atBot ∧
      ∀ᶠ t : ℝ in atBot, |(((x : ℂ) + t * I)).re| ≤
        (1 : ℝ) * -(((x : ℂ) + t * I)).im := by
  constructor
  · convert (tendsto_id : Tendsto (fun t : ℝ => t) atBot atBot) using 1
    funext t
    simp
  · filter_upwards [eventually_le_atBot (-|x|)] with t ht
    simpa using (show |x| ≤ -t by linarith)

/-! ### Horizontal segments

A fixed real segment translated to height `σY`, where `σ = ±1`, eventually lies in the
corresponding sector. A sector decay estimate is therefore uniform along the segment. -/

/-- A sector exponential bound for `f` gives a decaying uniform bound on every fixed
horizontal segment translated to height `σY`, for either `σ = 1` or `σ = -1`. -/
theorem exists_horizontal_segment_bound_of_sector (f : ℂ → ℂ) (a b s σ C κ R : ℝ)
    (hσ : σ ^ 2 = 1) (hκ : 0 < κ)
    (hbound : ∀ z : ℂ, |z.re| ≤ σ * z.im → R ≤ σ * z.im →
      ‖f z‖ ≤ C * Real.exp (-κ * (σ * z.im))) :
    ∃ g : ℝ → ℝ, Tendsto g atTop (𝓝 0) ∧
      ∀ᶠ Y : ℝ in atTop, ∀ t ∈ uIcc a b,
        ‖f ((t : ℂ) + (σ * Y) * I - (s : ℂ))‖ ≤ g Y := by
  have hdecay : Tendsto (fun Y : ℝ => C * Real.exp (-κ * Y)) atTop (𝓝 0) := by
    have hκY : Tendsto (fun Y : ℝ => κ * Y) atTop atTop :=
      (tendsto_id : Tendsto (fun Y : ℝ => Y) atTop atTop).const_mul_atTop hκ
    simpa only [Function.comp_def, mul_zero, neg_mul] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hκY).const_mul C
  refine ⟨fun Y => C * Real.exp (-κ * Y), hdecay, ?_⟩
  filter_upwards [eventually_ge_atTop (max R (max |a - s| |b - s|))]
    with Y hY t ht
  have hts : |t - s| ≤ max |a - s| |b - s| := by
    rcases Set.mem_uIcc.mp ht with h | h
    · exact abs_le_max_abs_abs (sub_le_sub_right h.1 s) (sub_le_sub_right h.2 s)
    · simpa [max_comm] using
        abs_le_max_abs_abs (sub_le_sub_right h.1 s) (sub_le_sub_right h.2 s)
  have hre : ((t : ℂ) + (σ * Y) * I - (s : ℂ)).re = t - s := by simp
  have him : ((t : ℂ) + (σ * Y) * I - (s : ℂ)).im = σ * Y := by simp
  have hheight : σ * (σ * Y) = Y := by
    rw [← mul_assoc, ← pow_two, hσ, one_mul]
  have hsector : |((t : ℂ) + (σ * Y) * I - (s : ℂ)).re| ≤
      σ * ((t : ℂ) + (σ * Y) * I - (s : ℂ)).im := by
    rw [hre, him, hheight]
    exact hts.trans ((le_max_right _ _).trans hY)
  have hR : R ≤ σ * ((t : ℂ) + (σ * Y) * I - (s : ℂ)).im := by
    rw [him, hheight]
    exact (le_max_left _ _).trans hY
  simpa only [him, hheight] using hbound _ hsector hR

/-! ### Affine images of sectors -/

/-- If `Im z → +∞` with eventually `|Re z| ≤ K Im z`, and `w` has `Im w = c Im z` and
`Re w = c Re z + b` for real `c > 0` and `b`, then `Im w → +∞` with eventually
`|Re w| ≤ (K + 1) Im w`: a real affine map with positive slope carries an upper sector into an
upper sector. -/
theorem upperSector_affine {α : Type*} {l : Filter α} (z w : α → ℂ) {c : ℝ} (b K : ℝ)
    (hc : 0 < c) (him : ∀ a, (w a).im = c * (z a).im)
    (hre : ∀ a, (w a).re = c * (z a).re + b)
    (hz : Tendsto (fun a => (z a).im) l atTop)
    (hK : ∀ᶠ a in l, |(z a).re| ≤ K * (z a).im) :
    Tendsto (fun a => (w a).im) l atTop ∧
      ∀ᶠ a in l, |(w a).re| ≤ (K + 1) * (w a).im := by
  constructor
  · convert hz.const_mul_atTop hc using 1
    funext a
    exact him a
  · filter_upwards [hK, hz.eventually (eventually_ge_atTop (|b| / c))] with a ha hy
    rw [hre a, him a]
    have hb : |b| ≤ c * (z a).im := by
      apply (div_le_iff₀ hc).mp at hy
      nlinarith
    calc
      |c * (z a).re + b| ≤ |c * (z a).re| + |b| := abs_add_le _ _
      _ = c * |(z a).re| + |b| := by rw [abs_mul, abs_of_pos hc]
      _ ≤ c * (K * (z a).im) + c * (z a).im :=
        add_le_add (mul_le_mul_of_nonneg_left ha hc.le) hb
      _ = (K + 1) * (c * (z a).im) := by ring

/-! ### Complex affine images near real coefficients

A complex affine map whose slope is close to a positive real number and whose intercept is close
to any fixed complex number carries every sufficiently high upper-sector point into one fixed
upper sector.
-/

/-- Bounds the real coordinate by distance from a complex center; used by
`affine_re_bound_near_real`. -/
private lemma abs_re_le_abs_add_of_norm_sub (z z₀ : ℂ) (ε : ℝ)
    (hz : ‖z - z₀‖ ≤ ε) : |z.re| ≤ |z₀.re| + ε := by
  have hcoord := (Complex.abs_re_le_norm (z - z₀)).trans hz
  simp only [Complex.sub_re] at hcoord
  rw [show z.re = (z.re - z₀.re) + z₀.re by ring]
  calc
    |z.re - z₀.re + z₀.re| ≤ |z.re - z₀.re| + |z₀.re| := abs_add_le _ _
    _ ≤ ε + |z₀.re| := add_le_add hcoord le_rfl
    _ = |z₀.re| + ε := by ring

/-- Bounds the imaginary part of a nearby complex affine image from below; used by
`exists_upperSector_affine_near_real`. -/
private lemma affine_im_lower_bound_near_real (a b z : ℂ) (a₀ : ℝ) (b₀ : ℂ) (K ε : ℝ)
    (hsmall : ε * (|K| + 2) ≤ a₀ / 4)
    (ha : ‖a - (a₀ : ℂ)‖ ≤ ε) (hb : ‖b - b₀‖ ≤ ε)
    (hz : |z.re| ≤ K * z.im) (hy : 0 ≤ z.im)
    (hintercept : |b₀.im| + ε ≤ a₀ / 4 * z.im) :
    a₀ / 2 * z.im ≤ (a * z + b).im := by
  have hε : 0 ≤ ε := (norm_nonneg (a - (a₀ : ℂ))).trans ha
  have hare := (Complex.abs_re_le_norm (a - (a₀ : ℂ))).trans ha
  have haim := (Complex.abs_im_le_norm (a - (a₀ : ℂ))).trans ha
  have hbim := (Complex.abs_im_le_norm (b - b₀)).trans hb
  simp only [Complex.sub_re, Complex.ofReal_re] at hare
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at haim
  simp only [Complex.sub_im] at hbim
  have hz' : |z.re| ≤ |K| * z.im :=
    hz.trans (mul_le_mul_of_nonneg_right (le_abs_self K) hy)
  have hare' : (a₀ - ε) * z.im ≤ a.re * z.im := by
    apply mul_le_mul_of_nonneg_right _ hy
    linarith [(abs_le.mp hare).1]
  have hcrossAbs : |a.im * z.re| ≤ ε * (|K| * z.im) := by
    rw [abs_mul]
    exact mul_le_mul haim hz' (abs_nonneg _) hε
  have hcross : -(ε * (|K| * z.im)) ≤ a.im * z.re := by
    nlinarith [neg_abs_le (a.im * z.re)]
  have hbim' : -(|b₀.im| + ε) ≤ b.im := by
    nlinarith [(abs_le.mp hbim).1, neg_le_abs b₀.im]
  have herr := mul_le_mul_of_nonneg_right hsmall hy
  simp only [Complex.add_im, Complex.mul_im]
  nlinarith

/-- Bounds the real part of a nearby complex affine image from above; used by
`exists_upperSector_affine_near_real`. -/
private lemma affine_re_bound_near_real (a b z : ℂ) (a₀ : ℝ) (b₀ : ℂ) (K ε : ℝ)
    (ha₀ : 0 < a₀) (ha : ‖a - (a₀ : ℂ)‖ ≤ ε) (hb : ‖b - b₀‖ ≤ ε)
    (hz : |z.re| ≤ K * z.im) (hy : 1 ≤ z.im) :
    |(a * z + b).re| ≤ ((a₀ + ε) * |K| + |b₀.re| + 2 * ε) * z.im := by
  have hε : 0 ≤ ε := (norm_nonneg (a - (a₀ : ℂ))).trans ha
  have haim := (Complex.abs_im_le_norm (a - (a₀ : ℂ))).trans ha
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at haim
  have hy0 : 0 ≤ z.im := by linarith
  have hz' : |z.re| ≤ |K| * z.im :=
    hz.trans (mul_le_mul_of_nonneg_right (le_abs_self K) hy0)
  have hareAbs : |a.re| ≤ a₀ + ε := by
    simpa [abs_of_pos ha₀] using abs_re_le_abs_add_of_norm_sub a (a₀ : ℂ) ε ha
  have hbreAbs := abs_re_le_abs_add_of_norm_sub b b₀ ε hb
  have hfirst : |a.re * z.re| ≤ (a₀ + ε) * (|K| * z.im) := by
    rw [abs_mul]
    exact mul_le_mul hareAbs hz' (abs_nonneg _) (by positivity)
  have hsecond : |a.im * z.im| ≤ ε * z.im := by
    rw [abs_mul, abs_of_nonneg hy0]
    exact mul_le_mul_of_nonneg_right haim hy0
  have hthird : |b.re| ≤ (|b₀.re| + ε) * z.im :=
    hbreAbs.trans (by nlinarith [abs_nonneg b₀.re])
  rw [Complex.add_re, Complex.mul_re]
  calc
    |a.re * z.re - a.im * z.im + b.re| ≤
        |a.re * z.re - a.im * z.im| + |b.re| := abs_add_le _ _
    _ ≤ (|a.re * z.re| + |a.im * z.im|) + |b.re| :=
      add_le_add (abs_sub _ _) le_rfl
    _ ≤ (a₀ + ε) * (|K| * z.im) + ε * z.im + (|b₀.re| + ε) * z.im := by
      gcongr
    _ = ((a₀ + ε) * |K| + |b₀.re| + 2 * ε) * z.im := by ring

/-- Complex affine maps with slope uniformly near `a₀ > 0` and intercept uniformly near the
complex number `b₀` send all sufficiently high points of an upper sector into one quantitative
upper sector. -/
theorem exists_upperSector_affine_near_real {a₀ : ℝ} (ha₀ : 0 < a₀) (b₀ : ℂ) (K : ℝ) :
    ∃ ε c L R : ℝ, 0 < ε ∧ 0 < c ∧ 0 < L ∧ 0 < R ∧
      ∀ (a b z : ℂ), ‖a - (a₀ : ℂ)‖ ≤ ε → ‖b - b₀‖ ≤ ε →
        |z.re| ≤ K * z.im → R ≤ z.im →
        c * z.im ≤ (a * z + b).im ∧
          |(a * z + b).re| ≤ L * (a * z + b).im := by
  let ε := a₀ / (4 * (|K| + 2))
  let c := a₀ / 2
  let B := |b₀.im| + ε
  let R := max 1 (4 * B / a₀)
  let D := (a₀ + ε) * |K| + |b₀.re| + 2 * ε
  let L := D / c
  have hε : 0 < ε := div_pos ha₀ (mul_pos (by norm_num) (by positivity))
  have hc : 0 < c := div_pos ha₀ (by norm_num)
  have hR : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hD : 0 < D := by dsimp [D]; positivity
  have hL : 0 < L := div_pos hD hc
  have hsmall : ε * (|K| + 2) = a₀ / 4 := by dsimp [ε]; field_simp
  refine ⟨ε, c, L, R, hε, hc, hL, hR, fun a b z ha hb hz hy => ?_⟩
  have hy1 : 1 ≤ z.im := (le_max_left _ _).trans (by simpa [R] using hy)
  have hBheight : B ≤ a₀ / 4 * z.im := by
    have hquot : 4 * B / a₀ ≤ z.im :=
      (le_max_right _ _).trans (by simpa [R] using hy)
    have := (div_le_iff₀ ha₀).mp hquot
    nlinarith
  have him := affine_im_lower_bound_near_real a b z a₀ b₀ K ε hsmall.le
    ha hb hz (by linarith) (by simpa [B] using hBheight)
  have hre := affine_re_bound_near_real a b z a₀ b₀ K ε ha₀ ha hb hz hy1
  refine ⟨by simpa [c] using him, hre.trans ?_⟩
  calc
    D * z.im = (D / c) * (c * z.im) := by field_simp
    _ ≤ (D / c) * (a * z + b).im :=
      mul_le_mul_of_nonneg_left (by simpa [c] using him) (div_nonneg hD.le hc.le)
    _ = L * (a * z + b).im := by rfl

/-- A continuous map between seminormed additive groups stays within any prescribed closed ball
about its value on a sufficiently small closed ball about the input point. -/
lemma ContinuousAt.exists_norm_sub_le
    {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    {f : E → F} {x : E}
    (hf : ContinuousAt f x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : E, ‖q - x‖ ≤ δ → ‖f q - f x‖ ≤ ε := by
  have hnear : {q : E | f q ∈ Metric.closedBall (f x) ε} ∈ nhds x :=
    hf (Metric.closedBall_mem_nhds _ hε)
  obtain ⟨δ, hδ, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  refine ⟨δ, hδ, fun q hq => ?_⟩
  have hmem := hsub (show q ∈ Metric.closedBall x δ by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hq)
  simpa only [Metric.mem_closedBall, dist_eq_norm, Set.mem_ofPred_eq] using hmem

/-- Continuous affine families whose limiting slope is positive real send one uniform upper
sector into another. -/
theorem exists_upperSector_affine_near_parameter
    {q₀ : ℂ} {a b : ℂ → ℂ} {a₀ : ℝ}
    (ha : ContinuousAt a q₀) (hb : ContinuousAt b q₀)
    (ha₀ : a q₀ = (a₀ : ℂ)) (ha₀pos : 0 < a₀) (K : ℝ) :
    ∃ ε c L R : ℝ, 0 < ε ∧ 0 < c ∧ 0 < L ∧ 0 < R ∧
      ∀ (q z : ℂ), ‖q - q₀‖ ≤ ε → |z.re| ≤ K * z.im → R ≤ z.im →
        c * z.im ≤ (a q * z + b q).im ∧
          |(a q * z + b q).re| ≤ L * (a q * z + b q).im := by
  obtain ⟨εg, c, L, R, hεg, hc, hL, hR, hgeom⟩ :=
    exists_upperSector_affine_near_real ha₀pos (b q₀) K
  obtain ⟨δa, hδa, ha'⟩ := ContinuousAt.exists_norm_sub_le ha hεg
  obtain ⟨δb, hδb, hb'⟩ := ContinuousAt.exists_norm_sub_le hb hεg
  refine ⟨min δa δb, c, L, R, by positivity, hc, hL, hR, ?_⟩
  intro q z hq hz hy
  have haq : ‖a q - (a₀ : ℂ)‖ ≤ εg := by
    simpa only [ha₀] using ha' q (hq.trans (min_le_left _ _))
  have hbq : ‖b q - b q₀‖ ≤ εg :=
    hb' q (hq.trans (min_le_right _ _))
  exact hgeom (a q) (b q) z haq hbq hz hy

/-- Continuous affine families whose limiting slope is positive real send one uniform lower
sector into another. This is the upper-sector geometry applied to `-z` and the negated
intercept. -/
theorem exists_lowerSector_affine_near_parameter
    {q₀ : ℂ} {a b : ℂ → ℂ} {a₀ : ℝ}
    (ha : ContinuousAt a q₀) (hb : ContinuousAt b q₀)
    (ha₀ : a q₀ = (a₀ : ℂ)) (ha₀pos : 0 < a₀) (K : ℝ) :
    ∃ ε c L R : ℝ, 0 < ε ∧ 0 < c ∧ 0 < L ∧ 0 < R ∧
      ∀ (q z : ℂ), ‖q - q₀‖ ≤ ε → |z.re| ≤ K * (-z.im) → R ≤ -z.im →
        c * (-z.im) ≤ -(a q * z + b q).im ∧
          |(a q * z + b q).re| ≤ L * (-(a q * z + b q).im) := by
  obtain ⟨ε, c, L, R, hε, hc, hL, hR, hgeom⟩ :=
    exists_upperSector_affine_near_parameter
      (a := a) (b := fun q => -b q) ha hb.neg ha₀ ha₀pos K
  refine ⟨ε, c, L, R, hε, hc, hL, hR, fun q z hq hz hy => ?_⟩
  have hg := hgeom q (-z) hq
    (by simpa only [Complex.neg_re, Complex.neg_im, abs_neg] using hz)
    (by simpa only [Complex.neg_im] using hy)
  have heq : a q * (-z) + -b q = -(a q * z + b q) := by ring
  rw [heq] at hg
  exact ⟨by simpa only [Complex.neg_im] using hg.1,
    by simpa only [Complex.neg_re, Complex.neg_im, abs_neg] using hg.2⟩

/-! ### Quantitative division of upper sectors

Integer translation into a fixed real unit window controls both the translation count and the
real parts of the finite shift phases. Division by a complex period sufficiently close to a
positive real period then preserves a fixed positive fraction of the imaginary part. -/

/-- Norm closeness to a real centre gives a lower bound on the real coordinate and an upper
bound on the absolute imaginary coordinate. -/
lemma re_ge_and_abs_im_le_of_norm_sub_le {τ : ℂ} {τ₀ ε b M : ℝ}
    (hτ : ‖τ - (τ₀ : ℂ)‖ ≤ ε) (hεb : ε ≤ τ₀ - b) (hεM : ε ≤ M) :
    b ≤ τ.re ∧ |τ.im| ≤ M := by
  have hre := Complex.abs_re_le_norm (τ - (τ₀ : ℂ))
  have him := Complex.abs_im_le_norm (τ - (τ₀ : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at him
  refine ⟨?_, (him.trans hτ).trans hεM⟩
  linarith [abs_le.mp (hre.trans hτ) |>.1]

/-- Subtracting `⌊Re z - a⌋` puts `z` in the real window `[a, a + 1]`; if
`|Re z| ≤ K Im z`, the translation count is at most `K Im z + |a| + 1`. -/
lemma floor_window_of_abs_re_le (z : ℂ) (a K : ℝ) (hre : |z.re| ≤ K * z.im) :
    let n : ℤ := ⌊z.re - a⌋
    (z - (n : ℂ)).re ∈ Set.Icc a (a + 1) ∧
      |(n : ℝ)| ≤ K * z.im + |a| + 1 := by
  dsimp
  let n : ℤ := ⌊z.re - a⌋
  have hlo : (n : ℝ) ≤ z.re - a := Int.floor_le _
  have hhi : z.re - a < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have hn : |(n : ℝ)| ≤ K * z.im + |a| + 1 := by
    apply abs_le.mpr
    constructor
    · nlinarith [neg_le_abs z.re, le_abs_self a]
    · nlinarith [le_abs_self z.re, neg_le_abs a]
  have hw : (z - (n : ℂ)).re ∈ Set.Icc a (a + 1) := by
    change a ≤ z.re - (n : ℝ) ∧ z.re - (n : ℝ) ≤ a + 1
    exact ⟨by linarith, by linarith⟩
  constructor
  · simpa [n] using hw
  · simpa only [n] using hn

/-- A complex number within distance `ε < τ₀` of a positive real number `τ₀` has positive real
part. -/
lemma re_pos_of_norm_sub_le {τ : ℂ} {τ₀ ε : ℝ} (hε : ε < τ₀)
    (hτ : ‖τ - (τ₀ : ℂ)‖ ≤ ε) : 0 < τ.re := by
  have hre := (re_ge_and_abs_im_le_of_norm_sub_le (b := τ₀ - ε) (M := ε)
    hτ (by linarith) le_rfl).1
  linarith

/-- Coordinate and norm-square bounds for a complex period in the neighborhood used by
`exists_uniform_div_im_lower_bound`. -/
private lemma near_pos_real_period_bounds (τ : ℂ) (τ₀ K : ℝ) (hτ₀ : 0 < τ₀)
    (hτ : ‖τ - (τ₀ : ℂ)‖ ≤ τ₀ / (4 * (|K| + 1))) :
    3 * τ₀ / 4 ≤ τ.re ∧ |τ.im| ≤ τ₀ / (4 * (|K| + 1)) ∧
      Complex.normSq τ ≤ 4 * τ₀ ^ 2 := by
  let ε := τ₀ / (4 * (|K| + 1))
  have hε : 0 < ε := div_pos hτ₀ (mul_pos (by norm_num) (by positivity))
  have hεeq : ε * (|K| + 1) = τ₀ / 4 := by
    dsimp [ε]
    field_simp
  have hεle : ε ≤ τ₀ / 4 := by nlinarith [abs_nonneg K]
  obtain ⟨hre, him⟩ := re_ge_and_abs_im_le_of_norm_sub_le
    (b := 3 * τ₀ / 4) (M := ε) hτ (by linarith) le_rfl
  have hnorm : ‖τ‖ ≤ 2 * τ₀ := calc
    ‖τ‖ = ‖(τ - (τ₀ : ℂ)) + (τ₀ : ℂ)‖ := by ring_nf
    _ ≤ ‖τ - (τ₀ : ℂ)‖ + ‖(τ₀ : ℂ)‖ := norm_add_le _ _
    _ ≤ ε + τ₀ := by simpa [ε, Complex.norm_real, abs_of_pos hτ₀] using
      add_le_add_right hτ τ₀
    _ ≤ 2 * τ₀ := by linarith
  refine ⟨hre, him, ?_⟩
  · rw [← Complex.sq_norm]
    nlinarith [norm_nonneg τ]

/-- Uniformly near a positive real period `τ₀`, division sends every upper-sector vector to a
vector whose imaginary part is at least a fixed positive multiple of the original imaginary
part. -/
theorem exists_uniform_div_im_lower_bound {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (K : ℝ) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧
      ∀ (τ z : ℂ), ‖τ - (τ₀ : ℂ)‖ ≤ ε → 0 ≤ z.im →
        |z.re| ≤ K * z.im → c * z.im ≤ (z / τ).im := by
  let ε := τ₀ / (4 * (|K| + 1))
  let c := 1 / (8 * τ₀)
  have hε : 0 < ε := div_pos hτ₀ (mul_pos (by norm_num) (by positivity))
  have hc : 0 < c := one_div_pos.mpr (mul_pos (by norm_num) hτ₀)
  refine ⟨ε, c, hε, hc, fun τ z hτ hz hre => ?_⟩
  obtain ⟨hτre, hτim, hτnorm⟩ := near_pos_real_period_bounds τ τ₀ K hτ₀ hτ
  have hεeq : ε * (|K| + 1) = τ₀ / 4 := by
    dsimp [ε]
    field_simp
  have hzre : |z.re| ≤ |K| * z.im :=
    hre.trans (mul_le_mul_of_nonneg_right (le_abs_self K) hz)
  have herr : z.re * τ.im ≤ τ₀ / 4 * z.im := calc
    z.re * τ.im ≤ |z.re * τ.im| := le_abs_self _
    _ ≤ (|K| * z.im) * ε := by
      rw [abs_mul]
      exact mul_le_mul hzre hτim (abs_nonneg _) (mul_nonneg (abs_nonneg K) hz)
    _ ≤ τ₀ / 4 * z.im := by nlinarith [mul_nonneg (abs_nonneg K) hε.le]
  have hnum : τ₀ / 2 * z.im ≤ z.im * τ.re - z.re * τ.im := by
    nlinarith [mul_le_mul_of_nonneg_left hτre hz]
  have hτne : τ ≠ 0 := by
    apply ne_of_apply_ne Complex.re
    simp only [Complex.zero_re]
    nlinarith
  rw [Complex.div_im, ← sub_div, le_div_iff₀ (Complex.normSq_pos.mpr hτne)]
  calc
    c * z.im * Complex.normSq τ ≤ c * z.im * (4 * τ₀ ^ 2) :=
      mul_le_mul_of_nonneg_left hτnorm (mul_nonneg hc.le hz)
    _ = τ₀ / 2 * z.im := by dsimp [c]; field_simp; ring
    _ ≤ z.im * τ.re - z.re * τ.im := hnum

/-- An integer between `n` and zero has absolute value at most `|n|`; used by
`exists_uniform_floor_phase_im_lower_bound`. -/
private lemma abs_intCast_le_of_mem_Ico_min_max {n j : ℤ}
    (hj : j ∈ Set.Ico (min n 0) (max n 0)) : |(j : ℝ)| ≤ |(n : ℝ)| := by
  have hju : j ∈ Set.uIcc n 0 := by
    simpa only [Set.uIcc] using Set.Ico_subset_Icc_self hj
  have h := Set.abs_sub_right_of_mem_uIcc hju
  simp only [zero_sub, abs_neg] at h
  exact_mod_cast h

/-- The real part of every finite floor-shift phase is bounded by one fixed multiple of `Im z`;
used by `exists_uniform_floor_phase_im_lower_bound`. -/
private lemma floor_phase_re_bound (z : ℂ) (a K : ℝ) (hz : 1 ≤ z.im)
    (hre : |z.re| ≤ K * z.im) :
    let n : ℤ := ⌊z.re - a⌋
    let w : ℂ := z - (n : ℂ)
    ∀ j ∈ Set.Ico (min n 0) (max n 0),
      |(w + 1 + (j : ℂ)).re| ≤ (|K| + 2 * |a| + 3) * z.im := by
  dsimp
  let n : ℤ := ⌊z.re - a⌋
  have hfloor := floor_window_of_abs_re_le z a K hre
  have hw : (z - (n : ℂ)).re ∈ Set.Icc a (a + 1) := by simpa only [n] using hfloor.1
  have hn : |(n : ℝ)| ≤ K * z.im + |a| + 1 := by simpa only [n] using hfloor.2
  intro j hj
  have hwabs : |(z - (n : ℂ)).re| ≤ |a| + 1 := by
    rw [abs_le]
    constructor
    · nlinarith [hw.1, neg_le_abs a]
    · nlinarith [hw.2, le_abs_self a]
  have hjabs : |(j : ℝ)| ≤ |(n : ℝ)| := abs_intCast_le_of_mem_Ico_min_max hj
  have hK : K * z.im ≤ |K| * z.im :=
    mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith)
  calc
    |(z - (n : ℂ)).re + 1 + (j : ℝ)| ≤ |(z - (n : ℂ)).re + 1| + |(j : ℝ)| :=
      abs_add_le _ _
    _ ≤ (|(z - (n : ℂ)).re| + |(1 : ℝ)|) + |(j : ℝ)| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ = |(z - (n : ℂ)).re| + 1 + |(j : ℝ)| := by norm_num
    _ ≤ |K| * z.im + 2 * |a| + 3 := by linarith
    _ ≤ (|K| + 2 * |a| + 3) * z.im := by
      nlinarith [abs_nonneg K, abs_nonneg a]

/-- Uniformly near a positive real period, every finite phase produced by translating `z` into
the unit window `[a, a + 1]` has imaginary part at least a fixed positive multiple of `Im z`. -/
theorem exists_uniform_floor_phase_im_lower_bound {τ₀ : ℝ} (hτ₀ : 0 < τ₀)
    (a K : ℝ) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧
      ∀ (τ z : ℂ), ‖τ - (τ₀ : ℂ)‖ ≤ ε → 1 ≤ z.im →
        |z.re| ≤ K * z.im →
        let n : ℤ := ⌊z.re - a⌋
        let w : ℂ := z - (n : ℂ)
        ∀ j ∈ Set.Ico (min n 0) (max n 0),
          c * z.im ≤ ((w + 1) / τ + (j : ℂ) * τ⁻¹).im := by
  obtain ⟨ε, c, hε, hc, hdiv⟩ :=
    exists_uniform_div_im_lower_bound hτ₀ (|K| + 2 * |a| + 3)
  refine ⟨ε, c, hε, hc, fun τ z hτ hz hre => ?_⟩
  dsimp
  intro j hj
  let n : ℤ := ⌊z.re - a⌋
  let w : ℂ := z - (n : ℂ)
  change c * z.im ≤ ((w + 1) / τ + (j : ℂ) * τ⁻¹).im
  have hphase := floor_phase_re_bound z a K hz hre j hj
  have him : (w + 1 + (j : ℂ)).im = z.im := by simp [w, n]
  have hbound : |(w + 1 + (j : ℂ)).re| ≤
      (|K| + 2 * |a| + 3) * (w + 1 + (j : ℂ)).im := by
    rw [him]
    exact hphase
  have hlower := hdiv τ (w + 1 + (j : ℂ)) hτ (by rw [him]; linarith) hbound
  rw [him] at hlower
  have heq : (w + 1) / τ + (j : ℂ) * τ⁻¹ = (w + 1 + (j : ℂ)) / τ := by
    simp only [div_eq_mul_inv]
    ring
  rw [heq]
  exact hlower

/-! ### Real translations of sectors -/

/-- A real translation widens a sector by at most its absolute value. -/
lemma abs_re_add_ofReal_le_widened_sector (z : ℂ) (y K s : ℝ)
    (hs : 1 ≤ s) (hz : |z.re| ≤ K * s) :
    |(z + y).re| ≤ (max K 0 + |y|) * s := by
  have hK : K * s ≤ max K 0 * s :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  have hy : |y| ≤ |y| * s := by nlinarith [abs_nonneg y]
  have h := abs_add_le z.re y
  simp only [Complex.add_re, Complex.ofReal_re]
  nlinarith


/-- A sector bound remains valid after increasing its slope. -/
lemma abs_re_le_widened_sector (z : ℂ) (y K s : ℝ)
    (hs : 0 ≤ s) (hz : |z.re| ≤ K * s) :
    |z.re| ≤ (max K 0 + |y|) * s := by
  have hK : K * s ≤ max K 0 * s :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hs
  nlinarith [abs_nonneg y]


end SIC

end
