/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SL2Z.Characteristics
import Mathlib.NumberTheory.NumberField.Basic

/-!
# The lattice `βℤ + ℤ` and pair maps in a field

The lattice `βℤ + ℤ` as the image of the pairing `⟨⟨·,β⟩⟩` on `ℤ²`, and its change under the
Möbius action; pair maps `M(β,1)ᵀ = η(γ,1)ᵀ`, unique when `β` is irrational, composing and
conjugating; the integer matrix of an element preserving `βℤ + ℤ`, with determinant the product of
its two real values.

This file takes the characteristic pairing `⟨⟨u, β⟩⟩ = u₂β - u₁` and the Jacobi denominator
`j_M(β) = M₁₀β + M₁₁` at an element `β` of a field `K` (`fracSymplecticFormRat`, `fltDenominator`
and `flt` of `SICs.SL2Z.Characteristics` and `SICs.SL2Z.FractionalLinear`, which are defined
over any
division ring), and relates their values in `K` to their real values through ring homomorphisms
`f : K →+* ℝ` (`map_fracSymplecticFormRat`, `map_fltDenominator`, `map_flt`). This is the
language in which Kopp's Shintani
decomposition [72, Kopp (2024), Proposition 7.10, `prop:shintanidecomp`] speaks of the lattice
`𝔟𝔪 = α(βℤ + ℤ)` of a real quadratic field `F`, of `w_0 = ⟨⟨r_0, β⟩⟩ ∈ F`, and of the unit
`ε^k = j_A(β)` acting on it, while the Hirzebruch--Jung data of `β` live in `ℝ` through the
real embeddings.

## Mathematical argument

*The lattice `βℤ + ℤ`.* Its elements are the pairings `⟨⟨v, β⟩⟩` with `v ∈ ℤ²`, and a
unimodular change of the generating pair does not change it. For `M = [[a,b],[c,d]] ∈ SL₂(ℤ)`
with `j_M(β) = cβ + d ≠ 0`, the relations `j_M(β)·(M·β) = aβ + b` and `j_M(β)·1 = cβ + d` give
`j_M(β)((M·β)ℤ + ℤ) = βℤ + ℤ`.

*Pair maps.* A relation `M(β,1)ᵀ = η(γ,1)ᵀ` determines the integer matrix `M` when the image
`f(β)` of `β` under some embedding `f : K →+* ℝ` is irrational, since
`(M_{i0} - M'_{i0})f(β) = M'_{i1} - M_{i1}` forces both sides to vanish; and such relations
compose. An element `x ∈ K` with `x·β, x·1 ∈ βℤ + ℤ` has an integer matrix `M` with
`x = j_M(β)` and `xβ = M₀₀β + M₀₁`, whose determinant is the product of two real values of `x`,
`(ad - bc)(f(β) - g(β)) = (a f(β) + b)(c g(β) + d) -
(a g(β) + b)(c f(β) + d) = f(x)g(x)(f(β) - g(β))`.
This is how a norm-one unit preserving the lattice becomes an element of `SL₂(ℤ)` fixing `f(β)`.

## References

- [72, Kopp (2024), Proposition 7.10, `prop:shintanidecomp`] and its proof, for the lattice
  `α(βℤ + ℤ)`, its unit, and the pairing `⟨⟨·, β⟩⟩` valued in `F`.
-/

open scoped MatrixGroups

namespace SIC

variable {K : Type*} [Field K]

/-! ### The lattice `βℤ + ℤ` as the image of the pairing

`βℤ + ℤ` is the image of `ℤ²` under `⟨⟨·, β⟩⟩ = (·)₂β - (·)₁`, and Kopp's `𝔟𝔪 = α(βℤ + ℤ)` its
scaling by `α`. Unimodular changes of the generating pair, and the coordinates of an arbitrary
element of a quadratic field with respect to `(β, 1)`, are read off `Submodule.mem_span_pair`. -/

/-- **The lattice `α(βℤ + ℤ)` is the set of scaled pairings with integral characteristics**:
`x ∈ span_ℤ {αβ, α}` if and only if `x = α⟨⟨v, β⟩⟩` for some `v ∈ ℤ²`
(`Submodule.mem_span_pair`; the coefficients `a, b` of `aαβ + bα` are `v = (-b, a)`). This is
Kopp's `𝔟𝔪 = α(βℤ + ℤ)` of [72, Kopp (2024), Proposition 7.10, `prop:shintanidecomp`] read
through the pairing. -/
theorem mem_span_pair_iff_exists_fracSymplecticFormRat (α β x : K) :
    x ∈ Submodule.span ℤ {α * β, α} ↔
      ∃ v : Fin 2 → ℚ, IsIntegralIndex v ∧ x = α * fracSymplecticFormRat v β := by
  constructor
  · intro hx
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hx
    refine ⟨![(-b : ℚ), (a : ℚ)], ?_, ?_⟩
    · exact isIntegralIndex_of_coords ⟨-b, by simp⟩ ⟨a, by simp⟩
    · rw [← hab]
      simp [fracSymplecticFormRat, zsmul_eq_mul]
      ring
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨b, hb⟩ := hv 0
    obtain ⟨a, ha⟩ := hv 1
    apply Submodule.mem_span_pair.mpr
    refine ⟨a, -b, ?_⟩
    simp [fracSymplecticFormRat, ha, hb, zsmul_eq_mul]
    ring

/-- **Scaling the lattice**: `αy ∈ span_ℤ {αβ, α}` if and only if `y ∈ span_ℤ {β, 1}`, for
`α ≠ 0`. -/
theorem mul_mem_span_pair_iff {α : K} (hα : α ≠ 0) (β y : K) :
    α * y ∈ Submodule.span ℤ {α * β, α} ↔ y ∈ Submodule.span ℤ {β, 1} := by
  constructor
  · intro h
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp h
    apply Submodule.mem_span_pair.mpr
    refine ⟨a, b, mul_left_cancel₀ hα ?_⟩
    calc
      α * (a • β + b • (1 : K)) = a • (α * β) + b • α := by
        simp [zsmul_eq_mul]
        ring
      _ = α * y := hab
  · intro h
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp h
    apply Submodule.mem_span_pair.mpr
    refine ⟨a, b, ?_⟩
    rw [← hab]
    simp [zsmul_eq_mul]
    ring

/-- **A unimodular change of generators does not change the `ℤ`-span**: for `M ∈ SL₂(ℤ)`,
`span_ℤ {M₀₀u + M₀₁v, M₁₀u + M₁₁v} = span_ℤ {u, v}`. The inclusion `⊆` is immediate; for `⊇`,
`u` and `v` are recovered from the new generators through the inverse matrix
`[[M₁₁, -M₀₁], [-M₁₀, M₀₀]]`, using `M₀₀M₁₁ - M₀₁M₁₀ = 1`. -/
theorem span_pair_matrix_eq (M : SL(2, ℤ)) (u v : K) :
    Submodule.span ℤ {(M 0 0 : K) * u + (M 0 1 : K) * v, (M 1 0 : K) * u + (M 1 1 : K) * v} =
      Submodule.span ℤ {u, v} := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = (1 : ℤ) := by
    simpa only [Matrix.det_fin_two] using M.det_coe
  have hdetK : (M 0 0 : K) * M 1 1 - M 0 1 * M 1 0 = 1 := by
    calc
      _ = ((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℤ) : K) := by push_cast; ring
      _ = 1 := by rw [hdet]; simp
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x (rfl | rfl)
    · exact Submodule.mem_span_pair.mpr ⟨M 0 0, M 0 1, by simp [zsmul_eq_mul]⟩
    · exact Submodule.mem_span_pair.mpr ⟨M 1 0, M 1 1, by simp [zsmul_eq_mul]⟩
  · apply Submodule.span_le.mpr
    rintro x (rfl | rfl)
    · apply Submodule.mem_span_pair.mpr
      refine ⟨M 1 1, -(M 0 1), ?_⟩
      simp only [zsmul_eq_mul, Int.cast_neg]
      linear_combination hdetK * x
    · apply Submodule.mem_span_pair.mpr
      refine ⟨-(M 1 0), M 0 0, ?_⟩
      simp only [zsmul_eq_mul, Int.cast_neg]
      linear_combination hdetK * x

/-- **Negating one generator does not change the span.** -/
theorem span_pair_neg_left_eq (u v : K) :
    Submodule.span ℤ {-u, v} = Submodule.span ℤ {u, v} := by
  ext z
  constructor <;> intro hz
  · obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz
    exact Submodule.mem_span_pair.mpr ⟨-a, b, by simp [zsmul_eq_mul]⟩
  · obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz
    exact Submodule.mem_span_pair.mpr ⟨-a, b, by simp [zsmul_eq_mul]⟩

/-- **Coordinates with respect to `(β, 1)`**: in a field `K` of degree two over `ℚ`, every `x`
is `⟨⟨r, β⟩⟩ = r₂β - r₁` for some `r ∈ ℚ²`, when `β` has an irrational real value `f(β)`. The
pair `1, β` is `ℚ`-linearly independent (`LinearIndependent.pair_iff`: `a + bβ = 0` forces
`b = 0` by irrationality of `f(β)`, then `a = 0`), hence spans `K`
(`LinearIndependent.span_eq_top_of_card_eq_finrank`), and `Submodule.mem_span_pair` reads off
the coordinates. -/
theorem exists_fracSymplecticFormRat_eq [CharZero K] (hfin : Module.finrank ℚ K = 2)
    {f : K →+* ℝ} {β : K} (hβ : Irrational (f β)) (x : K) :
    ∃ r : Fin 2 → ℚ, x = fracSymplecticFormRat r β := by
  have hli : LinearIndependent ℚ ![(1 : K), β] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    simp only [Rat.smul_def] at hab
    have hab' := congrArg f hab
    simp only [map_add, map_mul, map_ratCast, map_zero, mul_one] at hab'
    have hrel : (b : ℝ) * f β = ((-a : ℚ) : ℝ) := by
      rw [Rat.cast_neg]
      linarith
    obtain ⟨hb, ha⟩ := ratCast_eq_zero_of_irrational_mul hβ hrel
    exact ⟨by simpa using ha, hb⟩
  have hspan : Submodule.span ℚ ({(1 : K), β} : Set K) = ⊤ := by
    rw [← show Set.range ![(1 : K), β] = ({(1 : K), β} : Set K) by
      ext y
      simp [Set.range, Fin.exists_fin_two, eq_comm]]
    exact hli.span_eq_top_of_card_eq_finrank (by simpa using hfin.symm)
  have hx : x ∈ Submodule.span ℚ ({(1 : K), β} : Set K) := by rw [hspan]; trivial
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hx
  refine ⟨![-a, b], ?_⟩
  rw [← hab]
  simp [fracSymplecticFormRat, Rat.smul_def]
  ring

/-! ### The Jacobi denominator and the Möbius action in the field

`j_M(β) = M₁₀β + M₁₁ ∈ K` and `M·β = (M₀₀β + M₀₁)/j_M(β) ∈ K` are `fltDenominator` and `flt` at a
point of the field. Kopp's `β_n = A_{0,n}^{-1}·β ∈ F` of [72, Kopp (2024), Definition 7.4,
`defn:cycledata`] and his `j_{A_{0,n}}(β) = β_1⋯β_n ∈ F` of [72, Kopp (2024), Lemma 7.5,
`lem:betajs`], with the unit `ε^k = j_A(β)`, are their values at the cycle matrices. -/

/-- **The lattice of `M·β`**: for `M ∈ SL₂(ℤ)` with `j_M(β) ≠ 0`,
`x ∈ span_ℤ {M·β, 1}` if and only if `j_M(β)·x ∈ span_ℤ {β, 1}`, since
`j_M(β)·span_ℤ {M·β, 1} = span_ℤ {M₀₀β + M₀₁, M₁₀β + M₁₁} = span_ℤ {β, 1}`
(`mul_mem_span_pair_iff`, `span_pair_matrix_eq`). This is Kopp's
`α_n(β_nℤ + ℤ) = α_{n+1}(β_{n+1}ℤ + ℤ)` in the proof of [72, Kopp (2024), Proposition 7.10,
`prop:shintanidecomp`], for one matrix. -/
theorem mem_span_pair_flt_iff (M : SL(2, ℤ)) {β : K}
    (hj : fltDenominator (M : Mat(2, ℤ)) β ≠ 0) (x : K) :
    x ∈ Submodule.span ℤ {flt (M : Mat(2, ℤ)) β, 1} ↔
      fltDenominator (M : Mat(2, ℤ)) β * x ∈ Submodule.span ℤ {β, 1} := by
  rw [← mul_mem_span_pair_iff hj]
  have hjflt : fltDenominator (M : Mat(2, ℤ)) β *
      flt (M : Mat(2, ℤ)) β =
        (M 0 0 : K) * β + (M 0 1 : K) := by
    unfold flt
    exact mul_div_cancel₀ _ hj
  rw [hjflt, fltDenominator]
  have hspan : Submodule.span ℤ
      {(M 0 0 : K) * β + (M 0 1 : K) * 1,
        (M 1 0 : K) * β + (M 1 1 : K) * 1} = Submodule.span ℤ {β, 1} :=
    span_pair_matrix_eq M β 1
  simpa only [fltDenominator, mul_one] using (SetLike.ext_iff.mp hspan)
    (fltDenominator (M : Mat(2, ℤ)) β * x)

/-! ### Matrices carrying one pair to another

`M(β, 1)ᵀ = η(γ, 1)ᵀ` in `K`, the relation between two `ℤ`-bases `(β, 1)` and `(γ, 1)` of
similar lattices. A matrix is determined by this relation when `β` is irrational at some
embedding, and the relations compose; this is what identifies the cycle matrices of two
presentations of one lattice as conjugate. -/

/-- **`M` carries the pair `(β, 1)` to `η·(γ, 1)`**: `M₀₀β + M₀₁ = ηγ` and `M₁₀β + M₁₁ = η`, that
is `M(β,1)ᵀ = η(γ,1)ᵀ` in `K`. For `γ = β` this says that `M` is the matrix of multiplication by
`η` in the basis `(β, 1)` of `βℤ + ℤ`, the situation of `exists_matrix_of_mul_mem_span`; for
`M ∈ GL₂(ℤ)` and `η = j_M(β)` it says `γ = M·β`. -/
def IsPairMap (M : Mat(2, ℤ)) (β η γ : K) : Prop :=
  (M 0 0 : K) * β + (M 0 1 : K) = η * γ ∧ fltDenominator M β = η

/-- The first row of a pair map satisfies `M₀₀β + M₀₁ = ηγ`. -/
theorem IsPairMap.first_row {M : Mat(2, ℤ)} {β η γ : K}
    (h : IsPairMap M β η γ) : (M 0 0 : K) * β + (M 0 1 : K) = η * γ := h.1

/-- The second row of a pair map gives `j_M(β) = η`. -/
theorem IsPairMap.denominator_eq {M : Mat(2, ℤ)} {β η γ : K}
    (h : IsPairMap M β η γ) : fltDenominator M β = η := h.2

/-- The two row equations construct a pair map. -/
theorem IsPairMap.intro {M : Mat(2, ℤ)} {β η γ : K}
    (h0 : (M 0 0 : K) * β + (M 0 1 : K) = η * γ) (h1 : fltDenominator M β = η) :
    IsPairMap M β η γ := ⟨h0, h1⟩

/-- Equality of two integral linear expressions at an irrational field element forces equality
of their two coefficients. This is the row-wise step used by `IsPairMap.unique`. -/
private theorem intLinear_eq_of_eq_at_irrational {f : K →+* ℝ} {β : K}
    (hβ : Irrational (f β)) {a b a' b' : ℤ}
    (h : (a : K) * β + (b : K) = (a' : K) * β + (b' : K)) : a = a' ∧ b = b' := by
  have hf := congrArg f h
  simp only [map_add, map_mul, map_intCast] at hf
  have hrel : (((a - a' : ℤ) : ℚ) : ℝ) * f β = (((b' - b : ℤ) : ℚ) : ℝ) := by
    push_cast
    linarith
  obtain ⟨ha, hb⟩ := ratCast_eq_zero_of_irrational_mul hβ hrel
  constructor
  · have : a - a' = 0 := by exact_mod_cast ha
    exact sub_eq_zero.mp this
  · have : b' - b = 0 := by exact_mod_cast hb
    exact (sub_eq_zero.mp this).symm

/-- **A pair map is determined by the pair when `β` is irrational at some embedding**: two integer
matrices with `M(β,1)ᵀ = M'(β,1)ᵀ` have equal rows, since
`(M_{i0} - M'_{i0}) f(β) = M'_{i1} - M_{i1}` forces both differences to vanish
(`ratCast_eq_zero_of_irrational_mul`). -/
theorem IsPairMap.unique {f : K →+* ℝ} {β : K} (hβ : Irrational (f β))
    {M M' : Mat(2, ℤ)} {η γ : K} (h : IsPairMap M β η γ)
    (h' : IsPairMap M' β η γ) : M = M' := by
  have htop := intLinear_eq_of_eq_at_irrational hβ (h.first_row.trans h'.first_row.symm)
  have hbottom :=
    intLinear_eq_of_eq_at_irrational hβ (h.denominator_eq.trans h'.denominator_eq.symm)
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact htop.1
  · exact htop.2
  · exact hbottom.1
  · exact hbottom.2

/-- **Pair maps compose**: `M(β,1)ᵀ = η(γ,1)ᵀ` and `M'(γ,1)ᵀ = η'(δ,1)ᵀ` give
`(M'M)(β,1)ᵀ = η'η(δ,1)ᵀ`, by expanding `Matrix.mul_apply` on `Fin 2`. -/
theorem IsPairMap.mul {M M' : Mat(2, ℤ)} {β η γ η' δ : K}
    (h : IsPairMap M β η γ) (h' : IsPairMap M' γ η' δ) :
    IsPairMap (M' * M) β (η' * η) δ := by
  have h0 := h.first_row
  have h1 := h.denominator_eq
  have h0' := h'.first_row
  have h1' := h'.denominator_eq
  unfold IsPairMap fltDenominator at *
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · push_cast
    linear_combination (M' 0 0 : K) * h0 + (M' 0 1 : K) * h1 + η * h0'
  · push_cast
    linear_combination (M' 1 0 : K) * h0 + (M' 1 1 : K) * h1 + η * h1'

/-- **The identity is a pair map**: `1·(β,1)ᵀ = 1·(β,1)ᵀ`. -/
theorem IsPairMap.one (β : K) : IsPairMap (1 : Mat(2, ℤ)) β 1 β := by
  simp [IsPairMap, fltDenominator]

/-- **Conjugation of pair maps**: if `R(β,1)ᵀ = j(γ,1)ᵀ`, `M(β,1)ᵀ = η(β,1)ᵀ` and
`M'(γ,1)ᵀ = η(γ,1)ᵀ` with `β` irrational at `f`, then `M'R = RM`, since both carry `(β,1)ᵀ` to
`jη(γ,1)ᵀ`. This is how the cycle matrices of two presentations of one lattice are conjugate,
`A₂R = RA₁`, with `R` the change of basis. -/
theorem IsPairMap.conj {f : K →+* ℝ} {β : K} (hβ : Irrational (f β))
    {R M M' : Mat(2, ℤ)} {j η γ : K} (hR : IsPairMap R β j γ)
    (h : IsPairMap M β η β) (h' : IsPairMap M' γ η γ) : M' * R = R * M := by
  apply IsPairMap.unique hβ
  · exact hR.mul h'
  · simpa [mul_comm] using h.mul hR

/-- **A pair map with nonzero scalar acts on the point**: `M·β = γ` when `M(β,1)ᵀ = η(γ,1)ᵀ`
with `η ≠ 0`, since `M·β = (M₀₀β + M₀₁)/j_M(β) = ηγ/η`. -/
theorem IsPairMap.flt_eq {M : Mat(2, ℤ)} {β η γ : K} (h : IsPairMap M β η γ)
    (hη : η ≠ 0) : flt M β = γ := by
  have hden : (M 1 0 : K) * β + (M 1 1 : K) = η := h.denominator_eq
  rw [flt, h.first_row, hden]
  exact mul_div_cancel_left₀ γ hη

/-- **The determinant of a pair map with an inverse pair map is `±1`**: if `R(β,1)ᵀ = j(γ,1)ᵀ`
and `R'(γ,1)ᵀ = j⁻¹(β,1)ᵀ` with `β` irrational at `f` and `j ≠ 0`, then `R'R = 1`
(`IsPairMap.mul`, `IsPairMap.one`, `IsPairMap.unique`), so `det R · det R' = 1` and
`det R = ±1` (`Int.eq_one_or_neg_one_of_mul_eq_one'`). -/
theorem IsPairMap.det_eq_one_or_neg_one {f : K →+* ℝ} {β : K} (hβ : Irrational (f β))
    {R R' : Mat(2, ℤ)} {j γ : K} (hj : j ≠ 0) (hR : IsPairMap R β j γ)
    (hR' : IsPairMap R' γ j⁻¹ β) : R.det = 1 ∨ R.det = -1 := by
  have hcomp : IsPairMap (R' * R) β 1 β := by
    simpa [inv_mul_cancel₀ hj] using hR.mul hR'
  have hmat : R' * R = 1 := IsPairMap.unique hβ hcomp (IsPairMap.one β)
  have hdet : R'.det * R.det = 1 := by
    rw [← Matrix.det_mul, hmat, Matrix.det_one]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with h | h
  · exact Or.inl h.2
  · exact Or.inr h.2

/-! ### The matrix of an element preserving the lattice

An `x ∈ K` with `x·β, x·1 ∈ βℤ + ℤ` is `j_M(β)` for an integer matrix `M` with
`xβ = M₀₀β + M₀₁`; the determinant of `M` is the product of two real values of `x`. -/

/-- **An element preserving `βℤ + ℤ` has an integer matrix**: if `xβ` and `x` lie in
`span_ℤ {β, 1}`, there is `M ∈ M₂(ℤ)` with `x = j_M(β)` and `xβ = M₀₀β + M₀₁`
(`Submodule.mem_span_pair` for the two rows). -/
theorem exists_matrix_of_mul_mem_span {x β : K} (hxβ : x * β ∈ Submodule.span ℤ {β, 1})
    (hx : x ∈ Submodule.span ℤ {β, 1}) :
    ∃ M : Mat(2, ℤ),
      x = fltDenominator M β ∧ x * β = (M 0 0 : K) * β + (M 0 1 : K) := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hxβ
  obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.mp hx
  refine ⟨!![a, b; c, d], ?_, ?_⟩
  · rw [← hcd]
    simp [fltDenominator, zsmul_eq_mul]
  · rw [← hab]
    simp [zsmul_eq_mul]

/-- **The determinant of the matrix of `x` is the product of two real values of `x`**: if
`x = j_M(β)` and `xβ = M₀₀β + M₀₁`, then for `f, g : K →+* ℝ` with `f(β) ≠ g(β)`,
`det M = f(x)·g(x)`, from
`(ad - bc)(f(β) - g(β)) = (a f(β) + b)(c g(β) + d) - (a g(β) + b)(c f(β) + d)` with
`a f(β) + b = f(x)f(β)`, `c f(β) + d = f(x)`, and likewise at `g`. For a unit of a real quadratic
field this is `det M = N(x)`. -/
theorem det_eq_mul_of_fltDenominator_eq {f g : K →+* ℝ} {M : Mat(2, ℤ)}
    {x β : K} (hβ : f β ≠ g β) (hx : x = fltDenominator M β)
    (hxβ : x * β = (M 0 0 : K) * β + (M 0 1 : K)) : (M.det : ℝ) = f x * g x := by
  have hxf : f x = (M 1 0 : ℝ) * f β + M 1 1 := by
    simpa [fltDenominator] using congrArg f hx
  have hxg : g x = (M 1 0 : ℝ) * g β + M 1 1 := by
    simpa [fltDenominator] using congrArg g hx
  have hxfβ : f x * f β = (M 0 0 : ℝ) * f β + M 0 1 := by
    simpa using congrArg f hxβ
  have hxgβ : g x * g β = (M 0 0 : ℝ) * g β + M 0 1 := by
    simpa using congrArg g hxβ
  have hcross :
      ((M 0 0 : ℝ) * f β + M 0 1) * ((M 1 0 : ℝ) * g β + M 1 1) -
          ((M 0 0 : ℝ) * g β + M 0 1) * ((M 1 0 : ℝ) * f β + M 1 1) =
        f x * g x * (f β - g β) := by
    rw [← hxfβ, ← hxg, ← hxgβ, ← hxf]
    ring
  apply mul_left_cancel₀ (sub_ne_zero.mpr hβ)
  rw [mul_comm (f β - g β), mul_comm (f β - g β)]
  rw [Matrix.det_fin_two]
  push_cast
  calc
    ((M 0 0 : ℝ) * M 1 1 - (M 0 1 : ℝ) * M 1 0) * (f β - g β) =
        ((M 0 0 : ℝ) * f β + M 0 1) * ((M 1 0 : ℝ) * g β + M 1 1) -
          ((M 0 0 : ℝ) * g β + M 0 1) * ((M 1 0 : ℝ) * f β + M 1 1) := by ring
    _ = f x * g x * (f β - g β) := hcross

end SIC
