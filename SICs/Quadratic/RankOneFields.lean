/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quadratic.FundamentalUnits
import SICs.Quadratic.RankOne
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.Norm.Basic

/-!
# Concrete Quadratic Fields for Rank-One Tower Dimensions

The concrete field `K_d`, its embeddings, norm-one root unit, and exact level for every `d>3`.

For every dimension `d > 3`, this file constructs the quadratic field cut out by

`X² - (d - 1)X + 1`.

The larger real root is an algebraic-integer unit of norm one. Every complex embedding sends the
adjoined generator to one of the two real roots, so the field is totally real. The quadratic
number-field discriminant theorem and Dirichlet's unit theorem then produce exact
`RealQuadraticUnitData` and an exact positive `RankOneLevel` whose dimension is `d`.

This construction depends only on the rank-one tower dimension and not on a choice of binary
quadratic form. The bundle used by admissible tuples is assembled in `SICs.Admissible.RankOne`.

## Main definitions and results

- `RankOneField`: the field obtained by adjoining a root of the rank-one quadratic.
- `rankOneRealEmbedding`, `rankOneComplexEmbedding`: the selected larger-root embeddings.
- `rankOneRootUnit`: the distinguished algebraic-integer unit of norm one.
- `rankOneField_isTotallyReal`: total reality of the concrete field.
- `rankOneRealQuadraticUnitData`: exact oriented fundamental-unit data.
- `exists_rankOneFieldLevel`: an exact positive tower level in the prescribed dimension.
- `rankOneFieldLevel`: a chosen such level.

## References

- [AFK25, Definition 1.21, `dfn:admissiblePair`] and [AFK25, Definition 1.22,
  `dfn:fundamentalTotallyPositiveUnit`] and [AFK25, Definition 1.23,
  `dfn:sequenceofconductors`] and [AFK25, Definition 1.24, `dfn:fjrjmdjm`]
- [AFK25, Theorem 3.20, `thm:dimtowunique`]
- [14, Appleby, Flammia, McConnell, Yard (2020), Lemma 4, `pellemma`] in [AFK25]
-/

noncomputable section

open scoped NumberField Polynomial ComplexConjugate

namespace SIC

open Polynomial NumberField NumberField.InfinitePlace

/-! ### The rank-one polynomial

The polynomial `X² - (d-1)X + 1` has discriminant `Δ_d = (d+1)(d-3)`. For `d > 3` this
discriminant is not a rational square, so the quadratic has no rational root and is irreducible.
-/

/-- The integral rank-one quadratic `X² - (d-1)X + 1`. -/
def rankOnePolynomialInt (d : ℕ) : ℤ[X] :=
  X ^ 2 - C ((d : ℤ) - 1) * X + 1

/-- The rank-one quadratic over `ℚ`. -/
def rankOnePolynomialRat (d : ℕ) : ℚ[X] :=
  X ^ 2 - C ((d : ℚ) - 1) * X + 1

/-- Mapping the integral rank-one quadratic to `ℚ` gives the rational one. -/
lemma rankOnePolynomialInt_map (d : ℕ) :
    (rankOnePolynomialInt d).map (algebraMap ℤ ℚ) = rankOnePolynomialRat d := by
  simp [rankOnePolynomialInt, rankOnePolynomialRat]

/-- The integral rank-one quadratic is monic. -/
lemma rankOnePolynomialInt_monic (d : ℕ) : (rankOnePolynomialInt d).Monic := by
  have h := Polynomial.isMonicOfDegree_sub_add_two ((d : ℤ) - 1) 1
  simpa [rankOnePolynomialInt] using h.monic

/-- The rational rank-one quadratic is monic. -/
lemma rankOnePolynomialRat_monic (d : ℕ) : (rankOnePolynomialRat d).Monic := by
  have h := Polynomial.isMonicOfDegree_sub_add_two ((d : ℚ) - 1) 1
  simpa [rankOnePolynomialRat] using h.monic

/-- The rational rank-one quadratic has degree two. -/
@[simp]
lemma rankOnePolynomialRat_natDegree (d : ℕ) : (rankOnePolynomialRat d).natDegree = 2 := by
  have h := Polynomial.isMonicOfDegree_sub_add_two ((d : ℚ) - 1) 1
  simpa [rankOnePolynomialRat] using h.natDegree_eq

/-- The discriminant of the rational rank-one quadratic is the cast of `Δ_d`. -/
lemma rankOnePolynomial_discrim (d : ℕ) :
    discrim (1 : ℚ) (1 - d) 1 = (rankOneRadicand d : ℚ) := by
  norm_num [discrim, rankOneRadicand]
  ring

/-- The rational rank-one quadratic has no rational root. -/
lemma rankOnePolynomialRat_not_isRoot (d : ℕ) (hd : 3 < d) (x : ℚ) :
    ¬ IsRoot (rankOnePolynomialRat d) x := by
  intro hx
  have hquad : (1 : ℚ) * (x * x) + (1 - d) * x + 1 = 0 := by
    have hx' : x * x - ((d : ℚ) - 1) * x + 1 = 0 := by
      simpa [IsRoot, rankOnePolynomialRat, pow_two] using hx
    linarith
  have hdisc : discrim (1 : ℚ) (1 - d) 1 = (2 * x + (1 - d)) ^ 2 :=
    by simpa using discrim_eq_sq_of_quadratic_eq_zero hquad
  have hsquare : IsSquare (rankOneRadicand d : ℚ) := by
    refine ⟨2 * x + (1 - d), ?_⟩
    calc
      (rankOneRadicand d : ℚ) = discrim (1 : ℚ) (1 - d) 1 :=
        (rankOnePolynomial_discrim d).symm
      _ = (2 * x + (1 - d)) ^ 2 := hdisc
      _ = (2 * x + (1 - d)) * (2 * x + (1 - d)) := pow_two _
  exact rankOneRadicand_not_square d hd (Rat.isSquare_intCast_iff.mp hsquare)

/-- The rational rank-one quadratic is irreducible for `d > 3`. -/
lemma rankOnePolynomialRat_irreducible (d : ℕ) (hd : 3 < d) :
    Irreducible (rankOnePolynomialRat d) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp
  · exact rankOnePolynomialRat_not_isRoot d hd

/-! ### The adjoined root and its unit

Adjoining a root gives the concrete quadratic field `K_d`. The quadratic equation makes the root
an algebraic integer with explicit inverse `(d-1)-α_d`; hence it defines a unit of norm one. The
chosen real embedding sends this algebraic root to the larger real root `ρ_d`.
-/

/-- The quadratic field cut out by the rank-one quadratic. -/
abbrev RankOneField (d : RankOneDimension) :=
  AdjoinRoot (rankOnePolynomialRat d)

/-- Irreducibility data used by the `AdjoinRoot` field instance. -/
instance rankOnePolynomialRat_fact (d : RankOneDimension) :
    Fact (Irreducible (rankOnePolynomialRat d)) :=
  ⟨rankOnePolynomialRat_irreducible d d.property⟩

/-- The rank-one field has degree two over `ℚ`. -/
lemma rankOneField_finrank (d : RankOneDimension) :
    Module.finrank ℚ (RankOneField d) = 2 := by
  change Module.finrank ℚ (ℚ[X] ⧸ (Ideal.span {rankOnePolynomialRat d})) = 2
  rw [finrank_quotient_span_eq_natDegree]
  exact rankOnePolynomialRat_natDegree d

/-- The distinguished root of the rank-one quadratic. -/
def rankOneFieldRoot (d : RankOneDimension) : RankOneField d :=
  AdjoinRoot.root (rankOnePolynomialRat d)

/-- The distinguished root satisfies the rank-one quadratic. -/
lemma rankOneFieldRoot_quadratic (d : RankOneDimension) :
    rankOneFieldRoot d ^ 2 -
        AdjoinRoot.of (rankOnePolynomialRat d) ((d : ℚ) - 1) * rankOneFieldRoot d + 1 = 0 := by
  have h := AdjoinRoot.eval₂_root (rankOnePolynomialRat d)
  rw [rankOnePolynomialRat, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
    eval₂_C, eval₂_X, eval₂_one] at h
  exact h

/-- The distinguished root is integral over `ℤ`. -/
lemma rankOneFieldRoot_isIntegral (d : RankOneDimension) :
    IsIntegral ℤ (rankOneFieldRoot d) := by
  refine ⟨rankOnePolynomialInt d, rankOnePolynomialInt_monic d, ?_⟩
  change eval₂ (algebraMap ℤ (RankOneField d)) (rankOneFieldRoot d)
    (rankOnePolynomialInt d) = 0
  rw [AdjoinRoot.algebraMap_eq' ℤ, ← eval₂_map, rankOnePolynomialInt_map]
  exact AdjoinRoot.eval₂_root (rankOnePolynomialRat d)

/-- The distinguished root as an algebraic integer. -/
def rankOneRootInteger (d : RankOneDimension) :
    NumberField.RingOfIntegers (RankOneField d) :=
  ⟨rankOneFieldRoot d, rankOneFieldRoot_isIntegral d⟩

/-- Evaluation of the rank-one polynomial at its chosen positive real root vanishes. -/
lemma rankOnePolynomialRat_eval_rankOneRoot (d : RankOneDimension) :
    eval₂ (algebraMap ℚ ℝ) (rankOneRoot d) (rankOnePolynomialRat d) = 0 := by
  rw [rankOnePolynomialRat, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
    eval₂_C, eval₂_X, eval₂_one]
  norm_num
  exact rankOneRoot_satisfies_quadratic d d.property

/-- The real embedding that sends the adjoined root to the positive rank-one root. -/
def rankOneRealEmbedding (d : RankOneDimension) : RankOneField d →+* ℝ :=
  AdjoinRoot.lift (algebraMap ℚ ℝ) (rankOneRoot d)
    (rankOnePolynomialRat_eval_rankOneRoot d)

/-- The selected complex embedding of the rank-one field, obtained from
`rankOneRealEmbedding`. Its field range is the concrete copy of
$K_d = \mathbb{Q}(\sqrt{(d+1)(d-3)})$ inside `ℂ`. -/
def rankOneComplexEmbedding (d : RankOneDimension) : RankOneField d →ₐ[ℚ] ℂ :=
  (Complex.ofRealHom.comp (rankOneRealEmbedding d)).toRatAlgHom

/-- The chosen real embedding sends the distinguished algebraic root to `ρ_d`. -/
@[simp]
lemma rankOneRealEmbedding_root (d : RankOneDimension) :
    rankOneRealEmbedding d (rankOneFieldRoot d) = rankOneRoot d := by
  exact AdjoinRoot.lift_root _

/-- The elementary inverse formula for the distinguished root. -/
lemma rankOneFieldRoot_mul_sub (d : RankOneDimension) :
    rankOneFieldRoot d *
        (AdjoinRoot.of (rankOnePolynomialRat d) ((d : ℚ) - 1) - rankOneFieldRoot d) = 1 := by
  have h := rankOneFieldRoot_quadratic d
  calc
    rankOneFieldRoot d *
        (AdjoinRoot.of (rankOnePolynomialRat d) ((d : ℚ) - 1) - rankOneFieldRoot d) =
        AdjoinRoot.of (rankOnePolynomialRat d) ((d : ℚ) - 1) * rankOneFieldRoot d -
          rankOneFieldRoot d ^ 2 := by ring
    _ = 1 := by linear_combination -h

/-- The integral inverse `(d - 1) - α_d` of the distinguished algebraic integer. -/
def rankOneRootIntegerInv (d : RankOneDimension) :
    NumberField.RingOfIntegers (RankOneField d) :=
  algebraMap ℤ (NumberField.RingOfIntegers (RankOneField d)) ((d : ℤ) - 1) -
    rankOneRootInteger d

/-- The distinguished algebraic integer times its explicit integral inverse is one. -/
lemma rankOneRootInteger_mul_inv (d : RankOneDimension) :
    rankOneRootInteger d * rankOneRootIntegerInv d = 1 := by
  apply Subtype.ext
  change rankOneFieldRoot d *
    (algebraMap ℤ (RankOneField d) ((d : ℤ) - 1) - rankOneFieldRoot d) = 1
  rw [AdjoinRoot.algebraMap_eq' ℤ]
  simpa using rankOneFieldRoot_mul_sub d

/-- The distinguished root as a unit in the ring of integers. -/
def rankOneRootUnit (d : RankOneDimension) :
    (NumberField.RingOfIntegers (RankOneField d))ˣ :=
  Units.mkOfMulEqOne (rankOneRootInteger d) (rankOneRootIntegerInv d)
    (rankOneRootInteger_mul_inv d)

/-- The minimal polynomial of the distinguished root is the rank-one quadratic. -/
lemma rankOneFieldRoot_minpoly (d : RankOneDimension) :
    minpoly ℚ (rankOneFieldRoot d) = rankOnePolynomialRat d := by
  symm
  apply minpoly.eq_of_irreducible_of_monic (rankOnePolynomialRat_irreducible d d.property)
  · rw [aeval_def]
    change eval₂ (AdjoinRoot.of (rankOnePolynomialRat d))
      (AdjoinRoot.root (rankOnePolynomialRat d)) (rankOnePolynomialRat d) = 0
    exact AdjoinRoot.eval₂_root (rankOnePolynomialRat d)
  · exact rankOnePolynomialRat_monic d

/-- The field norm of the distinguished root is one. -/
lemma rankOneFieldRoot_norm (d : RankOneDimension) :
    Algebra.norm ℚ (rankOneFieldRoot d) = 1 := by
  let pb := AdjoinRoot.powerBasis (rankOnePolynomialRat_monic d).ne_zero
  change Algebra.norm ℚ pb.gen = 1
  calc
    Algebra.norm ℚ pb.gen =
        (-1) ^ pb.dim * coeff (minpoly ℚ pb.gen) 0 :=
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
    _ = 1 := by
      dsimp [pb]
      simp only [AdjoinRoot.powerBasis_gen, AdjoinRoot.powerBasis_dim]
      change (-1 : ℚ) ^ (rankOnePolynomialRat d).natDegree *
        coeff (minpoly ℚ (rankOneFieldRoot d)) 0 = 1
      rw [rankOnePolynomialRat_natDegree, rankOneFieldRoot_minpoly]
      simp [rankOnePolynomialRat]

/-- The underlying field element of the distinguished unit is the adjoined root. -/
@[simp]
lemma rankOneRootUnit_coe (d : RankOneDimension) :
    ((rankOneRootUnit d : NumberField.RingOfIntegers (RankOneField d)) :
      RankOneField d) = rankOneFieldRoot d := by
  rfl

/-- The ring-of-integers unit has field norm one. -/
lemma rankOneRootUnit_norm (d : RankOneDimension) :
    Algebra.norm ℚ ((rankOneRootUnit d :
      NumberField.RingOfIntegers (RankOneField d)) : RankOneField d) = 1 := by
  rw [rankOneRootUnit_coe]
  exact rankOneFieldRoot_norm d

/-! ### Total reality and the distinguished infinite place

Every complex embedding sends the generator to one of the two real roots of its quadratic.
Consequently `K_d` is totally real, and the embedding selecting `ρ_d` determines a real infinite
place with the expected signed embedding.
-/

/-- Every complex root of the rank-one polynomial is one of its two real roots. -/
lemma eq_rankOneRoot_or_conjugate_of_complex_quadratic
    (d : RankOneDimension) (z : ℂ)
    (hz : z ^ 2 - ((d : ℂ) - 1) * z + 1 = 0) :
    z = (rankOneRoot d : ℂ) ∨ z = (rankOneConjugateRoot d : ℂ) := by
  have hsumReal := rankOneRoot_add_conjugate d
  have hsum := congrArg (fun x : ℝ ↦ (x : ℂ)) hsumReal
  have hprodReal := rankOneRoot_mul_conjugate d d.property
  have hprod := congrArg (fun x : ℝ ↦ (x : ℂ)) hprodReal
  have hfac :
      (z - (rankOneRoot d : ℂ)) * (z - (rankOneConjugateRoot d : ℂ)) = 0 := by
    simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_natCast,
      Complex.ofReal_one] at hsum
    simp only [Complex.ofReal_mul, Complex.ofReal_one] at hprod
    rw [mul_sub, sub_mul, sub_mul, hprod]
    linear_combination hz - z * hsum
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

/-- Complex evaluation of the rational rank-one polynomial. -/
lemma rankOnePolynomialRat_aeval_complex (d : RankOneDimension) (z : ℂ) :
    aeval z (rankOnePolynomialRat d) = z ^ 2 - ((d : ℂ) - 1) * z + 1 := by
  simp [rankOnePolynomialRat]

/-- Every complex embedding of the rank-one field sends its generator to a real root. -/
lemma complexEmbedding_rankOneFieldRoot_real (d : RankOneDimension)
    (phi : RankOneField d →+* ℂ) :
    conj (phi (rankOneFieldRoot d)) = phi (rankOneFieldRoot d) := by
  have hz0 : phi (rankOneFieldRoot d) ^ 2 -
      ((d : ℂ) - 1) * phi (rankOneFieldRoot d) + 1 = 0 := by
    have hroot := AdjoinRoot.aeval_algHom_eq_zero
      (rankOnePolynomialRat d) phi.toRatAlgHom
    rw [rankOnePolynomialRat_aeval_complex] at hroot
    have happ : phi.toRatAlgHom (rankOneFieldRoot d) = phi (rankOneFieldRoot d) :=
      RingHom.toRatAlgHom_apply phi _
    erw [happ] at hroot
    exact hroot
  rcases eq_rankOneRoot_or_conjugate_of_complex_quadratic d _ hz0 with h | h
  · rw [h, Complex.conj_ofReal]
  · rw [h, Complex.conj_ofReal]

/-- The concrete rank-one quadratic field is totally real. -/
theorem rankOneField_isTotallyReal (d : RankOneDimension) :
    NumberField.IsTotallyReal (RankOneField d) where
  isReal v := by
    rw [NumberField.InfinitePlace.isReal_iff,
      NumberField.ComplexEmbedding.isReal_iff]
    apply AdjoinRoot.ringHom_ext
    · exact Subsingleton.elim _ _
    · exact complexEmbedding_rankOneFieldRoot_real d v.embedding

/-- The canonical totally-real instance on the rank-one field. -/
noncomputable instance rankOneFieldTotallyReal (d : RankOneDimension) :
    NumberField.IsTotallyReal (RankOneField d) :=
  rankOneField_isTotallyReal d

/-- The selected infinite place induced by the larger rank-one root. -/
def rankOneInfinitePlace (d : RankOneDimension) : InfinitePlace (RankOneField d) :=
  InfinitePlace.mk (rankOneComplexEmbedding d).toRingHom

/-- The complexification of the selected real embedding is fixed by conjugation. -/
lemma rankOneComplexEmbedding_isReal (d : RankOneDimension) :
    ComplexEmbedding.IsReal (rankOneComplexEmbedding d).toRingHom := by
  unfold rankOneComplexEmbedding
  rw [ComplexEmbedding.isReal_iff]
  apply AdjoinRoot.ringHom_ext
  · exact Subsingleton.elim _ _
  · erw [ComplexEmbedding.conjugate_coe_eq]
    simp

/-- Recovering the signed embedding from the selected place gives the larger-root embedding. -/
lemma realEmbeddingAt_rankOneInfinitePlace (d : RankOneDimension) :
    realEmbeddingAt (RankOneField d) (rankOneInfinitePlace d) =
      rankOneRealEmbedding d := by
  apply DFunLike.coe_injective
  funext x
  apply Complex.ofReal_injective
  unfold realEmbeddingAt rankOneInfinitePlace
  rw [InfinitePlace.embedding_of_isReal_apply]
  rw [InfinitePlace.embedding_mk_eq_of_isReal (rankOneComplexEmbedding_isReal d)]
  rfl

/-! ### Exact quadratic-tower data

Since `K_d` has degree two, Dirichlet's unit theorem provides canonical fundamental-unit data.
Since the explicit root unit is positive at the selected place and has norm one, it occurs at a
positive rank-one tower level whose canonical dimension is `d`; that level supplies the tower
conductor attached to the dimension.
-/

/-- Exact quadratic-field data for the rank-one presentation. -/
def rankOneRealQuadraticFieldData (d : RankOneDimension) :
    RealQuadraticFieldData (RankOneField d) where
  finrank_eq_two := rankOneField_finrank d
  place := rankOneInfinitePlace d

/-- Exact fundamental-unit data obtained from Dirichlet's unit theorem. -/
def rankOneRealQuadraticUnitData (d : RankOneDimension) :
    RealQuadraticUnitData (RankOneField d) :=
  (rankOneRealQuadraticFieldData d).toRealQuadraticUnitData

/-- The selected signed embedding sends the explicit root unit to the rank-one root. -/
lemma realEmbeddingAt_rankOneRootUnit (d : RankOneDimension) :
    realEmbeddingAt (RankOneField d) (rankOneInfinitePlace d)
      ((rankOneRootUnit d : NumberField.RingOfIntegers (RankOneField d)) :
        RankOneField d) = rankOneRoot d := by
  rw [realEmbeddingAt_rankOneInfinitePlace, rankOneRootUnit_coe,
    rankOneRealEmbedding_root]

/-- The explicit rank-one root unit occurs at a positive level of the canonical rank-one
dimension tower. This is the concrete field/unit realization of the forward direction of
[AFK25, Theorem 3.20, `thm:dimtowunique`]. -/
theorem exists_rankOneFieldLevel (d : RankOneDimension) :
    ∃ L : (rankOneRealQuadraticUnitData d).RankOneLevel d,
      rankOneRootUnit d =
        (rankOneRealQuadraticUnitData d).epsilon ^ (L.j : ℕ) := by
  apply RealQuadraticUnitData.exists_rankOneLevel_of_rankOneUnit d.property
    (rankOneRealQuadraticUnitData d) (rankOneRootUnit d)
    (rankOneRootUnit_norm d)
  exact realEmbeddingAt_rankOneRootUnit d

/-- A chosen exact positive rank-one tower level in the prescribed rank-one dimension. -/
noncomputable def rankOneFieldLevel (d : RankOneDimension) :
    (rankOneRealQuadraticUnitData d).RankOneLevel d :=
  Classical.choose (exists_rankOneFieldLevel d)

/-- The explicit rank-one root unit is the power of the fundamental unit indexed by the chosen
rank-one tower level. This is the chosen-level projection of `exists_rankOneFieldLevel`. -/
lemma rankOneRootUnit_eq_epsilon_pow (d : RankOneDimension) :
    rankOneRootUnit d =
      (rankOneRealQuadraticUnitData d).epsilon ^ ((rankOneFieldLevel d).j : ℕ) :=
  Classical.choose_spec (exists_rankOneFieldLevel d)

end SIC

end
