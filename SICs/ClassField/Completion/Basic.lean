/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.ProperSpace
import SICs.Source

/-!
# Maps between completions of number fields

Canonical maps between completions at finite and infinite places lying over one another, their
topological algebra instances and tower laws, the integral-unit criterion for a finite completion
map, and local compactness at finite places.

## The argument

Two continuous maps out of a completion into a Hausdorff space agree as soon as they agree on
the dense global field; the tower identities between completion maps follow this way.
Approximation first by a field element and then by a global integer gives integer approximants
with error norm below $N(v)^{-1}$; this is the density argument in Serre, *Local Fields*,
Chapter II, §3.

The algebra map between the valued global fields is uniformly continuous when one prime lies over
the other, so it extends through their uniform completions. Its formulas on the dense global
field give the scalar-tower law. Canonical maps compose in towers because they agree on this dense
global field. Continuity of the map gives continuous scalar multiplication, while a nonzero
element of the prime ideal shows that each finite completion has nontrivial norm. A finite
completion is finite-dimensional over the locally compact field $\mathbb Q_p$ below it, hence
locally compact, and so a proper metric space.

At infinite places the canonical completion map is isometric. It yields a normed-algebra
structure, and the upstairs completion is finite over the one below. The map and its algebra
instances compose in towers by equality on the dense global field.
-/

noncomputable section

open IsDedekindDomain NumberField

namespace SIC

/-! ### Density of the global field -/

namespace FinitePlace

section Density

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- Two continuous maps out of a finite completion agree when they agree on the dense global
field. -/
theorem funext_completion {F : Type*} [TopologicalSpace F] [T2Space F]
    {f g : v.adicCompletion K → F} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x : K, f (algebraMap K (v.adicCompletion K) x) =
      g (algebraMap K (v.adicCompletion K) x)) : f = g := by
  apply (HeightOneSpectrum.denseRange_algebraMap K v).equalizer hf hg
  funext x
  exact h x

/-- An element of `K` integral at `v` has an integer representative with error norm below
$N(v)^{-1}$.
Used in `exists_integral_approx`. -/
private theorem exists_global_integral_approx
    (v : HeightOneSpectrum (𝓞 K)) (x : K)
    (hx : ‖NumberField.FinitePlace.embedding v x‖ ≤ 1) :
    ∃ c : 𝓞 K,
      ‖NumberField.FinitePlace.embedding v (algebraMap (𝓞 K) K c - x)‖ <
        (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  have hv : v.valuation K x ≤ 1 := by
    rw [NumberField.FinitePlace.norm_embedding, HeightOneSpectrum.adicAbv_def] at hx
    have hn : (WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
      (v.valuation K x)) ≤ 1 := by exact_mod_cast hx
    exact (WithZeroMulInt.toNNReal_le_one_iff
      (HeightOneSpectrum.one_lt_absNorm_nnreal v)).mp hn
  let γ : (WithZero (Multiplicative ℤ))ˣ :=
    Units.mk0 (WithZero.exp (-(1 : ℤ))) WithZero.exp_ne_zero
  obtain ⟨c, hc⟩ := v.exists_valuation_sub_lt_of_integer hv γ
  refine ⟨c, ?_⟩
  rw [NumberField.FinitePlace.norm_embedding, HeightOneSpectrum.adicAbv_def]
  have hmono := (WithZeroMulInt.toNNReal_strictMono
    (HeightOneSpectrum.one_lt_absNorm_nnreal v)) hc
  have ht : (WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v)
    (WithZero.exp (-(1 : ℤ))) : ℝ) = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
    rw [WithZeroMulInt.toNNReal_neg_apply (HeightOneSpectrum.absNorm_ne_zero v)
      WithZero.exp_ne_zero]
    change ((Ideal.absNorm v.asIdeal : NNReal) ^ (-(1 : ℤ)) : ℝ) = _
    simp
  rw [show (γ : WithZero (Multiplicative ℤ)) = WithZero.exp (-(1 : ℤ)) from rfl] at hmono
  exact ht ▸ (by exact_mod_cast hmono)

/-- Every integral local element admits a global integer approximation modulo the square of the
maximal ideal, with error norm strictly less than $N(v)^{-1}$.
This is the residue-field density argument used in Serre, *Local Fields*, Chapter II, §3,
proof of Theorem 1(iii). -/
theorem exists_integral_approx
    (v : HeightOneSpectrum (𝓞 K)) {a : v.adicCompletion K} (ha : ‖a‖ ≤ 1) :
    ∃ c : 𝓞 K,
      ‖a - (algebraMap (𝓞 K) (v.adicCompletion K)) c‖ <
        (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  let t : ℝ := (Ideal.absNorm v.asIdeal : ℝ)⁻¹
  have ht0 : 0 < t := inv_pos.mpr (by
    exact_mod_cast (lt_trans zero_lt_one (HeightOneSpectrum.one_lt_absNorm v)))
  have ht1 : t < 1 := by
    dsimp [t]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v)
  obtain ⟨x : K, hx⟩ := (v.denseRange_algebraMap K).exists_dist_lt a ht0
  have hx' : ‖a - NumberField.FinitePlace.embedding v x‖ < t := by
    change ‖a - (algebraMap K (v.adicCompletion K)) x‖ < t
    simpa only [dist_eq_norm] using hx
  have hx1 : ‖NumberField.FinitePlace.embedding v x‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max a
      (-(a - NumberField.FinitePlace.embedding v x))
    have heq : a + -(a - NumberField.FinitePlace.embedding v x) =
        NumberField.FinitePlace.embedding v x := by abel
    rw [heq, norm_neg] at h
    exact h.trans (max_le ha (hx'.le.trans ht1.le))
  obtain ⟨c, hcx⟩ := exists_global_integral_approx v x hx1
  refine ⟨c, ?_⟩
  have hcmap : NumberField.FinitePlace.embedding v (algebraMap (𝓞 K) K c) =
      (algebraMap (𝓞 K) (v.adicCompletion K)) c :=
    (IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K) c).symm
  have hxc : ‖NumberField.FinitePlace.embedding v x -
      algebraMap (𝓞 K) (v.adicCompletion K) c‖ < t := by
    rw [← hcmap]
    simpa only [map_sub, norm_sub_rev] using hcx
  simpa only [dist_eq_norm] using
    (IsUltrametricDist.dist_triangle_max a (NumberField.FinitePlace.embedding v x)
      (algebraMap (𝓞 K) (v.adicCompletion K) c)).trans_lt (max_lt hx' hxc)

end Density

end FinitePlace

/-! ### Finite completion maps and instances -/

namespace FinitePlace

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- The canonical map between finite completions at primes lying over one another. -/
def completionMap : v.adicCompletion K →+* w.adicCompletion L := by
  exact
    ((HeightOneSpectrum.adicCompletion.equiv L w).symm.toRingHom.comp
      (UniformSpace.Completion.mapRingHom
        (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
        (v.uniformContinuous_algebraMap_liesOver K L w).continuous)).comp
      (HeightOneSpectrum.adicCompletion.equiv K v).toRingHom

/-- The canonical map between finite completions is continuous. -/
theorem continuous_completionMap : Continuous (completionMap v w) := by
  exact (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L w).comp <|
    UniformSpace.Completion.continuous_map.comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion K v)

/-- The finite-completion map agrees with the valued-field algebra map on the dense subfield. -/
theorem completionMap_coe (x : WithVal (v.valuation K)) :
    completionMap v w (x : v.adicCompletion K) =
      ((algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)) x :
        WithVal (w.valuation L)) : w.adicCompletion L) := by
  apply HeightOneSpectrum.adicCompletion.ext
  exact UniformSpace.Completion.mapRingHom_coe _ x

/-- The finite-completion map agrees with the global field embedding. -/
theorem completionMap_algebraMap (x : K) :
    completionMap v w (algebraMap K (v.adicCompletion K) x) =
      algebraMap L (w.adicCompletion L) (algebraMap K L x) := by
  change completionMap v w (x : v.adicCompletion K) =
    (algebraMap K L x : w.adicCompletion L)
  rw [show (x : v.adicCompletion K) = ((WithVal.toVal (v.valuation K) x :
    WithVal (v.valuation K)) : v.adicCompletion K) from rfl, completionMap_coe]
  rfl

/-- The completion map scales the normalized finite-place norm by the ramification index times
the inertia degree. -/
theorem completionMap_norm (x : v.adicCompletion K) :
    ‖completionMap v w x‖ =
      ‖x‖ ^ (w.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
        w.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) := by
  let e := w.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
    w.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)
  have heq :
      (fun y : v.adicCompletion K ↦ ‖completionMap v w y‖) =
      (fun y : v.adicCompletion K ↦ ‖y‖ ^ e) := by
    apply SIC.FinitePlace.funext_completion v
    · exact continuous_norm.comp (continuous_completionMap v w)
    · exact continuous_norm.pow e
    · intro a
      rw [completionMap_algebraMap]
      exact NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply_algebraMap
        (K := K) (L := L) v w a
  exact congrFun heq x

/-- A unit of $K_v$ is integral exactly when its image in $L_w$ is. -/
theorem units_map_completionMap_mem_iff {x : (v.adicCompletion K)ˣ} :
    Units.map (completionMap v w : v.adicCompletion K →* w.adicCompletion L) x ∈
        (Submonoid.ofClass (w.adicCompletionIntegers L)).units ↔
      x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  constructor
  · intro hx
    have hnorm : ‖((Units.map (completionMap v w :
        v.adicCompletion K →* w.adicCompletion L) x : (w.adicCompletion L)ˣ) :
        w.adicCompletion L)‖ = 1 :=
      Valued.toNormedField.norm_eq_one_iff.mpr
        (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hx)
    have he : 0 < w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) :=
      mul_pos (w.asIdeal.ramificationIdx_pos _) (w.asIdeal.inertiaDeg_pos _)
    have hpow : ‖(x : v.adicCompletion K)‖ ^
        (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)) = 1 := by
      rw [← completionMap_norm v w]
      exact hnorm
    apply HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
    exact Valued.toNormedField.norm_eq_one_iff.mp
      ((pow_eq_one_iff_of_nonneg (norm_nonneg (x : v.adicCompletion K)) he.ne').mp hpow)
  · intro hx
    have hnorm : ‖(x : v.adicCompletion K)‖ = 1 :=
      Valued.toNormedField.norm_eq_one_iff.mpr
        (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hx)
    have hnorm' : ‖((Units.map (completionMap v w) x : (w.adicCompletion L)ˣ) :
        w.adicCompletion L)‖ = 1 := by
      change ‖completionMap v w (x : v.adicCompletion K)‖ = 1
      rw [completionMap_norm, hnorm, one_pow]
    exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
      (Valued.toNormedField.norm_eq_one_iff.mp hnorm')

/-- The canonical scoped algebra structure between finite completions at lying-over primes. -/
noncomputable scoped instance instAlgebraAdicCompletion :
    Algebra (v.adicCompletion K) (w.adicCompletion L) := by
  exact (completionMap v w).toAlgebra

/-- In the finite-completion scope, the global-to-local algebra maps form a scalar tower. -/
scoped instance instIsScalarTowerAdicCompletion :
    IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  symm
  exact completionMap_algebraMap v w x

/-- In the finite-completion scope, scalar multiplication between completions is continuous. -/
scoped instance instContinuousSMulAdicCompletion :
    ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) := by
  constructor
  exact (continuous_completionMap v w).comp continuous_fst |>.mul continuous_snd

/-- A finite completion of a number field has characteristic zero, via the field embedding. -/
instance instCharZeroAdicCompletion
    {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    CharZero (v.adicCompletion K) :=
  charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective

/-- A finite completion of a number field has a nontrivial norm. -/
noncomputable instance instNontriviallyNormedFieldAdicCompletion
    {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    NontriviallyNormedField (v.adicCompletion K) := by
  apply NontriviallyNormedField.ofNormNeOne
  obtain ⟨x, hx⟩ := Submodule.nonzero_mem_of_bot_lt
    (bot_lt_iff_ne_bot.mpr v.ne_bot)
  refine ⟨NumberField.FinitePlace.embedding v (algebraMap (RingOfIntegers K) K x), ?_, ?_⟩
  · intro hzero
    apply hx
    apply Subtype.ext
    apply IsFractionRing.injective (RingOfIntegers K) K
    apply (NumberField.FinitePlace.embedding v).injective
    simpa using hzero
  · exact ne_of_lt ((NumberField.FinitePlace.norm_lt_one_iff_mem K v x).2 x.property)

variable {M : Type*} [Field M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [NumberField M]
  (u : HeightOneSpectrum (𝓞 M)) [u.asIdeal.LiesOver w.asIdeal]

/-- Canonical maps between finite completions compose in towers. -/
theorem completionMap_trans :
    letI : u.asIdeal.LiesOver v.asIdeal :=
      Ideal.LiesOver.trans u.asIdeal w.asIdeal v.asIdeal
    (completionMap (K := L) (L := M) w u).comp
        (completionMap (K := K) (L := L) v w) =
      completionMap (K := K) (L := M) v u := by
  let _ : u.asIdeal.LiesOver v.asIdeal :=
    Ideal.LiesOver.trans u.asIdeal w.asIdeal v.asIdeal
  apply RingHom.ext
  intro x
  have heq :
      (fun y ↦ completionMap (K := L) (L := M) w u
        (completionMap (K := K) (L := L) v w y)) =
      (fun y ↦ completionMap (K := K) (L := M) v u y) := by
    apply funext_completion v
    · exact (continuous_completionMap w u).comp (continuous_completionMap v w)
    · exact continuous_completionMap v u
    · intro a
      rw [completionMap_algebraMap, completionMap_algebraMap,
        completionMap_algebraMap, IsScalarTower.algebraMap_apply K L M]
  exact congrFun heq x

/-- In the finite-completion scope, canonical completion algebras form a scalar tower. -/
scoped instance instIsScalarTowerAdicCompletionTower :
    letI : u.asIdeal.LiesOver v.asIdeal :=
      Ideal.LiesOver.trans u.asIdeal w.asIdeal v.asIdeal
    IsScalarTower (v.adicCompletion K) (w.adicCompletion L) (u.adicCompletion M) := by
  let _ : u.asIdeal.LiesOver v.asIdeal :=
    Ideal.LiesOver.trans u.asIdeal w.asIdeal v.asIdeal
  apply IsScalarTower.of_algebraMap_eq
  intro x
  exact congrFun (congrArg DFunLike.coe (completionMap_trans v w u)).symm x

end FinitePlace

/-! ### Local compactness -/

namespace FinitePlace

variable (K : Type*) [Field K] [NumberField K]

/-- Every nonarchimedean completion of a number field is a proper metric space.
[83, Neukirch (1999), Chapter II, Propositions 5.1–5.2]. -/
@[source "83, Chapter II, Proposition 5.1, p. 135 (locally compact, as a proper space)"]
instance instProperSpaceAdicCompletion (w : HeightOneSpectrum (𝓞 K)) :
    ProperSpace (w.adicCompletion K) := by
  let v : HeightOneSpectrum (𝓞 ℚ) := w.under (𝓞 ℚ)
  let _ : w.asIdeal.LiesOver v.asIdeal := Ideal.over_under w.asIdeal
  let _ : LocallyCompactSpace (v.adicCompletion ℚ) := by
    let : Algebra ℚ (v.adicCompletion ℚ) :=
      HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v
    exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph
      |>.locallyCompactSpace_iff.mpr inferInstance
  let _ : LocallyCompactSpace (w.adicCompletion K) :=
    LocallyCompactSpace.of_finiteDimensional_of_complete
      (v.adicCompletion ℚ) (w.adicCompletion K)
  exact ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _

end FinitePlace

/-! ### Infinite completion maps and instances -/

namespace InfinitePlace

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L]
  (v : NumberField.InfinitePlace K) (w : NumberField.InfinitePlace L) [w.LiesOver v]

omit [NumberField K] [NumberField L] in
/-- The global-to-local algebra maps into an infinite completion form a scalar tower. -/
instance instIsScalarTowerCompletion : IsScalarTower K L w.Completion :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

omit [NumberField K] in
/-- Two continuous maps out of an infinite completion agree when they agree on the dense global
field. -/
theorem funext_completion {F : Type*} [TopologicalSpace F] [T2Space F]
    {f g : v.Completion → F} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x : K, f (algebraMap K v.Completion x) = g (algebraMap K v.Completion x)) :
    f = g := by
  apply (denseRange_coe v).equalizer hf hg
  funext x
  exact h x.ofAbs

omit [NumberField K] [NumberField L] in
/-- The canonical map between infinite completions at lying-over places is an isometry. -/
theorem completionMap_isometry :
    Isometry (NumberField.LiesOver.completionMap (v := v) (w := w)) := by
  exact (isometryEquivCompletion w).symm.isometry.comp
    ((UniformSpace.Completion.isometry_mapRingHom
      (NumberField.InfinitePlace.LiesOver.isometry_algebraMap w v)).comp
        (isometryEquivCompletion v).isometry)

/-- An infinite completion has a nontrivial norm. -/
noncomputable instance instNontriviallyNormedFieldCompletion
    {K : Type*} [Field K] (v : NumberField.InfinitePlace K) :
    NontriviallyNormedField v.Completion := by
  apply NontriviallyNormedField.ofNormNeOne
  refine ⟨2, ?_, ?_⟩
  · intro hzero
    have hzero' := congrArg (extensionEmbedding v) hzero
    have hzero'' : (2 : ℂ) = 0 := by
      simpa only [map_ofNat, map_zero] using hzero'
    exact (by norm_num : (2 : ℂ) ≠ 0) hzero''
  · have h :=
      (isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) (2 : v.Completion)
    have hvnorm : ‖(2 : v.Completion)‖ = 2 := by
      calc
        ‖(2 : v.Completion)‖ = ‖extensionEmbedding v (2 : v.Completion)‖ := h.symm
        _ = ‖(2 : ℂ)‖ := by rw [map_ofNat]
        _ = 2 := by norm_num
    rw [hvnorm]
    norm_num

/-- The canonical scoped algebra between infinite completions is a normed algebra. -/
noncomputable scoped instance instNormedAlgebraCompletion :
    NormedAlgebra v.Completion w.Completion := by
  refine
    { toAlgebra := inferInstance
      norm_smul_le := ?_ }
  intro r x
  change ‖NumberField.LiesOver.completionMap r * x‖ ≤ ‖r‖ * ‖x‖
  rw [norm_mul, (completionMap_isometry v w).norm_map_of_map_zero (map_zero _)]

/-- In the infinite-completion scope, the upstairs completion is finite over the one below. -/
noncomputable scoped instance instModuleFiniteCompletion :
    Module.Finite v.Completion w.Completion := by
  rcases w.isUnramified_or_isRamified K with hw | hw
  · exact Module.finite_of_finrank_eq_succ (by simpa using hw.finrank_eq_one v)
  · exact Module.finite_of_finrank_eq_succ (by simpa using hw.finrank_eq_two v)

variable {M : Type*} [Field M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [NumberField M] (u : NumberField.InfinitePlace M) [u.LiesOver w] [u.LiesOver v]

omit [NumberField K] [NumberField L] [NumberField M] in
/-- Canonical maps between infinite completions compose in towers. -/
theorem completionMap_trans :
    (NumberField.LiesOver.completionMap (v := w) (w := u)).comp
        (NumberField.LiesOver.completionMap (v := v) (w := w)) =
      NumberField.LiesOver.completionMap (v := v) (w := u) := by
  apply RingHom.ext
  intro x
  have heq :
      (fun y : v.Completion ↦ NumberField.LiesOver.completionMap
          (NumberField.LiesOver.completionMap (v := v) (w := w) y)) =
        (fun y : v.Completion ↦ NumberField.LiesOver.completionMap (v := v) (w := u) y) := by
    apply funext_completion v
    · exact NumberField.LiesOver.continuous_completionMap.comp
        NumberField.LiesOver.continuous_completionMap
    · exact NumberField.LiesOver.continuous_completionMap
    · intro y
      have hglobal : (algebraMap L u.Completion) ((algebraMap K L) y) =
          (algebraMap K u.Completion) y := by
        rw [IsScalarTower.algebraMap_apply L M u.Completion,
          ← IsScalarTower.algebraMap_apply K L M,
          ← IsScalarTower.algebraMap_apply K M u.Completion]
      change (algebraMap w.Completion u.Completion)
          ((algebraMap v.Completion w.Completion) ((algebraMap K v.Completion) y)) =
        (algebraMap v.Completion u.Completion) ((algebraMap K v.Completion) y)
      rw [← IsScalarTower.algebraMap_apply K v.Completion w.Completion y,
        IsScalarTower.algebraMap_apply K L w.Completion y,
        ← IsScalarTower.algebraMap_apply L w.Completion u.Completion (algebraMap K L y),
        hglobal,
        ← IsScalarTower.algebraMap_apply K v.Completion u.Completion y]
  exact congrFun heq x

omit [NumberField K] [NumberField L] [NumberField M] in
/-- In the infinite-completion scope, canonical completion algebras form a scalar tower. -/
scoped instance instIsScalarTowerCompletionTower :
    IsScalarTower v.Completion w.Completion u.Completion := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  exact congrFun (congrArg DFunLike.coe (completionMap_trans v w u)).symm x

end InfinitePlace

end SIC
