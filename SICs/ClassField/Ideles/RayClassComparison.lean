/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Ideles.RaySubgroup
import SICs.ClassField.RayClassGroup.Quotient

/-!
# The idèlic description of the ray class group

The exact isomorphism between the quotient of the idèle class group by the selected-place ray
subgroup and the ideal-theoretic ray class group `RayClassQuotient F m`, and the finite index of
the ray subgroup.

This is Milne, *Class Field Theory*, version 4.03 (2020), Chapter V, Proposition 4.6, and the
corrected Bonn Lectures, Chapter III, Proposition 9.3, for the modulus `𝔪∞₂` of
[AFK25, Definition 2.1, `defn:rayclassgroup`]: the distinguished real place is unrestricted and
the other real place is positive.  The ray class group is the one constructed on integral
representatives in `SICs.ClassField.RayClassGroup.Quotient`, so the isomorphism is built from ray
ideals to idèle classes, and no second presentation of the ray class group is introduced.

## The argument

Write `U = U_{𝔪∞₂}` for `IdeleGroup.raySubgroup` at
`InfinitePlace.raySupport F.place`, and `C_{𝔪∞₂}` for its image in the idèle class group
`C_K = I_K / K^×`. Let `I_𝔪` be the subgroup of idèles
congruent to one modulo `𝔪∞₂`: components in the higher unit group `U_v^{(n_v)}` at every prime
`v ∣ 𝔪`, and positive at the real place `∞₂`.  This is Milne's `I_𝔪`, and `U` is his `W_𝔪`.

1. *Kernel.*  On `I_𝔪` the fractional-ideal map has kernel exactly `U`: a trivial ideal means
   integral-unit finite components, and the remaining conditions of `U` are those of `I_𝔪`.
2. *Principal congruent idèles.*  If `a, b` are ray congruent and `cb = a`, then a common
   normalizer makes both generators `≡ 1 (mod 𝔪)`, so `c` lies in every finite ray factor at the
   primes dividing `𝔪`, and `c > 0` at `∞₂`: the principal idèle of `c` lies in `I_𝔪`.
   Conversely, let the principal idèle of `c` lie in `I_𝔪`, and let `I = cJ` for ray ideals
   `I, J`.  Choose `b ∈ J` totally positive with `b ≡ 1 (mod 𝔪)`.  Then `a = cb` is integral,
   `a - b = b(c - 1)` lies in `𝔪`, and `a, b` witness `I ∼ J`.
3. *The map.*  The uniformizer idèle `s(I)` of a ray ideal `I` has fractional ideal `I` and
   components `1` at the primes dividing `𝔪` and at infinity, so it lies in `I_𝔪`.  If `I ∼ J`
   through `a, b`, then `s(I)⁻¹ s(J) (a/b)` lies in `I_𝔪` and has trivial ideal, hence lies in
   `U` by step 1.  So the class of `s(I)` modulo `K^× U` descends to a homomorphism from
   `RayClassQuotient F m`.
4. *Injectivity.*  If `s(I)⁻¹ s(J) = c⁻¹ u` with `c ∈ K^×` and `u ∈ U`, then the principal idèle
   of `c` lies in `I_𝔪`, and comparing ideals gives `I = cJ`; step 2 gives `I ∼ J`.
5. *Surjectivity.* Mixed weak approximation moves any idèle into `I_𝔪` by a principal
   multiple. Its fractional ideal `J` is prime to `𝔪`, and comparison with the uniformizer
   idèle `s(J)` reduces to the kernel calculation of step 1.

The inverse of this bijection is `RayClassQuotient.ideleClassEquiv`.  Finiteness of
`RayClassQuotient F m` (Milne, Chapter V, Theorem 1.7) then gives finite index of `C_{𝔪∞₂}` in
`C_K`.
-/

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors

namespace SIC

universe u

variable {K : Type u} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
  (F : RealQuadraticFieldData K) {m : Ideal (𝓞 K)}

/-! ### Idèles congruent to one modulo `𝔪∞₂`

The subgroup `I_𝔪` of Milne, *Class Field Theory*, Chapter V, §4: higher-unit conditions at the
primes dividing `𝔪` and the sign condition at `∞₂`, with no condition at the other places.  On
it, the kernel of the fractional-ideal map is the ray subgroup. -/

/-! ### Principal congruent idèles

The principal idèles in `I_𝔪` are those of the group `K_{𝔪,1}` of Milne, *Class Field Theory*,
Chapter V, §4.  On integral representatives: quotients of ray-congruent generators are
congruent, and a congruent principal idèle relating two ray ideals makes them ray equivalent. -/

/-- **A quotient of ray-congruent generators is congruent to one modulo `𝔪∞₂`**: if
`RayCongruent F m a b` and `cb = a`, then the principal idèle of `c` lies in `I_𝔪`.  This is
the inclusion `K_{𝔪,1} ⊆ I_𝔪` of Milne, *Class Field Theory*, version 4.03 (2020), Chapter V,
§4. -/
theorem RayCongruent.unitEmbedding_mem_congruent
    {a b : 𝓞 K} (h : RayCongruent F m a b) {c : Kˣ} (hc : (c : K) * b = a) :
    NumberField.IdeleGroup.unitEmbedding (𝓞 K) K c ∈
      IdeleGroup.congruentSubgroup (InfinitePlace.raySupport F.place) m := by
  obtain ⟨d, hd, had, hbd, _⟩ := h.exists_common_normalizer
  have had0 : (a * d : 𝓞 K) ≠ 0 := mul_ne_zero h.ne_zero_left hd
  have hbd0 : (b * d : 𝓞 K) ≠ 0 := mul_ne_zero h.ne_zero_right hd
  let ua : Kˣ := Units.mk0 ((a * d : 𝓞 K) : K)
    (RingOfIntegers.coe_eq_zero_iff.not.mpr had0)
  let ub : Kˣ := Units.mk0 ((b * d : 𝓞 K) : K)
    (RingOfIntegers.coe_eq_zero_iff.not.mpr hbd0)
  have hcu : c = ua * ub⁻¹ := by
    have hmul : c * ub = ua := by
      apply Units.ext
      change (c : K) * ((b * d : 𝓞 K) : K) = ((a * d : 𝓞 K) : K)
      simp only [map_mul]
      calc
        (c : K) * ((b : K) * (d : K)) =
            ((c : K) * (b : K)) * (d : K) := by ring
        _ = (a : K) * (d : K) := by rw [hc]
    calc
      c = (c * ub) * ub⁻¹ := by simp
      _ = ua * ub⁻¹ := by rw [hmul]
  apply (IdeleGroup.mem_congruentSubgroup_iff (InfinitePlace.raySupport F.place) m _).mpr
  constructor
  · intro w
    rw [IdeleGroup.infiniteComponent_unitEmbedding,
      InfinitePlace.units_map_mem_rayUnitGroup_iff]
    by_cases hw : w = F.place
    · exact Or.inl (by simp [InfinitePlace.raySupport, hw])
    · right
      have hpos := h.pos w hw
      have hcb := congrArg (realEmbeddingAt K w) hc
      simp only [map_mul] at hcb
      rw [← hcb, mul_assoc] at hpos
      have hbnonneg : 0 ≤ realEmbeddingAt K w (b : K) *
          realEmbeddingAt K w (b : K) := mul_self_nonneg _
      exact pos_of_mul_pos_left hpos hbnonneg
  · intro v hv
    rw [IdeleGroup.finiteComponent_unitEmbedding, hcu, map_mul, map_inv]
    have hua : Units.map (algebraMap K (v.adicCompletion K)) ua ∈
        FinitePlace.rayUnitGroup m v :=
      FinitePlace.units_map_mem_rayUnitGroup_of_sub_one_mem (by simp [ua]) had hv
    have hub : Units.map (algebraMap K (v.adicCompletion K)) ub ∈
        FinitePlace.rayUnitGroup m v :=
      FinitePlace.units_map_mem_rayUnitGroup_of_sub_one_mem (by simp [ub]) hbd hv
    exact (FinitePlace.rayUnitGroup m v).mul_mem hua
      ((FinitePlace.rayUnitGroup m v).inv_mem hub)

/-- A ray equivalence supplies a congruent principal idèle relating the fractional ideals;
used by `RayIdeal.ideleClass_eq_of_isEquivalent`. -/
private theorem RayIdeal.exists_congruent_unitEmbedding_of_isEquivalent
    {I J : RayIdeal K m} (h : I.IsEquivalent F m J) :
    ∃ c : Kˣ, NumberField.IdeleGroup.unitEmbedding (𝓞 K) K c ∈
        IdeleGroup.congruentSubgroup (InfinitePlace.raySupport F.place) m ∧
      ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (c : K) *
          ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
  obtain ⟨a, b, hab, hIJ⟩ := h
  have ha0 : (a : K) ≠ 0 := RingOfIntegers.coe_eq_zero_iff.not.mpr hab.ne_zero_left
  have hb0 : (b : K) ≠ 0 := RingOfIntegers.coe_eq_zero_iff.not.mpr hab.ne_zero_right
  let ua : Kˣ := Units.mk0 (a : K) ha0
  let ub : Kˣ := Units.mk0 (b : K) hb0
  let c : Kˣ := ua * ub⁻¹
  have hc : (c : K) * b = a := by
    change ((ua : K) * (ub : K)⁻¹) * (b : K) = (a : K)
    simp [ua, ub, hb0]
  refine ⟨c, hab.unitEmbedding_mem_congruent F hc, ?_⟩
  have hfrac :
      ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (b : K) =
        ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) := by
    simpa only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton] using
      congrArg (fun L : Ideal (𝓞 K) ↦ (L : FractionalIdeal (𝓞 K)⁰ K)) hIJ
  have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (c : K) *
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (b : K) := by
    rw [FractionalIdeal.spanSingleton_mul_spanSingleton, hc]
  rw [hspan] at hfrac
  have hmul :
      ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (b : K) =
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (c : K) *
          ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) *
            FractionalIdeal.spanSingleton (𝓞 K)⁰ (b : K) := by
    calc
      _ = _ := hfrac
      _ = _ := by ac_rfl
  exact mul_right_cancel₀ (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hb0) hmul

/-- **A congruent principal idèle relating two ray ideals makes them ray equivalent**: if the
principal idèle of `c` lies in `I_𝔪` and `I = cJ` as fractional ideals, then `I ∼ J`.  This is
the equality `K_{𝔪,1} = K^× ∩ I_𝔪` of Milne, *Class Field Theory*, version 4.03 (2020),
Chapter V, §4, on integral representatives. -/
theorem RayIdeal.isEquivalent_of_unitEmbedding_mem (hm : m ≠ ⊥) {I J : RayIdeal K m} {c : Kˣ}
    (hc : NumberField.IdeleGroup.unitEmbedding (𝓞 K) K c ∈
      IdeleGroup.congruentSubgroup (InfinitePlace.raySupport F.place) m)
    (hIJ : ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (c : K) *
        ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) :
    I.IsEquivalent F m J := by
  obtain ⟨b, hbJ, hbm, hbpos⟩ := J.exists_mem_sub_one_mem_forall_pos
  have hcbmem : (c : K) * (b : K) ∈
      ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hIJ]
    exact FractionalIdeal.mem_singleton_mul.mpr
      ⟨(b : K), FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ hbJ, rfl⟩
  obtain ⟨a, haI, haeq⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hcbmem
  have hca : (c : K) * (b : K) = (a : K) := haeq.symm
  have hfin (v : HeightOneSpectrum (𝓞 K))
      (hv : FinitePlace.modulusExponent m v ≠ 0) :
      Units.map (algebraMap K (v.adicCompletion K)) c ∈ FinitePlace.rayUnitGroup m v := by
    have hcv := ((IdeleGroup.mem_congruentSubgroup_iff
      (InfinitePlace.raySupport F.place) m _).mp hc).2 v hv
    simpa only [IdeleGroup.finiteComponent_unitEmbedding] using hcv
  have habm : a - b ∈ m :=
    FinitePlace.sub_mem_of_units_map_mem_rayUnitGroup hm hca hfin
  have ham : a - 1 ∈ m := by
    convert m.add_mem habm hbm using 1; ring
  have hacop : IsCoprime (Ideal.span {a}) m :=
    isCoprime_span_singleton_of_sub_mem isCoprime_span_singleton_one ham
  have hpos : ∀ w : InfinitePlace K, w ≠ F.place →
      0 < realEmbeddingAt K w (a : K) * realEmbeddingAt K w (b : K) := by
    intro w hw
    have hcp : 0 < realEmbeddingAt K w (c : K) := by
      have hcw := ((IdeleGroup.mem_congruentSubgroup_iff
        (InfinitePlace.raySupport F.place) m _).mp hc).1 w
      exact ((InfinitePlace.units_map_mem_rayUnitGroup_iff
        (InfinitePlace.raySupport F.place) w c).mp
        (by simpa only [IdeleGroup.infiniteComponent_unitEmbedding] using hcw)).resolve_left
          (by simpa [InfinitePlace.raySupport] using hw)
    rw [← hca, map_mul]
    exact mul_pos (mul_pos hcp (hbpos w)) (hbpos w)
  refine ⟨a, b, ⟨hacop, habm, hpos⟩, ?_⟩
  apply FractionalIdeal.coeIdeal_injective (K := K)
  simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
  calc
    ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (b : K) =
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (c : K) *
        ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) *
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (b : K) := by rw [hIJ]
    _ = ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
        FractionalIdeal.spanSingleton (𝓞 K)⁰ ((c : K) * b) := by
      rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
      ac_rfl
    _ = ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) := by rw [hca]

/-! ### Uniformizer idèles of ray ideals

A ray ideal `I` gives the uniformizer idèle `s(I)` of `IdeleGroup.ofFractionalIdeal`, whose
fractional ideal is `I` and which is congruent to one modulo `𝔪∞₂`.  Its class modulo `K^× U`
depends only on the ray class of `I`. -/

/-- A ray ideal as an invertible fractional ideal. -/
def RayIdeal.toFractionalIdeal : RayIdeal K m →* (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  toFun I := Units.mk0 ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
    (FractionalIdeal.coeIdeal_ne_zero.mpr I.ne_bot)
  map_one' := by
    apply Units.ext
    simp only [RayIdeal.coe_one, FractionalIdeal.coeIdeal_top, Units.val_mk0, Units.val_one]
  map_mul' := by
    intro I J
    apply Units.ext
    simp only [Submonoid.coe_mul, FractionalIdeal.coeIdeal_mul, Units.val_mk0, Units.val_mul]

omit [NumberField.IsTotallyReal K] in
/-- The underlying fractional ideal of `RayIdeal.toFractionalIdeal I` is `I`. -/
@[simp]
theorem RayIdeal.coe_toFractionalIdeal (I : RayIdeal K m) :
    ((RayIdeal.toFractionalIdeal I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) = ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
  rfl

/-- The uniformizer idèle `s(I)` of a ray ideal. -/
def RayIdeal.idele : RayIdeal K m →* NumberField.IdeleGroup (𝓞 K) K :=
  IdeleGroup.ofFractionalIdeal.comp RayIdeal.toFractionalIdeal

omit [NumberField.IsTotallyReal K] in
/-- The fractional ideal of the uniformizer idèle of a ray ideal is that ideal. -/
@[simp]
theorem RayIdeal.toFractionalIdeal_idele (I : RayIdeal K m) :
    IdeleGroup.toFractionalIdeal (RayIdeal.idele I) = RayIdeal.toFractionalIdeal I := by
  exact IdeleGroup.toFractionalIdeal_ofFractionalIdeal _

omit [NumberField.IsTotallyReal K] in
/-- The ideal of a ray ideal has order zero at every prime dividing the modulus; used by
`RayIdeal.idele_mem_congruent`. -/
private theorem RayIdeal.count_eq_zero_of_modulusExponent_ne_zero
    (I : RayIdeal K m) (v : HeightOneSpectrum (𝓞 K))
    (hv : FinitePlace.modulusExponent m v ≠ 0) :
    FractionalIdeal.count K v ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  have hnot : ¬v.asIdeal ∣ (I : Ideal (𝓞 K)) :=
    FinitePlace.not_dvd_of_isCoprime I.isCoprime hv
  rw [FractionalIdeal.count_coe K v I.ne_bot]
  exact_mod_cast not_not.mp
    ((Associates.count_ne_zero_iff_dvd I.ne_bot v.irreducible).not.mpr hnot)

/-- The uniformizer idèle of a ray ideal is congruent to one modulo `𝔪∞₂`: its components at the
primes dividing `𝔪` and at infinity are `1`. -/
theorem RayIdeal.idele_mem_congruent (I : RayIdeal K m) :
    RayIdeal.idele I ∈ IdeleGroup.congruentSubgroup (InfinitePlace.raySupport F.place) m := by
  apply IdeleGroup.ofFractionalIdeal_mem_congruentSubgroup
    (InfinitePlace.raySupport F.place) m
  apply FractionalIdeal.mem_primeTo_iff.mpr
  intro v hv
  simpa only [RayIdeal.coe_toFractionalIdeal] using
    I.count_eq_zero_of_modulusExponent_ne_zero v (FinitePlace.mem_modulusSupport.mp hv)

variable (m) in
/-- The quotient `C_K / C_{𝔪∞₂}` of the idèle class group by the selected-place ray subgroup.
Instance search finds its `Group` structure but neither `CommGroup` nor `IsMulCommutative`;
commutativity must be supplied directly when a consumer needs it. -/
abbrev RayIdeleClassQuotient : Type u :=
  NumberField.IdeleClassGroup (𝓞 K) K ⧸
    IdeleClassGroup.raySubgroup (InfinitePlace.raySupport F.place) m

/-- The ray idèle class of an idèle. -/
def RayIdeleClassQuotient.mk (m : Ideal (𝓞 K)) :
    NumberField.IdeleGroup (𝓞 K) K →* RayIdeleClassQuotient F m :=
  (QuotientGroup.mk' (IdeleClassGroup.raySubgroup (InfinitePlace.raySupport F.place) m)).comp
    (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K))

/-- Evaluation of the ray idèle class map. -/
@[simp]
theorem RayIdeleClassQuotient.mk_apply (x : NumberField.IdeleGroup (𝓞 K) K) :
    RayIdeleClassQuotient.mk F m x =
      ((x : NumberField.IdeleClassGroup (𝓞 K) K) : RayIdeleClassQuotient F m) :=
  rfl

/-- A principal idèle has trivial ray idèle class. -/
@[simp]
theorem RayIdeleClassQuotient.mk_unitEmbedding (c : Kˣ) :
    RayIdeleClassQuotient.mk F m (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K c) = 1 := by
  rw [RayIdeleClassQuotient.mk_apply, IdeleClassGroup.coe_unitEmbedding]
  rfl

/-- The class in `C_K / C_{𝔪∞₂}` of the uniformizer idèle of a ray ideal. -/
def RayIdeal.ideleClass : RayIdeal K m →* RayIdeleClassQuotient F m :=
  (RayIdeleClassQuotient.mk F m).comp RayIdeal.idele

/-- Two congruent idèles with the same fractional ideal define the same ray idèle class;
used by the comparison map and its surjectivity. -/
private theorem congruent_ideleClass_eq_of_toFractionalIdeal_eq
    {x y : NumberField.IdeleGroup (𝓞 K) K}
    (hx : x ∈ IdeleGroup.congruentSubgroup (InfinitePlace.raySupport F.place) m)
    (hy : y ∈ IdeleGroup.congruentSubgroup (InfinitePlace.raySupport F.place) m)
    (hxy : IdeleGroup.toFractionalIdeal x = IdeleGroup.toFractionalIdeal y) :
    RayIdeleClassQuotient.mk F m x = RayIdeleClassQuotient.mk F m y := by
  apply QuotientGroup.eq.mpr
  apply (IdeleClassGroup.mem_raySubgroup_iff (InfinitePlace.raySupport F.place) m _).mpr
  refine ⟨x⁻¹ * y, ?_, ?_⟩
  · have hray := IdeleGroup.mul_inv_mem_raySubgroup
      (InfinitePlace.raySupport F.place) m hy hx hxy.symm
    simpa only [mul_comm] using hray
  · simp

/-- **Ray-equivalent ideals have the same idèle class modulo `C_{𝔪∞₂}`**: if `I ∼ J` through
`a, b`, then `s(I)⁻¹ s(J) (a/b)` lies in the ray subgroup.  This is the well-definedness of the
map of Milne, *Class Field Theory*, version 4.03 (2020), Chapter V, Proposition 4.6(a), on
integral representatives. -/
theorem RayIdeal.ideleClass_eq_of_isEquivalent {I J : RayIdeal K m}
    (h : I.IsEquivalent F m J) : RayIdeal.ideleClass F I = RayIdeal.ideleClass F J := by
  obtain ⟨c, hc, hIJ⟩ := I.exists_congruent_unitEmbedding_of_isEquivalent F h
  have hideal : IdeleGroup.toFractionalIdeal (RayIdeal.idele I) =
      IdeleGroup.toFractionalIdeal
        (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K c * RayIdeal.idele J) := by
    apply Units.ext
    simpa only [map_mul, RayIdeal.toFractionalIdeal_idele,
      RayIdeal.coe_toFractionalIdeal, IdeleGroup.coe_toFractionalIdeal_unitEmbedding,
      Units.val_mul] using hIJ
  have hclass := congruent_ideleClass_eq_of_toFractionalIdeal_eq F
    (RayIdeal.idele_mem_congruent F I)
    ((IdeleGroup.congruentSubgroup (InfinitePlace.raySupport F.place) m).mul_mem hc
      (RayIdeal.idele_mem_congruent F J)) hideal
  simpa only [RayIdeal.ideleClass, MonoidHom.comp_apply, map_mul,
    RayIdeleClassQuotient.mk_unitEmbedding, one_mul] using hclass

/-! ### The comparison isomorphism

The ideal classes of uniformizer idèles define a homomorphism from `RayClassQuotient F m` to
`C_K / C_{𝔪∞₂}`, which is injective by the principal-idèle criterion and surjective by
approximation.  Its inverse is the comparison isomorphism. -/

/-- The homomorphism from the ray class group to `C_K / C_{𝔪∞₂}` sending the class of `I` to the
class of its uniformizer idèle. -/
def RayClassQuotient.toIdeleClassQuotient (m : Ideal (𝓞 K)) :
    RayClassQuotient F m →* RayIdeleClassQuotient F m :=
  Con.lift (rayClassCon F m) (RayIdeal.ideleClass F) fun _ _ h ↦
    RayIdeal.ideleClass_eq_of_isEquivalent F h

/-- Evaluation of `RayClassQuotient.toIdeleClassQuotient` on a ray class. -/
@[simp]
theorem RayClassQuotient.toIdeleClassQuotient_mk (I : RayIdeal K m) :
    RayClassQuotient.toIdeleClassQuotient F m (RayClassQuotient.mk F m I) =
      RayIdeal.ideleClass F I :=
  rfl

omit [NumberField.IsTotallyReal K] in
/-- The fractional-ideal equation obtained from a principal relation between uniformizer
idèles after discarding a ray idèle of trivial ideal. -/
private theorem RayIdeal.fractional_eq_of_principal_idele_relation
    (I J : RayIdeal K m) {u : NumberField.IdeleGroup (𝓞 K) K}
    (hu : IdeleGroup.toFractionalIdeal u = 1) {c : Kˣ}
    (hc : NumberField.IdeleGroup.unitEmbedding (𝓞 K) K c =
      u⁻¹ * ((RayIdeal.idele I)⁻¹ * RayIdeal.idele J)) :
    ((I : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ ((c⁻¹ : Kˣ) : K) *
        ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
  have hfrac : IdeleGroup.toFractionalIdeal
      (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K c) =
      (RayIdeal.toFractionalIdeal I)⁻¹ * RayIdeal.toFractionalIdeal J := by
    rw [hc]
    simp only [map_mul, map_inv, hu, inv_one, one_mul,
      RayIdeal.toFractionalIdeal_idele]
  have hfrac' : RayIdeal.toFractionalIdeal I =
      IdeleGroup.toFractionalIdeal
        (NumberField.IdeleGroup.unitEmbedding (𝓞 K) K c⁻¹) *
        RayIdeal.toFractionalIdeal J := by
    rw [map_inv, map_inv, hfrac]
    simp [mul_inv_rev, mul_comm]
  have h := congrArg (fun z : (FractionalIdeal (𝓞 K)⁰ K)ˣ ↦
    (z : FractionalIdeal (𝓞 K)⁰ K)) hfrac'
  simpa only [RayIdeal.coe_toFractionalIdeal, Units.val_mul,
    IdeleGroup.coe_toFractionalIdeal_unitEmbedding] using h

/-- A principal relation between ray idèles yields ray equivalence; used by
`RayClassQuotient.toIdeleClassQuotient_injective`. -/
private theorem RayIdeal.isEquivalent_of_ray_idele_relation (hm : m ≠ ⊥)
    (I J : RayIdeal K m) {u : NumberField.IdeleGroup (𝓞 K) K}
    (hu : u ∈ IdeleGroup.raySubgroup (InfinitePlace.raySupport F.place) m)
    {c : Kˣ} (hceq : NumberField.IdeleGroup.unitEmbedding (𝓞 K) K c =
      u⁻¹ * ((RayIdeal.idele I)⁻¹ * RayIdeal.idele J)) :
    I.IsEquivalent F m J := by
  have hccong : NumberField.IdeleGroup.unitEmbedding (𝓞 K) K c ∈
      IdeleGroup.congruentSubgroup (InfinitePlace.raySupport F.place) m := by
    rw [hceq]
    exact (IdeleGroup.congruentSubgroup (InfinitePlace.raySupport F.place) m).mul_mem
      ((IdeleGroup.congruentSubgroup (InfinitePlace.raySupport F.place) m).inv_mem
        (IdeleGroup.raySubgroup_le_congruentSubgroup (InfinitePlace.raySupport F.place) m hu))
      ((IdeleGroup.congruentSubgroup (InfinitePlace.raySupport F.place) m).mul_mem
        ((IdeleGroup.congruentSubgroup (InfinitePlace.raySupport F.place) m).inv_mem
          (RayIdeal.idele_mem_congruent F I))
        (RayIdeal.idele_mem_congruent F J))
  have huideal : IdeleGroup.toFractionalIdeal u = 1 := by
    have hker : u ∈ IdeleGroup.congruentSubgroup
        (InfinitePlace.raySupport F.place) m ⊓ IdeleGroup.toFractionalIdeal.ker := by
      rw [IdeleGroup.congruentSubgroup_inf_ker_toFractionalIdeal]
      exact hu
    exact MonoidHom.mem_ker.mp hker.2
  have hIJ := RayIdeal.fractional_eq_of_principal_idele_relation I J huideal hceq
  have hrel : I.IsEquivalent F m J := by
    apply RayIdeal.isEquivalent_of_unitEmbedding_mem F hm (I := I) (J := J) (c := c⁻¹)
    · simpa only [map_inv] using (IdeleGroup.congruentSubgroup
        (InfinitePlace.raySupport F.place) m).inv_mem hccong
    · exact hIJ
  exact hrel

/-- **Injectivity of the comparison map**: ray ideals with the same idèle class modulo
`C_{𝔪∞₂}` are ray equivalent.  Milne, *Class Field Theory*, version 4.03 (2020), Chapter V,
Proposition 4.6(a). -/
theorem RayClassQuotient.toIdeleClassQuotient_injective (hm : m ≠ ⊥) :
    Function.Injective (RayClassQuotient.toIdeleClassQuotient F m) := by
  intro A B h
  obtain ⟨I, rfl⟩ := RayClassQuotient.mk_surjective F A
  obtain ⟨J, rfl⟩ := RayClassQuotient.mk_surjective F B
  rw [RayClassQuotient.toIdeleClassQuotient_mk,
    RayClassQuotient.toIdeleClassQuotient_mk] at h
  have hray := QuotientGroup.eq.mp h
  obtain ⟨u, hu, huclass⟩ :=
    (IdeleClassGroup.mem_raySubgroup_iff (InfinitePlace.raySupport F.place) m _).mp hray
  have hclass : (u : NumberField.IdeleClassGroup (𝓞 K) K) =
      ((RayIdeal.idele I)⁻¹ * RayIdeal.idele J :
        NumberField.IdeleGroup (𝓞 K) K) := by
    simpa only [RayIdeal.ideleClass, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv] using huclass
  have hp : u⁻¹ * ((RayIdeal.idele I)⁻¹ * RayIdeal.idele J) ∈
      NumberField.IdeleGroup.principalSubgroup (𝓞 K) K := QuotientGroup.eq.mp hclass
  obtain ⟨c, hc⟩ := hp
  have hceq : NumberField.IdeleGroup.unitEmbedding (𝓞 K) K c =
      u⁻¹ * ((RayIdeal.idele I)⁻¹ * RayIdeal.idele J) := hc
  exact (RayClassQuotient.mk_eq_mk F I J).mpr
    (RayIdeal.isEquivalent_of_ray_idele_relation F hm I J hu hceq)

/-- A fractional ideal supported away from the modulus has its uniformizer idèle class in
the range of the ray class comparison map; used for surjectivity. -/
private theorem ofFractionalIdeal_ideleClass_mem_range (hm : m ≠ ⊥)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hJ : J ∈ FractionalIdeal.primeTo K (FinitePlace.modulusSupport m)) :
    RayIdeleClassQuotient.mk F m (IdeleGroup.ofFractionalIdeal J) ∈
        (RayClassQuotient.toIdeleClassQuotient F m).range := by
  let f := RayClassQuotient.toIdeleClassQuotient F m
  let q := (RayIdeleClassQuotient.mk F m).comp IdeleGroup.ofFractionalIdeal
  obtain ⟨T, hT, hclosure⟩ := FractionalIdeal.exists_finset_mem_closure J
  have hgen : (primeFractionalIdeal K '' (T : Set (HeightOneSpectrum (𝓞 K)))) ⊆
      (f.range.comap q : Set _) := by
    rintro _ ⟨v, hv, rfl⟩
    have hvS : v ∉ FinitePlace.modulusSupport m := by
      intro hvS
      exact hT v hv ((FractionalIdeal.mem_primeTo_iff.mp hJ) v hvS)
    let I : RayIdeal K m := ⟨v.asIdeal, v.ne_bot,
      (FinitePlace.isCoprime_iff_modulusExponent_eq_zero hm v).mpr
        (by simpa using (FinitePlace.mem_modulusSupport).not.mp hvS)⟩
    exact ⟨RayClassQuotient.mk F m I, rfl⟩
  exact ((Subgroup.closure_le _).mpr hgen) hclosure

/-- **Surjectivity of the comparison map**: every class in `C_K / C_{𝔪∞₂}` is the class of the
uniformizer idèle of a ray ideal.  Milne, *Class Field Theory*, version 4.03 (2020), Chapter V,
Proposition 4.6(b), and the corrected Bonn Lectures, Chapter III, proof of Proposition 9.3. -/
theorem RayClassQuotient.toIdeleClassQuotient_surjective (hm : m ≠ ⊥) :
    Function.Surjective (RayClassQuotient.toIdeleClassQuotient F m) := by
  intro z
  obtain ⟨c, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (IdeleClassGroup.raySubgroup (InfinitePlace.raySupport F.place) m) z
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K) c
  obtain ⟨a, hy⟩ := IdeleGroup.exists_unitEmbedding_mul_mem_congruentSubgroup
    (InfinitePlace.raySupport F.place) m x
  let y := NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a * x
  let J := IdeleGroup.toFractionalIdeal y
  have hcount (v : HeightOneSpectrum (𝓞 K))
      (hv : FinitePlace.modulusExponent m v ≠ 0) :
      FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K) = 0 :=
    IdeleGroup.count_toFractionalIdeal_eq_zero_of_finite_ray m
      ((IdeleGroup.mem_congruentSubgroup_iff (InfinitePlace.raySupport F.place) m _).mp hy).2
      v hv
  have hJprime : J ∈ FractionalIdeal.primeTo K (FinitePlace.modulusSupport m) :=
    FractionalIdeal.mem_primeTo_iff.mpr (fun v hv ↦
      hcount v (FinitePlace.mem_modulusSupport.mp hv))
  have hJmem : IdeleGroup.ofFractionalIdeal J ∈
      IdeleGroup.congruentSubgroup (InfinitePlace.raySupport F.place) m :=
    IdeleGroup.ofFractionalIdeal_mem_congruentSubgroup
      (InfinitePlace.raySupport F.place) m hJprime
  have hsame := congruent_ideleClass_eq_of_toFractionalIdeal_eq F hy hJmem
    (by simp only [y, J, IdeleGroup.toFractionalIdeal_ofFractionalIdeal])
  have hrange := ofFractionalIdeal_ideleClass_mem_range F hm J hJprime
  have hxy : RayIdeleClassQuotient.mk F m x = RayIdeleClassQuotient.mk F m y := by
    simp only [y, map_mul, RayIdeleClassQuotient.mk_unitEmbedding, one_mul]
  rw [← hsame, ← hxy] at hrange
  exact (MonoidHom.mem_range).mp hrange

variable (m) in
/-- **The idèlic ray class group is the ideal-theoretic ray class group**:
`C_K / C_{𝔪∞₂} ≃ Cl_{𝔪∞₂}(𝒪_K)` for a nonzero modulus, inverse to the class of uniformizer
idèles.  Milne, *Class Field Theory*, version 4.03 (2020), Chapter V, Proposition 4.6, and the
corrected Bonn Lectures, Chapter III, Proposition 9.3, for the selected-place modulus `𝔪∞₂` of
[AFK25, Definition 2.1, `defn:rayclassgroup`]. -/
def RayClassQuotient.ideleClassEquiv (hm : m ≠ ⊥) :
    RayIdeleClassQuotient F m ≃* RayClassQuotient F m :=
  (MulEquiv.ofBijective (RayClassQuotient.toIdeleClassQuotient F m)
    ⟨RayClassQuotient.toIdeleClassQuotient_injective F hm,
      RayClassQuotient.toIdeleClassQuotient_surjective F hm⟩).symm

/-! ### Finite index

Finiteness of `RayClassQuotient F m` transfers to `C_K / C_{𝔪∞₂}`. -/

/-- The quotient `C_K / C_{𝔪∞₂}` is finite, by `RayClassQuotient.instFinite` (Milne, *Class Field
Theory*, version 4.03 (2020), Chapter V, Theorem 1.7). -/
theorem RayIdeleClassQuotient.instFinite (hm : m ≠ ⊥) :
    Finite (RayIdeleClassQuotient F m) := by
  exact Finite.of_equiv (RayClassQuotient F m)
    (RayClassQuotient.ideleClassEquiv F m hm).symm.toEquiv

/-- **The selected-place ray subgroup of the idèle class group has finite index.**  Milne, *Class
Field Theory*, version 4.03 (2020), Chapter V, Theorem 1.7 and Proposition 4.6. -/
theorem IdeleClassGroup.raySubgroup_finiteIndex (hm : m ≠ ⊥) :
    (IdeleClassGroup.raySubgroup (InfinitePlace.raySupport F.place) m).FiniteIndex := by
  let : Finite (RayIdeleClassQuotient F m) := RayIdeleClassQuotient.instFinite F hm
  exact Subgroup.finiteIndex_of_finite_quotient

end SIC

end
