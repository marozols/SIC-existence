/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Ideles.Galois
import SICs.ClassField.Ideles.RayModulus

/-!
# Ray and congruent idèle subgroups

Milne's modulus $\mathfrak m=\mathfrak m_0\mathfrak m_\infty$ has a finite integral part
$\mathfrak m_0$ and a set $P=\mathfrak m_\infty$ of infinite places where positivity is
imposed. The idèles in `congruentSubgroup P m` satisfy the higher-unit congruence at each
prime dividing $\mathfrak m_0$ and the prescribed signs at $P$. The subgroup
`raySubgroup P m` also has integral-unit components at all other finite places. They are
Milne's $I_{\mathfrak m}$ and $W_{\mathfrak m}$ (*Class Field Theory*, version 4.03 (2020),
Chapter V, §4). The image of $W_{\mathfrak m}$ in the idèle class group is
`IdeleClassGroup.raySubgroup P m`.

At $P=\mathrm{univ}$ these are Childress's $J^+_{K,\mathfrak m}$ and
$E^+_{K,\mathfrak m}$ (*Class Field Theory* (2009), Chapter IV, Proposition 3.4). The
selected-place construction uses $P=\operatorname{raySupport}(F.\mathrm{place})$, leaving
$F.\mathrm{place}$ unrestricted.

## The argument

Mixed weak approximation gives a principal multiple of any idèle in $I_{\mathfrak m}$:
its finite component satisfies the open higher-unit conditions at finitely many primes,
and its infinite components lie in the open factors selected by $P$. A congruent idèle
with trivial fractional ideal has integral-unit components everywhere, hence lies in
$W_{\mathfrak m}$. Field isomorphisms transport both $P$ and the finite modulus, so they
preserve congruence.
-/
noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField RestrictedProduct nonZeroDivisors

namespace SIC

universe u

/-! ### Idèles for a finite modulus and an infinite support

The set $P$ selects the real sign conditions. A ray idèle satisfies every finite ray
factor, while a congruent idèle requires these factors only at primes dividing $m$. -/
namespace IdeleGroup

variable {K : Type u} [Field K] [NumberField K]

/-- Milne's $W_{\mathfrak m}$: idèles in the positive local group at each place of $P$
and in the finite ray factor at every prime. At $P=\mathrm{univ}$ this is Childress's
$E^+_{K,\mathfrak m}$. Milne, *Class Field Theory*, Chapter V, §4; Childress,
*Class Field Theory*, Chapter IV, Proposition 3.4. -/
def raySubgroup (P : Set (InfinitePlace K)) (m : Ideal (𝓞 K)) :
    Subgroup (NumberField.IdeleGroup (𝓞 K) K) where
  carrier := {x | (∀ w, infiniteComponent K w x ∈ InfinitePlace.rayUnitGroup P w) ∧
    ∀ v, finiteComponent K v x ∈ FinitePlace.rayUnitGroup m v}
  one_mem' := ⟨fun w ↦ by simp, fun v ↦ by simp⟩
  mul_mem' hx hy := ⟨fun w ↦ by rw [map_mul]; exact mul_mem (hx.1 w) (hy.1 w),
    fun v ↦ by rw [map_mul]; exact mul_mem (hx.2 v) (hy.2 v)⟩
  inv_mem' hx := ⟨fun w ↦ by rw [map_inv]; exact inv_mem (hx.1 w),
    fun v ↦ by rw [map_inv]; exact inv_mem (hx.2 v)⟩

/-- Membership in $W_{\mathfrak m}$ is membership in every prescribed local factor. -/
theorem mem_raySubgroup_iff (P : Set (InfinitePlace K)) (m : Ideal (𝓞 K))
    (x : NumberField.IdeleGroup (𝓞 K) K) :
    x ∈ raySubgroup P m ↔
      (∀ w, infiniteComponent K w x ∈ InfinitePlace.rayUnitGroup P w) ∧
      ∀ v, finiteComponent K v x ∈ FinitePlace.rayUnitGroup m v :=
  Iff.rfl

/-- With every infinite place selected, ray-idèle membership is real positivity together with
all finite ray conditions. -/
theorem mem_raySubgroup_univ_iff (m : Ideal (𝓞 K))
    (x : NumberField.IdeleGroup (𝓞 K) K) :
    x ∈ raySubgroup Set.univ m ↔
      (∀ w (hw : w.IsReal),
        0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
          (infiniteComponent K w x : w.Completion)) ∧
      ∀ v, finiteComponent K v x ∈ FinitePlace.rayUnitGroup m v := by
  simp only [mem_raySubgroup_iff, InfinitePlace.rayUnitGroup_univ,
    InfinitePlace.mem_positiveUnitGroup_iff]

/-- Milne's $I_{\mathfrak m}$: idèles in the positive local group at each place of $P$
and in the finite ray factor at each prime dividing $m$. At $P=\mathrm{univ}$ this is
Childress's $J^+_{K,\mathfrak m}$. Milne, *Class Field Theory*, Chapter V, §4; Childress,
*Class Field Theory*, Chapter IV, Proposition 3.4. -/
def congruentSubgroup (P : Set (InfinitePlace K)) (m : Ideal (𝓞 K)) :
    Subgroup (NumberField.IdeleGroup (𝓞 K) K) where
  carrier := {x | (∀ w, infiniteComponent K w x ∈ InfinitePlace.rayUnitGroup P w) ∧
    ∀ v, FinitePlace.modulusExponent m v ≠ 0 →
      finiteComponent K v x ∈ FinitePlace.rayUnitGroup m v}
  one_mem' := ⟨fun w ↦ by simp, fun v _ ↦ by simp⟩
  mul_mem' hx hy := ⟨fun w ↦ by rw [map_mul]; exact mul_mem (hx.1 w) (hy.1 w),
    fun v hv ↦ by rw [map_mul]; exact mul_mem (hx.2 v hv) (hy.2 v hv)⟩
  inv_mem' hx := ⟨fun w ↦ by rw [map_inv]; exact inv_mem (hx.1 w),
    fun v hv ↦ by rw [map_inv]; exact inv_mem (hx.2 v hv)⟩

/-- Membership in $I_{\mathfrak m}$ is membership in the infinite factors selected by $P$
and the finite factors at primes dividing $m$. -/
theorem mem_congruentSubgroup_iff (P : Set (InfinitePlace K)) (m : Ideal (𝓞 K))
    (x : NumberField.IdeleGroup (𝓞 K) K) :
    x ∈ congruentSubgroup P m ↔
      (∀ w, infiniteComponent K w x ∈ InfinitePlace.rayUnitGroup P w) ∧
      ∀ v, FinitePlace.modulusExponent m v ≠ 0 →
        finiteComponent K v x ∈ FinitePlace.rayUnitGroup m v :=
  Iff.rfl

/-- With every infinite place selected, congruent-idèle membership is real positivity and the
finite congruences at the modulus support. -/
theorem mem_congruentSubgroup_univ_iff (m : Ideal (𝓞 K))
    (x : NumberField.IdeleGroup (𝓞 K) K) :
    x ∈ congruentSubgroup Set.univ m ↔
      (∀ w (hw : w.IsReal),
        0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
          (infiniteComponent K w x : w.Completion)) ∧
      ∀ v, FinitePlace.modulusExponent m v ≠ 0 →
        finiteComponent K v x ∈ FinitePlace.rayUnitGroup m v := by
  simp only [mem_congruentSubgroup_iff, InfinitePlace.rayUnitGroup_univ,
    InfinitePlace.mem_positiveUnitGroup_iff]

/-- Finite ray conditions are the congruences at the support together with a trivial
fractional ideal. -/
theorem finite_ray_iff_congruent_and_ideal (m : Ideal (𝓞 K))
    (x : NumberField.IdeleGroup (𝓞 K) K) :
    (∀ v, finiteComponent K v x ∈ FinitePlace.rayUnitGroup m v) ↔
      (∀ v, FinitePlace.modulusExponent m v ≠ 0 →
        finiteComponent K v x ∈ FinitePlace.rayUnitGroup m v) ∧
        toFractionalIdeal x = 1 := by
  rw [toFractionalIdeal_eq_one_iff]
  constructor
  · intro h
    exact ⟨fun v _ ↦ h v, fun v ↦
      (FinitePlace.mem_unitGroup_iff_valued v _).mp
        (FinitePlace.rayUnitGroup_le_unitGroup m v (h v))⟩
  · rintro ⟨h, hval⟩ v
    by_cases hv : FinitePlace.modulusExponent m v = 0
    · rw [FinitePlace.rayUnitGroup_eq_of_exponent_eq_zero hv]
      exact (FinitePlace.mem_unitGroup_iff_valued v _).mpr (hval v)
    · exact h v hv

/-- Congruent finite components with the same fractional ideal differ by finite ray factors. -/
theorem mul_inv_mem_finite_ray (m : Ideal (𝓞 K))
    {x y : NumberField.IdeleGroup (𝓞 K) K}
    (hx : ∀ v, FinitePlace.modulusExponent m v ≠ 0 →
      finiteComponent K v x ∈ FinitePlace.rayUnitGroup m v)
    (hy : ∀ v, FinitePlace.modulusExponent m v ≠ 0 →
      finiteComponent K v y ∈ FinitePlace.rayUnitGroup m v)
    (h : toFractionalIdeal x = toFractionalIdeal y) :
    ∀ v, finiteComponent K v (x * y⁻¹) ∈ FinitePlace.rayUnitGroup m v := by
  apply (finite_ray_iff_congruent_and_ideal m _).mpr
  constructor
  · intro v hv
    rw [map_mul, map_inv]
    exact mul_mem (hx v hv) (inv_mem (hy v hv))
  · simp [map_mul, map_inv, h]

/-- A finite ray condition forces the associated ideal to have order zero at that prime. -/
theorem count_toFractionalIdeal_eq_zero_of_finite_ray (m : Ideal (𝓞 K))
    {y : NumberField.IdeleGroup (𝓞 K) K}
    (hfin : ∀ v, FinitePlace.modulusExponent m v ≠ 0 →
      finiteComponent K v y ∈ FinitePlace.rayUnitGroup m v)
    (v : HeightOneSpectrum (𝓞 K)) (hv : FinitePlace.modulusExponent m v ≠ 0) :
    FractionalIdeal.count K v
      ((toFractionalIdeal y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  have hunit := FinitePlace.rayUnitGroup_le_unitGroup m v (hfin v hv)
  have hval := (FinitePlace.mem_unitGroup_iff_valued v _).mp hunit
  rw [count_toFractionalIdeal, hval, WithZero.log_one, neg_zero]

/-- The uniformizer idèle of an ideal prime to the finite modulus satisfies every finite
ray congruence. -/
theorem ofFractionalIdeal_finite_ray (m : Ideal (𝓞 K))
    {J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJ : J ∈ FractionalIdeal.primeTo K (FinitePlace.modulusSupport m)) :
    ∀ v, FinitePlace.modulusExponent m v ≠ 0 →
      finiteComponent K v (ofFractionalIdeal J) ∈ FinitePlace.rayUnitGroup m v := by
  intro v hv
  have hcount := (FractionalIdeal.mem_primeTo_iff.mp hJ) v
    (FinitePlace.mem_modulusSupport.mpr hv)
  rw [finiteComponent_ofFractionalIdeal, hcount, zpow_zero]
  exact one_mem _

/-- Ray subgroups grow when the modulus shrinks: $E^+_{K,\mathfrak m}\subseteq
E^+_{K,\mathfrak m'}$ for $\mathfrak m'\mid\mathfrak m\ne 0$. -/
theorem raySubgroup_mono (P : Set (InfinitePlace K)) {m m' : Ideal (𝓞 K)}
    (hm : m ≠ ⊥) (h : m ≤ m') :
    raySubgroup P m ≤ raySubgroup P m' := by
  intro x hx
  refine ⟨hx.1, fun v ↦ ?_⟩
  exact FinitePlace.rayUnitGroup_mono hm h v (hx.2 v)

/-- Congruent subgroups grow when the modulus shrinks: $J^+_{K,\mathfrak m}\subseteq
J^+_{K,\mathfrak m'}$ for $\mathfrak m'\mid\mathfrak m\ne 0$. -/
theorem congruentSubgroup_mono (P : Set (InfinitePlace K)) {m m' : Ideal (𝓞 K)}
    (hm : m ≠ ⊥) (h : m ≤ m') :
    congruentSubgroup P m ≤ congruentSubgroup P m' := by
  intro x hx
  refine ⟨hx.1, fun v hv ↦ ?_⟩
  have hexp := FinitePlace.modulusExponent_anti hm h v
  have hvm : FinitePlace.modulusExponent m v ≠ 0 := by
    exact Nat.ne_zero_of_lt (lt_of_lt_of_le (Nat.pos_of_ne_zero hv) hexp)
  exact FinitePlace.rayUnitGroup_mono hm h v (hx.2 v hvm)

/-- Milne's ray subgroup $W_{\mathfrak m}$ lies in his congruent subgroup
$I_{\mathfrak m}$. -/
theorem raySubgroup_le_congruentSubgroup (P : Set (InfinitePlace K)) (m : Ideal (𝓞 K)) :
    raySubgroup P m ≤ congruentSubgroup P m :=
  fun _ hx ↦ ⟨hx.1, fun v _ ↦ hx.2 v⟩

omit [NumberField K] in
/-- A translated infinite ray factor is open; used by
`exists_unitEmbedding_mul_mem_congruentSubgroup`. -/
private theorem isOpen_mul_ray (P : Set (InfinitePlace K))
    (w : InfinitePlace K) (y : w.Completionˣ) :
    IsOpen {u : w.Completionˣ | u * y ∈ InfinitePlace.rayUnitGroup P w} :=
  (InfinitePlace.isOpen_rayUnitGroup P w).preimage (continuous_id.mul_const y)

/-- **Every idèle is congruent up to a principal idèle**: $J_K = K^\times J^+_{K,\mathfrak m}$.
Childress, *Class Field Theory*, Chapter IV, proof of Proposition 3.4. -/
theorem exists_unitEmbedding_mul_mem_congruentSubgroup (P : Set (InfinitePlace K)) (m : Ideal (𝓞 K))
    (x : NumberField.IdeleGroup (𝓞 K) K) :
    ∃ a : Kˣ, NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a * x ∈ congruentSubgroup P m := by
  classical
  let S := FinitePlace.modulusSupport m
  let UI (w : InfinitePlace K) : Set w.Completionˣ :=
    {u | u * infiniteComponent K w x ∈ InfinitePlace.rayUnitGroup P w}
  let UF (v : S) : Set (v.1.adicCompletion K)ˣ :=
    {u | u * finiteComponent K v.1 x ∈ FinitePlace.rayUnitGroup m v.1}
  have hUI (w : InfinitePlace K) : IsOpen (UI w) :=
    isOpen_mul_ray P w (infiniteComponent K w x)
  have hUF (v : S) : IsOpen (UF v) :=
    (FinitePlace.isOpen_rayUnitGroup m v.1).preimage
      (continuous_id.mul_const (finiteComponent K v.1 x))
  have hneUI (w : InfinitePlace K) : (UI w).Nonempty :=
    ⟨(infiniteComponent K w x)⁻¹, by simp [UI]⟩
  have hneUF (v : S) : (UF v).Nonempty :=
    ⟨(finiteComponent K v.1 x)⁻¹, by simp [UF]⟩
  obtain ⟨a, ha⟩ := exists_units_map_mem_of_isOpen S hUI hUF hneUI hneUF
  refine ⟨a, (mem_congruentSubgroup_iff P m _).mpr ⟨?_, ?_⟩⟩
  · intro w
    have haw := ha.1 w
    rw [map_mul, infiniteComponent_unitEmbedding]
    exact haw
  · intro v hv
    have hav := ha.2 ⟨v, FinitePlace.mem_modulusSupport.mpr hv⟩
    rw [map_mul, finiteComponent_unitEmbedding]
    exact hav

/-- Every idèle class has a congruent representative: $C_K = J^+_{K,\mathfrak m}K^\times/K^\times$.
Childress, *Class Field Theory*, Chapter IV, Proposition 3.4. -/
theorem exists_mem_congruentSubgroup_mk_eq (P : Set (InfinitePlace K)) (m : Ideal (𝓞 K))
    (x : NumberField.IdeleClassGroup (𝓞 K) K) :
    ∃ y ∈ congruentSubgroup P m, (y : NumberField.IdeleClassGroup (𝓞 K) K) = x := by
  refine QuotientGroup.induction_on x ?_
  intro y
  obtain ⟨a, ha⟩ := exists_unitEmbedding_mul_mem_congruentSubgroup P m y
  exact ⟨NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a * y, ha,
    IdeleClassGroup.mk_unitEmbedding_mul a y⟩

/-! ### Fractional ideals of congruent idèles

A congruent idèle has unit components at the primes of the modulus, so its fractional ideal is
prime to them, and the uniformizer idèle of an ideal prime to the modulus is congruent, as is the
norm of the uniformizer idèle of an ideal prime to the primes above it. A congruent idèle with
trivial fractional ideal has unit components everywhere, so it is a ray idèle:
$I_{\mathfrak m}\cap\ker(\,\cdot\,) = W_{\mathfrak m}$. Hence two congruent idèles with
the same fractional ideal differ by a ray idèle. -/

/-- The uniformizer idèle of an ideal prime to the modulus is congruent. -/
theorem ofFractionalIdeal_mem_congruentSubgroup (P : Set (InfinitePlace K)) (m : Ideal (𝓞 K))
    {J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJ : J ∈ FractionalIdeal.primeTo K (FinitePlace.modulusSupport m)) :
    ofFractionalIdeal J ∈ congruentSubgroup P m := by
  refine (mem_congruentSubgroup_iff P m _).mpr ⟨?_, ?_⟩
  · intro w
    rw [infiniteComponent_ofFractionalIdeal]
    exact one_mem _
  · exact ofFractionalIdeal_finite_ray m hJ

/-- The fractional ideal of a congruent idèle is prime to the modulus. -/
theorem toFractionalIdeal_mem_primeTo (P : Set (InfinitePlace K)) (m : Ideal (𝓞 K))
    {y : NumberField.IdeleGroup (𝓞 K) K} (hy : y ∈ congruentSubgroup P m) :
    toFractionalIdeal y ∈ FractionalIdeal.primeTo K (FinitePlace.modulusSupport m) := by
  apply FractionalIdeal.mem_primeTo_iff.mpr
  intro v hv
  exact count_toFractionalIdeal_eq_zero_of_finite_ray m
    ((mem_congruentSubgroup_iff P m y).mp hy).2 v (FinitePlace.mem_modulusSupport.mp hv)

/-- **Ray idèles are the congruent idèles with trivial fractional ideal**:
$W_{\mathfrak m}=I_{\mathfrak m}\cap\ker(y\mapsto(y))$. Milne, *Class Field Theory*,
Chapter V, proof of Proposition 4.6(a); at $P=\mathrm{univ}$, Childress,
*Class Field Theory*, Chapter IV, proof of Proposition 5.6. -/
theorem congruentSubgroup_inf_ker_toFractionalIdeal (P : Set (InfinitePlace K)) (m : Ideal (𝓞 K)) :
    congruentSubgroup P m ⊓ (toFractionalIdeal (K := K)).ker = raySubgroup P m := by
  ext x
  rw [Subgroup.mem_inf, MonoidHom.mem_ker, mem_congruentSubgroup_iff,
    mem_raySubgroup_iff]
  constructor
  · rintro ⟨⟨hpos, hcong⟩, hideal⟩
    exact ⟨hpos, (finite_ray_iff_congruent_and_ideal m x).mpr ⟨hcong, hideal⟩⟩
  · rintro ⟨hpos, hfin⟩
    obtain ⟨hcong, hideal⟩ := (finite_ray_iff_congruent_and_ideal m x).mp hfin
    exact ⟨⟨hpos, hcong⟩, hideal⟩

/-- Two congruent idèles with the same fractional ideal differ by a ray idèle. -/
theorem mul_inv_mem_raySubgroup (P : Set (InfinitePlace K)) (m : Ideal (𝓞 K))
    {x y : NumberField.IdeleGroup (𝓞 K) K} (hx : x ∈ congruentSubgroup P m)
    (hy : y ∈ congruentSubgroup P m) (h : toFractionalIdeal x = toFractionalIdeal y) :
    x * y⁻¹ ∈ raySubgroup P m := by
  refine (mem_raySubgroup_iff P m _).mpr ⟨?_, mul_inv_mem_finite_ray m hx.2 hy.2 h⟩
  intro w
  rw [map_mul, map_inv]
  exact mul_mem (hx.1 w) (inv_mem (hy.1 w))

end IdeleGroup

/-! ### Ray subgroups of the idèle class group -/

namespace IdeleClassGroup

variable {K : Type u} [Field K] [NumberField K]

/-- The image of Milne's $W_{\mathfrak m}$ in the idèle class group for infinite part $P$.
Milne, *Class Field Theory*, version 4.03, Chapter V, Proposition 4.6. -/
def raySubgroup (P : Set (InfinitePlace K)) (m : Ideal (𝓞 K)) :
    Subgroup (NumberField.IdeleClassGroup (𝓞 K) K) :=
  (IdeleGroup.raySubgroup P m).map
    (QuotientGroup.mk' (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K))

/-- An idèle class belongs to the ray subgroup exactly when it has a ray-idèle
representative. -/
@[simp]
theorem mem_raySubgroup_iff (P : Set (InfinitePlace K)) (m : Ideal (𝓞 K))
    (c : NumberField.IdeleClassGroup (𝓞 K) K) :
    c ∈ raySubgroup P m ↔ ∃ x ∈ IdeleGroup.raySubgroup P m,
      (x : NumberField.IdeleClassGroup (𝓞 K) K) = c := by
  rfl

end IdeleClassGroup

variable {K K' : Type*} [Field K] [Field K'] [NumberField K] [NumberField K']

/-! ### Congruent idèles

The chosen infinite places and the finite modulus move together under a field isomorphism. -/

namespace IdeleGroup

/-- An isomorphism transports congruent idèles and the infinite support:
$\sigma(I_{\mathfrak m_0 P})\subseteq I_{\sigma(\mathfrak m_0)\,\sigma(P)}$.
Childress, *Class Field Theory*, Chapter VI, proof of Proposition 1.3, at
$P=\mathrm{univ}$. -/
theorem congr_mem_congruentSubgroup (σ : K ≃+* K') (P : Set (InfinitePlace K))
    {m : Ideal (𝓞 K)} {y : NumberField.IdeleGroup (𝓞 K) K}
    (hy : y ∈ congruentSubgroup P m) :
    congr σ y ∈ congruentSubgroup (InfinitePlace.mapEquiv σ '' P)
      (m.map (RingOfIntegers.mapRingEquiv σ)) := by
  obtain ⟨hpos, hfin⟩ := (mem_congruentSubgroup_iff P m y).mp hy
  apply (mem_congruentSubgroup_iff _ _ _).mpr
  constructor
  · intro w'
    let w := (InfinitePlace.mapEquiv σ).symm w'
    have hmap : InfinitePlace.mapEquiv σ w = w' := Equiv.apply_symm_apply _ _
    rw [InfinitePlace.mem_rayUnitGroup_iff]
    by_cases hwP' : w' ∈ InfinitePlace.mapEquiv σ '' P
    · right
      obtain ⟨v, hv, hvw⟩ := hwP'
      have hveq : v = w := (InfinitePlace.mapEquiv σ).injective (hvw.trans hmap.symm)
      have hwP : w ∈ P := hveq ▸ hv
      have hsource := (InfinitePlace.mem_rayUnitGroup_iff P w _).mp (hpos w)
      have hpositive := hsource.resolve_left (by simp [hwP])
      intro hw'
      have hw : w.IsReal := by
        change (w'.comap σ.toRingHom).IsReal
        exact (NumberField.InfinitePlace.isReal_comap_iff σ).mpr hw'
      rw [infiniteComponent_congr σ w w' hmap y]
      change 0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw'
        (InfinitePlace.completionEquiv σ w w' hmap
          (infiniteComponent K w y : w.Completion))
      rw [InfinitePlace.extensionEmbeddingOfIsReal_completionEquiv σ w w' hmap hw hw']
      exact hpositive hw
    · exact Or.inl hwP'
  · intro v' hv'
    obtain ⟨v, rfl⟩ := (FinitePlace.mapEquiv σ).surjective v'
    have hv : FinitePlace.modulusExponent m v ≠ 0 := by
      rw [← FinitePlace.modulusExponent_map σ m v]
      exact hv'
    rw [finiteComponent_congr σ v (FinitePlace.mapEquiv σ v) rfl y]
    exact FinitePlace.completionEquiv_mem_rayUnitGroup σ (hfin v hv)

end IdeleGroup


end SIC

end
