/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Local.NormIndex
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# Topology of local norm subgroups

Local norm subgroups are closed, and finite-index local norm subgroups are open.

This follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter I, Lemma 1.3,
with the cyclic local norm index of Chapter III, Lemma 2.5.

## The argument

The norm maps integral units onto a compact subgroup. A local element whose norm is a unit
is itself a unit, so this compact subgroup is the intersection of the norm subgroup with
the open integral-unit subgroup. This proves closedness, and finite index then gives openness.
At infinite places the norm subgroup is the whole multiplicative group or the positive reals.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField SIC.FinitePlace

/-! ### Finite places

The integral-unit equivalence from `SICs.ClassField.Completion.Norm` identifies the norm image of
the upper unit group with the intersection of the norm subgroup and the lower unit group.
Compactness then shows that the norm subgroup is locally closed near one, hence closed; finite
index gives openness.
-/

namespace SIC.FinitePlace

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- A local norm is an integral unit exactly when its argument is an integral unit.
This is `localNorm_mem_integral_units_iff` in the local-unit notation. -/
theorem localNorm_mem_unitGroup_iff {x : (w.adicCompletion L)ˣ} :
    localNorm v w x ∈ unitGroup v ↔ x ∈ unitGroup w := by
  exact localNorm_mem_integral_units_iff v w

/-- The norms of integral units are exactly the integral units in the local norm subgroup.
Milne, *Class Field Theory*, Chapter I, proof of Lemma 1.3. -/
theorem map_localNorm_unitGroup_eq_inf :
    (unitGroup w).map (localNorm v w) = (localNorm v w).range ⊓ unitGroup v := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, rfl⟩, (localNorm_mem_unitGroup_iff v w).mpr hy⟩
  · rintro ⟨⟨y, rfl⟩, hy⟩
    exact ⟨y, (localNorm_mem_unitGroup_iff v w).mp hy, rfl⟩

/-- A local norm subgroup at a finite place is closed, by compactness of the integral-unit
norms. Milne, *Class Field Theory*, Chapter I, proof of Lemma 1.3. -/
theorem isClosed_range_localNorm :
    IsClosed ((localNorm v w).range : Set (v.adicCompletion K)ˣ) := by
  have hc : IsClosed (((localNorm v w).range ⊓ unitGroup v :
      Subgroup (v.adicCompletion K)ˣ) : Set (v.adicCompletion K)ˣ) := by
    rw [← map_localNorm_unitGroup_eq_inf v w, Subgroup.coe_map]
    exact ((isCompact_unitGroup w).image (continuous_localNorm v w)).isClosed
  apply (localNorm v w).range.isClosed_of_isLocallyClosedAt (localNorm v w).range.one_mem
  exact ⟨unitGroup v, (isOpen_unitGroup v).mem_nhds (unitGroup v).one_mem,
    _, hc, by ext x; simp only [Subgroup.coe_inf, Set.mem_inter_iff]; tauto⟩

/-- A finite-index local norm subgroup is open. Milne, *Class Field Theory*, Chapter I,
Lemma 1.3. -/
theorem isOpen_range_localNorm_of_finiteIndex [(localNorm v w).range.FiniteIndex] :
    IsOpen ((localNorm v w).range : Set (v.adicCompletion K)ˣ) := by
  exact (localNorm v w).range.isOpen_of_isClosed_of_finiteIndex (isClosed_range_localNorm v w)

/-- Cyclic local norm subgroups at finite places are open, by the local norm index.
Milne, *Class Field Theory*, Chapter I, Lemma 1.3 and Chapter III, Lemma 2.5. -/
theorem isOpen_range_localNorm [IsGalois K L]
    [IsCyclic (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)] :
    IsOpen ((localNorm v w).range : Set (v.adicCompletion K)ˣ) := by
  have : (localNorm v w).range.FiniteIndex := by
    apply Subgroup.finiteIndex_iff.mpr
    change Nat.card ((v.adicCompletion K)ˣ ⧸ (localNorm v w).range) ≠ 0
    rw [card_quotient_range_localNorm]
    exact Module.finrank_pos.ne'
  exact isOpen_range_localNorm_of_finiteIndex v w

end SIC.FinitePlace

/-! ### Infinite places

The classification in `SIC.InfinitePlace.mem_range_localNorm_iff_pos` identifies the ramified
norm subgroup with the positive reals; in the unramified case the norm is surjective.
-/

namespace SIC.InfinitePlace

open scoped NumberField.LiesOver SIC.InfinitePlace

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  (v : NumberField.InfinitePlace K) (w : NumberField.InfinitePlace L) [w.LiesOver v]

omit [NumberField K] [NumberField L] in
/-- The norm subgroup at an infinite place is open. Milne, *Class Field Theory*, Chapter I,
§1.6; it is the whole group or the positive reals. -/
theorem isOpen_range_localNorm :
    IsOpen ((localNorm v w).range : Set v.Completionˣ) := by
  rcases w.isUnramified_or_isRamified K with hw | hw
  · rw [(localNorm v w).range_eq_top_of_surjective
      (localNorm_surjective_of_unramified v w hw)]
    exact isOpen_univ
  · have hset : ((localNorm v w).range : Set v.Completionˣ) =
        {x : v.Completionˣ | 0 <
          NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
            (NumberField.InfinitePlace.IsRamified.liesOver_isReal_under w v hw)
            (x : v.Completion)} := by
      ext x
      exact mem_range_localNorm_iff_pos v w hw x
    rw [hset]
    exact isOpen_lt continuous_const
      ((NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
        (NumberField.InfinitePlace.IsRamified.liesOver_isReal_under w v hw)).continuous.comp
        Units.continuous_val)

end SIC.InfinitePlace
