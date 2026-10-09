/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Ideles.Basic
import SICs.RestrictedProductUnits
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# Topology of idèles and their local components

The component homeomorphism for idèles, the topological group of finite local idèle
coordinates, and continuity of idèle homomorphisms with continuous local parts.

## The argument

The general homeomorphism between restricted-product units and the restricted product of local
unit groups comes from `SICs.RestrictedProductUnits`. Applied to finite adèles and combined with
the product description of infinite adèles, it makes the algebraic idèle component equivalence
continuous in both directions. The integral-unit subgroups of the finite completions are open,
so the finite local coordinates form a topological group. An idèle homomorphism assembled from
continuous maps on the infinite and finite coordinates is therefore continuous.

These topological properties support the idèlic construction of global reciprocity.
-/

noncomputable section

open Filter Set Topology
open scoped RestrictedProduct

namespace SIC

/-! ### Finite adèles -/

namespace FiniteAdeleRing

open NumberField IsDedekindDomain

section FiniteAdeleTopology

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The units of the finite adèle ring are continuously equivalent to the restricted product of
the multiplicative groups of the finite completions. -/
def unitsContinuousEquiv :
    (IsDedekindDomain.FiniteAdeleRing R K)ˣ ≃ₜ*
      Πʳ v : HeightOneSpectrum R,
        [(v.adicCompletion K)ˣ,
          (Submonoid.ofClass (v.adicCompletionIntegers K)).units] := by
  letI : Fact (∀ v : HeightOneSpectrum R,
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  letI : Fact (∀ v : HeightOneSpectrum R,
      IsOpen (Submonoid.ofClass (v.adicCompletionIntegers K) :
        Set (v.adicCompletion K))) :=
    ⟨fun v ↦ (inferInstance : Fact (∀ w : HeightOneSpectrum R,
      IsOpen (w.adicCompletionIntegers K : Set (w.adicCompletion K)))).out v⟩
  change
    (Πʳ v : HeightOneSpectrum R,
      [v.adicCompletion K, v.adicCompletionIntegers K])ˣ ≃ₜ*
        Πʳ v : HeightOneSpectrum R,
          [(v.adicCompletion K)ˣ,
            (Submonoid.ofClass (v.adicCompletionIntegers K)).units]
  exact SIC.RestrictedProduct.unitsContinuousMulEquiv
    (fun v : HeightOneSpectrum R ↦ v.adicCompletion K)
    (fun v : HeightOneSpectrum R ↦ Submonoid.ofClass (v.adicCompletionIntegers K))

end FiniteAdeleTopology

end FiniteAdeleRing

/-! ### Idèles -/

namespace IdeleGroup

open NumberField IsDedekindDomain

/-- The finite local idèle coordinates form a topological group. The defining integral-unit
subgroups are open, so Mathlib's restricted-product group topology applies. -/
instance instIsTopologicalGroupFiniteLocalIdele
    (K : Type*) [Field K] [NumberField K] : IsTopologicalGroup (FiniteLocalIdele K) := by
  let : Fact (∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
        Set (v.adicCompletion K)ˣ)) :=
    ⟨fun v => Submonoid.isOpen_units (Valued.isOpen_valuationSubring (v.adicCompletion K))⟩
  infer_instance

/-- The algebraic component decomposition of number-field idèles, upgraded to a continuous
multiplicative equivalence. -/
def componentsContinuousEquiv
    (K : Type*) [Field K] [NumberField K] :
    NumberField.IdeleGroup (𝓞 K) K ≃ₜ*
      InfiniteLocalIdele K × FiniteLocalIdele K := by
  refine
    { __ := componentsEquiv K
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · exact
      ((ContinuousMulEquiv.piUnits (M := fun v : NumberField.InfinitePlace K ↦
          v.Completion)).continuous.prodMap
        (FiniteAdeleRing.unitsContinuousEquiv (𝓞 K) K).continuous).comp
        (Homeomorph.prodUnits (α := NumberField.InfiniteAdeleRing K)
          (β := IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)).continuous
  · exact
      (Homeomorph.prodUnits (α := NumberField.InfiniteAdeleRing K)
        (β := IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)).symm.continuous.comp
        ((ContinuousMulEquiv.piUnits (M := fun v : NumberField.InfinitePlace K ↦
          v.Completion)).symm.continuous.prodMap
          (FiniteAdeleRing.unitsContinuousEquiv (𝓞 K) K).symm.continuous)

end IdeleGroup

/-! ### Idèle homomorphisms given by their local parts -/

namespace IdeleGroup

open NumberField IsDedekindDomain

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M]

/-- An idèle homomorphism with continuous local parts is continuous. -/
theorem continuous_mapComponents {f : InfiniteLocalIdele K →* InfiniteLocalIdele L}
    {g : FiniteLocalIdele K →* FiniteLocalIdele L} (hf : Continuous f) (hg : Continuous g) :
    Continuous (mapComponents f g) := by
  exact (componentsContinuousEquiv L).symm.continuous.comp <|
    (hf.prodMap hg).comp (componentsContinuousEquiv K).continuous

end IdeleGroup

end SIC

end
