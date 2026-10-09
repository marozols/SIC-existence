/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Ideles.SIdeles
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.RingTheory.DedekindDomain.SInteger

/-!
# S-units as principal idèles

The S-unit group, its Galois representation, its bridge to Mathlib's `Set.unit`, its valuation
sequence, and power saturation $U(T)\cap L^{\times n}=U(T)^n$.

This follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, §3, before
Proposition 3.1. Its finite generation is the S-unit theorem cited there (Milne, *Algebraic
Number Theory*, Theorem 5.11 in version 3.08): valuation at the finitely many places above S
has ordinary units as its kernel. Dirichlet's unit theorem makes the kernel finitely generated,
and the valuation image is a subgroup of a finite product of copies of the integers.
The valuations are torsion-free, so an nth root in the field of an S-unit is again an S-unit
for $n\ne0$. This gives power saturation $U(T)\cap L^{\times n}=U(T)^n$.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField

namespace SIC.IdeleGroup

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-! ### The S-unit subgroup

A field element is an S-unit when its principal idèle is integral at every finite place outside
those above S. The equivalent valuation condition is Milne's definition. -/

/-- The group $U(T)$ of elements of $L^\times$ whose valuations are trivial away from the
places $T$ of $L$ above $S$. Milne, *Class Field Theory*, Chapter VII, §3, before Proposition
3.1. -/
def sUnits (S : Finset (HeightOneSpectrum (𝓞 K))) : Subgroup Lˣ :=
  (sSubgroup (L := L) S).comap (NumberField.IdeleGroup.unitEmbedding (𝓞 L) L)

omit [NumberField K] in
/-- An element is an S-unit exactly when its principal idèle belongs to the S-idèle subgroup. -/
theorem mem_sUnits (S : Finset (HeightOneSpectrum (𝓞 K))) (x : Lˣ) :
    x ∈ sUnits (L := L) S ↔
      NumberField.IdeleGroup.unitEmbedding (𝓞 L) L x ∈ sSubgroup (L := L) S :=
  Iff.rfl

omit [NumberField K] in
/-- An element is an S-unit exactly when $\operatorname{ord}_w(x)=0$ at each finite place $w$
not above S; in Mathlib's multiplicative convention this is $v_w(x)=1$. -/
theorem mem_sUnits_iff_valuation (S : Finset (HeightOneSpectrum (𝓞 K))) (x : Lˣ) :
    x ∈ sUnits (L := L) S ↔
      ∀ w : HeightOneSpectrum (𝓞 L), FinitePlace.below (K := K) w ∉ S →
        w.valuation L (x : L) = 1 := by
  rw [mem_sUnits, mem_sSubgroup]
  simp only [finiteComponent_unitEmbedding]
  exact forall_congr' fun w => imp_congr_right fun _ =>
    FinitePlace.units_map_mem_unitGroup_iff w x

omit [NumberField K] in
/-- A nonzero power is an S-unit exactly when its base is an S-unit. This gives
$U(T)\cap L^{\times n}=U(T)^n$ in Milne, *Class Field Theory*, Chapter VII, §6. -/
@[simp]
theorem pow_mem_sUnits_iff (S : Finset (HeightOneSpectrum (𝓞 K))) (x : Lˣ)
    {n : ℕ} (hn : n ≠ 0) : x ^ n ∈ sUnits (L := L) S ↔ x ∈ sUnits (L := L) S := by
  simp only [mem_sUnits_iff_valuation, Units.val_pow_eq_pow_val, map_pow,
    pow_eq_one_iff_left hn]

omit [NumberField K] in
/-- The valuation criterion introduces membership in the S-unit group. -/
theorem mem_sUnits_of_valuation (S : Finset (HeightOneSpectrum (𝓞 K))) (x : Lˣ)
    (h : ∀ w : HeightOneSpectrum (𝓞 L), FinitePlace.below (K := K) w ∉ S →
      w.valuation L (x : L) = 1) : x ∈ sUnits (L := L) S :=
  (mem_sUnits_iff_valuation S x).2 h

omit [NumberField K] in
/-- Every S-unit has trivial valuation outside the places above S. -/
theorem sUnits_valuation_eq_one (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : sUnits (L := L) S) (w : HeightOneSpectrum (𝓞 L))
    (hw : FinitePlace.below (K := K) w ∉ S) : w.valuation L (x.1 : L) = 1 :=
  (mem_sUnits_iff_valuation S x.1).1 x.2 w hw

omit [NumberField K] in
/-- Enlarging S enlarges the S-unit group. -/
theorem sUnits_mono {S T : Finset (HeightOneSpectrum (𝓞 K))} (h : S ⊆ T) :
    sUnits (L := L) S ≤ sUnits (L := L) T :=
  Subgroup.comap_mono (sSubgroup_mono (L := L) h)

omit [NumberField K] in
/-- Every nonzero field element is an S-unit for some finite S. -/
theorem exists_mem_sUnits (x : Lˣ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), x ∈ sUnits (L := L) S := by
  obtain ⟨S, hS⟩ := exists_mem_sSubgroup (K := K)
    (NumberField.IdeleGroup.unitEmbedding (𝓞 L) L x)
  exact ⟨S, (mem_sUnits S x).2 hS⟩

/-- The S-units of `L` relative to its own places above `S` are its S-units relative to `S`:
$U(T) = U(S)$ for the set `T` of places of `L` above `S`. -/
theorem sUnits_placesAbove (S : Finset (HeightOneSpectrum (𝓞 K))) :
    sUnits (K := L) (L := L) (FinitePlace.placesAbove (L := L) S) = sUnits (L := L) S := by
  ext x
  simp only [mem_sUnits_iff_valuation, FinitePlace.mem_placesAbove, FinitePlace.below_self]

omit [NumberField K] in
/-- Galois automorphisms over K preserve S-units. -/
theorem smul_mem_sUnits (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L) (x : Lˣ) (hx : x ∈ sUnits (L := L) S) :
    σ • x ∈ sUnits (L := L) S := by
  apply (mem_sUnits S _).2
  rw [← smul_unitEmbedding]
  exact smul_mem_sSubgroup S σ _ ((mem_sUnits S x).1 hx)

/-- The S-unit group as a subrepresentation of the Galois action on $L^\times$. -/
def sUnitsSubrep (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  Representation.subgroupSubrep (sUnits (L := L) S) (smul_mem_sUnits S)

omit [NumberField K] in
/-- The action on the S-unit representation is the field's Galois action. -/
@[simp]
theorem sUnitsSubrep_smul (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L) (x : (sUnitsSubrep (L := L) S).toSubmodule) :
    (((sUnitsSubrep (L := L) S).toRepresentation σ x).1.toMul) = σ • x.1.toMul :=
  rfl

/-! ### Power classes

The valuations outside S are torsion-free, so an nth root in the field of an S-unit is
again an S-unit. Thus the intrinsic S-unit power classes inject into the field's power classes. -/

omit [NumberField K] in
/-- The intersection $U(T)\cap L^{\times n}$ equals $U(T)^n$ for $n\ne0$.
Milne, *Class Field Theory*, Chapter VII, §6, construction preceding Lemma 6.2. -/
theorem sUnits_power_comap (S : Finset (HeightOneSpectrum (𝓞 K))) {n : ℕ} (hn : n ≠ 0) :
    ((powMonoidHom n : Lˣ →* Lˣ).range).comap (sUnits (L := L) S).subtype =
      (powMonoidHom n : sUnits (L := L) S →* sUnits (L := L) S).range := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    have hy' : y ^ n = x.val := hy
    have hyS : y ∈ sUnits (L := L) S :=
      (pow_mem_sUnits_iff S y hn).1 (hy'.symm ▸ x.property)
    exact ⟨⟨y, hyS⟩, Subtype.ext hy⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y.val, rfl⟩

/-! ### Ordinary units

At the empty exceptional set, the valuation criterion is precisely the condition for a unit of
the ring of integers. -/

omit [NumberField K] in
/-- The idèlic S-unit group equals Mathlib's valuation-based S-unit group. -/
theorem sUnits_eq_setUnit (S : Finset (HeightOneSpectrum (𝓞 K))) :
    sUnits (L := L) S =
      ({w : HeightOneSpectrum (𝓞 L) | FinitePlace.below (K := K) w ∈ S} :
        Set (HeightOneSpectrum (𝓞 L))).unit L := by
  apply Subgroup.ext
  intro x
  exact mem_sUnits_iff_valuation S x

omit [NumberField K] in
/-- With no exceptional finite places, S-units are Mathlib's ordinary valuation units. -/
private theorem sUnits_empty_eq_setUnit :
    sUnits (L := L) (∅ : Finset (HeightOneSpectrum (𝓞 K))) =
      (∅ : Set (HeightOneSpectrum (𝓞 L))).unit L := by
  simpa using (sUnits_eq_setUnit (L := L)
    (∅ : Finset (HeightOneSpectrum (𝓞 K))))

omit [NumberField K] in
/-- At $S=\varnothing$, $U(T)$ is multiplicatively equivalent to $(\mathcal O_L)^\times$.
The equivalence preserves the underlying element of $L$. -/
def sUnitsEmptyEquiv :
    sUnits (L := L) (∅ : Finset (HeightOneSpectrum (𝓞 K))) ≃* (𝓞 L)ˣ := by
  let e₁ : sUnits (L := L) (∅ : Finset (HeightOneSpectrum (𝓞 K))) ≃*
      (∅ : Set (HeightOneSpectrum (𝓞 L))).unit L :=
    MulEquiv.subgroupCongr sUnits_empty_eq_setUnit
  let e₂ : (∅ : Set (HeightOneSpectrum (𝓞 L))).unit L ≃*
      ((∅ : Set (HeightOneSpectrum (𝓞 L))).integer L)ˣ :=
    Set.unitEquivUnitsInteger _ L
  let e₃ : ((∅ : Set (HeightOneSpectrum (𝓞 L))).integer L)ˣ ≃* (𝓞 L)ˣ :=
    Units.mapEquiv ((Subalgebra.equivOfEq _ _
      (IsDedekindDomain.integer_empty (𝓞 L) L)).trans
        (Algebra.botEquivOfInjective
          (IsFractionRing.injective (𝓞 L) L))).toMulEquiv
  exact e₁.trans (e₂.trans e₃)

omit [NumberField K] in
/-- The ordinary-unit equivalence is the identity on underlying field elements. -/
@[simp]
theorem sUnitsEmptyEquiv_coe
    (x : sUnits (L := L) (∅ : Finset (HeightOneSpectrum (𝓞 K)))) :
    ((sUnitsEmptyEquiv (K := K) (L := L) x : (𝓞 L)ˣ) : L) = (x.1 : L) := by
  let e₁ : sUnits (L := L) (∅ : Finset (HeightOneSpectrum (𝓞 K))) ≃*
      (∅ : Set (HeightOneSpectrum (𝓞 L))).unit L :=
    MulEquiv.subgroupCongr sUnits_empty_eq_setUnit
  let e₂ := Set.unitEquivUnitsInteger (∅ : Set (HeightOneSpectrum (𝓞 L))) L
  let e₃ := Subalgebra.equivOfEq _ _ (IsDedekindDomain.integer_empty (𝓞 L) L)
  let z : (⊥ : Subalgebra (𝓞 L) L) := e₃ ((e₂ (e₁ x) : _) : _)
  change (algebraMap (𝓞 L) L)
    (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 L) L) z) = (x.1 : L)
  let e := Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 L) L)
  exact (congrArg Subtype.val (e.symm_apply_apply z)).trans rfl

/-! ### Finite generation

There are finitely many places of L above S. Valuations there define a homomorphism from
S-units to a finite product of copies of the integers. Its kernel is the ordinary units, so
Dirichlet's theorem and the exact-sequence finite generation lemma apply. -/

/-- The valuation homomorphism $U(T) \to \prod_{w\in T}\mathbb Z$, written multiplicatively
as a product of copies of $\mathbb Z^{\mathrm{mult}}$. Its additive coordinate is
$-\operatorname{ord}_w$, so a uniformizer maps to $-1$, following `FinitePlace.unitsValuation`.
This is the negative of the exponent convention in Milne, *Algebraic Number Theory*,
version 3.08 (2020), Theorem 5.11; its kernel and image are unchanged. -/
def sUnitsValuation (S : Finset (HeightOneSpectrum (𝓞 K))) :
    sUnits (L := L) S →* (∀ _w : FinitePlace.placesAbove (L := L) S, Multiplicative ℤ) :=
  MonoidHom.pi fun w =>
    (FinitePlace.unitsValuation w.1).comp
      ((finiteComponent L w.1).comp
        ((NumberField.IdeleGroup.unitEmbedding (𝓞 L) L).comp
          (sUnits (L := L) S).subtype))

/-- The $w$-coordinate of the S-unit valuation is the valuation of its principal idèle. -/
@[simp]
theorem sUnitsValuation_apply (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : sUnits (L := L) S) (w : FinitePlace.placesAbove (L := L) S) :
    sUnitsValuation (L := L) S x w =
      FinitePlace.unitsValuation w.1
        (finiteComponent L w.1 (NumberField.IdeleGroup.unitEmbedding (𝓞 L) L x.1)) :=
  rfl

/-- A principal idèle has unit valuation at $w$ exactly when its field element has trivial
$w$-valuation; used by `sUnitsValuation_eq_one_iff`. -/
private theorem unitsValuation_principal_eq_one_iff (w : HeightOneSpectrum (𝓞 L)) (x : Lˣ) :
    FinitePlace.unitsValuation w
        (finiteComponent L w (NumberField.IdeleGroup.unitEmbedding (𝓞 L) L x)) = 1 ↔
      w.valuation L (x : L) = 1 := by
  rw [FinitePlace.unitsValuation_eq_one_iff, finiteComponent_unitEmbedding]
  exact FinitePlace.units_map_mem_unitGroup_iff w x

/-- The kernel of the valuation map consists exactly of ordinary units. -/
theorem sUnitsValuation_eq_one_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : sUnits (L := L) S) :
    sUnitsValuation (L := L) S x = 1 ↔
      x.1 ∈ sUnits (L := L) (∅ : Finset (HeightOneSpectrum (𝓞 K))) := by
  rw [mem_sUnits_iff_valuation]
  constructor
  · intro hx w _
    by_cases hw : FinitePlace.below (K := K) w ∈ S
    · have hw' : w ∈ FinitePlace.placesAbove (L := L) S := (FinitePlace.mem_placesAbove S w).2 hw
      have hval := congrArg (fun f => f ⟨w, hw'⟩) hx
      have hval' : sUnitsValuation (L := L) S x ⟨w, hw'⟩ = 1 := by
        simpa using hval
      exact (unitsValuation_principal_eq_one_iff w x.1).1
        (by simpa only [sUnitsValuation_apply] using hval')
    · exact (mem_sUnits_iff_valuation S x.1).1 x.2 w hw
  · intro hx
    funext w
    have hw := hx w.1 (by simp)
    exact (unitsValuation_principal_eq_one_iff w.1 x.1).2 hw

/-- The integer-linear valuation map on S-units. Its $w$-coordinate is
$-\operatorname{ord}_w(x)$, as for `sUnitsValuation`. -/
def sUnitsValuationLinear (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Additive (sUnits (L := L) S) →ₗ[ℤ] (∀ _w : FinitePlace.placesAbove (L := L) S, ℤ) := by
  let e : Additive (∀ _w : FinitePlace.placesAbove (L := L) S, Multiplicative ℤ) ≃ₗ[ℤ]
      (∀ _w : FinitePlace.placesAbove (L := L) S, ℤ) :=
    ((AddEquiv.piAdditive fun _ : FinitePlace.placesAbove (L := L) S => Multiplicative ℤ).trans
      (AddEquiv.piCongrRight fun _ => AddEquiv.additiveMultiplicative ℤ)).toIntLinearEquiv
  exact e.toLinearMap.comp ((sUnitsValuation (L := L) S).toAdditive.toIntLinearMap)

/-- Each coordinate of the integer-linear map is the additive form of the S-unit valuation,
with sign $-\operatorname{ord}_w$. -/
@[simp]
theorem sUnitsValuationLinear_apply (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : Additive (sUnits (L := L) S)) (w : FinitePlace.placesAbove (L := L) S) :
    sUnitsValuationLinear (L := L) S x w =
      (sUnitsValuation (L := L) S x.toMul w).toAdd :=
  rfl

/-- An S-unit has zero finite valuation vector exactly when it is an ordinary unit. -/
theorem sUnitsValuationLinear_eq_zero_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : Additive (sUnits (L := L) S)) :
    sUnitsValuationLinear (L := L) S x = 0 ↔
      x.toMul.1 ∈ sUnits (L := L) (∅ : Finset (HeightOneSpectrum (𝓞 K))) := by
  rw [← sUnitsValuation_eq_one_iff S x.toMul]
  constructor
  · intro hx
    funext w
    have hw := congrArg (fun f => f w) hx
    rw [sUnitsValuationLinear_apply] at hw
    exact hw
  · intro hx
    funext w
    have hw := congrArg (fun f => f w) hx
    rw [sUnitsValuationLinear_apply]
    exact hw

/-- The integer-linear inclusion of ordinary units into S-units. -/
def emptySUnitsLinear (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Additive (sUnits (L := L) (∅ : Finset (HeightOneSpectrum (𝓞 K)))) →ₗ[ℤ]
      Additive (sUnits (L := L) S) :=
  ((Subgroup.inclusion (sUnits_mono (L := L) (Finset.empty_subset S))).toAdditive).toIntLinearMap

omit [NumberField K] in
/-- Inclusion into S-units preserves the underlying field unit. -/
@[simp]
theorem emptySUnitsLinear_apply (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : Additive (sUnits (L := L) (∅ : Finset (HeightOneSpectrum (𝓞 K))))) :
    ((emptySUnitsLinear (L := L) S x).toMul.1 : Lˣ) = x.toMul.1 :=
  rfl

omit [NumberField K] in
/-- Inclusion of ordinary units into S-units is injective. -/
theorem emptySUnitsLinear_injective (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective (emptySUnitsLinear (L := L) S) := by
  intro x y h
  have h' := congrArg (fun z : Additive (sUnits (L := L) S) => z.toMul.1) h
  simpa using h'

/-- The integer-linear sequence from ordinary units to S-units to their finite valuation
vectors is exact: ordinary units are precisely the kernel of valuation. -/
theorem exact_emptySUnitsLinear_sUnitsValuationLinear
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Exact (emptySUnitsLinear (L := L) S)
      (sUnitsValuationLinear (L := L) S) := by
  intro x
  rw [sUnitsValuationLinear_eq_zero_iff]
  constructor
  · intro hx
    refine ⟨Additive.ofMul (⟨x.toMul.1, hx⟩ :
      sUnits (L := L) (∅ : Finset (HeightOneSpectrum (𝓞 K)))), ?_⟩
    apply Subtype.ext
    rfl
  · rintro ⟨y, rfl⟩
    exact y.toMul.2

/-- The S-unit group is finitely generated as an abelian group. This is the finite generation
part of the S-unit theorem cited by Milne, *Class Field Theory*, Chapter VII, §3 (Milne,
*Algebraic Number Theory*, version 3.08, Theorem 5.11). -/
instance finite_sUnits (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Module.Finite ℤ (Additive (sUnits (L := L) S)) := by
  classical
  let e : Additive (sUnits (L := L) (∅ : Finset (HeightOneSpectrum (𝓞 K)))) ≃ₗ[ℤ]
      Additive (𝓞 L)ˣ := (sUnitsEmptyEquiv (K := K) (L := L)).toAdditive.toIntLinearEquiv
  have : Module.Finite ℤ
      (Additive (sUnits (L := L) (∅ : Finset (HeightOneSpectrum (𝓞 K))))) :=
    Module.Finite.equiv e.symm
  let V := sUnitsValuationLinear (L := L) S
  have : Module.Finite ℤ (∀ _w : FinitePlace.placesAbove (L := L) S, ℤ) := inferInstance
  have : IsNoetherian ℤ (∀ _w : FinitePlace.placesAbove (L := L) S, ℤ) := inferInstance
  have : Module.Finite ℤ V.range :=
    Module.Finite.of_injective V.range.subtype Subtype.val_injective
  have hexact : Function.Exact (emptySUnitsLinear (L := L) S) V.rangeRestrict :=
    (V.range.injective_subtype.comp_exact_iff_exact).mp
      (exact_emptySUnitsLinear_sUnitsValuationLinear (L := L) S)
  exact Module.Finite.of_exact hexact (LinearMap.surjective_rangeRestrict V)

/-- The finitely generated subgroup formulation of `finite_sUnits`, suitable for the
radical-extension construction `kummerExtension_finiteDimensional`. -/
theorem sUnits_fg (S : Finset (HeightOneSpectrum (𝓞 K))) : (sUnits (L := L) S).FG :=
  (Group.fg_iff_subgroup_fg _).1
    (GroupFG.iff_add_fg.2 (Module.Finite.iff_addGroup_fg.1 inferInstance))

end SIC.IdeleGroup
