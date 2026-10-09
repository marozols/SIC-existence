/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Topology.Algebra.Group.Units
import SICs.Source

/-!
# Weak approximation at finite and infinite places

A number field is dense in the product of its completions at finitely many distinct finite
places, or simultaneously at all infinite places and finitely many finite places. Its
multiplicative group is likewise dense in the corresponding product of completion-unit groups.

This is the approximation theorem [83, Neukirch (1999), Chapter II, Theorem 3.4], used in
Milne, *Class Field Theory*, Chapter VII, proof of Proposition 4.6.

## The argument

The normalized absolute values `adicAbv` of distinct finite places are nontrivial and pairwise
inequivalent: an element of one prime ideal outside another has absolute value less than one at
the first place and equal to one at the second. They are also inequivalent to infinite absolute
values, since they send natural integers to values at most one, whereas infinite places send
$2$ to $2$. Mathlib's abstract weak approximation theorem
`AbsoluteValue.denseRange_algebraMap_pi` therefore applies to the finite or mixed family.

Each field `WithAbs v` maps isometrically, with dense range, into its completion. Composing the
dense diagonal with the product of these maps gives approximation in the completions. The unit
groups are open in these finite products of complete normed fields, so restricting the dense
scalar map to nonzero elements gives multiplicative weak approximation.
-/

noncomputable section

open IsDedekindDomain NumberField

namespace SIC

/-! ### Transporting density

Dense isometric scalar maps transport absolute-value weak approximation to completions. An open
unit group then inherits density from a dense scalar map: any scalar mapping to a unit is nonzero.
-/

/-- Transfer absolute-value weak approximation to normed extensions with dense scalar maps;
used by the finite and mixed completion theorems below. -/
private theorem denseRange_normedExtensions {K : Type*} [Field K] {ι : Type*} [Finite ι]
    (v : ι → AbsoluteValue K ℝ) (L : ι → Type*) [∀ i, NormedRing (L i)]
    [∀ i, Algebra K (L i)] (hnontrivial : ∀ i, (v i).IsNontrivial)
    (hpair : Pairwise fun i j ↦ ¬(v i).IsEquiv (v j))
    (hnorm : ∀ i x, ‖algebraMap K (L i) x‖ = v i x)
    (hdense : ∀ i, DenseRange (algebraMap K (L i))) :
    DenseRange (algebraMap K (∀ i, L i)) := by
  have hdense' (i : ι) : DenseRange (algebraMap (WithAbs (v i)) (L i)) := by
    refine DenseRange.of_comp (g := algebraMap K (WithAbs (v i))) ?_
    simpa [Function.comp_def, WithAbs.algebraMap_left_apply,
      WithAbs.algebraMap_right_apply] using hdense i
  have hcontinuous (i : ι) : Continuous (algebraMap (WithAbs (v i)) (L i)) := by
    apply Isometry.continuous
    apply (AddMonoidHomClass.isometry_iff_norm _).2
    intro x
    simpa only [WithAbs.algebraMap_left_apply, WithAbs.norm_eq_apply_ofAbs] using
      hnorm i x.ofAbs
  have h := (DenseRange.piMap hdense').comp
    (AbsoluteValue.denseRange_algebraMap_pi hnontrivial hpair)
    (Continuous.piMap hcontinuous)
  convert h using 1
  ext x i
  rfl

/-- A dense map from a group with zero induces a dense map on units when target units are
open; used to pass `denseRange_mixedCompletions` to multiplicative groups. -/
private theorem denseRange_unitsMap {G M : Type*} [GroupWithZero G] [MonoidWithZero M]
    [Nontrivial M] [TopologicalSpace M] (f : G →*₀ M) (hf : DenseRange f)
    (ho : IsOpenMap (Units.val : Mˣ → M)) : DenseRange (Units.map f.toMonoidHom) := by
  rw [DenseRange, dense_iff_inter_open]
  intro U hU hne
  obtain ⟨x, y, hy, hxy⟩ := hf.exists_mem_open (ho U hU) (hne.image Units.val)
  have hx : x ≠ 0 := by
    intro hx
    exact y.ne_zero (hxy.trans (by simp [hx]))
  exact ⟨y, hy, Units.mk0 x hx, Units.ext hxy.symm⟩

/-! ### Finite places

A nonzero algebraic integer in one prime has absolute value less than one there. Choosing it
outside another prime distinguishes the two absolute values, allowing weak approximation.
-/

namespace FinitePlace

variable {K : Type*} [Field K] [NumberField K]

/-- The absolute value at a finite place is nontrivial; used in
`denseRange_algebraMap_pi`. -/
lemma adicAbv_isNontrivial (v : HeightOneSpectrum (𝓞 K)) :
    (HeightOneSpectrum.adicAbv K v).IsNontrivial := by
  have hne : ¬v.asIdeal ≤ (⊥ : Ideal (𝓞 K)) := by
    intro h
    exact v.ne_bot (le_antisymm h bot_le)
  obtain ⟨x, hx, hx0⟩ := SetLike.not_le_iff_exists.mp hne
  refine ⟨algebraMap (𝓞 K) K x, ?_, ?_⟩
  · exact (FaithfulSMul.algebraMap_eq_zero_iff (𝓞 K) K).not.mpr (by simpa using hx0)
  · have hlt : HeightOneSpectrum.adicAbv K v (algebraMap (𝓞 K) K x) < 1 := by
      rw [← NumberField.FinitePlace.norm_embedding]
      exact (FinitePlace.norm_lt_one_iff_mem K v x).2 hx
    exact ne_of_lt hlt

/-- Distinct finite places give inequivalent absolute values; used in
`denseRange_algebraMap_pi`. -/
lemma adicAbv_not_isEquiv {v₁ v₂ : HeightOneSpectrum (𝓞 K)} (h : v₁ ≠ v₂) :
    ¬(HeightOneSpectrum.adicAbv K v₁).IsEquiv (HeightOneSpectrum.adicAbv K v₂) := by
  have hne : ¬v₁.asIdeal ≤ v₂.asIdeal := by
    intro hle
    exact h (HeightOneSpectrum.ext (v₁.isMaximal.eq_of_le v₂.isMaximal.ne_top hle))
  obtain ⟨x, hx₁, hx₂⟩ := SetLike.not_le_iff_exists.mp hne
  have hlt : HeightOneSpectrum.adicAbv K v₁ (algebraMap (𝓞 K) K x) < 1 := by
    rw [← NumberField.FinitePlace.norm_embedding]
    exact (FinitePlace.norm_lt_one_iff_mem K v₁ x).2 hx₁
  have heq : HeightOneSpectrum.adicAbv K v₂ (algebraMap (𝓞 K) K x) = 1 := by
    rw [← NumberField.FinitePlace.norm_embedding]
    exact (FinitePlace.norm_eq_one_iff_notMem K v₂ x).2 hx₂
  exact fun hequiv => (heq ▸ (hequiv.lt_one_iff.mp hlt)).false

/-- Weak approximation at finitely many distinct finite places: `K` is dense in
$\prod_i K_{v_i}$. [83, Neukirch (1999), Chapter II, Theorem 3.4]. -/
@[source "83, Chapter II, Theorem 3.4, p. 117 (finite places)"]
theorem denseRange_algebraMap_pi {ι : Type*} [Finite ι]
    (v : ι → HeightOneSpectrum (𝓞 K)) (hv : Function.Injective v) :
    DenseRange (algebraMap K (∀ i, (v i).adicCompletion K)) := by
  exact denseRange_normedExtensions (fun i => HeightOneSpectrum.adicAbv K (v i))
    (fun i => (v i).adicCompletion K) (fun i => adicAbv_isNontrivial (v i))
    (fun _ _ hij => adicAbv_not_isEquiv (hv.ne hij))
    (fun i x => NumberField.FinitePlace.norm_embedding (v i) x)
    (fun i => HeightOneSpectrum.denseRange_algebraMap (K := K) (v := v i))

end FinitePlace

/-! ### Simultaneous finite and infinite approximation

The finite and infinite absolute values are pairwise inequivalent, so the same approximation
argument applies to their combined family. -/

/-- Finite and infinite places give inequivalent absolute values; used in
`denseRange_mixedCompletions`. -/
private lemma finite_not_isEquiv_infinite {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (w : InfinitePlace K) :
    ¬(HeightOneSpectrum.adicAbv K v).IsEquiv w.1 := by
  intro h
  have hle := h.le_one_iff.mp
    (NumberField.HeightOneSpectrum.adicAbv_natCast_le_one K v 2)
  change w (2 : K) ≤ 1 at hle
  have hw : w (2 : K) = 2 := by simpa using w.map_natCast 2
  norm_num [hw] at hle

/-- Weak approximation simultaneously at every infinite place and a finite set $S$ of finite
places. [83, Neukirch (1999), Chapter II, Theorem 3.4]; Milne, *Class Field Theory*, Chapter VII,
proof of Proposition 4.6. -/
@[source "83, Chapter II, Theorem 3.4, p. 117 (infinite places and finitely many finite places)"]
theorem denseRange_mixedCompletions {K : Type*} [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DenseRange (fun x : K =>
      ((fun v : InfinitePlace K => algebraMap K v.Completion x),
        fun v : S => algebraMap K (v.1.adicCompletion K) x)) := by
  let v : InfinitePlace K ⊕ S → AbsoluteValue K ℝ :=
    Sum.elim (fun w => w.1) (fun w => HeightOneSpectrum.adicAbv K w.1)
  let L : InfinitePlace K ⊕ S → Type _ :=
    Sum.elim (fun w => w.Completion) (fun w => w.1.adicCompletion K)
  let : ∀ i, NormedField (L i) := fun i => by cases i <;> dsimp [L] <;> infer_instance
  let : ∀ i, Algebra K (L i) := fun i => by cases i <;> dsimp [L] <;> infer_instance
  have hnontrivial (i) : (v i).IsNontrivial := by
    cases i with
    | inl w => exact w.isNontrivial
    | inr w => exact FinitePlace.adicAbv_isNontrivial w.1
  have hpair : Pairwise fun i j ↦ ¬(v i).IsEquiv (v j) := by
    rintro (w | w) (u | u) h
    · exact InfinitePlace.eq_iff_isEquiv.not.mp (fun hwu => h (congrArg Sum.inl hwu))
    · exact fun he => finite_not_isEquiv_infinite u.1 w he.symm
    · exact finite_not_isEquiv_infinite w.1 u
    · exact FinitePlace.adicAbv_not_isEquiv
        (fun hwu => h (congrArg Sum.inr (Subtype.ext hwu)))
  have hnorm (i) (x : K) : ‖algebraMap K (L i) x‖ = v i x := by
    cases i with
    | inl w => exact InfinitePlace.Completion.norm_coe w (WithAbs.toAbs w.1 x)
    | inr w => exact NumberField.FinitePlace.norm_embedding w.1 x
  have hdense (i) : DenseRange (algebraMap K (L i)) := by
    cases i with
    | inl w =>
      exact (InfinitePlace.Completion.denseRange_coe w).comp
        (WithAbs.equiv w.1).symm.surjective.denseRange
        (InfinitePlace.Completion.continuous_coe w)
    | inr w => exact HeightOneSpectrum.denseRange_algebraMap K w.1
  let e := Homeomorph.sumPiEquivProdPi (InfinitePlace K) S L
  exact e.surjective.denseRange.comp
    (denseRange_normedExtensions v L hnontrivial hpair hnorm hdense) e.continuous

/-- Multiplicative weak approximation at every infinite place and a finite set $S$ of finite
places. This is `denseRange_mixedCompletions` restricted to the open unit groups; it is the
approximation used by Milne, *Class Field Theory*, Chapter VII, proof of Proposition 4.6. -/
theorem denseRange_mixedCompletionUnits {K : Type*} [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DenseRange (fun x : Kˣ =>
      ((fun v : InfinitePlace K => Units.map (algebraMap K v.Completion).toMonoidHom x),
        fun v : S => Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom x)) := by
  let : Inhabited (InfinitePlace K) := Classical.inhabited_of_nonempty inferInstance
  let f := (RingHom.pi (fun v : InfinitePlace K => algebraMap K v.Completion)).prod
    (RingHom.pi (fun v : S => algebraMap K (v.1.adicCompletion K)))
  let e := Homeomorph.prodUnits.trans
    (Homeomorph.prodCongr
      (ContinuousMulEquiv.piUnits (M := fun v : InfinitePlace K => v.Completion)).toHomeomorph
      (ContinuousMulEquiv.piUnits (M := fun v : S => v.1.adicCompletion K)).toHomeomorph)
  exact e.surjective.denseRange.comp
    (denseRange_unitsMap f.toMonoidWithZeroHom (denseRange_mixedCompletions S)
      Units.isOpenEmbedding_val.isOpenMap) e.continuous

/-- **Approximation by open conditions**: given nonempty open sets of local units at every
infinite place and at the finite places of `S`, some `a ∈ K^×` lies in all of them. This is the
mixed form of [83, Neukirch (1999), Chapter II, Theorem 3.4] (`denseRange_mixedCompletionUnits`).
-/
theorem exists_units_map_mem_of_isOpen {K : Type*} [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {UI : ∀ w : NumberField.InfinitePlace K, Set w.Completionˣ}
    {UF : ∀ v : S, Set (v.1.adicCompletion K)ˣ}
    (hUI : ∀ w, IsOpen (UI w)) (hUF : ∀ v, IsOpen (UF v))
    (hneI : ∀ w, (UI w).Nonempty) (hneF : ∀ v, (UF v).Nonempty) :
    ∃ a : Kˣ, (∀ w, Units.map (algebraMap K w.Completion : K →* w.Completion) a ∈ UI w) ∧
      ∀ v : S, Units.map (algebraMap K (v.1.adicCompletion K) : K →* v.1.adicCompletion K) a ∈
        UF v := by
  have hopen : IsOpen (Set.univ.pi UI ×ˢ Set.univ.pi UF) :=
    (isOpen_set_pi Set.finite_univ (fun w _ ↦ hUI w)).prod
      (isOpen_set_pi Set.finite_univ (fun v _ ↦ hUF v))
  have hne : (Set.univ.pi UI ×ˢ Set.univ.pi UF).Nonempty := by
    have hi : (Set.univ.pi UI).Nonempty := Set.univ_pi_nonempty_iff.mpr hneI
    have hf : (Set.univ.pi UF).Nonempty := Set.univ_pi_nonempty_iff.mpr hneF
    exact hi.prod hf
  obtain ⟨a, ha⟩ := (denseRange_mixedCompletionUnits S).exists_mem_open hopen hne
  exact ⟨a, fun w ↦ ha.1 w (Set.mem_univ _), fun v ↦ ha.2 v (Set.mem_univ _)⟩

end SIC
