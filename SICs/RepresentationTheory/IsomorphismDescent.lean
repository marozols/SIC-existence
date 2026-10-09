/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.MatrixNotation
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Descent of intertwiners across field extensions

Finite dimensional representations over an infinite field that become isomorphic after scalar
extension are already isomorphic over the ground field.

This module follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII, Lemma 3.2.
The intertwiner equations are homogeneous linear equations over the ground field. Flatness of a
field extension identifies their extended solution space with the span of ground field solutions.
The determinant of a linear combination of a basis of solutions is a multivariate polynomial.
Since the given isomorphism gives a nonzero value after extension, this polynomial is nonzero;
over an infinite field it has a nonzero ground field value.
-/

noncomputable section

namespace SIC.Representation

open Matrix TensorProduct
open scoped MatrixGroups

/-! ### Scalar extension of homogeneous solution spaces

Flatness identifies the extended kernel of the linear equations with the span of their original
solutions. This is Milne's basis-extension step. -/

/-- A solution after scalar extension lies in the span of scalar extensions of solutions to the
original homogeneous linear equations. Used by `matrixIntertwinerDescends`. -/
private theorem mem_span_ker_of_baseChange
    {k Ω V W V' W' : Type*} [Field k] [Field Ω] [Algebra k Ω]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [AddCommGroup V'] [Module k V'] [Module Ω V'] [IsScalarTower k Ω V']
    [AddCommGroup W'] [Module k W'] [Module Ω W'] [IsScalarTower k Ω W']
    (jV : V →ₗ[k] V') (jW : W →ₗ[k] W')
    (bcV : IsBaseChange Ω jV) (bcW : IsBaseChange Ω jW)
    (f : V →ₗ[k] W) (f' : V' →ₗ[Ω] W')
    (hcomm : ∀ v, f' (jV v) = jW (f v))
    (x : V') (hx : f' x = 0) :
    x ∈ Submodule.span Ω (jV '' (f.ker : Set V)) := by
  let T := TensorProduct.AlgebraTensorModule.lTensor Ω Ω f
  have hT : ∀ y : Ω ⊗[k] V, f' (bcV.equiv y) = bcW.equiv (T y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp [hy, hz]
    | tmul a v => simp [T, IsBaseChange.equiv_tmul, hcomm]
  have hy : bcV.equiv.symm x ∈ T.ker := by
    rw [LinearMap.mem_ker]
    apply bcW.equiv.injective
    rw [← hT, bcV.equiv.apply_symm_apply, hx, map_zero]
  rw [show T.ker = (TensorProduct.AlgebraTensorModule.lTensor Ω Ω f.ker.subtype).range from
    Module.Flat.ker_lTensor_eq Ω Ω f] at hy
  obtain ⟨z, hz⟩ := hy
  have hzspan : ∀ z : Ω ⊗[k] f.ker,
      bcV.equiv ((TensorProduct.AlgebraTensorModule.lTensor Ω Ω f.ker.subtype) z) ∈
        Submodule.span Ω (jV '' (f.ker : Set V)) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => simpa using (Submodule.add_mem _ ha hb)
    | tmul a v =>
      simpa [IsBaseChange.equiv_tmul] using
        (Submodule.smul_mem (Submodule.span Ω (jV '' (f.ker : Set V))) a
          (Submodule.subset_span ⟨v.1, v.2, rfl⟩))
  have hx' : x = bcV.equiv ((TensorProduct.AlgebraTensorModule.lTensor Ω Ω f.ker.subtype) z) := by
    rw [hz, bcV.equiv.apply_symm_apply]
  rw [hx']
  exact hzspan z

/-! ### Nonvanishing determinant in a finite matrix span

The determinant polynomial is evaluated first at extension field coefficients and then at ground
field coefficients, following the last step of Milne's proof. -/

/-- The determinant of the generic linear combination of `X`; used by
`exists_unit_det_combination`. -/
private def detCombinationPolynomial {k ι n : Type*} [CommRing k] [Fintype ι]
    [Fintype n] [DecidableEq n] (X : ι → Matrix n n k) : MvPolynomial ι k :=
  (∑ i, (MvPolynomial.X i : MvPolynomial ι k) •
    (X i).map (MvPolynomial.C : k →+* MvPolynomial ι k)).det

/-- Evaluation of the determinant polynomial at scalar extension coefficients; used by
`exists_unit_det_combination`. -/
private theorem eval_detCombinationPolynomial
    {k K ι n : Type*} [Field k] [Field K] [Algebra k K]
    [Fintype ι] [Fintype n] [DecidableEq n]
    (X : ι → Matrix n n k) (a : ι → K) :
    MvPolynomial.eval₂ (algebraMap k K) a (detCombinationPolynomial X) =
      (∑ i, a i • (X i).map (algebraMap k K)).det := by
  classical
  change (MvPolynomial.eval₂Hom (algebraMap k K) a)
    (∑ i, (MvPolynomial.X i : MvPolynomial ι k) •
      (X i).map (MvPolynomial.C : k →+* MvPolynomial ι k)).det = _
  rw [RingHom.map_det]
  congr 1
  ext r c
  simp [Matrix.map_apply, Matrix.sum_apply]

/-- If the scalar extension of a finite family of square matrices has an invertible linear
combination, so does the family over the infinite ground field. Used by
`matrixIntertwinerDescends`. -/
private theorem exists_unit_det_combination
    {k Ω ι n : Type*} [Field k] [Infinite k] [Field Ω] [Algebra k Ω]
    [Fintype ι] [Fintype n] [DecidableEq n] (X : ι → Matrix n n k)
    (h : ∃ a : ι → Ω, IsUnit (∑ i, a i • (X i).map (algebraMap k Ω)).det) :
    ∃ a : ι → k, IsUnit (∑ i, a i • X i).det := by
  classical
  obtain ⟨a, ha⟩ := h
  have hP : detCombinationPolynomial X ≠ 0 := by
    intro hz
    have hz' := congrArg (MvPolynomial.eval₂ (algebraMap k Ω) a) hz
    rw [MvPolynomial.eval₂_zero, eval_detCombinationPolynomial] at hz'
    exact ha.ne_zero hz'
  have hb : ∃ b : ι → k, MvPolynomial.eval b (detCombinationPolynomial X) ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hP (MvPolynomial.funext (q := 0) (by simpa using hn))
  obtain ⟨b, hb⟩ := hb
  refine ⟨b, ?_⟩
  have he := eval_detCombinationPolynomial X b
  have he' : MvPolynomial.eval b (detCombinationPolynomial X) =
      (∑ i, b i • X i).det := by simpa using he
  rw [he'] at hb
  exact isUnit_iff_ne_zero.mpr hb

/-- A matrix subspace containing an invertible point after scalar extension contains an
invertible ground field point. Used by `matrixIntertwinerDescends`. -/
private theorem exists_unit_det_in_submodule
    {k Ω n : Type*} [Field k] [Infinite k] [Field Ω] [Algebra k Ω]
    [Fintype n] [DecidableEq n]
    (p : Submodule k (Matrix n n k))
    (j : Matrix n n k →ₗ[k] Matrix n n Ω)
    (hj : ∀ D, j D = D.map (algebraMap k Ω))
    (C : Matrix n n Ω)
    (hspan : C ∈ Submodule.span Ω (j '' (p : Set (Matrix n n k))))
    (hC : IsUnit C.det) :
    ∃ D : Matrix n n k, D ∈ p ∧ IsUnit D.det := by
  classical
  let b := Module.finBasis k p
  let q : Submodule Ω (Matrix n n Ω) :=
    Submodule.span Ω (Set.range (fun i => j (b i : Matrix n n k)))
  have hspanb : C ∈ q := by
    apply Submodule.span_le.mpr ?_ hspan
    intro D hD
    obtain ⟨E, hE, rfl⟩ := hD
    let e : p := ⟨E, hE⟩
    have he : e = ∑ i, (b.repr e i) • b i := (b.sum_repr e).symm
    have he' : E = ∑ i, (b.repr e i) • (b i : Matrix n n k) :=
      by simpa only [Submodule.coe_sum, SetLike.val_smul] using congrArg Subtype.val he
    rw [he']
    simp only [map_sum, map_smul]
    exact Submodule.sum_mem q (fun i hi => by
      have hbi : j (b i : Matrix n n k) ∈ q :=
        Submodule.subset_span (Set.mem_range_self i)
      simpa only [IsScalarTower.algebraMap_smul] using
        (q.smul_mem (algebraMap k Ω (b.repr e i)) hbi))
  change C ∈ Submodule.span Ω (Set.range (fun i => j (b i : Matrix n n k))) at hspanb
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).mp hspanb
  have ha' : IsUnit (∑ i, a i • (j (b i : Matrix n n k))).det := by
    rw [ha]
    exact hC
  obtain ⟨d, hd⟩ := exists_unit_det_combination
    (fun i => (b i : Matrix n n k)) ⟨a, by simpa only [hj] using ha'⟩
  refine ⟨∑ i, d i • (b i : Matrix n n k), ?_, hd⟩
  exact Submodule.sum_mem p (fun i hi => p.smul_mem _ (b i).property)

/-! ### Intertwiner matrices

For actions with matrices `A` and `B`, the equations are `D A_g - B_g D = 0` for each `g`.
Their kernel is the space of intertwiner matrices. -/

/-- The homogeneous linear system $D A_g-B_g D=0$; used by
`matrixIntertwinerDescends`. -/
private def intertwinerEquations {k G n : Type*} [Field k]
    [Fintype n] [DecidableEq n] (A B : G → Matrix n n k) :
    Matrix n n k →ₗ[k] (G → Matrix n n k) where
  toFun D g := D * A g - B g * D
  map_add' D E := by
    ext g i j
    simp [add_mul, mul_add, sub_eq_add_neg]
    abel
  map_smul' a D := by
    change (fun g => (a • D) * A g - B g * (a • D)) =
      (RingHom.id k) a • (fun g => D * A g - B g * D)
    funext g
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [smul_mul_assoc, mul_smul_comm, smul_sub]


/-- Existence of an invertible intertwiner matrix over an extension field implies existence
over the infinite ground field. Milne, *Class Field Theory*, version 4.03
(2020), Chapter VII, Lemma 3.2, matrix form. -/
private theorem matrixIntertwinerDescends
    {k Ω G n : Type*} [Field k] [Infinite k] [Field Ω] [Algebra k Ω]
    [Finite G] [Fintype n] [DecidableEq n]
    (A B : G → Matrix n n k)
    (h : ∃ C : Matrix n n Ω, IsUnit C.det ∧
      ∀ g, C * (A g).map (algebraMap k Ω) = (B g).map (algebraMap k Ω) * C) :
    ∃ D : Matrix n n k, IsUnit D.det ∧ ∀ g, D * A g = B g * D := by
  classical
  let j : Matrix n n k →ₗ[k] Matrix n n Ω :=
    ((Algebra.linearMap k Ω).compLeft n).compLeft n
  let jG : (G → Matrix n n k) →ₗ[k] (G → Matrix n n Ω) := j.compLeft G
  have bcj : IsBaseChange Ω j :=
    (IsBaseChange.linearMap k Ω).finitePow n |>.finitePow n
  have bcjG : IsBaseChange Ω jG := bcj.finitePow G
  let f := intertwinerEquations A B
  let f' := intertwinerEquations
    (fun g => (A g).map (algebraMap k Ω))
    (fun g => (B g).map (algebraMap k Ω))
  have hj (D : Matrix n n k) : j D = D.map (algebraMap k Ω) := by
    ext i j'
    rfl
  have hcomm (D : Matrix n n k) : f' (j D) = jG (f D) := by
    ext g i j'
    simp [f, f', jG, intertwinerEquations, hj, Matrix.map_apply,
      Matrix.mul_apply]
  obtain ⟨C, hC, hCA⟩ := h
  have hker : f' C = 0 := by
    ext g i j'
    simp [f', intertwinerEquations, hCA g]
  have hspan := mem_span_ker_of_baseChange j jG bcj bcjG f f' hcomm C hker
  obtain ⟨D, hDker, hDunit⟩ := exists_unit_det_in_submodule f.ker j hj C hspan hC
  refine ⟨D, hDunit, ?_⟩
  intro g
  have hg := congrArg (fun F : G → Matrix n n k => F g) (LinearMap.mem_ker.mp hDker)
  simpa [f, intertwinerEquations, sub_eq_zero] using hg

/-! ### Representations on base-changed modules

Bases of the two original carriers and their base changes convert a representation isomorphism
to an invertible intertwiner matrix. The matrix result then gives a representation isomorphism
over the ground field. -/

/-- Matrix entries of an action on a base-changed module are the images of the original
action's matrix entries. Used by `nonempty_equiv_of_baseChange`. -/
private theorem action_toMatrix_baseChange
    {k Ω G V VΩ ι : Type*} [Field k] [Field Ω] [Algebra k Ω] [Monoid G]
    [AddCommGroup V] [Module k V]
    [AddCommGroup VΩ] [Module k VΩ] [Module Ω VΩ] [IsScalarTower k Ω VΩ]
    [Fintype ι] [DecidableEq ι]
    (ρ : _root_.Representation k G V) (ρΩ : _root_.Representation Ω G VΩ)
    (j : V →ₗ[k] VΩ) (bc : IsBaseChange Ω j)
    (hρ : ∀ g v, ρΩ g (j v) = j (ρ g v)) (b : Module.Basis ι k V) (g : G) :
    LinearMap.toMatrix (bc.basis b) (bc.basis b) (ρΩ g) =
      (LinearMap.toMatrix b b (ρ g)).map (algebraMap k Ω) := by
  ext i l
  simp only [LinearMap.toMatrix_apply, Matrix.map_apply]
  change ((bc.basis b).repr (ρΩ g ((bc.basis b) l))) i =
    (algebraMap k Ω) ((b.repr (ρ g (b l))) i)
  rw [IsBaseChange.basis_apply b bc l, hρ]
  exact IsBaseChange.basis_repr_comp_apply b bc _ _

/-- An invertible intertwiner matrix in bases of two representations gives a representation
isomorphism. Used by `nonempty_equiv_of_baseChange`. -/
private theorem equiv_of_matrix_intertwiner
    {k G V W n : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [Fintype n] [DecidableEq n]
    (ρ : _root_.Representation k G V) (σ : _root_.Representation k G W)
    (bV : Module.Basis n k V) (bW : Module.Basis n k W)
    (D : Matrix n n k) (hD : IsUnit D.det)
    (hDA : ∀ g, D * LinearMap.toMatrix bV bV (ρ g) =
      LinearMap.toMatrix bW bW (σ g) * D) : Nonempty (ρ.Equiv σ) := by
  let F : V →ₗ[k] W := Matrix.toLin bV bW D
  have hF (g : G) : F ∘ₗ ρ g = σ g ∘ₗ F := by
    apply (LinearMap.toMatrix bV bW).injective
    rw [LinearMap.toMatrix_comp bV bV bW,
      LinearMap.toMatrix_comp bV bW bW,
      LinearMap.toMatrix_toLin]
    change D * LinearMap.toMatrix bV bV (ρ g) =
      LinearMap.toMatrix bW bW (σ g) * D
    exact hDA g
  have hdet : IsUnit ((LinearMap.toMatrix bV bW) F).det := by
    simpa [F] using hD
  let e := LinearEquiv.ofIsUnitDet hdet
  exact ⟨_root_.Representation.Equiv.mk e (by
    intro g
    simpa [e] using hF g)⟩

/-- If the scalar extensions of finite dimensional $k[G]$-modules are isomorphic over $Ω$,
then the original modules are isomorphic over the infinite field $k$. The maps `jV` and `jW`
realize the scalar extensions via `IsBaseChange`. Milne, *Class Field Theory*, version 4.03 (2020),
Chapter VII, Lemma 3.2. -/
theorem nonempty_equiv_of_baseChange
    {k Ω G V W VΩ WΩ : Type*} [Field k] [Infinite k] [Field Ω] [Algebra k Ω]
    [Monoid G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [AddCommGroup VΩ] [Module k VΩ] [Module Ω VΩ] [IsScalarTower k Ω VΩ]
    [AddCommGroup WΩ] [Module k WΩ] [Module Ω WΩ] [IsScalarTower k Ω WΩ]
    (ρ : _root_.Representation k G V) (σ : _root_.Representation k G W)
    (ρΩ : _root_.Representation Ω G VΩ) (σΩ : _root_.Representation Ω G WΩ)
    (jV : V →ₗ[k] VΩ) (jW : W →ₗ[k] WΩ)
    (bcV : IsBaseChange Ω jV) (bcW : IsBaseChange Ω jW)
    (hρ : ∀ g v, ρΩ g (jV v) = jV (ρ g v))
    (hσ : ∀ g w, σΩ g (jW w) = jW (σ g w))
    (eΩ : ρΩ.Equiv σΩ) : Nonempty (ρ.Equiv σ) := by
  classical
  have hdim : Module.finrank k W = Module.finrank k V := by
    rw [← bcW.finrank_eq, ← bcV.finrank_eq]
    exact eΩ.toLinearEquiv.finrank_eq.symm
  let bV := Module.finBasis k V
  let bW := Module.finBasisOfFinrankEq k W hdim
  let bVΩ := bcV.basis bV
  let bWΩ := bcW.basis bW
  let A : G → Mat(Module.finrank k V, k) :=
    fun g => LinearMap.toMatrix bV bV (ρ g)
  let B : G → Mat(Module.finrank k V, k) :=
    fun g => LinearMap.toMatrix bW bW (σ g)
  have hA (g : G) : LinearMap.toMatrix bVΩ bVΩ (ρΩ g) =
      (A g).map (algebraMap k Ω) :=
    action_toMatrix_baseChange ρ ρΩ jV bcV hρ bV g
  have hB (g : G) : LinearMap.toMatrix bWΩ bWΩ (σΩ g) =
      (B g).map (algebraMap k Ω) :=
    action_toMatrix_baseChange σ σΩ jW bcW hσ bW g
  let C := LinearMap.toMatrix bVΩ bWΩ eΩ.toLinearEquiv.toLinearMap
  have hC : IsUnit C.det := eΩ.toLinearEquiv.isUnit_det bVΩ bWΩ
  have hCA (g : G) : C * (A g).map (algebraMap k Ω) =
      (B g).map (algebraMap k Ω) * C := by
    have heq := eΩ.toIntertwiningMap.isIntertwining' g
    have heq' := congrArg (LinearMap.toMatrix bVΩ bWΩ) heq
    rw [LinearMap.toMatrix_comp bVΩ bVΩ bWΩ,
      LinearMap.toMatrix_comp bVΩ bWΩ bWΩ] at heq'
    rw [hA, hB] at heq'
    exact heq'
  obtain ⟨D, hD, hDA⟩ := matrixIntertwinerDescends A B ⟨C, hC, hCA⟩
  exact equiv_of_matrix_intertwiner ρ σ bV bW D hD hDA

end SIC.Representation
