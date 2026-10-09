/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix

/-!
# Norms and base changes of finite extensions

Norms of units in a finite field extension, continuity of algebraic norms, and the canonical
algebra map from a base change `A ⊗_K L` into a finite product of `A`-algebras receiving `L`,
with its density criterion and product norm formula. Equality of pure tensors descending from
the two factors also detects a common base-field scalar.

These are the algebraic and topological inputs of the decompositions
$K_v \otimes_K L \cong \prod_{w \mid v} L_w$ at finite and infinite places,
[83, Neukirch (1999), Chapter II, Proposition 8.3 and Corollary 8.4], which are proved in
`SICs.ClassField.Completion.FiniteBaseChange` and `SICs.ClassField.Completion.InfiniteBaseChange`.

## The argument

A family of `K`-algebra maps `L → E_i` into `A`-algebras extends `A`-linearly to `A ⊗_K L`.
When `A` is a complete nontrivially normed field and the target is a Hausdorff topological
vector space, the range of an `A`-linear map from the finite-dimensional space `A ⊗_K L` is a
finite-dimensional subspace, hence closed; if it contains a dense set, it is everything. This is
the density argument of Serre, *Local Fields*, Chapter II, §3, proof of Theorem 1.

The norm of a base-field unit included in an extension is its extension-degree power, so every
power divisible by that degree is a norm and a degree-one norm is surjective. For a topological
finite extension, the algebraic norm is the determinant of left multiplication in a basis;
continuity of the matrix entries and determinant gives continuity of the norm.

The norm of $1 \otimes x$ over `A` is the image of the norm of `x` over `K`, because left
multiplication by $1 \otimes x$ is the base change of left multiplication by `x` and the
determinant commutes with base change. The norm on a finite product of algebras is the product of
the componentwise norms, because left multiplication is block diagonal. An `A`-algebra isomorphism
preserves norms, so a decomposition $A \otimes_K L \cong \prod_i E_i$ gives
$N_{L/K}(x) = \prod_i N_{E_i/A}(x)$ in `A`, and comparing dimensions gives
$[L : K] = \sum_i [E_i : A]$ [83, Neukirch (1999), Chapter II, Corollary 8.4].
If $c \otimes 1=1\otimes a$, a linear retraction of $K\to L$ recovers $c$ from the equality;
injectivity of $L\to A\otimes_K L$ then recovers $a$ from the same scalar.
-/

noncomputable section

open scoped TensorProduct

namespace SIC

/-! ### The canonical map into a product -/

section Map

variable {K A L : Type*} [CommRing K] [CommRing A] [Algebra K A] [CommRing L] [Algebra K L]
  {ι : Type*} {E : ι → Type*} [∀ i, CommRing (E i)] [∀ i, Algebra A (E i)]
  [∀ i, Algebra K (E i)] [∀ i, IsScalarTower K A (E i)]

/-- The `A`-algebra map $A \otimes_K L \to \prod_i E_i$, $a \otimes x \mapsto (a f_i(x))_i$,
extending a family of `K`-algebra maps $f_i : L \to E_i$. -/
def baseChangePi (f : ∀ i, L →ₐ[K] E i) : A ⊗[K] L →ₐ[A] ∀ i, E i :=
  Algebra.TensorProduct.lift (Algebra.ofId A _) (AlgHom.pi f) fun _ _ ↦ Commute.all _ _

/-- Evaluation of `baseChangePi` on a pure tensor. -/
@[simp]
theorem baseChangePi_tmul (f : ∀ i, L →ₐ[K] E i) (a : A) (x : L) (i : ι) :
    baseChangePi f (a ⊗ₜ x) i = algebraMap A (E i) a * f i x := by
  simp [baseChangePi, Algebra.TensorProduct.lift_tmul]

end Map

/-! ### Descent of equal pure tensors

Equality of the two pure tensors forces their factors to come from one scalar of the base field.
-/

/-- The equality $c \otimes 1 = 1 \otimes a$ in $A \otimes_K L$ makes both factors images of
the same scalar in `K`. Used by `IdeleClassGroup.inclusion_injective`. -/
theorem exists_eq_algebraMap_of_tmul_one_eq_one_tmul {K A L : Type*} [Field K] [Ring A]
    [Algebra K A] [Nontrivial A] [Ring L] [Algebra K L] [Nontrivial L] {c : A} {a : L}
    (h : c ⊗ₜ[K] (1 : L) = (1 : A) ⊗ₜ[K] a) :
    ∃ k : K, a = algebraMap K L k ∧ c = algebraMap K A k := by
  obtain ⟨φ, hφ⟩ := (Algebra.linearMap K L).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (RingHom.injective (algebraMap K L)))
  have hφ1 : φ (1 : L) = 1 := by
    have h1 := LinearMap.congr_fun hφ (1 : K)
    simpa using h1
  let k : K := φ a
  have hc : c = algebraMap K A k := by
    have hh := congrArg (TensorProduct.rid K A) (congrArg (LinearMap.lTensor A φ) h)
    simpa [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, hφ1,
      Algebra.algebraMap_eq_smul_one, k] using hh
  have ha : a = algebraMap K L k := by
    apply (Algebra.TensorProduct.includeRight_injective
      (RingHom.injective (algebraMap K A)))
    change (1 : A) ⊗ₜ[K] a = (1 : A) ⊗ₜ[K] algebraMap K L k
    calc
      _ = c ⊗ₜ[K] 1 := h.symm
      _ = _ := by rw [hc]; simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  exact ⟨k, ha, hc⟩

/-! ### Surjectivity from density -/

/-- An `A`-linear map from a base change `A ⊗_K L`, with `L` finite over `K`, into a Hausdorff
topological vector space over a complete nontrivially normed field `A` is surjective as soon as
the image of `L` is dense. Serre, *Local Fields*, Chapter II, §3, proof of Theorem 1. -/
theorem surjective_of_denseRange_tmul {K A L B : Type*} [CommRing K] [NontriviallyNormedField A]
    [CompleteSpace A] [Algebra K A] [AddCommGroup L] [Module K L] [Module.Finite K L]
    [AddCommGroup B] [Module A B] [TopologicalSpace B] [IsTopologicalAddGroup B]
    [ContinuousSMul A B] [T2Space B] (Φ : A ⊗[K] L →ₗ[A] B)
    (h : DenseRange fun x : L ↦ Φ ((1 : A) ⊗ₜ x)) :
    Function.Surjective Φ := by
  have : FiniteDimensional A (A ⊗[K] L) := inferInstance
  rw [← Set.range_eq_univ, ← Φ.coe_range, ← Φ.range.closed_of_finiteDimensional.closure_eq]
  apply DenseRange.closure_range
  exact h.mono (by
    rintro _ ⟨x, rfl⟩
    exact ⟨(1 : A) ⊗ₜ x, rfl⟩)

/-! ### Norms of units -/

/-- The norm of a unit included from the base field is its degree-th power. This supplies
the principal formulas for both finite and infinite local norms. -/
theorem unitsMap_norm_algebraMap {k E : Type*} [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] (x : kˣ) :
    Units.map (Algebra.norm k : E →* k) (Units.map (algebraMap k E) x) =
      x ^ Module.finrank k E := by
  apply Units.ext
  exact Algebra.norm_algebraMap (S := E) (x : k)

/-- Every power divisible by the extension degree is the norm of a unit. This supplies the
power-in-range statements for both kinds of local norm. -/
theorem pow_mem_range_unitsMap_norm {k E : Type*} [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] {n : ℕ} (hd : Module.finrank k E ∣ n) (x : kˣ) :
    x ^ n ∈ (Units.map (Algebra.norm k : E →* k)).range := by
  obtain ⟨m, rfl⟩ := hd
  refine ⟨Units.map (algebraMap k E) (x ^ m), ?_⟩
  rw [unitsMap_norm_algebraMap, ← pow_mul, Nat.mul_comm]

/-- A degree-one extension has a surjective norm on units. This supplies the degree-one
surjectivity statements for both kinds of local norm. -/
theorem unitsMap_norm_surjective_of_finrank_eq_one {k E : Type*} [Field k] [Field E]
    [Algebra k E] (h : Module.finrank k E = 1) :
    Function.Surjective (Units.map (Algebra.norm k : E →* k)) := by
  intro x
  refine ⟨Units.map (algebraMap k E) x, ?_⟩
  apply Units.ext
  change Algebra.norm k (algebraMap k E (x : k)) = (x : k)
  rw [Algebra.norm_algebraMap, h, pow_one]

/-- The algebraic norm of a finite topological ring extension is continuous when scalar
multiplication is continuous. Used for both finite and infinite local norms. -/
theorem continuous_algebraNorm_of_continuousSMul
    {k E : Type*} [NontriviallyNormedField k] [CompleteSpace k]
    [Ring E] [Algebra k E] [Module.Finite k E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
    [ContinuousSMul k E] [ContinuousMul E] :
    Continuous (Algebra.norm k : E → k) := by
  let b := Module.finBasis k E
  change Continuous fun x : E ↦ LinearMap.det ((Algebra.lmul k E) x)
  have hmat : Continuous fun x : E ↦
      LinearMap.toMatrix b b ((Algebra.lmul k E) x) := by
    apply continuous_matrix
    intro i j
    have heq : (fun a : E ↦ LinearMap.toMatrix b b ((Algebra.lmul k E) a) i j) =
        (fun a : E ↦ (b.repr (a * b j)) i) := by
      funext a
      rw [LinearMap.toMatrix_apply]
      rfl
    rw [heq]
    exact (continuous_apply i).comp <|
      (continuous_equivFun_basis b).comp (continuous_id.mul continuous_const)
  have hdet := hmat.matrix_det
  convert hdet using 1
  funext x
  exact (LinearMap.det_toMatrix b _).symm

/-! ### Norms on base changes and products -/

section Norm

universe u v

/-- The equivalence step of the induction proving `det_pi_family`: reindexing transports the
componentwise determinant formula. -/
private theorem det_pi_family_equiv {R : Type*} [CommRing R] {α β : Type u}
    [Fintype α] [Fintype β] (e : α ≃ β) {N : β → Type v}
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    [∀ i, Module.Free R (N i)] [∀ i, Module.Finite R (N i)]
    (g : ∀ i, N i →ₗ[R] N i)
    (h : LinearMap.det (LinearMap.pi fun i : α => g (e i) ∘ₗ LinearMap.proj i) =
      ∏ i : α, LinearMap.det (g (e i))) :
    LinearMap.det (LinearMap.pi fun i : β => g i ∘ₗ LinearMap.proj i) =
      ∏ i, LinearMap.det (g i) := by
  let p := LinearEquiv.piCongrLeft R N e
  have hc : (LinearMap.pi fun i : β => g i ∘ₗ LinearMap.proj i) =
      (p : _ →ₗ[R] _) ∘ₗ
        (LinearMap.pi fun i : α => g (e i) ∘ₗ LinearMap.proj i) ∘ₗ
        (p.symm : _ →ₗ[R] _) := by
    apply LinearMap.ext
    intro y
    funext i
    rcases e.surjective i with ⟨a, rfl⟩
    change g (e a) (y (e a)) =
      (Equiv.piCongrLeft N e)
        (fun j => g (e j) ((Equiv.piCongrLeft N e).symm y j)) (e a)
    simp
  rw [hc, LinearMap.det_conj, h]
  exact Fintype.prod_equiv e (fun i => LinearMap.det (g (e i)))
    (fun i => LinearMap.det (g i)) (by intro i; rfl)

/-- The successor step of the induction proving `det_pi_family`: adding one factor multiplies
the componentwise determinant by that factor's determinant. -/
private theorem det_pi_family_option {R : Type*} [CommRing R] {α : Type u} [Fintype α]
    {N : Option α → Type v} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    [∀ i, Module.Free R (N i)] [∀ i, Module.Finite R (N i)]
    (g : ∀ i, N i →ₗ[R] N i)
    (h : LinearMap.det (LinearMap.pi fun i : α => g (some i) ∘ₗ LinearMap.proj i) =
      ∏ i : α, LinearMap.det (g (some i))) :
    LinearMap.det (LinearMap.pi fun i : Option α => g i ∘ₗ LinearMap.proj i) =
      ∏ i, LinearMap.det (g i) := by
  let p := LinearEquiv.piOptionEquivProd R (M := N)
  have hc : (LinearMap.pi fun i : Option α => g i ∘ₗ LinearMap.proj i) =
      (p.symm : _ →ₗ[R] _) ∘ₗ
        LinearMap.prodMap (g none)
          (LinearMap.pi fun i : α => g (some i) ∘ₗ LinearMap.proj i) ∘ₗ
        (p : _ →ₗ[R] _) := by
    apply LinearMap.ext
    intro y
    funext i
    cases i <;> rfl
  rw [hc]
  calc
    LinearMap.det ((p.symm : _ →ₗ[R] _) ∘ₗ
        LinearMap.prodMap (g none)
          (LinearMap.pi fun i : α => g (some i) ∘ₗ LinearMap.proj i) ∘ₗ
        (p : _ →ₗ[R] _)) =
        LinearMap.det (LinearMap.prodMap (g none)
          (LinearMap.pi fun i : α => g (some i) ∘ₗ LinearMap.proj i)) := by
            simpa using LinearMap.det_conj
              (LinearMap.prodMap (g none)
                (LinearMap.pi fun i : α => g (some i) ∘ₗ LinearMap.proj i)) p.symm
    _ = ∏ i, LinearMap.det (g i) := by
      rw [LinearMap.det_prodMap, h]
      simp

/-- The determinant of a componentwise endomorphism of a finite dependent product is the
product of the component determinants. This supplies the block diagonal step in
`algebraNorm_pi`. -/
theorem det_pi_family {R : Type*} [CommRing R] {ι : Type u} [Fintype ι]
    {M : ι → Type v} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]
    (f : ∀ i, M i →ₗ[R] M i) :
    LinearMap.det (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i) =
      ∏ i, LinearMap.det (f i) := by
  classical
  let P : ∀ (α : Type u) [Fintype α], Prop := fun α _ =>
    ∀ (N : α → Type v) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
      [∀ i, Module.Free R (N i)] [∀ i, Module.Finite R (N i)]
      (g : ∀ i, N i →ₗ[R] N i),
      LinearMap.det (LinearMap.pi fun i => g i ∘ₗ LinearMap.proj i) =
        ∏ i, LinearMap.det (g i)
  have hp : P ι := by
    refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ ι
    · intro α β _ e ih N _ _ _ _ g
      exact @det_pi_family_equiv R _ α β (Fintype.ofEquiv β e.symm) inferInstance
        e N inferInstance inferInstance inferInstance inferInstance g
        (ih (fun i => N (e i)) (fun i => g (e i)))
    · intro N _ _ _ _ g
      simpa using (LinearMap.det_eq_one_of_subsingleton
        (LinearMap.pi fun i : PEmpty => g i ∘ₗ LinearMap.proj i))
    · intro α _ ih N _ _ _ _ g
      exact det_pi_family_option g (ih (fun i => N (some i)) (fun i => g (some i)))
  exact hp M f

/-- The norm of $1 \otimes x$ in a base change is the image of the norm of `x`:
$N_{(A \otimes_K L)/A}(1 \otimes x) = N_{L/K}(x)$. -/
theorem algebraNorm_one_tmul {K A L : Type*} [CommRing K] [CommRing A] [Algebra K A]
    [CommRing L] [Algebra K L] [Module.Free K L] [Module.Finite K L] (x : L) :
    Algebra.norm A ((1 : A) ⊗ₜ[K] x) = algebraMap K A (Algebra.norm K x) := by
  have h : Algebra.lmul A (A ⊗[K] L) ((1 : A) ⊗ₜ x) =
      (Algebra.lmul K L x).baseChange A := by
    apply LinearMap.ext
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a y => simp [Algebra.coe_lmul_eq_mul, LinearMap.baseChange_tmul]
    | add t u ht hu =>
        change (1 ⊗ₜ[K] x) * (t + u) = _
        rw [mul_add, map_add]
        exact congrArg₂ (· + ·) ht hu
  rw [Algebra.norm_apply, h, LinearMap.det_baseChange, ← Algebra.norm_apply]

/-- The norm on a finite product of finite free algebras is the product of the componentwise
norms. -/
theorem algebraNorm_pi {A ι : Type*} [CommRing A] [Fintype ι] {E : ι → Type*}
    [∀ i, CommRing (E i)] [∀ i, Algebra A (E i)] [∀ i, Module.Free A (E i)]
    [∀ i, Module.Finite A (E i)] (x : ∀ i, E i) :
    Algebra.norm A x = ∏ i, Algebra.norm A (x i) := by
  have h : Algebra.lmul A (∀ i, E i) x =
      LinearMap.pi (fun i => Algebra.lmul A (E i) (x i) ∘ₗ LinearMap.proj i) := by
    apply LinearMap.ext
    intro y
    funext i
    rfl
  rw [Algebra.norm_apply, h, det_pi_family]
  simp_rw [← Algebra.norm_apply]

variable {K A L : Type*} [Field K] [Field A] [Algebra K A] [Field L] [Algebra K L]

/-- A decomposition $A \otimes_K L \cong \prod_i E_i$ expresses the norm of `x ∈ L` as the
product of its local norms: $N_{L/K}(x) = \prod_i N_{E_i/A}(x)$ in `A`.
[83, Neukirch (1999), Chapter II, Corollary 8.4]. -/
theorem algebraMap_norm_eq_prod_of_algEquiv [FiniteDimensional K L] {ι : Type*} [Fintype ι]
    {E : ι → Type*} [∀ i, Field (E i)] [∀ i, Algebra A (E i)]
    [∀ i, FiniteDimensional A (E i)] (e : A ⊗[K] L ≃ₐ[A] ∀ i, E i) (x : L) :
    algebraMap K A (Algebra.norm K x) = ∏ i, Algebra.norm A (e ((1 : A) ⊗ₜ x) i) := by
  rw [← algebraNorm_one_tmul, ← Algebra.norm_eq_of_algEquiv e, algebraNorm_pi]

/-- A decomposition $A \otimes_K L \cong \prod_i E_i$ gives $[L : K] = \sum_i [E_i : A]$.
[83, Neukirch (1999), Chapter II, Corollary 8.4]. -/
theorem finrank_eq_sum_of_algEquiv [FiniteDimensional K L] {ι : Type*} [Fintype ι]
    {E : ι → Type*} [∀ i, Field (E i)] [∀ i, Algebra A (E i)]
    [∀ i, FiniteDimensional A (E i)]
    (e : A ⊗[K] L ≃ₐ[A] ∀ i, E i) :
    Module.finrank K L = ∑ i, Module.finrank A (E i) := by
  rw [← Module.finrank_baseChange (R := A) (S := K) (M' := L),
    e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]

end Norm

end SIC
