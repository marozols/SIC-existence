/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Local.ValuationSequence
import SICs.GroupCohomology.Filtration
import SICs.FieldTheory.NormalBasis
import Mathlib.Topology.Algebra.Group.Units
import SICs.Analysis.UltrametricUnitFiltration

/-!
# The Herbrand quotient of local units

For a Galois extension of number fields `L/K` and a finite place `w` of `L` above `v`, the
integral units $U_w$ contain an open $\operatorname{Gal}(L_w/K_v)$-stable subgroup of finite
index whose
Tate groups in degrees $0$ and $-1$ vanish; hence $h(U_w) = 1$ when $L_w/K_v$ is cyclic.

This is Serre, *Local class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
*Algebraic Number Theory* (1967), Chapter VI, §1.4, Proposition 3 (its second method, valid in
every characteristic) and Corollary 1, which are Milne, *Class Field Theory*, version 4.03 (2020),
Chapter III, Lemmas 2.3–2.5; Milne's proof of Lemma 2.4 uses the exponential map instead of the
filtration below. Serre's open subgroup has finite index in $U_w$, the property the Herbrand
quotient uses.

## The argument

Let $G = \operatorname{Gal}(L_w/K_v)$ and fix $\varpi \in K_v$ with $0 < |\varpi| < 1$.
Choose a normal basis $\{\sigma\beta\}_{\sigma\in G}$ and let
$A = \bigoplus_\sigma \mathcal O_v\,\sigma\beta$. The Galois group permutes the coordinates.
Each coordinate map is continuous, so $A$ is open and closed. It is compact as the image of a
finite product of compact integral balls. Compactness and openness give $k$ such that
$|\varpi^{k+1}a| < 1$ and $\varpi^k ab \in A$ for all $a,b \in A$. Put
$M = \varpi^{k+1}A$; then $M\cdot M \subseteq \varpi M$.

Let $V_i = \{x \in L_w^\times : x - 1 \in \varpi^i M\}$. These are `G`-stable subgroups of $U_w$:
$(1+a)(1+b)-1=a+b+ab$, and $(1+a)^{-1}-1=\sum_{j\ge1}(-a)^j$ converges in the closed lattice
$\varpi^i M$. The subgroups decrease and meet in `1`. Compactness of $V_0$ and closedness of
all $V_i$ supply limits for products $\prod_i x_i$ with $x_i\in V_i$, so this is a complete
filtration (`IsCompleteFiltration`). The `UnitLattice` record carries $\varpi$, $A$, and the
chosen scale $k$ through these steps. Products of elements $1+a_\sigma$ linearize to
$1+\sum_\sigma a_\sigma$ modulo $\varpi^{i+1}M$.

*Successive quotients in degree $0$.* If $x=1+\varpi^{k+1+i}m\in V_i$ is fixed, then so is
$m\in A$. All its normal-basis coordinates are equal, hence
$m=\sum_\sigma\sigma m_0$ with $m_0=a\beta$ for some $a\in\mathcal O_v$. Thus
$x/N_G(1+\varpi^{k+1+i}m_0)\in V_{i+1}$.

*Successive quotients in degree $-1$.* If $x=1+\varpi^{k+1+i}m$ has norm one and
$m=\sum_\sigma a_\sigma\sigma\beta$, then $\sum_\sigma\sigma m\in\varpi A$. Thus
$\sum_\sigma a_\sigma\in\varpi\mathcal O_v$. With
$y_\sigma=1+\varpi^{k+1+i}a_\sigma\beta$, we obtain
$x/\prod_\sigma(\sigma y_\sigma/y_\sigma)\in V_{i+1}$.

Serre's filtration lemma gives $\widehat H^0(G,V_0)=\widehat H^{-1}(G,V_0)=0$. Since $A$ is
open, $V_0$ is an open subgroup of the compact group $U_w$ and has finite index. For cyclic
`G`, finite-kernel-and-cokernel invariance gives $h(U_w)=h(V_0)=1$.
-/

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField WithZero SIC.FinitePlace

namespace SIC

namespace FinitePlace

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [IsGalois K L]

/-! ### The normal-basis lattice -/

/-- The completion of the base number field at `v`, used in the local-unit construction. -/
private abbrev localBase := v.adicCompletion K
/-- The completion of the extension number field at `w`, used in the local-unit construction. -/
private abbrev localExtension := w.adicCompletion L
/-- The Galois group of the finite local extension, used in the normal-basis lattice. -/
private abbrev localGalois := localExtension w ≃ₐ[localBase v] localExtension w


/-- The integral coordinate lattice in the normal basis; used in
`exists_unitSubgroup_tateTrivial`. -/
private def normalBasisLattice : AddSubgroup (localExtension w) where
  carrier := {x | ∀ σ : localGalois v w,
    ‖(IsGalois.normalBasis (localBase v) (localExtension w)).repr x σ‖ ≤ 1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy σ
    rw [map_add, Finsupp.add_apply]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx σ) (hy σ))
  neg_mem' := by
    intro x hx σ
    simpa using hx σ

/-- The integral ball in the base completion is clopen; used for
`normalBasisLattice_isClopen`. -/
private theorem isClopen_baseIntegers : IsClopen {a : localBase v | ‖a‖ ≤ 1} := by
  convert Valued.isClopen_valuationSubring (localBase v) using 1
  ext x
  simp only [Set.mem_ofPred_eq]
  exact Valued.toNormedField.norm_le_one_iff

/-- The normal-basis coordinate lattice is clopen; used in
`exists_unitSubgroup_tateTrivial`. -/
private theorem normalBasisLattice_isClopen :
    IsClopen (normalBasisLattice v w : Set (localExtension w)) := by
  let b := IsGalois.normalBasis (localBase v) (localExtension w)
  have hc : Continuous b.equivFun := continuous_equivFun_basis b
  have hset : (normalBasisLattice v w : Set (localExtension w)) =
      ⋂ σ : localGalois v w, {x : localExtension w | ‖b.repr x σ‖ ≤ 1} := by
    ext x
    simp [normalBasisLattice, b]
  rw [hset]
  constructor
  · apply isClosed_iInter
    intro σ
    exact (isClopen_baseIntegers v).isClosed.preimage ((continuous_apply σ).comp hc)
  · apply isOpen_iInter_of_finite
    intro σ
    exact (isClopen_baseIntegers v).isOpen.preimage ((continuous_apply σ).comp hc)

/-- Openness of the normal-basis lattice, used in `exists_unitSubgroup_tateTrivial`. -/
private theorem normalBasisLattice_isOpen :
    IsOpen (normalBasisLattice v w : Set (localExtension w)) :=
  (normalBasisLattice_isClopen v w).isOpen

/-- The integral ball in the base completion is compact; used for `normalBasisLattice_isCompact`. -/
private theorem isCompact_baseIntegers : IsCompact {a : localBase v | ‖a‖ ≤ 1} := by
  convert isCompact_adicCompletionIntegers v using 1
  ext a
  simpa only [Set.mem_ofPred_eq, SetLike.mem_coe,
    HeightOneSpectrum.mem_adicCompletionIntegers] using
    (Valued.toNormedField.norm_le_one_iff (x := a))

/-- The normal-basis coordinate lattice is compact; used in `exists_unitSubgroup_tateTrivial`. -/
private theorem normalBasisLattice_isCompact :
    IsCompact (normalBasisLattice v w : Set (localExtension w)) := by
  let b := IsGalois.normalBasis (localBase v) (localExtension w)
  have hci : Continuous b.equivFun.symm :=
    b.equivFun.symm.toLinearMap.continuous_of_finiteDimensional
  have hpi : IsCompact (Set.pi Set.univ (fun _ : localGalois v w =>
      {a : localBase v | ‖a‖ ≤ 1})) :=
    isCompact_univ_pi fun _ => isCompact_baseIntegers v
  have himg : Set.image b.equivFun.symm
      (Set.pi Set.univ (fun _ : localGalois v w => {a : localBase v | ‖a‖ ≤ 1})) =
      (normalBasisLattice v w : Set (localExtension w)) := by
    rw [b.equivFun.image_symm_eq_preimage]
    ext x
    simp [normalBasisLattice, b]
  rw [← himg]
  exact hpi.image hci

/-- The normal-basis lattice is Galois-stable; used for `UnitLattice.scaledLevel_stable`. -/
private theorem normalBasisLattice_stable (τ : localGalois v w) (x : localExtension w)
    (hx : x ∈ normalBasisLattice v w) :
    τ x ∈ normalBasisLattice v w := by
  intro σ
  rw [normalBasis_repr_algEquiv]
  exact hx _

/-- Integral scalars preserve the normal-basis lattice; used in
`exists_unitSubgroup_tateTrivial`. -/
private theorem normalBasisLattice_smul (c : localBase v) (hc : ‖c‖ ≤ 1) (x : localExtension w)
    (hx : x ∈ normalBasisLattice v w) : c • x ∈ normalBasisLattice v w := by
  intro σ
  change ‖(IsGalois.normalBasis (localBase v) (localExtension w)).repr (c • x) σ‖ ≤ 1
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  exact (mul_le_mul hc (hx σ) (norm_nonneg _) (by norm_num)).trans (by simp)

/-- Each filtration subgroup consists of integral units in the local field. -/
private theorem _root_.SIC.UnitLattice.unitSubgroup_le_unitGroup
    (D : UnitLattice (localExtension w)) (i : ℕ) :
    D.unitSubgroup i ≤ unitGroup w := by
  intro x hx
  have hnormx : ‖(x : localExtension w)‖ = 1 :=
    D.unitSubgroup_norm_eq_one i hx
  exact (mem_unitGroup_iff_norm_eq_one w x).mpr hnormx

/-- The scaled normal-basis lattice is Galois-stable when its scalar is fixed. -/
private theorem _root_.SIC.UnitLattice.scaledLevel_stable (D : UnitLattice (localExtension w))
    (hA : D.A = normalBasisLattice v w)
    (hπfix : ∀ σ : localGalois v w, σ D.π = D.π)
    (i : ℕ) (σ : localGalois v w) (x : localExtension w) (hx : x ∈ D.scaledLevel i) :
    σ x ∈ D.scaledLevel i := by
  rcases (D.mem_level i x).mp hx with ⟨a, ha, rfl⟩
  apply (D.mem_level i _).mpr
  have ha' : a ∈ normalBasisLattice v w := hA ▸ ha
  have hσa : σ a ∈ D.A := hA.symm ▸ normalBasisLattice_stable v w σ a ha'
  refine ⟨σ a, hσa, ?_⟩
  simp [map_mul, map_pow, hπfix]

/-- Every normal-basis unit filtration term is Galois-stable. -/
private theorem _root_.SIC.UnitLattice.unitSubgroup_stable (D : UnitLattice (localExtension w))
    (hA : D.A = normalBasisLattice v w)
    (hπfix : ∀ σ : localGalois v w, σ D.π = D.π)
    (i : ℕ) (σ : localGalois v w) (x : (localExtension w)ˣ)
    (hx : x ∈ D.unitSubgroup i) : σ • x ∈ D.unitSubgroup i := by
  have h := D.scaledLevel_stable v w hA hπfix i σ ((x : localExtension w) - 1) hx
  change ((σ • x : (localExtension w)ˣ) : localExtension w) - 1 ∈ D.scaledLevel i
  simpa [AlgEquiv.smul_units_def] using h

/-! ### Successive quotients in degree 0 -/

/-- A fixed lattice element is a sum of conjugates of one lattice element; used in the
degree-zero step. -/
private theorem normalBasisLattice_fixed_sum (m : localExtension w)
    (hm : m ∈ normalBasisLattice v w)
    (hfix : ∀ σ : localGalois v w, σ m = m) :
    ∃ m₀ ∈ normalBasisLattice v w, ∑ σ : localGalois v w, σ m₀ = m := by
  classical
  let b := IsGalois.normalBasis (localBase v) (localExtension w)
  let c := b.repr m 1
  let m₀ := c • b 1
  have hc : ‖c‖ ≤ 1 := hm 1
  have hm₀ : m₀ ∈ normalBasisLattice v w := by
    intro σ
    change ‖b.repr (c • b 1) σ‖ ≤ 1
    rw [map_smul, Finsupp.smul_apply, b.repr_self_apply]
    split_ifs <;> simp [hc]
  refine ⟨m₀, hm₀, ?_⟩
  have hcoords : ∀ σ : localGalois v w, b.repr m σ = c := by
    intro σ
    have h := normalBasis_repr_algEquiv σ m σ
    simpa [hfix σ] using h
  calc
    ∑ σ : localGalois v w, σ m₀ = ∑ σ : localGalois v w, c • b σ := by
      apply Finset.sum_congr rfl
      intro σ hσ
      change σ.toLinearMap (c • b 1) = c • b σ
      rw [map_smul, σ.toLinearMap_apply, algEquiv_normalBasis σ 1, mul_one]
    _ = m := by
      conv_rhs => rw [← b.sum_repr m]
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [hcoords σ]

/-- An integral multiple of a normal-basis vector lies in the lattice; used in the
degree-minus-one step. -/
private theorem normalBasisLattice_single_mem (c : localBase v) (hc : ‖c‖ ≤ 1)
    (τ : localGalois v w) :
    c • (IsGalois.normalBasis (localBase v) (localExtension w)) τ ∈ normalBasisLattice v w := by
  classical
  intro σ
  let b := IsGalois.normalBasis (localBase v) (localExtension w)
  change ‖b.repr (c • b τ) σ‖ ≤ 1
  rw [map_smul, Finsupp.smul_apply, b.repr_self_apply]
  split_ifs <;> simp [hc]

/-- A lattice element with trace divisible by a base scalar is a coboundary modulo that
scalar; used in the degree-minus-one step. -/
private theorem normalBasisLattice_augmentation (π : localBase v) (m : localExtension w)
    (hm : m ∈ normalBasisLattice v w)
    (hNorm : ∃ a ∈ normalBasisLattice v w,
      (algebraMap (localBase v) (localExtension w) π) * a = ∑ σ : localGalois v w, σ m) :
    ∃ y : localGalois v w → localExtension w,
      (∀ σ, y σ ∈ normalBasisLattice v w) ∧
      ∃ a ∈ normalBasisLattice v w,
        (algebraMap (localBase v) (localExtension w) π) * a =
          m - ∑ σ : localGalois v w, (σ (y σ) - y σ) := by
  classical
  let b := IsGalois.normalBasis (localBase v) (localExtension w)
  let c : localGalois v w → localBase v := fun σ => b.repr m σ
  let y : localGalois v w → localExtension w := fun σ => c σ • b 1
  have hy : ∀ σ, y σ ∈ normalBasisLattice v w := by
    intro σ
    exact normalBasisLattice_single_mem v w (c σ) (hm σ) 1
  obtain ⟨a, ha, hnorm⟩ := hNorm
  have hsum : (∑ σ : localGalois v w, c σ) = π * b.repr a 1 := by
    rw [← normalBasis_repr_sum_algEquiv m]
    rw [← hnorm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply]
    rfl
  let a₀ : localExtension w := (b.repr a 1) • b 1
  have ha₀ : a₀ ∈ normalBasisLattice v w :=
    normalBasisLattice_single_mem v w (b.repr a 1) (ha 1) 1
  refine ⟨y, hy, a₀, ha₀, ?_⟩
  have hσy : ∑ σ : localGalois v w, σ (y σ) = m := by
    conv_rhs => rw [← b.sum_repr m]
    apply Finset.sum_congr rfl
    intro σ hσ
    change σ.toLinearMap (c σ • b 1) = c σ • b σ
    rw [map_smul, σ.toLinearMap_apply, algEquiv_normalBasis σ 1, mul_one]
  have hY : ∑ σ : localGalois v w, y σ = (∑ σ : localGalois v w, c σ) • b 1 := by
    simp [y, Finset.sum_smul]
  rw [Finset.sum_sub_distrib, hσy]
  have hsub : m - (m - ∑ σ : localGalois v w, y σ) = ∑ σ : localGalois v w, y σ := by abel
  rw [hsub]
  rw [hY, hsum]
  simp [a₀, Algebra.smul_def, mul_assoc]
omit [IsGalois K L] in
/-- Fixedness of a filtered unit descends to its additive lattice coordinate. -/
private theorem _root_.SIC.UnitLattice.fixed_level_rep (D : UnitLattice (localExtension w))
    (hπfix : ∀ σ : localGalois v w, σ D.π = D.π)
    (i : ℕ) (x : (localExtension w)ˣ) (hx : x ∈ D.unitSubgroup i)
    (hfixed : ∀ σ : localGalois v w, σ • x = x) :
    ∃ m ∈ D.A, D.π ^ (D.k + 1 + i) * m = (x : localExtension w) - 1 ∧
      ∀ σ : localGalois v w, σ m = m := by
  obtain ⟨m, hm, heq⟩ := (D.mem_level i ((x : localExtension w) - 1)).mp hx
  refine ⟨m, hm, heq, ?_⟩
  intro σ
  have hfx : σ ((x : localExtension w) - 1) = (x : localExtension w) - 1 := by
    have h := congrArg (fun u : (localExtension w)ˣ => (u : localExtension w)) (hfixed σ)
    simpa [AlgEquiv.smul_units_def] using congrArg (fun u : localExtension w => u - 1) h
  have h : D.π ^ (D.k + 1 + i) * σ m = D.π ^ (D.k + 1 + i) * m := by
    calc
      D.π ^ (D.k + 1 + i) * σ m = σ (D.π ^ (D.k + 1 + i) * m) := by
        simp [hπfix]
      _ = D.π ^ (D.k + 1 + i) * m := by rw [heq, hfx]
  exact mul_left_cancel₀ (pow_ne_zero _ D.π_ne) h

/-- The norm of `1 + a` agrees with the sum of conjugates of `a` modulo the next level. -/
private theorem _root_.SIC.UnitLattice.norm_oneAdd_mod (D : UnitLattice (localExtension w))
    (hA : D.A = normalBasisLattice v w)
    (hπfix : ∀ σ : localGalois v w, σ D.π = D.π)
    (i : ℕ) (a : localExtension w) (ha : a ∈ D.scaledLevel i) :
    (((Representation.mulNorm (localGalois v w) (localExtension w)ˣ)
      (D.oneAdd i a ha) : (localExtension w)ˣ) : localExtension w) - 1 -
      ∑ σ : localGalois v w, σ a ∈ D.scaledLevel (i + 1) := by
  have hfa : ∀ σ : localGalois v w, σ a ∈ D.scaledLevel i := by
    intro σ
    exact D.scaledLevel_stable v w hA hπfix i σ a ha
  convert prod_one_add_mod (D.scaledLevel i) (D.scaledLevel (i + 1))
    (D.scaledLevel_antitone (Nat.le_succ i)) (fun a ha b hb => D.mul_level i ha hb)
    Finset.univ (fun σ : localGalois v w => σ a) (fun σ _ => hfa σ) using 1
  simp [Representation.mulNorm_apply, D.oneAdd_val,
    AlgEquiv.smul_units_def, map_add]

/-- The degree-zero correction in Serre's normal-basis unit filtration. -/
private theorem _root_.SIC.UnitLattice.zero_step (D : UnitLattice (localExtension w))
    (hA : D.A = normalBasisLattice v w)
    (hπfix : ∀ σ : localGalois v w, σ D.π = D.π)
    (i : ℕ) (x : (localExtension w)ˣ) (hx : x ∈ D.unitSubgroup i)
    (hfixed : ∀ σ : localGalois v w, σ • x = x) :
    ∃ y ∈ D.unitSubgroup i,
      x / (Representation.mulNorm (localGalois v w) (localExtension w)ˣ) y ∈
        D.unitSubgroup (i + 1) := by
  classical
  let A := D.A
  let B := D.scaledLevel i
  let C := D.scaledLevel (i + 1)
  let F := D.unitSubgroup
  have hCB : C ≤ B := D.scaledLevel_antitone (Nat.le_succ i)
  have hBC : ∀ a ∈ B, ∀ b ∈ B, a * b ∈ C :=
    fun a ha b hb => D.mul_level i ha hb
  obtain ⟨m, hm, heq, hfixm⟩ := D.fixed_level_rep v w hπfix i x hx hfixed
  have hm' : m ∈ normalBasisLattice v w := hA ▸ hm
  obtain ⟨m₀, hm₀, hsum⟩ := normalBasisLattice_fixed_sum v w m hm' hfixm
  have hm₀' : m₀ ∈ A := by simpa only [A, hA] using hm₀
  let a₀ : localExtension w := D.π ^ (D.k + 1 + i) * m₀
  have ha₀ : a₀ ∈ B := (D.mem_level i _).mpr ⟨m₀, hm₀', rfl⟩
  let y : (localExtension w)ˣ := D.oneAdd i a₀ ha₀
  have hy : y ∈ F i := D.oneAdd_mem i a₀ ha₀
  have hsum' : (∑ σ : localGalois v w, σ a₀) = (x : localExtension w) - 1 := by
    calc
      ∑ σ : localGalois v w, σ a₀ = D.π ^ (D.k + 1 + i) * ∑ σ : localGalois v w, σ m₀ := by
        simp [a₀, hπfix, Finset.mul_sum]
      _ = (x : localExtension w) - 1 := by rw [hsum, heq]
  have hlin : (((Representation.mulNorm (localGalois v w) (localExtension w)ˣ) y :
      (localExtension w)ˣ) : localExtension w) - 1 -
      (∑ σ : localGalois v w, σ a₀) ∈ C := D.norm_oneAdd_mod v w hA hπfix i a₀ ha₀
  have hdiff : (x : localExtension w) -
      ((Representation.mulNorm (localGalois v w) (localExtension w)ˣ) y :
        (localExtension w)ˣ) ∈ C := by
    convert C.neg_mem hlin using 1; rw [hsum']; ring
  have hnormV : (Representation.mulNorm (localGalois v w) (localExtension w)ˣ) y ∈ F i := by
    rw [Representation.mulNorm_apply]
    apply Subgroup.prod_mem
    intro σ _
    exact D.unitSubgroup_stable v w hA hπfix i σ y hy
  have hzin : (((Representation.mulNorm (localGalois v w) (localExtension w)ˣ) y)⁻¹ :
      (localExtension w)ˣ) ∈ F i :=
    (F i).inv_mem hnormV
  refine ⟨y, hy, ?_⟩
  exact div_mod_of_sub_mem B C hCB hBC x _ hzin hdiff

/-- Norm one makes the additive trace of a filtered unit vanish at the next level. -/
private theorem _root_.SIC.UnitLattice.norm_one_trace (D : UnitLattice (localExtension w))
    (hA : D.A = normalBasisLattice v w)
    (hπfix : ∀ σ : localGalois v w, σ D.π = D.π)
    (i : ℕ) (x : (localExtension w)ˣ) (hx : x ∈ D.unitSubgroup i)
    (hNormOne : (Representation.mulNorm (localGalois v w) (localExtension w)ˣ) x = 1) :
    (∑ σ : localGalois v w, σ ((x : localExtension w) - 1)) ∈ D.scaledLevel (i + 1) := by
  have hfa : ∀ σ : localGalois v w, σ ((x : localExtension w) - 1) ∈ D.scaledLevel i := by
    intro σ
    exact D.scaledLevel_stable v w hA hπfix i σ _ hx
  have hlin : (((Representation.mulNorm (localGalois v w) (localExtension w)ˣ) x :
      (localExtension w)ˣ) : localExtension w) - 1 -
      (∑ σ : localGalois v w, σ ((x : localExtension w) - 1)) ∈ D.scaledLevel (i + 1) := by
    convert prod_units_mod (D.scaledLevel i) (D.scaledLevel (i + 1))
      (D.scaledLevel_antitone (Nat.le_succ i)) (fun a ha b hb => D.mul_level i ha hb)
      Finset.univ (fun σ : localGalois v w => σ • x) (fun σ _ => by
        simpa [AlgEquiv.smul_units_def] using hfa σ) using 1
    simp [Representation.mulNorm_apply, AlgEquiv.smul_units_def, map_sub]
  have h := (D.scaledLevel (i + 1)).neg_mem hlin
  simpa [hNormOne] using h

/-! ### Successive quotients in degree −1 -/

omit [IsGalois K L] in
/-- Divisibility of a scaled additive trace descends to the normal-basis coordinate. -/
private theorem _root_.SIC.UnitLattice.trace_scale (D : UnitLattice (localExtension w))
    (hπfix : ∀ σ : localGalois v w, σ D.π = D.π)
    (i : ℕ) (x m : localExtension w)
    (heq : D.π ^ (D.k + 1 + i) * m = x)
    (htrace : (∑ σ : localGalois v w, σ x) ∈ D.scaledLevel (i + 1)) :
    ∃ a ∈ D.A, D.π * a = ∑ σ : localGalois v w, σ m := by
  have hsum : D.π ^ (D.k + 1 + i) * (∑ σ : localGalois v w, σ m) =
      ∑ σ : localGalois v w, σ x := by
    rw [← heq]
    simp [hπfix, Finset.mul_sum]
  obtain ⟨a, ha, haeq⟩ := (D.mem_level (i + 1) _).mp htrace
  refine ⟨a, ha, ?_⟩
  have h : D.π ^ (D.k + 1 + i) * (D.π * a) =
      D.π ^ (D.k + 1 + i) * (∑ σ : localGalois v w, σ m) := by
    rw [hsum, ← haeq]
    rw [show D.k + 1 + (i + 1) = (D.k + 1 + i) + 1 by omega, pow_succ]
    ring
  exact mul_left_cancel₀ (pow_ne_zero _ D.π_ne) h

/-- A single coboundary unit linearizes to `σ b - b` modulo the next level. -/
private theorem _root_.SIC.UnitLattice.coboundary_term_mod (D : UnitLattice (localExtension w))
    (hA : D.A = normalBasisLattice v w)
    (hπfix : ∀ σ : localGalois v w, σ D.π = D.π)
    (i : ℕ) (σ : localGalois v w) (b : localExtension w)
    (hb : b ∈ D.scaledLevel i) (y : (localExtension w)ˣ)
    (hy : y ∈ D.unitSubgroup i) (hval : (y : localExtension w) = 1 + b) :
    ((((σ • y) / y : (localExtension w)ˣ) : localExtension w) - 1) - (σ b - b) ∈
      D.scaledLevel (i + 1) := by
  have hσb := D.scaledLevel_stable v w hA hπfix i σ b hb
  have h := div_unit_linear_mod (D.scaledLevel i) (D.scaledLevel (i + 1))
    (fun a ha c hc => D.mul_level i ha hc) (σ • y) y
    (by simpa [AlgEquiv.smul_units_def, hval] using hσb)
    hy ((D.unitSubgroup i).inv_mem hy)
  convert h using 1
  simp [hval, AlgEquiv.smul_units_def, map_add]

/-- A product of coboundary units linearizes to the sum of additive coboundaries. -/
private theorem _root_.SIC.UnitLattice.coboundary_product_mod (D : UnitLattice (localExtension w))
    (hA : D.A = normalBasisLattice v w)
    (hπfix : ∀ σ : localGalois v w, σ D.π = D.π)
    (i : ℕ) (b : localGalois v w → localExtension w)
    (hb : ∀ σ, b σ ∈ D.scaledLevel i) (y : localGalois v w → (localExtension w)ˣ)
    (hy : ∀ σ, y σ ∈ D.unitSubgroup i)
    (hval : ∀ σ, (y σ : localExtension w) = 1 + b σ) :
    let z := ∏ σ : localGalois v w, (σ • y σ) / y σ
    z ∈ D.unitSubgroup i ∧
      (z : localExtension w) - 1 - ∑ σ, (σ (b σ) - b σ) ∈ D.scaledLevel (i + 1) := by
  classical
  intro z
  let B := D.scaledLevel i
  let C := D.scaledLevel (i + 1)
  let F := D.unitSubgroup
  have hz : z ∈ F i := by
    apply Subgroup.prod_mem
    intro σ _
    exact (F i).div_mem (D.unitSubgroup_stable v w hA hπfix i σ (y σ) (hy σ)) (hy σ)
  have hp := prod_units_mod B C (D.scaledLevel_antitone (Nat.le_succ i))
    (fun a ha c hc => D.mul_level i ha hc) Finset.univ
    (fun σ : localGalois v w => (σ • y σ) / y σ)
    (fun σ _ => (F i).div_mem
      (D.unitSubgroup_stable v w hA hπfix i σ (y σ) (hy σ)) (hy σ))
  have hs : (Finset.univ.sum (fun σ : localGalois v w =>
      ((((σ • y σ) / y σ : (localExtension w)ˣ) : localExtension w) - 1) -
        (σ (b σ) - b σ))) ∈ C :=
    C.sum_mem (fun σ _ => D.coboundary_term_mod v w hA hπfix i σ (b σ)
      (hb σ) (y σ) (hy σ) (hval σ))
  refine ⟨hz, ?_⟩
  convert C.add_mem hp hs using 1
  simp only [Finset.sum_sub_distrib]
  ring

omit [IsGalois K L] in
/-- The normal-basis augmentation relation survives scaling modulo the next lattice level. -/
private theorem _root_.SIC.UnitLattice.scaled_augmentation_mod (D : UnitLattice (localExtension w))
    (hπfix : ∀ σ : localGalois v w, σ D.π = D.π)
    (i : ℕ) (x : (localExtension w)ˣ) (m a : localExtension w)
    (mY : localGalois v w → localExtension w) (ha : a ∈ D.A)
    (heq : D.π ^ (D.k + 1 + i) * m = (x : localExtension w) - 1)
    (hres : D.π * a = m - ∑ σ, (σ (mY σ) - mY σ)) :
    (x : localExtension w) - 1 -
      ∑ σ : localGalois v w,
        (σ (D.π ^ (D.k + 1 + i) * mY σ) - D.π ^ (D.k + 1 + i) * mY σ) ∈
          D.scaledLevel (i + 1) := by
  have hresB : D.π ^ (D.k + 1 + i) * (D.π * a) ∈ D.scaledLevel (i + 1) := by
    apply (D.mem_level (i + 1) _).mpr
    refine ⟨a, ha, ?_⟩
    rw [show D.k + 1 + (i + 1) = (D.k + 1 + i) + 1 by omega, pow_succ]
    ring
  convert hresB using 1
  rw [← heq]
  calc
    D.π ^ (D.k + 1 + i) * m -
        ∑ σ : localGalois v w,
          (σ (D.π ^ (D.k + 1 + i) * mY σ) - D.π ^ (D.k + 1 + i) * mY σ) =
        D.π ^ (D.k + 1 + i) * (m - ∑ σ, (σ (mY σ) - mY σ)) := by
          simp [hπfix, Finset.mul_sum, Finset.sum_sub_distrib, mul_sub]
    _ = D.π ^ (D.k + 1 + i) * (D.π * a) := by rw [← hres]

/-- The degree-minus-one correction in Serre's normal-basis unit filtration. -/
private theorem _root_.SIC.UnitLattice.negOne_step (πK : localBase v)
    (D : UnitLattice (localExtension w))
    (hπ : D.π = algebraMap (localBase v) (localExtension w) πK)
    (hA : D.A = normalBasisLattice v w)
    (i : ℕ) (x : (localExtension w)ˣ) (hx : x ∈ D.unitSubgroup i)
    (hNormOne : (Representation.mulNorm (localGalois v w) (localExtension w)ˣ) x = 1) :
    ∃ y : localGalois v w → (localExtension w)ˣ,
      (∀ σ, y σ ∈ D.unitSubgroup i) ∧
      x / ∏ σ, (σ • y σ) / y σ ∈ D.unitSubgroup (i + 1) := by
  classical
  let A := D.A
  let B := D.scaledLevel i
  let C := D.scaledLevel (i + 1)
  let F := D.unitSubgroup
  have hπfix : ∀ σ : localGalois v w, σ D.π = D.π := by
    intro σ
    rw [hπ]
    exact AlgEquiv.commutes σ πK
  have hCB : C ≤ B := D.scaledLevel_antitone (Nat.le_succ i)
  have hBC : ∀ a ∈ B, ∀ b ∈ B, a * b ∈ C :=
    fun a ha b hb => D.mul_level i ha hb
  obtain ⟨m, hm, heq⟩ := (D.mem_level i ((x : localExtension w) - 1)).mp hx
  have htrace := D.norm_one_trace v w hA hπfix i x hx hNormOne
  have hsumM : ∃ a ∈ A, D.π * a = ∑ σ : localGalois v w, σ m :=
    D.trace_scale v w hπfix i ((x : localExtension w) - 1) m heq htrace
  have hm' : m ∈ normalBasisLattice v w := hA ▸ hm
  have hsumM' : ∃ a ∈ normalBasisLattice v w,
      (algebraMap (localBase v) (localExtension w) πK) * a =
        ∑ σ : localGalois v w, σ m := by
    simpa only [← hπ, ← hA] using hsumM
  obtain ⟨mY, hmY, a, ha, hres⟩ :=
    normalBasisLattice_augmentation v w πK m hm' hsumM'
  have hmY' : ∀ σ, mY σ ∈ A := fun σ => by simpa only [A, hA] using hmY σ
  have ha' : a ∈ A := by simpa only [A, hA] using ha
  rw [← hπ] at hres
  let b : localGalois v w → localExtension w := fun σ => D.π ^ (D.k + 1 + i) * mY σ
  have hb : ∀ σ, b σ ∈ B := by
    intro σ
    exact (D.mem_level i _).mpr ⟨mY σ, hmY' σ, rfl⟩
  let y : localGalois v w → (localExtension w)ˣ := fun σ => D.oneAdd i (b σ) (hb σ)
  have hy : ∀ σ, y σ ∈ F i := fun σ => D.oneAdd_mem i (b σ) (hb σ)
  have hval : ∀ σ, (y σ : localExtension w) = 1 + b σ :=
    fun σ => D.oneAdd_val i (b σ) (hb σ)
  let z : (localExtension w)ˣ := ∏ σ : localGalois v w, (σ • y σ) / y σ
  obtain ⟨hzV, hprodlin⟩ := D.coboundary_product_mod v w hA hπfix i b hb y hy hval
  have hxlin : (x : localExtension w) - 1 -
      ∑ σ : localGalois v w, (σ (b σ) - b σ) ∈ C := by
    simpa only [b] using D.scaled_augmentation_mod v w hπfix i x m a mY ha' heq hres
  have hdiff : (x : localExtension w) - (z : localExtension w) ∈ C := by
    have h := C.sub_mem hxlin hprodlin
    convert h using 1; ring
  refine ⟨y, hy, ?_⟩
  exact div_mod_of_sub_mem B C hCB hBC x z ((F i).inv_mem hzV) hdiff

/-! ### A cohomologically trivial subgroup -/

/-- The integral units $U_w$ contain a $\operatorname{Gal}(L_w/K_v)$-stable subgroup `V` of finite
index, open in $L_w^\times$, with $\widehat H^0(G, V) = \widehat H^{-1}(G, V) = 0$.
Serre, *Local class field theory*, in
Cassels–Fröhlich (1967), Chapter VI, §1.4, Proposition 3; Milne, *Class Field Theory*,
Chapter III, Lemma 2.4. -/
theorem exists_unitSubgroup_tateTrivial :
    ∃ (V : Subgroup (w.adicCompletion L)ˣ)
      (hV : ∀ σ : w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L,
        ∀ x ∈ V, σ • x ∈ V),
      V ≤ unitGroup w ∧ IsOpen (V : Set (w.adicCompletion L)ˣ) ∧
        (V.subgroupOf (unitGroup w)).FiniteIndex ∧
        Subsingleton
          (Representation.TateZero (Representation.subgroupSubrep V hV).toRepresentation) ∧
        Subsingleton
          (Representation.TateNegOne (Representation.subgroupSubrep V hV).toRepresentation) := by
  obtain ⟨πK, hπK0, hπK1⟩ := NormedField.exists_norm_lt_one (localBase v)
  let π : localExtension w := algebraMap (localBase v) (localExtension w) πK
  have he : 0 < w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) :=
    mul_pos (w.asIdeal.ramificationIdx_pos _) (w.asIdeal.inertiaDeg_pos _)
  have hπnorm : ‖π‖ = ‖πK‖ ^
      (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)) :=
    completionMap_norm v w πK
  have hπpos : 0 < ‖π‖ := by rw [hπnorm]; positivity
  have hπ1 : ‖π‖ < 1 := by
    rw [hπnorm]
    exact pow_lt_one₀ hπK0.le hπK1 he.ne'
  let A := normalBasisLattice v w
  have hπA : ∀ a ∈ A, π * a ∈ A := by
    intro a ha
    simpa only [Algebra.smul_def] using normalBasisLattice_smul v w πK hπK1.le a ha
  let D : UnitLattice (localExtension w) := UnitLattice.ofCompactOpen π hπpos hπ1 A
    (normalBasisLattice_isCompact v w) (normalBasisLattice_isOpen v w) hπA
  have hA : D.A = normalBasisLattice v w := by
    simp [D, UnitLattice.ofCompactOpen, A]
  have hπ : D.π = π := rfl
  have hπfix : ∀ σ : localGalois v w, σ D.π = D.π := by
    intro σ
    exact AlgEquiv.commutes σ πK
  let F := D.unitSubgroup
  have hstable : ∀ i (σ : localGalois v w), ∀ x ∈ F i, σ • x ∈ F i := by
    intro i σ x hx
    exact D.unitSubgroup_stable v w hA hπfix i σ x hx
  have hVU : F 0 ≤ unitGroup w := D.unitSubgroup_le_unitGroup w 0
  have hcompact : IsCompact (F 0 : Set (localExtension w)ˣ) :=
    (isCompact_unitGroup w).of_isClosed_subset (D.unitSubgroup_isClosed 0) hVU
  have hcomplete : Representation.IsCompleteFiltration F :=
    Representation.IsCompleteFiltration.of_isCompact (F := F)
      D.unitSubgroup_antitone D.unitSubgroup_isClosed hcompact D.unitSubgroup_separated
  have h0 : Subsingleton (Representation.TateZero
      (Representation.subgroupSubrep (F 0) (hstable 0)).toRepresentation) :=
    Representation.subsingleton_tateZero_of_isCompleteFiltration hcomplete hstable
      (D.zero_step v w hA hπfix)
  have h1 : Subsingleton (Representation.TateNegOne
      (Representation.subgroupSubrep (F 0) (hstable 0)).toRepresentation) :=
    Representation.subsingleton_tateNegOne_of_isCompleteFiltration hcomplete hstable
      (D.negOne_step v w πK hπ hA)
  exact ⟨F 0, hstable 0, hVU, D.unitSubgroup_isOpen 0,
    finiteIndex_subgroupOf_unitGroup w (V := F 0) (D.unitSubgroup_isOpen 0), h0, h1⟩

/-! ### The Herbrand quotient -/

/-- For cyclic $L_w/K_v$ the integral units have a Herbrand quotient. Serre, *Local class field
theory*, in Cassels–Fröhlich (1967), Chapter VI, §1.4, Corollary 1. -/
theorem hasHerbrandQuotient_unitGroupSubrep
    [IsCyclic (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)] :
    Representation.HasHerbrandQuotient (unitGroupSubrep v w).toRepresentation := by
  obtain ⟨V, hV, hVU, _hopen, hindex, h₀, h₁⟩ := exists_unitSubgroup_tateTrivial v w
  exact (Representation.hasHerbrandQuotient_subgroupSubrep_iff hV
    (fun σ _ hx => smul_mem_unitGroup v w σ hx) hVU hindex).mp
    (Representation.hasHerbrandQuotient_of_subsingleton _ h₀ h₁)

/-- For cyclic $L_w/K_v$, $h(U_w) = 1$. Serre, *Local class field theory*, in Cassels–Fröhlich
(1967), Chapter VI, §1.4, Corollary 1; Milne, *Class Field Theory*, Chapter III, Lemma 2.5. -/
theorem herbrandQuotient_unitGroupSubrep
    [IsCyclic (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)] :
    Representation.herbrandQuotient (unitGroupSubrep v w).toRepresentation = 1 := by
  obtain ⟨V, hV, hVU, _hopen, hindex, h₀, h₁⟩ := exists_unitSubgroup_tateTrivial v w
  calc
    Representation.herbrandQuotient (unitGroupSubrep v w).toRepresentation =
        Representation.herbrandQuotient (Representation.subgroupSubrep V hV).toRepresentation :=
      (Representation.herbrandQuotient_subgroupSubrep_eq hV
        (fun σ _ hx => smul_mem_unitGroup v w σ hx) hVU hindex).symm
    _ = 1 := Representation.herbrandQuotient_eq_one_of_subsingleton _ h₀ h₁

end FinitePlace

end SIC
