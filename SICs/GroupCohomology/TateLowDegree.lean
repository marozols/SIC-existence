/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Tate cohomology in degrees zero and minus one

The explicit Tate groups $\widehat H^0(G, V) = V^G / N_G V$ and
$\widehat H^{-1}(G, V) = \ker N_G / I_G V$ of a representation of a finite group, their
functoriality along intertwining maps such as the inclusions of subrepresentations, and their
invariance under equivalences and under reindexing of the acting group.

This module follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter II, §3, where Tate's
groups in degrees $0$ and $-1$ are defined by these formulas. The explicit groups carry the
Herbrand quotient of `SICs.GroupCohomology.Herbrand` and the norm-residue descriptions of
the idèle class groups.

## The argument

For $g' \in G$ the elements $g'g$ and $gg'$ run through `G` with `g`, so
$g' N_G(v) = N_G(v) = N_G(g' v)$ for the norm $N_G = \sum_{g \in G} g$. Hence $N_G V \subseteq V^G$
and $N_G$ vanishes on the augmentation submodule $I_G V$ spanned by the $gv - v$ (Mathlib's
`Representation.Coinvariants.ker`), so `TateZero` and `TateNegOne` are defined. An intertwining
map commutes with $N_G$ and with every $g$, so it maps invariants to invariants, kernels of norms
to kernels of norms, augmentation submodules into augmentation submodules, and norms into norms;
it therefore induces maps of both quotients, functorially. The inclusion of a subrepresentation
is such a map.
-/

noncomputable section

namespace SIC

namespace Representation

variable {k G V W U : Type*} [CommRing k] [Group G] [Fintype G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
  (ρ : _root_.Representation k G V) (σ : _root_.Representation k G W)
  (τ : _root_.Representation k G U)

/-! ### The two Tate groups

The norm lands in the invariants and kills the augmentation submodule; the quotients are the Tate
groups in degrees $0$ and $-1$. -/

/-- The norm lands in the invariants: $N_G V \subseteq V^G$. Milne, *Class Field Theory*,
Chapter II, §3. -/
theorem range_norm_le_invariants : LinearMap.range ρ.norm ≤ ρ.invariants := by
  rintro x ⟨v, rfl⟩
  exact (ρ.mem_invariants _).2 fun g ↦ ρ.self_norm_apply g v

/-- The norm vanishes on the augmentation submodule: $I_G V \subseteq \ker N_G$. Milne,
*Class Field Theory*, Chapter II, §3. -/
theorem coinvariantsKer_le_ker_norm :
    _root_.Representation.Coinvariants.ker ρ ≤ LinearMap.ker ρ.norm := by
  apply Submodule.span_le.mpr
  rintro x ⟨⟨g, v⟩, rfl⟩
  simp [ρ.norm_self_apply]

/-- The norms $N_G V$, as a submodule of the invariants $V^G$. -/
def normSubmodule : Submodule k ρ.invariants :=
  (LinearMap.range ρ.norm).comap ρ.invariants.subtype

/-- The augmentation submodule $I_G V$, as a submodule of the kernel of the norm. -/
def augmentationSubmodule : Submodule k (LinearMap.ker ρ.norm) :=
  (_root_.Representation.Coinvariants.ker ρ).comap (LinearMap.ker ρ.norm).subtype

/-- The Tate group $\widehat H^0(G, V) = V^G / N_G V$. Milne, *Class Field Theory*, Chapter II,
§3. -/
abbrev TateZero := ρ.invariants ⧸ normSubmodule ρ

/-- The Tate group $\widehat H^{-1}(G, V) = \ker N_G / I_G V$. Milne, *Class Field Theory*,
Chapter II, §3. -/
abbrev TateNegOne := LinearMap.ker ρ.norm ⧸ augmentationSubmodule ρ

/-- An invariant vector has trivial class in $\widehat H^0$ exactly when it is a norm. -/
theorem TateZero.mk_eq_zero_iff (x : ρ.invariants) :
    (Submodule.Quotient.mk x : TateZero ρ) = 0 ↔ (x : V) ∈ LinearMap.range ρ.norm := by
  exact (Submodule.Quotient.mk_eq_zero _).trans Submodule.mem_comap

/-- A vector of norm zero has trivial class in $\widehat H^{-1}$ exactly when it lies in the
augmentation submodule $I_G V$. -/
theorem TateNegOne.mk_eq_zero_iff (x : LinearMap.ker ρ.norm) :
    (Submodule.Quotient.mk x : TateNegOne ρ) = 0 ↔
      (x : V) ∈ _root_.Representation.Coinvariants.ker ρ := by
  exact (Submodule.Quotient.mk_eq_zero _).trans Submodule.mem_comap

/-- The augmentation submodule $I_G V$ consists of the sums $\sum_g (g y_g - y_g)$ with one
term for each `g ∈ G`. Milne, *Class Field Theory*, Chapter II, §3. -/
theorem mem_coinvariantsKer_iff_exists_sum (x : V) :
    x ∈ _root_.Representation.Coinvariants.ker ρ ↔ ∃ y : G → V, ∑ g, (ρ g (y g) - y g) = x := by
  classical
  let d : (G → V) →ₗ[k] V := {
    toFun := fun y => ∑ g : G, (ρ g (y g) - y g)
    map_add' := by
      intro y z
      simp only [Pi.add_apply, map_add, add_sub_add_comm, Finset.sum_add_distrib]
    map_smul' := by
      intro c y
      simp [Pi.smul_apply, smul_sub, Finset.smul_sum]
  }
  have hd : LinearMap.range d = _root_.Representation.Coinvariants.ker ρ := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      change (∑ g : G, (ρ g (y g) - y g)) ∈ _root_.Representation.Coinvariants.ker ρ
      apply Submodule.sum_mem
      intro g _
      exact _root_.Representation.Coinvariants.sub_mem_ker g (y g)
    · apply Submodule.span_le.mpr
      rintro x ⟨⟨g, v⟩, rfl⟩
      refine ⟨fun h => if h = g then v else 0, ?_⟩
      change (∑ h : G, (ρ h (if h = g then v else 0) - (if h = g then v else 0))) =
        ρ g v - v
      simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      congr 1
      calc
        (∑ h : G, ρ h (if h = g then v else 0)) =
            ∑ h : G, if h = g then ρ h v else 0 := by
              apply Finset.sum_congr rfl
              intro h _
              split_ifs <;> simp
        _ = ρ g v := by simp
  rw [← hd]
  rfl

/-! ### Functoriality

An intertwining map preserves invariants, norms, kernels of norms, and augmentation submodules,
and so induces maps of the Tate groups. -/

variable {ρ σ τ}

/-- An intertwining map commutes with the norms: $f(N_G v) = N_G f(v)$. -/
theorem IntertwiningMap.map_norm (f : ρ.IntertwiningMap σ) (v : V) :
    f (ρ.norm v) = σ.norm (f v) := by
  simp [_root_.Representation.norm, f.isIntertwining]

/-- The restriction of an intertwining map to the invariants. -/
def IntertwiningMap.invariantsMap (f : ρ.IntertwiningMap σ) : ρ.invariants →ₗ[k] σ.invariants :=
  f.toLinearMap.restrict fun v hv g ↦ by
    change σ g (f v) = f v
    rw [← f.isIntertwining, (ρ.mem_invariants v).mp hv g]

/-- The restriction of an intertwining map to the kernels of the norms. -/
def IntertwiningMap.kerNormMap (f : ρ.IntertwiningMap σ) :
    LinearMap.ker ρ.norm →ₗ[k] LinearMap.ker σ.norm :=
  f.toLinearMap.restrict fun v hv ↦ by
    change σ.norm (f v) = 0
    rw [← IntertwiningMap.map_norm f v, LinearMap.mem_ker.mp hv, map_zero]

/-- The map $\widehat H^0(G, V) \to \widehat H^0(G, W)$ induced by an intertwining map. -/
def TateZero.map (f : ρ.IntertwiningMap σ) : TateZero ρ →ₗ[k] TateZero σ :=
  (normSubmodule ρ).mapQ (normSubmodule σ) (IntertwiningMap.invariantsMap f) fun x hx ↦ by
    obtain ⟨v, hv⟩ : (x : V) ∈ LinearMap.range ρ.norm := hx
    change (f (x : V)) ∈ LinearMap.range σ.norm
    exact ⟨f v, by rw [← IntertwiningMap.map_norm f v, ← hv]⟩

/-- The map $\widehat H^{-1}(G, V) \to \widehat H^{-1}(G, W)$ induced by an intertwining map. -/
def TateNegOne.map (f : ρ.IntertwiningMap σ) : TateNegOne ρ →ₗ[k] TateNegOne σ :=
  (augmentationSubmodule ρ).mapQ (augmentationSubmodule σ) (IntertwiningMap.kerNormMap f)
    fun x hx ↦ by
    change (x : V) ∈ _root_.Representation.Coinvariants.ker ρ at hx
    change f (x : V) ∈ _root_.Representation.Coinvariants.ker σ
    have h : _root_.Representation.Coinvariants.ker ρ ≤
        (_root_.Representation.Coinvariants.ker σ).comap f.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g, v⟩, rfl⟩
      change f (ρ g v - v) ∈ _root_.Representation.Coinvariants.ker σ
      simpa only [map_sub, f.isIntertwining] using
        _root_.Representation.Coinvariants.sub_mem_ker (ρ := σ) g (f v)
    exact h hx

/-- Linear maps out of $\widehat H^0$ agree if they agree on invariant-vector classes. -/
@[ext (iff := false)] theorem TateZero.hom_ext {f g : TateZero ρ →ₗ[k] TateZero σ}
    (h : ∀ x : ρ.invariants,
      f (Submodule.Quotient.mk x) = g (Submodule.Quotient.mk x)) : f = g := by
  apply Submodule.linearMap_qext (normSubmodule ρ)
  ext x
  exact h x

/-- Linear maps out of $\widehat H^{-1}$ agree if they agree on norm-kernel classes. -/
@[ext (iff := false)] theorem TateNegOne.hom_ext {f g : TateNegOne ρ →ₗ[k] TateNegOne σ}
    (h : ∀ x : LinearMap.ker ρ.norm,
      f (Submodule.Quotient.mk x) = g (Submodule.Quotient.mk x)) : f = g := by
  apply Submodule.linearMap_qext (augmentationSubmodule ρ)
  ext x
  exact h x

/-- The identity induces the identity on $\widehat H^0$. -/
@[simp]
theorem TateZero.map_id :
    TateZero.map (_root_.Representation.IntertwiningMap.id ρ) = LinearMap.id := by
  apply TateZero.hom_ext
  intro x
  rfl

/-- Induced maps on $\widehat H^0$ compose. -/
theorem TateZero.map_comp (f : σ.IntertwiningMap τ) (g : ρ.IntertwiningMap σ) :
    TateZero.map (f.comp g) = TateZero.map f ∘ₗ TateZero.map g := by
  apply TateZero.hom_ext
  intro x
  rfl

/-- The identity induces the identity on $\widehat H^{-1}$. -/
@[simp]
theorem TateNegOne.map_id :
    TateNegOne.map (_root_.Representation.IntertwiningMap.id ρ) = LinearMap.id := by
  apply TateNegOne.hom_ext
  intro x
  rfl

/-- Induced maps on $\widehat H^{-1}$ compose. -/
theorem TateNegOne.map_comp (f : σ.IntertwiningMap τ) (g : ρ.IntertwiningMap σ) :
    TateNegOne.map (f.comp g) = TateNegOne.map f ∘ₗ TateNegOne.map g := by
  apply TateNegOne.hom_ext
  intro x
  rfl

/-! An equivariant equivalence, including reindexing by an isomorphism of finite groups, induces
equivalences of both Tate groups. -/

section Transport

variable {H : Type*} [Group H] [Fintype H]

/-! ### Reindexing the acting group

An isomorphism of finite groups leaves the invariant vectors, norm, and augmentation span
unchanged. These are the numerator and denominator data for the two Tate quotients. -/

omit [Fintype G] [Fintype H] in
/-- Reindexing the action by a group isomorphism leaves its invariants unchanged; used by
`tateZeroCompEquiv`. Milne, *Class Field Theory*, Chapter II, §§1 and 3. -/
theorem invariants_comp_equiv (τ : _root_.Representation k H V) (e : G ≃* H) :
    _root_.Representation.invariants (τ.comp e.toMonoidHom) = τ.invariants := by
  ext v
  change (∀ g : G, τ (e g) v = v) ↔ (∀ h : H, τ h v = v)
  constructor
  · intro hv h
    obtain ⟨g, rfl⟩ := e.surjective h
    exact hv g
  · intro hv g
    exact hv (e g)

/-- Reindexing the action by a group isomorphism leaves its norm unchanged; used by both
`tateZeroCompEquiv` and `tateNegOneCompEquiv`. Milne, *Class Field Theory*, Chapter II, §3. -/
theorem norm_comp_equiv (τ : _root_.Representation k H V) (e : G ≃* H) :
    _root_.Representation.norm (τ.comp e.toMonoidHom) = τ.norm := by
  ext v
  simp only [_root_.Representation.norm, LinearMap.sum_apply]
  exact e.toEquiv.sum_comp (fun h : H => τ h v)

omit [Fintype G] [Fintype H] in
/-- Reindexing the action by a group isomorphism leaves its augmentation submodule unchanged;
used by `tateNegOneCompEquiv`. Milne, *Class Field Theory*, Chapter II, §3. -/
theorem coinvariantsKer_comp_equiv (τ : _root_.Representation k H V) (e : G ≃* H) :
    _root_.Representation.Coinvariants.ker (τ.comp e.toMonoidHom) =
      _root_.Representation.Coinvariants.ker τ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨⟨g, v⟩, rfl⟩
    exact _root_.Representation.Coinvariants.sub_mem_ker (ρ := τ) (e g) v
  · apply Submodule.span_le.mpr
    rintro x ⟨⟨h, v⟩, rfl⟩
    obtain ⟨g, rfl⟩ := e.surjective h
    exact _root_.Representation.Coinvariants.sub_mem_ker (ρ := τ.comp e.toMonoidHom) g v

/-- Equal numerator and denominator submodules induce the quotient equivalence used by
`tateZeroCompEquiv` and `tateNegOneCompEquiv`. -/
private def quotientComapEquiv (P Q R S : Submodule k V) (hP : P = Q) (hR : R = S) :
    (P ⧸ R.comap P.subtype) ≃ₗ[k] (Q ⧸ S.comap Q.subtype) := by
  cases hP
  cases hR
  exact LinearEquiv.refl k _

/-! ### Equivalences of Tate groups

An intertwining equivalence and its inverse act on both quotients; for a group isomorphism,
the preceding equalities give the quotient equivalences directly. -/

/-- An equivalence of representations induces an equivalence of degree-zero Tate groups. -/
def tateZeroEquiv (e : ρ.Equiv σ) : TateZero ρ ≃ₗ[k] TateZero σ := by
  apply LinearEquiv.ofLinearMap (TateZero.map e.toIntertwiningMap)
    (TateZero.map e.symm.toIntertwiningMap)
  · rw [← TateZero.map_comp, ← _root_.Representation.Equiv.toIntertwiningMap_trans,
      e.symm_trans, _root_.Representation.Equiv.toIntertwiningMap_refl, TateZero.map_id]
  · rw [← TateZero.map_comp, ← _root_.Representation.Equiv.toIntertwiningMap_trans,
      e.trans_symm, _root_.Representation.Equiv.toIntertwiningMap_refl, TateZero.map_id]

/-- An equivalence of representations induces an equivalence of degree-minus-one Tate groups. -/
def tateNegOneEquiv (e : ρ.Equiv σ) : TateNegOne ρ ≃ₗ[k] TateNegOne σ := by
  apply LinearEquiv.ofLinearMap (TateNegOne.map e.toIntertwiningMap)
    (TateNegOne.map e.symm.toIntertwiningMap)
  · rw [← TateNegOne.map_comp, ← _root_.Representation.Equiv.toIntertwiningMap_trans,
      e.symm_trans, _root_.Representation.Equiv.toIntertwiningMap_refl, TateNegOne.map_id]
  · rw [← TateNegOne.map_comp, ← _root_.Representation.Equiv.toIntertwiningMap_trans,
      e.trans_symm, _root_.Representation.Equiv.toIntertwiningMap_refl, TateNegOne.map_id]

/-- Reindexing the acting group preserves the degree-zero Tate group. -/
def tateZeroCompEquiv (τ : _root_.Representation k H V) (e : G ≃* H) :
    TateZero (τ.comp e.toMonoidHom) ≃ₗ[k] TateZero τ := by
  exact quotientComapEquiv
    (_root_.Representation.invariants (τ.comp e.toMonoidHom)) τ.invariants
    (LinearMap.range (_root_.Representation.norm (τ.comp e.toMonoidHom)))
    (LinearMap.range τ.norm) (invariants_comp_equiv τ e)
    (congrArg LinearMap.range (norm_comp_equiv τ e))

/-- Reindexing the acting group preserves the degree-minus-one Tate group. -/
def tateNegOneCompEquiv (τ : _root_.Representation k H V) (e : G ≃* H) :
    TateNegOne (τ.comp e.toMonoidHom) ≃ₗ[k] TateNegOne τ := by
  exact quotientComapEquiv
    (LinearMap.ker (_root_.Representation.norm (τ.comp e.toMonoidHom)))
    (LinearMap.ker τ.norm)
    (_root_.Representation.Coinvariants.ker (τ.comp e.toMonoidHom))
    (_root_.Representation.Coinvariants.ker τ)
    (congrArg LinearMap.ker (norm_comp_equiv τ e)) (coinvariantsKer_comp_equiv τ e)

end Transport

end Representation

end SIC
