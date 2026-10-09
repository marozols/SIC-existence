/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.GroupCohomology.Herbrand
import SICs.RepresentationTheory.PermutedFamily
import Mathlib.RepresentationTheory.Coinduced

/-!
# Shapiro's lemma in degrees zero and minus one

For a subgroup `S` of a finite group `G` and a representation `A` of `S`, the Tate groups of the
coinduced representation $\operatorname{Coind}_S^G A$ in degrees $0$ and $-1$ are those of `A`.
The same comparison applies to transitive families of permuted component spaces.

This is Shapiro's lemma, Milne, *Class Field Theory*, version 4.03 (2020), Chapter II,
Proposition 1.11, in the degrees $0$ and $-1$ of the Tate groups, where it holds by Chapter II,
§3 (after Proposition 3.1). The coinduced representation is Mathlib's
`Representation.coind S.subtype`: the functions $f : G \to A$ with $f(s g) = s f(g)$ for
$s \in S$, on which `G` acts by $(g f)(x) = f(x g)$; this is Milne's $\operatorname{Ind}_S^G A$
(Chapter II, §1). It computes the cohomology of the semi-local modules
$\prod_{w \mid v} L_w^\times$ (Milne, Chapter VII, Propositions 2.2 and 2.3).

## The argument

Fix representatives `t` of the right cosets $S t$ of `S` in `G`. A function in
$\operatorname{Coind}_S^G A$ is determined by its values $f(t)$, which are arbitrary, and
$\sum_{g \in G} f(g) = \sum_t N_S f(t) = N_S \sum_t f(t)$.

*Degree $0$.* A `G`-invariant `f` satisfies $f(x g) = f(x)$, so it is the constant $f(1)$, which
is `S`-invariant; conversely every $a \in A^S$ is a constant function in the coinduced module.
Evaluation at `1` therefore identifies the invariants. The norm $N_G f$ is the constant
$\sum_g f(g) = N_S \sum_t f(t)$; as the $f(t)$ are arbitrary, evaluation at `1` maps the norms
$N_G \operatorname{Coind}_S^G A$ onto $N_S A$, and so induces
$\widehat H^0(G, \operatorname{Coind}_S^G A) \cong \widehat H^0(S, A)$.

*Degree $-1$.* The map $f \mapsto \sum_t f(t)$ is well defined modulo $I_S A$, because changing
`t` to `s t` changes $f(t)$ to $s f(t) \equiv f(t)$; it sends $\ker N_G$ into $\ker N_S$, by the
norm formula above, and $I_G \operatorname{Coind}_S^G A$ into $I_S A$, because right
multiplication by `g` permutes the right cosets. In the other direction, $a \in A$ goes to the
function $f_a$ supported on `S` with $f_a(s) = s a$; then $g f_{a} - f_a$ for $g \in S$ is
$f_{g a - a}$, and every `f` is $\sum_t t^{-1} f_{f(t)} \equiv f_{\sum_t f(t)}$ modulo
$I_G \operatorname{Coind}_S^G A$. The two maps are mutually inverse on the quotients.
-/

noncomputable section

namespace SIC

namespace Representation

variable {k G A : Type*} [CommRing k] [Group G] [AddCommGroup A] [Module k A]
  (S : Subgroup G) (σ : _root_.Representation k S A)

/-! ### Degree zero -/

/-- Evaluation at `1` on the invariants of the coinduced representation:
$(\operatorname{Coind}_S^G A)^G \to A^S$, $f \mapsto f(1)$. -/
def coindInvariantsEval :
    (_root_.Representation.coind S.subtype σ).invariants →ₗ[k] σ.invariants where
  toFun f := ⟨((f : _root_.Representation.coindV S.subtype σ) : G → A) 1, by
    apply (σ.mem_invariants _).2
    intro s
    have hs := (_root_.Representation.mem_coindV S.subtype σ _).1 f.1.2 s 1
    have hi := ((_root_.Representation.coind S.subtype σ).mem_invariants f.1).1 f.2 (s : G)
    have hv := congrArg (fun x : _root_.Representation.coindV S.subtype σ => (x : G → A) 1) hi
    change (f.1 : G → A) (1 * (s : G)) = (f.1 : G → A) 1 at hv
    simpa using hs.symm.trans (by simpa using hv)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [Fintype G] [Fintype S]

/-- Finiteness of the right coset space, used by the two Tate isomorphisms. -/
noncomputable local instance cosetFintype :
    Fintype (Quotient (QuotientGroup.rightRel S)) := Fintype.ofFinite _


/-- Representatives of right cosets, with `1` chosen for the coset `S`; used by the two Tate
isomorphisms. -/
private def cosetRep (q : Quotient (QuotientGroup.rightRel S)) : G := by
  classical
  exact if q = Quotient.mk'' (1 : G) then 1 else q.out

omit [Fintype G] [Fintype S] in
/-- A chosen representative belongs to its coset; used by `cosetEquiv`. -/
private theorem cosetRep_mk (q : Quotient (QuotientGroup.rightRel S)) :
    (Quotient.mk'' (cosetRep S q) : Quotient (QuotientGroup.rightRel S)) = q := by
  classical
  by_cases h : q = Quotient.mk'' (1 : G)
  · simp [cosetRep, h]
  · simp [cosetRep, h]

/-- Representatives of the right cosets identify `S × (S \\ G)` with `G`; used by
`tateZeroCoindEquiv` and `tateNegOneCoindEquiv`. -/
private def cosetEquiv : S × Quotient (QuotientGroup.rightRel S) ≃ G where
  toFun p := p.1.1 * cosetRep S p.2
  invFun g :=
    let q : Quotient (QuotientGroup.rightRel S) := Quotient.mk'' g
    (⟨g * (cosetRep S q)⁻¹, QuotientGroup.rightRel_apply.mp
      (Quotient.exact (cosetRep_mk S q))⟩, q)
  left_inv := by
    rintro ⟨s, q⟩
    have hq : (Quotient.mk'' (s.1 * cosetRep S q) :
        Quotient (QuotientGroup.rightRel S)) = q := by
      apply Eq.trans (b := (Quotient.mk'' (cosetRep S q) :
        Quotient (QuotientGroup.rightRel S)))
      · exact Quotient.sound (QuotientGroup.rightRel_apply.2 (by simp))
      · exact cosetRep_mk S q
    apply Prod.ext
    · apply Subtype.ext
      dsimp
      rw [hq]
      simp
    · exact hq
  right_inv := by
    intro g
    dsimp
    simp

/-- Sum over right coset representatives, used by `tateZeroCoindEquiv` and
`tateNegOneCoindEquiv`. -/
private def coindSum : _root_.Representation.coindV S.subtype σ →ₗ[k] A :=
  (∑ q : Quotient (QuotientGroup.rightRel S),
    (LinearMap.proj (cosetRep S q) : (G → A) →ₗ[k] A)).comp
    (_root_.Representation.coindV S.subtype σ).subtype

/-- The norm of a coinduced function, evaluated at `1`, is the subgroup norm of its sum over
right coset representatives; used by both Tate isomorphisms. -/
private theorem coind_norm_one (f : _root_.Representation.coindV S.subtype σ) :
    (((_root_.Representation.coind S.subtype σ).norm f :
      _root_.Representation.coindV S.subtype σ) : G → A) 1 = σ.norm (coindSum S σ f) := by
  let Q := Quotient (QuotientGroup.rightRel S)
  have h₁ : (((_root_.Representation.coind S.subtype σ).norm f :
      _root_.Representation.coindV S.subtype σ) : G → A) 1 = ∑ g : G, (f : G → A) g := by
    simp only [_root_.Representation.norm, LinearMap.sum_apply]
    simp only [Submodule.coe_sum, Finset.sum_apply]
    change (∑ g : G, (f : G → A) (1 * g)) = _
    simp
  have h₂ : (∑ g : G, (f : G → A) g) =
      ∑ q : Q, ∑ s : S, σ s ((f : G → A) (cosetRep S q)) := by
    calc
      _ = ∑ p : S × Q, (f : G → A) ((cosetEquiv S) p) :=
        ((cosetEquiv S).sum_comp (fun g => (f : G → A) g)).symm
      _ = ∑ q : Q, ∑ s : S, σ s ((f : G → A) (cosetRep S q)) := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro q _
        apply Finset.sum_congr rfl
        intro s _
        exact (_root_.Representation.mem_coindV S.subtype σ _).1 f.2 s (cosetRep S q)
  rw [h₁, h₂]
  simp only [coindSum, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.proj_apply,
    Submodule.subtype_apply]
  change (∑ q : Q, ∑ s : S, σ s ((f : G → A) (cosetRep S q))) =
    σ.norm (∑ q : Q, (f : G → A) (cosetRep S q))
  simp only [_root_.Representation.norm, LinearMap.sum_apply, map_sum]

/-- The coinduced function supported on `S`, taking `s` to `σ s a`; used by both Tate
isomorphisms. -/
private def coindDelta : A →ₗ[k] _root_.Representation.coindV S.subtype σ := by
  classical
  refine (LinearMap.pi fun g : G => if h : g ∈ S then σ ⟨g, h⟩ else 0).codRestrict _ ?_
  intro a
  apply (_root_.Representation.mem_coindV S.subtype σ _).2
  intro s g
  by_cases hg : g ∈ S
  · have hsg : (s : G) * g ∈ S := S.mul_mem s.2 hg
    simp only [LinearMap.pi_apply]
    simpa [hsg, hg, map_mul] using congrArg (fun t : S => σ t a)
      (show (⟨(s : G) * g, hsg⟩ : S) = s * ⟨g, hg⟩ from Subtype.ext rfl)
  · have hsg : ¬(s : G) * g ∈ S := fun h => hg ((S.mul_mem_cancel_left s.2).mp h)
    simp only [LinearMap.pi_apply]
    simp [hsg, hg]

omit [Fintype G] [Fintype S] in
/-- The chosen representative lies in `S` only for the identity coset; used by
`coindSum_delta`. -/
private theorem cosetRep_mem_iff (q : Quotient (QuotientGroup.rightRel S)) :
    cosetRep S q ∈ S ↔ q = Quotient.mk'' (1 : G) := by
  constructor
  · intro h
    calc
      q = Quotient.mk'' (cosetRep S q) := (cosetRep_mk S q).symm
      _ = Quotient.mk'' (1 : G) := Quotient.sound
        (QuotientGroup.rightRel_apply.2 (by simpa using S.inv_mem h))
  · intro h
    subst q
    simp [cosetRep]

omit [Fintype S] in
/-- Summing the function supported on `S` recovers its value at `1`; used by both Tate
isomorphisms. -/
private theorem coindSum_delta (a : A) : coindSum S σ (coindDelta S σ a) = a := by
  classical
  simp only [coindSum, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.proj_apply,
    Submodule.subtype_apply]
  change (∑ q : Quotient (QuotientGroup.rightRel S),
    ((coindDelta S σ a : _root_.Representation.coindV S.subtype σ) : G → A)
      (cosetRep S q)) = a
  rw [Finset.sum_eq_single (Quotient.mk'' (1 : G))]
  · simp only [coindDelta, cosetRep, ite_true, LinearMap.codRestrict_apply,
      LinearMap.pi_apply, Subgroup.one_mem, dite_true]
    change σ (1 : S) a = a
    simp
  · intro q _ hq
    have h : cosetRep S q ∉ S := fun hs => hq ((cosetRep_mem_iff S q).mp hs)
    simp [coindDelta, h]
  · simp

omit [Fintype G] [Fintype S] in
/-- Evaluation at `1` identifies the invariant coinduced functions with `A^S`; used by
`tateZeroCoindEquiv`. -/
private theorem coindInvariantsEval_bijective : Function.Bijective (coindInvariantsEval S σ) := by
  constructor
  · intro f g h
    apply Subtype.ext
    apply Subtype.ext
    funext x
    have hf := ((_root_.Representation.coind S.subtype σ).mem_invariants f.1).1 f.2 x
    have hg := ((_root_.Representation.coind S.subtype σ).mem_invariants g.1).1 g.2 x
    have hfx := congrArg
      (fun v : _root_.Representation.coindV S.subtype σ => (v : G → A) 1) hf
    have hgx := congrArg
      (fun v : _root_.Representation.coindV S.subtype σ => (v : G → A) 1) hg
    change (f.1 : G → A) (1 * x) = (f.1 : G → A) 1 at hfx
    change (g.1 : G → A) (1 * x) = (g.1 : G → A) 1 at hgx
    simpa using hfx.trans ((congrArg Subtype.val h).trans hgx.symm)
  · intro a
    let v : _root_.Representation.coindV S.subtype σ :=
      ⟨fun _ => (a : A), (_root_.Representation.mem_coindV S.subtype σ _).2
        (fun s _ => (((σ.mem_invariants a.1).1 a.2 s).symm))⟩
    have hv : v ∈ (_root_.Representation.coind S.subtype σ).invariants := by
      apply ((_root_.Representation.coind S.subtype σ).mem_invariants v).2
      intro g
      apply Subtype.ext
      funext x
      rfl
    exact ⟨⟨v, hv⟩, rfl⟩

/-- Evaluation as a linear equivalence of invariants; used by `tateZeroCoindEquiv`. -/
private def coindInvariantsEquiv :
    (_root_.Representation.coind S.subtype σ).invariants ≃ₗ[k] σ.invariants :=
  LinearEquiv.ofBijective (coindInvariantsEval S σ) (coindInvariantsEval_bijective S σ)

/-- Evaluation carries the norm submodule onto the subgroup norm submodule; used by
`tateZeroCoindEquiv`. -/
private theorem coindNormSubmodule_map :
    Submodule.map (coindInvariantsEquiv S σ).toLinearMap
      (normSubmodule (_root_.Representation.coind S.subtype σ)) = normSubmodule σ := by
  let ρ := _root_.Representation.coind S.subtype σ
  let e : ρ.invariants ≃ₗ[k] σ.invariants := coindInvariantsEquiv S σ
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨v, hv⟩ : (x : _root_.Representation.coindV S.subtype σ) ∈
        LinearMap.range ρ.norm := hx
    change (e x : A) ∈ LinearMap.range σ.norm
    refine ⟨coindSum S σ v, ?_⟩
    change σ.norm (coindSum S σ v) = (e x : A)
    rw [← coind_norm_one S σ v]
    change (((ρ.norm v : _root_.Representation.coindV S.subtype σ) : G → A) 1) =
      (x.1 : G → A) 1
    exact congrArg (fun w : _root_.Representation.coindV S.subtype σ => (w : G → A) 1) hv
  · rintro y ⟨a, ha⟩
    let v := coindDelta S σ a
    let x : ρ.invariants := ⟨ρ.norm v, (range_norm_le_invariants ρ) ⟨v, rfl⟩⟩
    have hx : x ∈ normSubmodule ρ := ⟨v, rfl⟩
    refine ⟨x, hx, ?_⟩
    apply Subtype.ext
    change (((ρ.norm v : _root_.Representation.coindV S.subtype σ) : G → A) 1) = (y : A)
    rw [coind_norm_one S σ, coindSum_delta S σ, ha]
    rfl

/-- **Shapiro's lemma in degree $0$**: evaluation at `1` induces
$\widehat H^0(G, \operatorname{Coind}_S^G A) \cong \widehat H^0(S, A)$. Milne, *Class Field
Theory*, Chapter II, Proposition 1.11, with §3 for the Tate groups. -/
def tateZeroCoindEquiv :
    TateZero (_root_.Representation.coind S.subtype σ) ≃ₗ[k] TateZero σ := by
  let e := coindInvariantsEquiv S σ
  have h := coindNormSubmodule_map S σ
  exact Submodule.Quotient.equiv (normSubmodule _) (normSubmodule σ) e h

/-! ### Degree minus one -/

omit [Fintype S] in
/-- Every coinduced function is the sum of translates of its components supported on `S`;
used by `tateNegOneCoindEquiv`. -/
private theorem coind_decomp (f : _root_.Representation.coindV S.subtype σ) :
    f = ∑ q : Quotient (QuotientGroup.rightRel S),
      (_root_.Representation.coind S.subtype σ) (cosetRep S q)⁻¹
        (coindDelta S σ ((f : G → A) (cosetRep S q))) := by
  apply Subtype.ext
  funext t
  simp only [Submodule.coe_sum, Finset.sum_apply]
  symm
  rw [Finset.sum_eq_single (Quotient.mk'' t : Quotient (QuotientGroup.rightRel S))]
  · have hm : t * (cosetRep S (Quotient.mk'' t :
        Quotient (QuotientGroup.rightRel S)))⁻¹ ∈ S :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact
        (cosetRep_mk S (Quotient.mk'' t : Quotient (QuotientGroup.rightRel S))))
    have hc : (f : G → A) t = σ ⟨t * (cosetRep S (Quotient.mk'' t :
        Quotient (QuotientGroup.rightRel S)))⁻¹, hm⟩
        ((f : G → A) (cosetRep S (Quotient.mk'' t :
          Quotient (QuotientGroup.rightRel S)))) := by
      simpa using (_root_.Representation.mem_coindV S.subtype σ _).1 f.2
        ⟨t * (cosetRep S (Quotient.mk'' t :
          Quotient (QuotientGroup.rightRel S)))⁻¹, hm⟩
        (cosetRep S (Quotient.mk'' t : Quotient (QuotientGroup.rightRel S)))
    change ((coindDelta S σ ((f : G → A) (cosetRep S (Quotient.mk'' t :
      Quotient (QuotientGroup.rightRel S)))) :
      _root_.Representation.coindV S.subtype σ) : G → A)
      (t * (cosetRep S (Quotient.mk'' t :
        Quotient (QuotientGroup.rightRel S)))⁻¹) = (f : G → A) t
    simpa [coindDelta, hm] using hc.symm
  · intro q _ hq
    have hnot : t * (cosetRep S q)⁻¹ ∉ S := by
      intro h
      have heq : (Quotient.mk'' (cosetRep S q) : Quotient (QuotientGroup.rightRel S)) =
          Quotient.mk'' t := Quotient.sound (QuotientGroup.rightRel_apply.2 h)
      exact hq ((cosetRep_mk S q).symm.trans heq)
    change ((coindDelta S σ ((f : G → A) (cosetRep S q)) :
      _root_.Representation.coindV S.subtype σ) : G → A)
      (t * (cosetRep S q)⁻¹) = 0
    simp [coindDelta, hnot]
  · simp

omit [Fintype S] in
/-- The coset sum of a translate of a function supported on `S` has the same coinvariant
class as its value at `1`; used by `coindSum_augmentation`. -/
private theorem coindSum_shift_delta (g : G) (a : A) :
    _root_.Representation.Coinvariants.mk σ
      (coindSum S σ ((_root_.Representation.coind S.subtype σ) g (coindDelta S σ a))) =
        _root_.Representation.Coinvariants.mk σ a := by
  classical
  let qg : Quotient (QuotientGroup.rightRel S) := Quotient.mk'' g⁻¹
  have hmem : cosetRep S qg * g ∈ S := by
    have h := QuotientGroup.rightRel_apply.mp (Quotient.exact (cosetRep_mk S qg))
    simpa only [mul_inv_rev, inv_inv] using S.inv_mem h
  simp only [coindSum, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.proj_apply,
    Submodule.subtype_apply]
  change _root_.Representation.Coinvariants.mk σ
    (∑ q : Quotient (QuotientGroup.rightRel S),
      ((coindDelta S σ a : _root_.Representation.coindV S.subtype σ) : G → A)
        (cosetRep S q * g)) = _
  rw [Finset.sum_eq_single qg]
  · simp [coindDelta, hmem, _root_.Representation.Coinvariants.mk_self_apply]
  · intro q _ hq
    have hnot : cosetRep S q * g ∉ S := by
      intro h
      have heq : (Quotient.mk'' g⁻¹ : Quotient (QuotientGroup.rightRel S)) =
          Quotient.mk'' (cosetRep S q) :=
        Quotient.sound (QuotientGroup.rightRel_apply.2 (by simpa using h))
      exact hq ((heq.trans (cosetRep_mk S q)).symm)
    simp [coindDelta, hnot]
  · simp

omit [Fintype S] in
/-- The coset sum is invariant modulo `I_S A` under the `G` action; used by
`coindSum_augmentation`. -/
private theorem coindSum_shift (g : G) (f : _root_.Representation.coindV S.subtype σ) :
    _root_.Representation.Coinvariants.mk σ
      (coindSum S σ ((_root_.Representation.coind S.subtype σ) g f)) =
        _root_.Representation.Coinvariants.mk σ (coindSum S σ f) := by
  let ρ := _root_.Representation.coind S.subtype σ
  let C : _root_.Representation.coindV S.subtype σ →ₗ[k]
      _root_.Representation.Coinvariants σ :=
    (_root_.Representation.Coinvariants.mk σ).comp (coindSum S σ)
  have hC (h : G) (a : A) : C (ρ h (coindDelta S σ a)) = C (coindDelta S σ a) := by
    change _root_.Representation.Coinvariants.mk σ
      (coindSum S σ (ρ h (coindDelta S σ a))) =
        _root_.Representation.Coinvariants.mk σ (coindSum S σ (coindDelta S σ a))
    rw [coindSum_shift_delta S σ, coindSum_delta S σ]
  change C (ρ g f) = C f
  conv_lhs => rw [coind_decomp S σ f]
  conv_rhs => rw [coind_decomp S σ f]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  calc
    C (ρ g (ρ (cosetRep S q)⁻¹ (coindDelta S σ ((f : G → A) (cosetRep S q))))) =
        C (ρ (g * (cosetRep S q)⁻¹)
          (coindDelta S σ ((f : G → A) (cosetRep S q)))) := by rw [map_mul]; rfl
    _ = C (coindDelta S σ ((f : G → A) (cosetRep S q))) := hC _ _
    _ = C (ρ (cosetRep S q)⁻¹
      (coindDelta S σ ((f : G → A) (cosetRep S q)))) := (hC _ _).symm

omit [Fintype S] in
/-- The coset sum sends the augmentation submodule of the coinduced representation into
`I_S A`; used by `tateNegOneCoindEquiv`. -/
private theorem coindSum_augmentation :
    _root_.Representation.Coinvariants.ker (_root_.Representation.coind S.subtype σ) ≤
      (_root_.Representation.Coinvariants.ker σ).comap (coindSum S σ) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g, f⟩, rfl⟩
  change coindSum S σ ((_root_.Representation.coind S.subtype σ) g f - f) ∈
    _root_.Representation.Coinvariants.ker σ
  apply (_root_.Representation.Coinvariants.mk_eq_zero σ).1
  simpa only [map_sub, sub_eq_zero] using coindSum_shift S σ g f

omit [Fintype G] [Fintype S] in
/-- Subgroup translation of the function supported on `S` agrees with applying the subgroup
representation to its value; used by `coindDelta_augmentation`. -/
private theorem coindDelta_intertwine (s : S) (a : A) :
    (_root_.Representation.coind S.subtype σ) (s : G) (coindDelta S σ a) =
      coindDelta S σ (σ s a) := by
  apply Subtype.ext
  funext g
  by_cases hg : g ∈ S
  · have hgs : g * (s : G) ∈ S := S.mul_mem hg s.2
    change ((coindDelta S σ a : _root_.Representation.coindV S.subtype σ) : G → A)
      (g * (s : G)) =
        ((coindDelta S σ (σ s a) : _root_.Representation.coindV S.subtype σ) : G → A) g
    simpa [coindDelta, hg, hgs, map_mul] using congrArg (fun t : S => σ t a)
      (show (⟨g * (s : G), hgs⟩ : S) = ⟨g, hg⟩ * s from Subtype.ext rfl)
  · have hgs : g * (s : G) ∉ S := fun h => hg ((S.mul_mem_cancel_right s.2).mp h)
    change ((coindDelta S σ a : _root_.Representation.coindV S.subtype σ) : G → A)
      (g * (s : G)) =
        ((coindDelta S σ (σ s a) : _root_.Representation.coindV S.subtype σ) : G → A) g
    simp [coindDelta, hg, hgs]

omit [Fintype G] [Fintype S] in
/-- The supported-function map carries `I_S A` into the augmentation submodule of the
coinduced representation; used by `tateNegOneCoindEquiv`. -/
private theorem coindDelta_augmentation :
    _root_.Representation.Coinvariants.ker σ ≤
      (_root_.Representation.Coinvariants.ker
        (_root_.Representation.coind S.subtype σ)).comap (coindDelta S σ) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨s, a⟩, rfl⟩
  change coindDelta S σ (σ s a - a) ∈
    _root_.Representation.Coinvariants.ker (_root_.Representation.coind S.subtype σ)
  rw [map_sub, ← coindDelta_intertwine S σ s a]
  exact _root_.Representation.Coinvariants.sub_mem_ker (s : G) (coindDelta S σ a)

omit [Fintype S] in
/-- A coinduced function and the supported function of its coset sum have the same class
modulo the augmentation submodule; used by `tateNegOneCoindEquiv`. -/
private theorem coind_sub_delta_sum_mem (f : _root_.Representation.coindV S.subtype σ) :
    f - coindDelta S σ (coindSum S σ f) ∈
      _root_.Representation.Coinvariants.ker (_root_.Representation.coind S.subtype σ) := by
  have hsum : coindSum S σ f = ∑ q : Quotient (QuotientGroup.rightRel S),
      (f : G → A) (cosetRep S q) := by
    simp [coindSum]
  have heq : f - coindDelta S σ (coindSum S σ f) =
      (∑ q : Quotient (QuotientGroup.rightRel S),
        (_root_.Representation.coind S.subtype σ) (cosetRep S q)⁻¹
          (coindDelta S σ ((f : G → A) (cosetRep S q)))) -
        coindDelta S σ (∑ q : Quotient (QuotientGroup.rightRel S),
          (f : G → A) (cosetRep S q)) := by
    rw [← coind_decomp S σ f, ← hsum]
  rw [heq, map_sum, ← Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro q _
  exact _root_.Representation.Coinvariants.sub_mem_ker
    (cosetRep S q)⁻¹ (coindDelta S σ ((f : G → A) (cosetRep S q)))

/-- The coset sum carries the coinduced norm kernel into the subgroup norm kernel; used by
`tateNegOneCoindEquiv`. -/
private theorem coindSum_kerNorm {f : _root_.Representation.coindV S.subtype σ}
    (hf : f ∈ LinearMap.ker (_root_.Representation.coind S.subtype σ).norm) :
    coindSum S σ f ∈ LinearMap.ker σ.norm := by
  change σ.norm (coindSum S σ f) = 0
  rw [← coind_norm_one S σ f, LinearMap.mem_ker.mp hf]
  rfl

/-- The supported-function map carries the subgroup norm kernel into the coinduced norm
kernel; used by `tateNegOneCoindEquiv`. -/
private theorem coindDelta_kerNorm {a : A} (ha : a ∈ LinearMap.ker σ.norm) :
    coindDelta S σ a ∈
      LinearMap.ker (_root_.Representation.coind S.subtype σ).norm := by
  let ρ := _root_.Representation.coind S.subtype σ
  let v := coindDelta S σ a
  let n : ρ.invariants := ⟨ρ.norm v, (range_norm_le_invariants ρ) ⟨v, rfl⟩⟩
  have hn : coindInvariantsEval S σ n = 0 := by
    apply Subtype.ext
    change (((ρ.norm v : _root_.Representation.coindV S.subtype σ) : G → A) 1) = 0
    rw [coind_norm_one S σ, coindSum_delta S σ, LinearMap.mem_ker.mp ha]
  have hzero : n = 0 := (coindInvariantsEval_bijective S σ).1 (by simpa using hn)
  exact congrArg Subtype.val hzero

/-- The coset sum restricted to norm kernels; used by `tateNegOneCoindEquiv`. -/
private def coindKerSum :
    LinearMap.ker (_root_.Representation.coind S.subtype σ).norm →ₗ[k]
      LinearMap.ker σ.norm :=
  (coindSum S σ).restrict (fun _ hf => coindSum_kerNorm S σ hf)

/-- The supported-function map restricted to norm kernels; used by
`tateNegOneCoindEquiv`. -/
private def coindKerDelta :
    LinearMap.ker σ.norm →ₗ[k]
      LinearMap.ker (_root_.Representation.coind S.subtype σ).norm :=
  (coindDelta S σ).restrict (fun _ ha => coindDelta_kerNorm S σ ha)

/-- A map of norm kernels descends to degree-minus-one Tate groups when it preserves
augmentation submodules; used by `tateNegOneCoindEquiv`. -/
private def tateNegOneQuotMap {H V W : Type*} [Group H] [Fintype H]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : _root_.Representation k G V) (τ : _root_.Representation k H W)
    (f : LinearMap.ker ρ.norm →ₗ[k] LinearMap.ker τ.norm)
    (hf : augmentationSubmodule ρ ≤ (augmentationSubmodule τ).comap f) :
    TateNegOne ρ →ₗ[k] TateNegOne τ :=
  (augmentationSubmodule ρ).mapQ (augmentationSubmodule τ) f hf

/-- The coset sum on degree-minus-one Tate groups; used by `tateNegOneCoindEquiv`. -/
private def coindNegMap :
    TateNegOne (_root_.Representation.coind S.subtype σ) →ₗ[k] TateNegOne σ :=
  tateNegOneQuotMap (_root_.Representation.coind S.subtype σ) σ
    (coindKerSum S σ) (by
      intro x hx
      change (x : _root_.Representation.coindV S.subtype σ) ∈
        _root_.Representation.Coinvariants.ker
          (_root_.Representation.coind S.subtype σ) at hx
      change coindSum S σ (x : _root_.Representation.coindV S.subtype σ) ∈
        _root_.Representation.Coinvariants.ker σ
      exact coindSum_augmentation S σ hx)

/-- The supported-function map on degree-minus-one Tate groups; used by
`tateNegOneCoindEquiv`. -/
private def coindNegInvMap :
    TateNegOne σ →ₗ[k]
      TateNegOne (_root_.Representation.coind S.subtype σ) :=
  tateNegOneQuotMap σ (_root_.Representation.coind S.subtype σ)
    (coindKerDelta S σ) (by
      intro x hx
      change (x : A) ∈ _root_.Representation.Coinvariants.ker σ at hx
      change coindDelta S σ (x : A) ∈
        _root_.Representation.Coinvariants.ker
          (_root_.Representation.coind S.subtype σ)
      exact coindDelta_augmentation S σ hx)

/-- Summing after forming the supported function is the identity on degree-minus-one classes;
used by `tateNegOneCoindEquiv`. -/
private theorem coindNegMap_comp_inv :
    coindNegMap S σ ∘ₗ coindNegInvMap S σ = LinearMap.id := by
  apply TateNegOne.hom_ext
  intro a
  change (Submodule.Quotient.mk (coindKerSum S σ (coindKerDelta S σ a)) :
    TateNegOne σ) = Submodule.Quotient.mk a
  congr 1
  apply Subtype.ext
  exact coindSum_delta S σ (a : A)

/-- Forming the supported function after summing is the identity on degree-minus-one classes;
used by `tateNegOneCoindEquiv`. -/
private theorem coindNegInvMap_comp :
    coindNegInvMap S σ ∘ₗ coindNegMap S σ = LinearMap.id := by
  apply TateNegOne.hom_ext
  intro f
  apply (Submodule.Quotient.eq _).2
  change coindDelta S σ (coindSum S σ (f : _root_.Representation.coindV S.subtype σ)) -
    (f : _root_.Representation.coindV S.subtype σ) ∈
    _root_.Representation.Coinvariants.ker (_root_.Representation.coind S.subtype σ)
  simpa only [neg_sub] using
    (_root_.Representation.Coinvariants.ker
      (_root_.Representation.coind S.subtype σ)).neg_mem
        (coind_sub_delta_sum_mem S σ (f : _root_.Representation.coindV S.subtype σ))

/-- **Shapiro's lemma in degree $-1$**:
$\widehat H^{-1}(G, \operatorname{Coind}_S^G A) \cong \widehat H^{-1}(S, A)$, induced by
$f \mapsto \sum_t f(t)$ over representatives `t` of the right cosets of `S`. Milne, *Class Field
Theory*, Chapter II, Proposition 1.11, with §3 for the Tate groups. -/
def tateNegOneCoindEquiv :
    TateNegOne (_root_.Representation.coind S.subtype σ) ≃ₗ[k] TateNegOne σ := by
  exact LinearEquiv.ofLinearMap (coindNegMap S σ) (coindNegInvMap S σ)
    (coindNegMap_comp_inv S σ) (coindNegInvMap_comp S σ)

/-- Shapiro's degree-zero comparison for a representation identified with a coinduced module.
Milne, *Class Field Theory*, Chapter II, Proposition 1.11, used in Chapter VII, Proposition 2.3. -/
def tateZeroEquivOfCoind {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : _root_.Representation k G V}
    (e : ρ.Equiv (_root_.Representation.coind S.subtype σ)) :
    TateZero ρ ≃ₗ[k] TateZero σ := by
  exact (tateZeroEquiv e).trans (tateZeroCoindEquiv S σ)

/-- Shapiro's degree-minus-one comparison for a representation identified with a coinduced
module. Milne, *Class Field Theory*, Chapter II, Proposition 1.11, used in Chapter VII,
Proposition 2.3. -/
def tateNegOneEquivOfCoind {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : _root_.Representation k G V}
    (e : ρ.Equiv (_root_.Representation.coind S.subtype σ)) :
    TateNegOne ρ ≃ₗ[k] TateNegOne σ := by
  exact (tateNegOneEquiv e).trans (tateNegOneCoindEquiv S σ)

/-! ### Transitive permuted families

A transitive family is coinduced from one fiber. Reindexing its stabilizer action then gives
Shapiro equivalences and equality of Herbrand quotients with the chosen fiber representation. -/

namespace PermutedFamily

variable {H ι : Type*} [Group H] [Fintype H] [MulAction G ι]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  (F : PermutedFamily k G ι V)

/-- Shapiro's degree-zero equivalence for a transitive permuted family whose fiber action is
identified with `τ` through the stabilizer isomorphism `e`. -/
def tateZeroEquivOfFiber (i : ι) (htrans : ∀ j, ∃ g : G, g • i = j)
    (τ : _root_.Representation k H (V i))
    (e : MulAction.stabilizer G i ≃* H)
    (hF : F.fiber i = τ.comp e.toMonoidHom) :
    TateZero F.sections ≃ₗ[k] TateZero τ := by
  letI : Fintype (MulAction.stabilizer G i) := Fintype.ofFinite _
  exact (tateZeroEquivOfCoind (MulAction.stabilizer G i) (F.fiber i)
    (F.coindEquiv i htrans)).trans (by
      rw [hF]
      exact tateZeroCompEquiv τ e)

/-- Shapiro's degree-minus-one equivalence for a transitive permuted family whose fiber action
is identified with `τ` through the stabilizer isomorphism `e`. -/
def tateNegOneEquivOfFiber (i : ι) (htrans : ∀ j, ∃ g : G, g • i = j)
    (τ : _root_.Representation k H (V i))
    (e : MulAction.stabilizer G i ≃* H)
    (hF : F.fiber i = τ.comp e.toMonoidHom) :
    TateNegOne F.sections ≃ₗ[k] TateNegOne τ := by
  letI : Fintype (MulAction.stabilizer G i) := Fintype.ofFinite _
  exact (tateNegOneEquivOfCoind (MulAction.stabilizer G i) (F.fiber i)
    (F.coindEquiv i htrans)).trans (by
      rw [hF]
      exact tateNegOneCompEquiv τ e)

/-- The Herbrand quotient of a transitive permuted family equals that of any identified fiber
representation; this packages its two Shapiro equivalences. -/
theorem herbrandQuotient_sections (i : ι) (htrans : ∀ j, ∃ g : G, g • i = j)
    (τ : _root_.Representation k H (V i))
    (e : MulAction.stabilizer G i ≃* H)
    (hF : F.fiber i = τ.comp e.toMonoidHom) :
    herbrandQuotient F.sections = herbrandQuotient τ :=
  herbrandQuotient_eq_of_equivs _ _
    (F.tateZeroEquivOfFiber i htrans τ e hF).toEquiv
    (F.tateNegOneEquivOfFiber i htrans τ e hF).toEquiv

end PermutedFamily

end Representation

end SIC
