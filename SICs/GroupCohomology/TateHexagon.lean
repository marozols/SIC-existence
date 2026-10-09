/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.GroupCohomology.TateLowDegree
import Mathlib.RepresentationTheory.Homological.FiniteCyclic
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.Algebra.Module.SnakeLemma

/-!
# The exact hexagon of Tate groups of a cyclic group

A short exact sequence of representations of a finite cyclic group induces an exact hexagon in
Tate degrees zero and minus one, with explicit connecting maps.

This module follows Milne, *Class Field Theory*, version 4.03 (2020), Chapter II, §3,
Proposition 3.6. Its maps are used to count the Tate groups in the Herbrand quotient.

## The argument

A generator identifies the invariant vectors with the kernel of $\sigma-1$ and the augmentation
submodule with its image. Thus the two Tate groups are the homology of the two-periodic complex
alternating $N_G$ and $\sigma-1$. Quotienting by the image of one differential and restricting to
the kernel of that differential gives an exact diagram of modules for a short exact sequence of
representations. Mathlib's module snake lemma supplies the connecting map and exactness at the
outer vertices. Interchanging the differentials gives the other half of the hexagon.
-/

noncomputable section

namespace SIC
namespace Representation

variable {k G V W U : Type*} [CommRing k] [Group G] [Fintype G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
  (ρ : _root_.Representation k G V) (σ : _root_.Representation k G W)
  (τ : _root_.Representation k G U)

/-! ### Short exact sequences

A short exact sequence $0 \to V' \xrightarrow{f} V \xrightarrow{g} V'' \to 0$ of representations
of a cyclic group gives the periodic hexagon of Tate groups, whence multiplicativity. -/

variable {ρ σ τ}

/-! The two Tate degrees are the homology of the same two-periodic complex. The cycle and
boundary submodules are recorded separately so that the resulting quotients are definitionally
the existing Tate groups, even when a submodule is identified with a kernel or range only by a
theorem. -/

/-- A two-periodic complex with chosen cycle and boundary submodules in both degrees. -/
private structure TwoPeriodic (k M : Type*) [CommRing k] [AddCommGroup M] [Module k M] where
  /-- The first differential. -/
  a : M →ₗ[k] M
  /-- The second differential. -/
  b : M →ₗ[k] M
  /-- Cycles of the first differential. -/
  Z : Submodule k M
  /-- Cycles of the second differential. -/
  Z' : Submodule k M
  /-- Boundaries of the second differential. -/
  B : Submodule k M
  /-- Boundaries of the first differential. -/
  B' : Submodule k M
  /-- The first cycle identification. -/
  hZ : Z = a.ker
  /-- The second cycle identification. -/
  hZ' : Z' = b.ker
  /-- The first boundary identification. -/
  hB : B = b.range
  /-- The second boundary identification. -/
  hB' : B' = a.range
  /-- Consecutive differentials vanish in one direction. -/
  ab : a.comp b = 0
  /-- Consecutive differentials vanish in the other direction. -/
  ba : b.comp a = 0

/-- Swap the two differentials and the two homology degrees of a two-periodic complex. -/
private abbrev TwoPeriodic.flip (P : TwoPeriodic k V) : TwoPeriodic k V where
  a := P.b
  b := P.a
  Z := P.Z'
  Z' := P.Z
  B := P.B'
  B' := P.B
  hZ := P.hZ'
  hZ' := P.hZ
  hB := P.hB'
  hB' := P.hB
  ab := P.ba
  ba := P.ab

/-- The quotient of a chosen cycle submodule by the boundaries it contains. -/
private abbrev cycleQuotient (Z B : Submodule k V) := Z ⧸ B.comap Z.subtype

/-- Homology of a two-periodic complex at the differential `a`: `ker a / range b`. -/
private abbrev TwoPeriodic.H (P : TwoPeriodic k V) := cycleQuotient P.Z P.B

/-- A map of two-periodic complexes, commuting with both differentials. -/
private structure TwoPeriodic.Hom (P : TwoPeriodic k V) (Q : TwoPeriodic k W) where
  /-- The underlying linear map. -/
  map : V →ₗ[k] W
  /-- Commutation with the first differential. -/
  comm_a : map.comp P.a = Q.a.comp map
  /-- Commutation with the second differential. -/
  comm_b : map.comp P.b = Q.b.comp map

/-- The map of complexes after interchanging their two differentials. -/
private def TwoPeriodic.Hom.flip {P : TwoPeriodic k V} {Q : TwoPeriodic k W}
    (F : P.Hom Q) : P.flip.Hom Q.flip where
  map := F.map
  comm_a := F.comm_b
  comm_b := F.comm_a

/-- A map of two-periodic complexes induces a map on `ker a / range b`. -/
private def TwoPeriodic.Hom.homology {P : TwoPeriodic k V} {Q : TwoPeriodic k W}
    (F : P.Hom Q) : P.H →ₗ[k] Q.H := by
  let zmap : P.Z →ₗ[k] Q.Z := F.map.restrict (by
    intro x hx
    rw [Q.hZ]
    apply LinearMap.mem_ker.mpr
    have ha : P.a x = 0 := LinearMap.mem_ker.mp (P.hZ ▸ hx)
    have hcomm := congrArg (fun m : V →ₗ[k] W => m x) F.comm_a
    change F.map (P.a x) = Q.a (F.map x) at hcomm
    rw [← hcomm, ha, map_zero])
  exact (P.B.comap P.Z.subtype).mapQ (Q.B.comap Q.Z.subtype) zmap (by
    intro x hx
    change F.map (x : V) ∈ Q.B
    rw [P.hB] at hx
    rw [Q.hB]
    obtain ⟨v, hv⟩ := hx
    refine ⟨F.map v, ?_⟩
    have hcomm := congrArg (fun m : V →ₗ[k] W => m v) F.comm_b
    change F.map (P.b v) = Q.b (F.map v) at hcomm
    rw [← hcomm, hv]
    rfl)

/-- The induced homology map sends a cycle class to the class of its image. -/
private theorem TwoPeriodic.Hom.homology_mk {P : TwoPeriodic k V} {Q : TwoPeriodic k W}
    (F : P.Hom Q) (x : P.Z) :
    F.homology (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨F.map x, by
        rw [Q.hZ]
        apply LinearMap.mem_ker.mpr
        have ha : P.a x = 0 := LinearMap.mem_ker.mp (P.hZ ▸ x.property)
        have hcomm := congrArg (fun m : V →ₗ[k] W => m x) F.comm_a
        change F.map (P.a x) = Q.a (F.map x) at hcomm
        rw [← hcomm, ha, map_zero]⟩ := rfl

/-- Exactness at the middle quotient of a short exact sequence whose boundaries are ranges of
commuting endomorphisms and whose cycle condition is reflected by the first map. -/
private theorem quotient_exact_middle
    {ZV : Submodule k V} {ZW : Submodule k W} {ZU : Submodule k U}
    {BV : Submodule k V} {BW : Submodule k W} {BU : Submodule k U}
    {bW : W →ₗ[k] W} {bU : U →ₗ[k] U} {f : V →ₗ[k] W} {g : W →ₗ[k] U}
    {F₀ : cycleQuotient ZV BV →ₗ[k] cycleQuotient ZW BW}
    {G₀ : cycleQuotient ZW BW →ₗ[k] cycleQuotient ZU BU}
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hbZ : ∀ w, bW w ∈ ZW) (hreflect : ∀ v, f v ∈ ZW → v ∈ ZV)
    (hbg : ∀ w, g (bW w) = bU (g w))
    (hBW : BW = bW.range) (hBU : BU = bU.range)
    (hFmk : ∀ x : ZV, ∃ y : ZW, (y : W) = f x ∧
      F₀ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y)
    (hGmk : ∀ x : ZW, ∃ y : ZU, (y : U) = g x ∧
      G₀ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y) :
    Function.Exact F₀ G₀ := by
  intro q
  induction q using Quotient.inductionOn with | _ x =>
  constructor
  · intro hx
    obtain ⟨u, hu, hGu⟩ := hGmk x
    change G₀ (Submodule.Quotient.mk x) = 0 at hx
    rw [hGu] at hx
    have huB' := (Submodule.Quotient.mk_eq_zero (BU.comap ZU.subtype)).mp hx
    have huB : (u : U) ∈ BU := huB'
    rw [hBU] at huB
    obtain ⟨v, hv⟩ := huB
    obtain ⟨w, hw⟩ := hg v
    have hgw : g ((x : W) - bW w) = 0 := by
      calc
        g ((x : W) - bW w) = g (x : W) - bU (g w) := by rw [map_sub, hbg]
        _ = (u : U) - bU v := by rw [hu, hw]
        _ = 0 := by rw [hv, sub_self]
    obtain ⟨v', hv'⟩ := (hfg _).mp hgw
    have hvZ : v' ∈ ZV := hreflect v' (by
      rw [hv']
      exact ZW.sub_mem x.property (hbZ w))
    obtain ⟨y, hy, hFy⟩ := hFmk ⟨v', hvZ⟩
    refine ⟨Submodule.Quotient.mk ⟨v', hvZ⟩, ?_⟩
    change F₀ (Submodule.Quotient.mk ⟨v', hvZ⟩) = Submodule.Quotient.mk x
    rw [hFy]
    apply (Submodule.Quotient.eq _).mpr
    change (y : W) - (x : W) ∈ BW
    rw [hBW, hy, hv']
    exact ⟨-w, by simp⟩
  · rintro ⟨p, hp⟩
    induction p using Quotient.inductionOn with | _ y =>
    rw [← hp]
    obtain ⟨z, hz, hFz⟩ := hFmk y
    change G₀ (F₀ (Submodule.Quotient.mk y)) = 0
    rw [hFz]
    obtain ⟨u, hu, hGu⟩ := hGmk z
    rw [hGu]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change (u : U) ∈ BU
    rw [hu, hz, hfg.apply_apply_eq_zero y]
    exact Submodule.zero_mem _

/-- Exactness at the middle homology group of a short exact sequence of two-periodic
complexes. -/
private theorem TwoPeriodic.exact_middle {P : TwoPeriodic k V} {Q : TwoPeriodic k W}
    {R : TwoPeriodic k U} {F : P.Hom Q} {J : Q.Hom R}
    (hf : Function.Injective F.map) (hg : Function.Surjective J.map)
    (hfg : Function.Exact F.map J.map) :
    Function.Exact F.homology J.homology := by
  apply quotient_exact_middle hg hfg
    (bW := Q.b) (bU := R.b) (hBW := Q.hB) (hBU := R.hB)
  · intro w
    rw [Q.hZ]
    apply LinearMap.mem_ker.mpr
    have hab := congrArg (fun m : W →ₗ[k] W => m w) Q.ab
    exact hab
  · intro v hv
    rw [P.hZ]
    apply LinearMap.mem_ker.mpr
    apply hf
    have hcomm := congrArg (fun m : V →ₗ[k] W => m v) F.comm_a
    change F.map (P.a v) = Q.a (F.map v) at hcomm
    rw [hcomm]
    simpa using LinearMap.mem_ker.mp (Q.hZ ▸ hv)
  · intro w
    have hcomm := congrArg (fun m : W →ₗ[k] U => m w) J.comm_b
    exact hcomm
  · intro x
    refine ⟨⟨F.map x, ?_⟩, rfl, F.homology_mk x⟩
    rw [Q.hZ]
    apply LinearMap.mem_ker.mpr
    have hcomm := congrArg (fun m : V →ₗ[k] W => m x) F.comm_a
    change F.map (P.a x) = Q.a (F.map x) at hcomm
    have hx : P.a x = 0 := LinearMap.mem_ker.mp (P.hZ ▸ x.property)
    simp [← hcomm, hx]
  · intro x
    refine ⟨⟨J.map x, ?_⟩, rfl, J.homology_mk x⟩
    rw [R.hZ]
    apply LinearMap.mem_ker.mpr
    have hcomm := congrArg (fun m : W →ₗ[k] U => m x) J.comm_a
    change J.map (Q.a x) = R.a (J.map x) at hcomm
    have hx : Q.a x = 0 := LinearMap.mem_ker.mp (Q.hZ ▸ x.property)
    simp [← hcomm, hx]

/-! ### The snake-lemma diagram

For either orientation of the periodic complex, the top row is the quotient by the image of
`b`, the bottom row is the kernel of `b`, and the vertical differential is induced by `a`.
The kernel and cokernel of that vertical map are the two Tate degrees. -/

/-- The quotient by the `b` boundaries, used as the top row of the snake-lemma diagram. -/
private abbrev TwoPeriodic.M (P : TwoPeriodic k V) := V ⧸ P.B

/-- The `b` cycles, used as the bottom row of the snake-lemma diagram. -/
private abbrev TwoPeriodic.N (P : TwoPeriodic k V) := P.Z'

/-- The differential `a : V / im b → ker b` in the snake-lemma diagram. -/
private def TwoPeriodic.i (P : TwoPeriodic k V) : P.M →ₗ[k] P.N :=
  P.B.liftQ (P.a.codRestrict P.Z' (by
    intro x
    rw [P.hZ']
    exact LinearMap.mem_ker.mpr (congrArg (fun m : V →ₗ[k] V => m x) P.ba))) (by
    intro x hx
    rw [P.hB] at hx
    obtain ⟨y, rfl⟩ := hx
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    exact congrArg (fun m : V →ₗ[k] V => m y) P.ab)

/-- The inclusion `ker a / im b → V / im b` in the snake-lemma diagram. -/
private def TwoPeriodic.ι (P : TwoPeriodic k V) : P.H →ₗ[k] P.M :=
  (P.B.comap P.Z.subtype).liftQ (P.B.mkQ.comp P.Z.subtype) (by
    intro x hx
    exact LinearMap.mem_ker.mpr ((Submodule.Quotient.mk_eq_zero _).mpr hx))

/-- The projection `ker b → ker b / im a` in the snake-lemma diagram. -/
private def TwoPeriodic.π (P : TwoPeriodic k V) : P.N →ₗ[k] P.flip.H :=
  (P.B'.comap P.Z'.subtype).mkQ

/-- The top-row map induced by a morphism of two-periodic complexes. -/
private def TwoPeriodic.Hom.top {P : TwoPeriodic k V} {Q : TwoPeriodic k W}
    (F : P.Hom Q) : P.M →ₗ[k] Q.M :=
  P.B.mapQ Q.B F.map (by
    intro x hx
    rw [P.hB] at hx
    rw [Q.hB]
    obtain ⟨y, rfl⟩ := hx
    refine ⟨F.map y, ?_⟩
    exact (congrArg (fun m : V →ₗ[k] W => m y) F.comm_b).symm)

/-- The bottom-row map induced by a morphism of two-periodic complexes. -/
private def TwoPeriodic.Hom.bottom {P : TwoPeriodic k V} {Q : TwoPeriodic k W}
    (F : P.Hom Q) : P.N →ₗ[k] Q.N :=
  F.map.restrict (by
    intro x hx
    change F.map x ∈ Q.Z'
    rw [Q.hZ']
    apply LinearMap.mem_ker.mpr
    have h := congrArg (fun m : V →ₗ[k] W => m x) F.comm_b
    change F.map (P.b x) = Q.b (F.map x) at h
    have hx0 : P.b x = 0 := by
      apply LinearMap.mem_ker.mp
      rw [← P.hZ']
      exact hx
    rw [← h, hx0, map_zero])

/-- The top-row maps form an exact sequence; used by `TwoPeriodic.snake`. -/
private theorem TwoPeriodic.top_exact {P : TwoPeriodic k V} {Q : TwoPeriodic k W}
    {R : TwoPeriodic k U} {F : P.Hom Q} {J : Q.Hom R}
    (hg : Function.Surjective J.map) (hfg : Function.Exact F.map J.map) :
    Function.Exact F.top J.top := by
  apply (hfg.exact_mapQ_iff _ _).2
  intro x hx
  obtain ⟨hxJ, hxB⟩ := hx
  rw [R.hB] at hxB
  obtain ⟨u, hu⟩ := hxB
  obtain ⟨w, hw⟩ := hg u
  refine ⟨Q.b w, ?_, ?_⟩
  · rw [Q.hB]
    exact ⟨w, rfl⟩
  · have h := congrArg (fun m : W →ₗ[k] U => m w) J.comm_b
    change J.map (Q.b w) = R.b (J.map w) at h
    rw [hw] at h
    exact h.trans hu

/-- The second top-row map is onto; used by `TwoPeriodic.snake`. -/
private theorem TwoPeriodic.top_surjective {Q : TwoPeriodic k W} {R : TwoPeriodic k U}
    {J : Q.Hom R} (hg : Function.Surjective J.map) : Function.Surjective J.top := by
  intro x
  induction x using Quotient.inductionOn with | _ u =>
    obtain ⟨w, hw⟩ := hg u
    refine ⟨Submodule.Quotient.mk w, ?_⟩
    change (Submodule.Quotient.mk (J.map w) : R.M) = Submodule.Quotient.mk u
    rw [hw]

/-- The bottom-row maps form an exact sequence; used by `TwoPeriodic.snake`. -/
private theorem TwoPeriodic.bottom_exact {P : TwoPeriodic k V} {Q : TwoPeriodic k W}
    {R : TwoPeriodic k U} {F : P.Hom Q} {J : Q.Hom R}
    (hf : Function.Injective F.map) (hfg : Function.Exact F.map J.map) :
    Function.Exact F.bottom J.bottom := by
  intro x
  constructor
  · intro hx
    have hx' : J.map (x : W) = 0 := congrArg Subtype.val hx
    obtain ⟨v, hv⟩ := (hfg _).mp hx'
    have hvZ : v ∈ P.Z' := by
      rw [P.hZ']
      apply LinearMap.mem_ker.mpr
      apply hf
      have h := congrArg (fun m : V →ₗ[k] W => m v) F.comm_b
      change F.map (P.b v) = Q.b (F.map v) at h
      rw [h, hv, LinearMap.mem_ker.mp (Q.hZ' ▸ x.property), map_zero]
    exact ⟨⟨v, hvZ⟩, Subtype.ext hv⟩
  · rintro ⟨v, rfl⟩
    apply Subtype.ext
    exact hfg.apply_apply_eq_zero v

/-- The first bottom-row map is injective; used by `TwoPeriodic.snake`. -/
private theorem TwoPeriodic.bottom_injective {P : TwoPeriodic k V} {Q : TwoPeriodic k W}
    {F : P.Hom Q} (hf : Function.Injective F.map) : Function.Injective F.bottom := by
  intro x y h
  exact Subtype.ext (hf (congrArg Subtype.val h))

/-- Each square of the snake-lemma diagram commutes; used by `TwoPeriodic.snake`. -/
private theorem TwoPeriodic.Hom.square {P : TwoPeriodic k V} {Q : TwoPeriodic k W}
    (F : P.Hom Q) : F.bottom.comp P.i = Q.i.comp F.top := by
  apply Submodule.linearMap_qext P.B
  ext x
  change F.map (P.a x) = Q.a (F.map x)
  exact congrArg (fun m : V →ₗ[k] W => m x) F.comm_a

/-- The kernel of the vertical differential is the chosen first homology; used by
`TwoPeriodic.snake` and its outer exactness lemmas. -/
private theorem TwoPeriodic.exact_ι_i (P : TwoPeriodic k V) :
    Function.Exact P.ι P.i := by
  intro q
  induction q using Quotient.inductionOn with | _ x =>
  constructor
  · intro hx
    have hax : P.a x = 0 := congrArg Subtype.val hx
    have hxZ : x ∈ P.Z := by
      rw [P.hZ]
      exact LinearMap.mem_ker.mpr hax
    exact ⟨Submodule.Quotient.mk ⟨x, hxZ⟩, rfl⟩
  · rintro ⟨z, hz⟩
    induction z using Quotient.inductionOn with | _ y =>
    have hy : P.a (y : V) = 0 := LinearMap.mem_ker.mp (P.hZ ▸ y.property)
    rw [← hz]
    apply Subtype.ext
    exact hy

/-- The image of the vertical differential is the kernel of the second homology quotient;
used by `TwoPeriodic.snake` and its outer exactness lemmas. -/
private theorem TwoPeriodic.exact_i_π (P : TwoPeriodic k V) :
    Function.Exact P.i P.π := by
  intro x
  constructor
  · intro hx
    change (Submodule.Quotient.mk x : P.flip.H) = 0 at hx
    have hxB : x ∈ P.B'.comap P.Z'.subtype := (Submodule.Quotient.mk_eq_zero _).mp hx
    change (x : V) ∈ P.B' at hxB
    rw [P.hB'] at hxB
    obtain ⟨v, hv⟩ := hxB
    exact ⟨Submodule.Quotient.mk v, Subtype.ext hv⟩
  · rintro ⟨q, rfl⟩
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    induction q using Quotient.inductionOn with | _ v =>
      change P.a v ∈ P.B'
      rw [P.hB']
      exact ⟨v, rfl⟩

/-- The first homology embeds in the top row; used by `TwoPeriodic.snake_right`. -/
private theorem TwoPeriodic.ι_injective (P : TwoPeriodic k V) : Function.Injective P.ι := by
  apply LinearMap.ker_eq_bot.mp
  ext q
  induction q using Quotient.inductionOn with | _ x =>
  change (Submodule.Quotient.mk ((x : V) : V) : P.M) = 0 ↔
    (Submodule.Quotient.mk x : P.H) = 0
  simp only [Submodule.Quotient.mk_eq_zero]
  rfl

/-- The second homology is a quotient of the bottom row; used by `TwoPeriodic.snake_left`. -/
private theorem TwoPeriodic.π_surjective (P : TwoPeriodic k V) : Function.Surjective P.π :=
  Submodule.mkQ_surjective _

/-- The top-row map commutes with the inclusion of first homology; used by
`TwoPeriodic.snake_right`. -/
private theorem TwoPeriodic.Hom.top_ι {P : TwoPeriodic k V} {Q : TwoPeriodic k W}
    (F : P.Hom Q) : F.top.comp P.ι = Q.ι.comp F.homology := by
  apply Submodule.linearMap_qext (P.B.comap P.Z.subtype)
  ext x
  rfl

/-- The bottom-row map commutes with the projection to second homology; used by
`TwoPeriodic.snake_left`. -/
private theorem TwoPeriodic.Hom.bottom_π {P : TwoPeriodic k V} {Q : TwoPeriodic k W}
    (F : P.Hom Q) : F.flip.homology.comp P.π = Q.π.comp F.bottom := by
  ext x
  rfl

/-- The snake-lemma connecting map for a short exact sequence of two-periodic complexes;
used by both Tate connecting maps. -/
private def TwoPeriodic.snake {P : TwoPeriodic k V} {Q : TwoPeriodic k W}
    {R : TwoPeriodic k U} {F : P.Hom Q} {J : Q.Hom R}
    (hf : Function.Injective F.map) (hg : Function.Surjective J.map)
    (hfg : Function.Exact F.map J.map) : R.H →ₗ[k] P.flip.H :=
  SnakeLemma.δ' P.i Q.i R.i F.top J.top
    (top_exact hg hfg) F.bottom J.bottom (bottom_exact hf hfg)
    F.square J.square R.ι R.exact_ι_i P.π P.exact_i_π
    (top_surjective hg) (bottom_injective hf)

/-- The snake connecting map sends a lifted cycle to its pulled-back differential; used by
`TateZero.δ` and `TateNegOne.δ`. -/
private theorem TwoPeriodic.snake_mk {P : TwoPeriodic k V} {Q : TwoPeriodic k W}
    {R : TwoPeriodic k U} {F : P.Hom Q} {J : Q.Hom R}
    (hf : Function.Injective F.map) (hg : Function.Surjective J.map)
    (hfg : Function.Exact F.map J.map) (x : R.Z) (w : W) (v : P.Z')
    (hw : J.map w = (x : U)) (hv : F.map (v : V) = Q.a w) :
    snake hf hg hfg (Submodule.Quotient.mk x) = Submodule.Quotient.mk v := by
  have htop : J.top (Submodule.Quotient.mk w) = R.ι (Submodule.Quotient.mk x) := by
    change (Submodule.Quotient.mk (J.map w) : R.M) = Submodule.Quotient.mk (x : U)
    rw [hw]
  have hbottom : F.bottom v = Q.i (Submodule.Quotient.mk w) := Subtype.ext hv
  exact SnakeLemma.δ'_eq P.i Q.i R.i F.top J.top
    (top_exact hg hfg) F.bottom J.bottom (bottom_exact hf hfg)
    F.square J.square R.ι R.exact_ι_i P.π P.exact_i_π
    (top_surjective hg) (bottom_injective hf)
    (Submodule.Quotient.mk x) (Submodule.Quotient.mk w) htop v hbottom

/-- The right-hand homology map and the snake connecting map are exact; used by
`exact_zero_right` and `exact_neg_right`. -/
private theorem TwoPeriodic.snake_right {P : TwoPeriodic k V} {Q : TwoPeriodic k W}
    {R : TwoPeriodic k U} {F : P.Hom Q} {J : Q.Hom R}
    (hf : Function.Injective F.map) (hg : Function.Surjective J.map)
    (hfg : Function.Exact F.map J.map) :
    Function.Exact J.homology (snake hf hg hfg) :=
  SnakeLemma.exact_δ'_right P.i Q.i R.i F.top J.top
    (top_exact hg hfg) F.bottom J.bottom (bottom_exact hf hfg)
    F.square J.square Q.ι Q.exact_ι_i R.ι R.exact_ι_i P.π P.exact_i_π
    (top_surjective hg) (bottom_injective hf)
    J.homology J.top_ι R.ι_injective

/-- The snake connecting map and the left-hand homology map are exact; used by
`exact_neg_left` and `exact_zero_left`. -/
private theorem TwoPeriodic.snake_left {P : TwoPeriodic k V} {Q : TwoPeriodic k W}
    {R : TwoPeriodic k U} {F : P.Hom Q} {J : Q.Hom R}
    (hf : Function.Injective F.map) (hg : Function.Surjective J.map)
    (hfg : Function.Exact F.map J.map) :
    Function.Exact (snake hf hg hfg) F.flip.homology :=
  SnakeLemma.exact_δ'_left P.i Q.i R.i F.top J.top
    (top_exact hg hfg) F.bottom J.bottom (bottom_exact hf hfg)
    F.square J.square R.ι R.exact_ι_i P.π P.exact_i_π Q.π Q.exact_i_π
    (top_surjective hg) (bottom_injective hf)
    F.flip.homology F.bottom_π P.π_surjective

/-- The two-periodic complex with differentials `σ - 1` and `N` has the explicit Tate groups
as its two homology groups. -/
private def tatePeriodic (ρ : _root_.Representation k G V) (s : G)
    (hs : ∀ x : G, x ∈ Subgroup.zpowers s) : TwoPeriodic k V where
  a := ρ s - LinearMap.id
  b := ρ.norm
  Z := ρ.invariants
  Z' := LinearMap.ker ρ.norm
  B := LinearMap.range ρ.norm
  B' := _root_.Representation.Coinvariants.ker ρ
  hZ := by
    ext x
    simp only [_root_.Representation.mem_invariants_iff_of_forall_mem_zpowers ρ s hs x,
      LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  hZ' := rfl
  hB := rfl
  hB' := _root_.Representation.FiniteCyclicGroup.coinvariantsKer_eq_range ρ s hs
  ab := by
    ext x
    simp [LinearMap.sub_apply]
  ba := by
    ext x
    simp [LinearMap.sub_apply]

/-- An intertwining map is a map of the Tate two-periodic complexes. -/
private def tatePeriodicHom {f : ρ.IntertwiningMap σ} (s : G)
    (hs : ∀ x : G, x ∈ Subgroup.zpowers s) :
    (tatePeriodic ρ s hs).Hom (tatePeriodic σ s hs) where
  map := f.toLinearMap
  comm_a := by
    ext v
    simp [tatePeriodic, LinearMap.sub_apply,
      _root_.Representation.IntertwiningMap.isIntertwining ρ σ f s v]
  comm_b := by
    ext v
    exact IntertwiningMap.map_norm f v

-- Middle exactness in degree zero holds for every finite group, so this application uses the
-- cycle-quotient lemma without choosing a cyclic generator.
/-- Exactness at `Ĥ⁰(V)` in the Tate hexagon of a short exact sequence. -/
theorem TateZero.exact_middle {f : ρ.IntertwiningMap σ} {g : σ.IntertwiningMap τ}
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    Function.Exact (TateZero.map f) (TateZero.map g) := by
  apply quotient_exact_middle (f := f.toLinearMap) (g := g.toLinearMap)
    (bW := σ.norm) (bU := τ.norm) (BW := LinearMap.range σ.norm)
    (BU := LinearMap.range τ.norm) hg hfg
    (hBW := rfl) (hBU := rfl)
  · intro w
    exact range_norm_le_invariants σ ⟨w, rfl⟩
  · intro v hv
    rw [_root_.Representation.mem_invariants] at hv ⊢
    intro γ
    apply hf
    calc
      f (ρ γ v) = σ γ (f v) :=
        _root_.Representation.IntertwiningMap.isIntertwining ρ σ f γ v
      _ = f v := hv γ
  · intro w
    exact IntertwiningMap.map_norm g w
  · intro x
    exact ⟨IntertwiningMap.invariantsMap f x, rfl, rfl⟩
  · intro x
    exact ⟨IntertwiningMap.invariantsMap g x, rfl, rfl⟩

/-- Exactness at `Ĥ⁻¹(V)` in the Tate hexagon of a short exact cyclic sequence. -/
theorem TateNegOne.exact_middle [IsCyclic G]
    {f : ρ.IntertwiningMap σ} {g : σ.IntertwiningMap τ}
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    Function.Exact (TateNegOne.map f) (TateNegOne.map g) := by
  obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := G)
  let F := tatePeriodicHom (f := f) s hs
  let J := tatePeriodicHom (f := g) s hs
  change Function.Exact F.flip.homology J.flip.homology
  exact TwoPeriodic.exact_middle (F := F.flip) (J := J.flip) hf hg hfg

/-! ### Connecting maps and the remaining four vertices -/

/-- The connecting map `Ĥ⁰(V″) → Ĥ⁻¹(V′)` and its lift formula for the Tate hexagon. -/
def TateZero.δ {f : ρ.IntertwiningMap σ} {g : σ.IntertwiningMap τ}
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (s : G) (hs : ∀ x : G, x ∈ Subgroup.zpowers s) :
    {d : TateZero τ →ₗ[k] TateNegOne ρ //
      ∀ (x : τ.invariants) (w : W) (v : LinearMap.ker ρ.norm),
        g w = (x : U) → f (v : V) = (σ s - LinearMap.id : W →ₗ[k] W) w →
          d (Submodule.Quotient.mk x) = Submodule.Quotient.mk v} := by
  refine ⟨TwoPeriodic.snake (F := tatePeriodicHom (f := f) s hs)
    (J := tatePeriodicHom (f := g) s hs) hf hg hfg, ?_⟩
  intro x w v hw hv
  exact TwoPeriodic.snake_mk (F := tatePeriodicHom (f := f) s hs)
    (J := tatePeriodicHom (f := g) s hs) hf hg hfg x w v hw hv

/-- The connecting map `Ĥ⁻¹(V″) → Ĥ⁰(V′)` and its norm-lift formula for the Tate hexagon. -/
def TateNegOne.δ {f : ρ.IntertwiningMap σ} {g : σ.IntertwiningMap τ}
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (s : G) (hs : ∀ x : G, x ∈ Subgroup.zpowers s) :
    {d : TateNegOne τ →ₗ[k] TateZero ρ //
      ∀ (x : LinearMap.ker τ.norm) (w : W) (v : ρ.invariants),
        g w = (x : U) → f (v : V) = σ.norm w →
          d (Submodule.Quotient.mk x) = Submodule.Quotient.mk v} := by
  refine ⟨TwoPeriodic.snake (F := (tatePeriodicHom (f := f) s hs).flip)
    (J := (tatePeriodicHom (f := g) s hs).flip) hf hg hfg, ?_⟩
  intro x w v hw hv
  exact TwoPeriodic.snake_mk (F := (tatePeriodicHom (f := f) s hs).flip)
    (J := (tatePeriodicHom (f := g) s hs).flip) hf hg hfg x w v hw hv

/-- Exactness at `Ĥ⁰(V″)` in the Tate hexagon. -/
theorem exact_zero_right {f : ρ.IntertwiningMap σ} {g : σ.IntertwiningMap τ}
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (s : G) (hs : ∀ x : G, x ∈ Subgroup.zpowers s) :
    Function.Exact (TateZero.map g) (TateZero.δ hf hg hfg s hs).val :=
  TwoPeriodic.snake_right (F := tatePeriodicHom (f := f) s hs)
    (J := tatePeriodicHom (f := g) s hs) hf hg hfg

/-- Exactness at `Ĥ⁻¹(V′)` in the Tate hexagon. -/
theorem exact_neg_left {f : ρ.IntertwiningMap σ} {g : σ.IntertwiningMap τ}
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (s : G) (hs : ∀ x : G, x ∈ Subgroup.zpowers s) :
    Function.Exact (TateZero.δ hf hg hfg s hs).val (TateNegOne.map f) :=
  TwoPeriodic.snake_left (F := tatePeriodicHom (f := f) s hs)
    (J := tatePeriodicHom (f := g) s hs) hf hg hfg

/-- Exactness at `Ĥ⁻¹(V″)` in the Tate hexagon. -/
theorem exact_neg_right {f : ρ.IntertwiningMap σ} {g : σ.IntertwiningMap τ}
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (s : G) (hs : ∀ x : G, x ∈ Subgroup.zpowers s) :
    Function.Exact (TateNegOne.map g) (TateNegOne.δ hf hg hfg s hs).val :=
  TwoPeriodic.snake_right (F := (tatePeriodicHom (f := f) s hs).flip)
    (J := (tatePeriodicHom (f := g) s hs).flip) hf hg hfg

/-- Exactness at `Ĥ⁰(V′)` in the Tate hexagon. -/
theorem exact_zero_left {f : ρ.IntertwiningMap σ} {g : σ.IntertwiningMap τ}
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (s : G) (hs : ∀ x : G, x ∈ Subgroup.zpowers s) :
    Function.Exact (TateNegOne.δ hf hg hfg s hs).val (TateZero.map f) :=
  TwoPeriodic.snake_left (F := (tatePeriodicHom (f := f) s hs).flip)
    (J := (tatePeriodicHom (f := g) s hs).flip) hf hg hfg


end Representation
end SIC
