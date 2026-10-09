/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Modules with permuted component spaces

A compatible family of linear transports over a group action defines a representation on its
sections, equivalent to coinduction from a stabilizer when the action is transitive.

This is the coordinate argument of Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII,
Proposition 2.2: a section `x` is sent to the function $g \mapsto g(x_{g^{-1}i})$. Its inverse
at $j=gi$ is $g(f(g^{-1}))$. The coinduction relation makes this independent of the choice of
`g`. The linear formulation shares this argument between finite and infinite completions and
between multiplicative groups and their integral-unit subgroups.
-/

noncomputable section
namespace SIC.Representation
variable (k G ι : Type*) [CommRing k] [Group G] [MulAction G ι]
  (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

/-- Linear transports between component spaces, compatible with the action on their indices.
This packages the coordinate action in Milne, Chapter VII, Proposition 2.2. -/
structure PermutedFamily where
  /-- Transport by `g` from the component at `i` to the component at `g • i = j`. -/
  map : ∀ (g : G) (i j : ι), g • i = j → V i ≃ₗ[k] V j
  /-- The identity transport fixes every component. -/
  map_one : ∀ i, map 1 i i (one_smul G i) = LinearEquiv.refl k (V i)
  /-- Transport by a product is successive transport. -/
  map_mul : ∀ (g h : G) (i j l : ι) (hij : h • i = j) (hjl : g • j = l),
    map (g * h) i l ((mul_smul g h i).trans (by rw [hij, hjl])) =
      (map h i j hij).trans (map g j l hjl)

variable {k G ι V}
namespace PermutedFamily
variable (F : PermutedFamily k G ι V)

/-- Changing the displayed source index does not change a coordinate transport used by
`sections`. -/
private lemma map_apply_congr (g : G) {a b c : ι} (hab : a = b)
    (ha : g • a = c) (hb : g • b = c) (x : ∀ i, V i) :
    F.map g a c ha (x a) = F.map g b c hb (x b) := by
  cases hab
  rfl

/-- The action on sections is $(g x)_j=g(x_{g^{-1}j})$. -/
def sections (F : PermutedFamily k G ι V) : _root_.Representation k G (∀ i, V i) := by
  refine {
    toFun := fun g => LinearMap.pi fun j =>
      (F.map g (g⁻¹ • j) j (smul_inv_smul g j)).toLinearMap.comp
        (LinearMap.proj (g⁻¹ • j))
    map_one' := ?_
    map_mul' := ?_
  }
  · ext x j
    change (F.map 1 (1⁻¹ • j) j (smul_inv_smul 1 j)) (x (1⁻¹ • j)) = x j
    convert congrArg (fun e : V j ≃ₗ[k] V j => e (x j)) (F.map_one j) using 1
    · exact F.map_apply_congr 1 (by simp) _ _ x
    · simp
  · intro g h
    ext x j
    have hi : (g * h)⁻¹ • j = h⁻¹ • g⁻¹ • j := by
      rw [mul_inv_rev, mul_smul]
    have hij : h • (h⁻¹ • g⁻¹ • j) = g⁻¹ • j := smul_inv_smul h (g⁻¹ • j)
    have hjl : g • (g⁻¹ • j) = j := smul_inv_smul g j
    have hm := F.map_mul g h (h⁻¹ • g⁻¹ • j) (g⁻¹ • j) j hij hjl
    change (F.map (g * h) ((g * h)⁻¹ • j) j (smul_inv_smul (g * h) j))
        (x ((g * h)⁻¹ • j)) =
      (F.map g (g⁻¹ • j) j (smul_inv_smul g j))
        ((F.map h (h⁻¹ • g⁻¹ • j) (g⁻¹ • j) (smul_inv_smul h (g⁻¹ • j)))
          (x (h⁻¹ • g⁻¹ • j)))
    convert congrArg (fun e : V (h⁻¹ • g⁻¹ • j) ≃ₗ[k] V j =>
      e (x (h⁻¹ • g⁻¹ • j))) hm using 1
    · exact F.map_apply_congr (g * h) hi _ _ x
    · simp only [LinearEquiv.trans_apply]

/-- Evaluation of the action on sections at one component. -/
@[simp] theorem sections_apply (g : G) (x : ∀ i, V i) (j : ι) :
    F.sections g x j = F.map g (g⁻¹ • j) j (smul_inv_smul g j) (x (g⁻¹ • j)) := rfl

/-- The stabilizer of `i` acts on the component at `i`. -/
def fiber (F : PermutedFamily k G ι V) (i : ι) :
    _root_.Representation k (MulAction.stabilizer G i) (V i) := by
  refine {
    toFun := fun s => (F.map s.1 i i (MulAction.mem_stabilizer_iff.mp s.2)).toLinearMap
    map_one' := ?_
    map_mul' := ?_
  }
  · ext x
    change (F.map (1 : G) i i (one_smul G i)) x = x
    exact congrArg (fun e : V i ≃ₗ[k] V i => e x) (F.map_one i)
  · intro s t
    ext x
    have hs : (s : G) • i = i := MulAction.mem_stabilizer_iff.mp s.2
    have ht : (t : G) • i = i := MulAction.mem_stabilizer_iff.mp t.2
    have hm := F.map_mul (s : G) (t : G) i i i ht hs
    change (F.map ((s * t : MulAction.stabilizer G i) : G) i i
        (MulAction.mem_stabilizer_iff.mp (s * t).2)) x =
      (F.map (s : G) i i hs) ((F.map (t : G) i i ht) x)
    simpa only [Subgroup.coe_mul, LinearEquiv.trans_apply] using
      congrArg (fun e : V i ≃ₗ[k] V i => e x) hm

/-- Evaluation of the stabilizer action on a component. -/
@[simp] theorem fiber_apply (i : ι) (s : MulAction.stabilizer G i) (x : V i) :
    F.fiber i s x = F.map s.1 i i (MulAction.mem_stabilizer_iff.mp s.2) x := rfl

/-- The section action at a transported index is the given component transport. -/
theorem sections_apply_image (g : G) (a b : ι) (hab : g • a = b)
    (x : ∀ j, V j) : F.sections g x b = F.map g a b hab (x a) := by
  rw [F.sections_apply]
  apply F.map_apply_congr
  rw [← hab, inv_smul_smul]

/-- Evaluation at a fixed index intertwines the section and stabilizer actions. -/
theorem sections_stabilizer_apply (i : ι) (s : MulAction.stabilizer G i)
    (x : ∀ j, V j) : F.sections (s : G) x i = F.fiber i s (x i) := by
  simpa only [F.fiber_apply] using
    F.sections_apply_image (s : G) i i (MulAction.mem_stabilizer_iff.mp s.2) x

/-- The map from sections to covariant functions in `coindEquiv`. -/
private def toCoind (i : ι) : (∀ j, V j) →ₗ[k]
    _root_.Representation.coindV (MulAction.stabilizer G i).subtype (F.fiber i) := by
  refine {
    toFun := fun x => ⟨fun g => F.sections g x i, ?_⟩
    map_add' := ?_
    map_smul' := ?_
  }
  · intro s g
    change F.sections ((s : G) * g) x i = F.fiber i s (F.sections g x i)
    rw [_root_.map_mul (F.sections) (s : G) g, Module.End.mul_apply]
    exact F.sections_stabilizer_apply i s (F.sections g x)
  · intro x y
    ext g
    exact congrArg (fun z => z i) (map_add (F.sections g) x y)
  · intro a x
    ext g
    exact congrArg (fun z => z i) (map_smul (F.sections g) a x)

/-- A representative carrying the base index to a given index, used by `coindEquiv`. -/
private def representative (i : ι) (htrans : ∀ j, ∃ g : G, g • i = j) (j : ι) : G :=
  Classical.choose (htrans j)

/-- The chosen representative carries the base index to its target, used by `coindEquiv`. -/
private lemma representative_spec (i : ι) (htrans : ∀ j, ∃ g : G, g • i = j)
    (j : ι) : representative i htrans j • i = j := Classical.choose_spec (htrans j)

/-- The coordinate inverse of `toCoind`, used by `coindEquiv`. -/
private def fromCoind (i : ι) (htrans : ∀ j, ∃ g : G, g • i = j)
    (f : _root_.Representation.coindV (MulAction.stabilizer G i).subtype (F.fiber i))
    (j : ι) : V j :=
  F.map (representative i htrans j) i j (representative_spec i htrans j)
    (f.1 (representative i htrans j)⁻¹)

/-- Reconstructing a section after forming its covariant function, used by `coindEquiv`. -/
private lemma fromCoind_toCoind (i : ι) (htrans : ∀ j, ∃ g : G, g • i = j)
    (x : ∀ j, V j) : F.fromCoind i htrans (F.toCoind i x) = x := by
  funext j
  let g := representative i htrans j
  have hg : g • i = j := representative_spec i htrans j
  change (F.map g i j hg) (F.sections g⁻¹ x i) = x j
  calc
    _ = F.sections g (F.sections g⁻¹ x) j :=
      (F.sections_apply_image g i j hg (F.sections g⁻¹ x)).symm
    _ = x j := congrFun (_root_.Representation.self_inv_apply F.sections g x) j

/-- Forming the covariant function after reconstructing a section, used by `coindEquiv`. -/
private lemma toCoind_fromCoind (i : ι) (htrans : ∀ j, ∃ g : G, g • i = j)
    (f : _root_.Representation.coindV (MulAction.stabilizer G i).subtype (F.fiber i)) :
    F.toCoind i (F.fromCoind i htrans f) = f := by
  ext g
  let j := g⁻¹ • i
  let r := representative i htrans j
  have hr : r • i = j := representative_spec i htrans j
  have hg : g • j = i := smul_inv_smul g i
  let s : MulAction.stabilizer G i := ⟨g * r, by
    change (g * r) • i = i
    rw [mul_smul, hr, hg]⟩
  have hcov : f.1 g = F.fiber i s (f.1 r⁻¹) := by
    have h := f.2 s r⁻¹
    simpa [s, mul_assoc] using h
  have hm := F.map_mul g r i j i hr hg
  change F.sections g (F.fromCoind i htrans f) i = f.1 g
  rw [F.sections_apply_image g j i hg]
  change (F.map g j i hg) ((F.map r i j hr) (f.1 r⁻¹)) = f.1 g
  have hcomp : (F.map g j i hg) ((F.map r i j hr) (f.1 r⁻¹)) =
      F.fiber i s (f.1 r⁻¹) := by
    simpa only [F.fiber_apply, LinearEquiv.trans_apply] using
      (congrArg (fun e : V i ≃ₗ[k] V i => e (f.1 r⁻¹)) hm).symm
  exact hcomp.trans hcov.symm

/-- The product of a transitive family is coinduced from any one component.
Milne, *Class Field Theory*, Chapter VII, Proposition 2.2, coordinate argument. -/
def coindEquiv (i : ι) (htrans : ∀ j, ∃ g : G, g • i = j) :
    (F.sections).Equiv
      (_root_.Representation.coind (MulAction.stabilizer G i).subtype (F.fiber i)) := by
  let e : (∀ j, V j) ≃ₗ[k]
      _root_.Representation.coindV (MulAction.stabilizer G i).subtype (F.fiber i) :=
    { F.toCoind i with
      invFun := F.fromCoind i htrans
      left_inv := F.fromCoind_toCoind i htrans
      right_inv := F.toCoind_fromCoind i htrans }
  refine _root_.Representation.Equiv.mk e ?_
  intro g
  ext x h
  change F.sections h (F.sections g x) i = F.sections (h * g) x i
  rw [_root_.map_mul]
  rfl

end PermutedFamily
end SIC.Representation
