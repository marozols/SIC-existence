/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Indices in groups

Equality from finite relative indices, products and intersections with a third subgroup,
complementary index counting, and power indices from free rank and invariance under finite-index
subgroups.

The power-index calculation is used in Milne, *Class Field Theory*, version 4.03 (2020),
Chapter VII, §6, in the construction preceding Lemma 6.2 and Proposition 6.8; the product and
intersection identity is his Lemma 6.5. The complementary counting is the index argument of
Childress, *Class Field Theory* (2009), Chapter VI, proof of Theorem 2.9.

## The argument

For nested subgroups, multiplicativity of relative indices shows that equal nonzero relative
indices force the intermediate index to be one, hence the subgroups are equal.

For `B ≤ A` and a third subgroup `C` of a commutative group, the modular law and the second
isomorphism theorem give $[A\,C:B\,C]\cdot[A\cap C:B\cap C]=[A:B]$. If `B₁` and `B₂` have
intersection `E` and join `G`, then $[B_1:E]=[G:B_2]$, so $[G:E]=[G:B_1][G:B_2]$. When subgroups
$N_i\supseteq P\,B_i$ have the indices of the principal parts of the opposite subgroups, these
two identities turn the inclusions into two inequalities whose product is an equality.

The torsion subgroup of a finitely generated abelian group is finite, and its quotient is
free. The resulting exact sequence splits. On the free factor, multiplication by n has
index n to the rank; on the finite factor its kernel and cokernel have equal cardinality.
For a finite-index subgroup, compare the indices of its power image through the subgroup
and through the full power image. The discrepancy is the index of the subgroup inside its
product with the power kernel, exactly the discrepancy between the two kernel orders.
-/

noncomputable section

namespace SIC

/-! ### Power kernels -/

/-- The kernel of powering on a subgroup containing the roots of unity is the full
root-of-unity group. This is the common kernel calculation for local units and S-units. -/
def powKerEquivRootsOfUnity {M : Type*} [CommMonoid M] (n : ℕ)
    (H : _root_.Subgroup Mˣ) (hH : rootsOfUnity n M ≤ H) :
    (powMonoidHom n : H →* H).ker ≃ rootsOfUnity n M where
  toFun x := ⟨x.val.val, by
    rw [rootsOfUnity_eq_ker]
    exact congrArg Subtype.val x.property⟩
  invFun x := ⟨⟨x.val, hH x.property⟩, by
    apply Subtype.ext
    exact (mem_rootsOfUnity n x.val).mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### Equality from relative indices

Multiplicativity of indices in a subgroup tower detects equality when the upper index is
nonzero. -/

namespace Subgroup

/-- If `A ≤ B ≤ H` and their nonzero relative indices in `H` agree, then `A = B`. -/
theorem eq_of_le_of_relIndex_eq {G : Type*} [Group G] (A B H : _root_.Subgroup G)
    (hAB : A ≤ B) (hBH : B ≤ H) (heq : A.relIndex H = B.relIndex H)
    (hH : B.relIndex H ≠ 0) : A = B := by
  have hm := _root_.Subgroup.relIndex_mul_relIndex A B H hAB hBH
  have hone : A.relIndex B = 1 := Nat.mul_right_cancel (Nat.pos_of_ne_zero hH) (by
    rw [hm, heq, one_mul])
  exact le_antisymm hAB (_root_.Subgroup.relIndex_eq_one.mp hone)

/-- If `A ≤ B` and their nonzero indices agree, then `A = B`. -/
theorem eq_of_le_of_index_eq {G : Type*} [Group G] (A B : _root_.Subgroup G)
    (hAB : A ≤ B) (heq : A.index = B.index) (hB : B.index ≠ 0) : A = B := by
  apply eq_of_le_of_relIndex_eq A B ⊤ hAB le_top
  · simpa only [_root_.Subgroup.relIndex_top_right] using heq
  · simpa only [_root_.Subgroup.relIndex_top_right] using hB

/-! ### Products and intersections with a third subgroup

For `B ≤ A`, joining with and intersecting with a subgroup `C` splits the relative index of `B`
in `A`; along an injective homomorphism, intersection with its range is pullback. These identities
compare the local-power subgroups with their principal parts in the second inequality and in the
complementary Kummer counting, where both a product and an intersection with the principal
idèles occur. -/

/-- The product/intersection index identity
$[A\,C:B\,C]\cdot[A\cap C:B\cap C]=[A:B]$ for `B ≤ A` in a commutative group. Milne,
*Class Field Theory*, Chapter VII, Lemma 6.5. -/
theorem relIndex_sup_mul_inf {G : Type*} [CommGroup G]
    (A B C : _root_.Subgroup G) (hBA : B ≤ A) :
    (B ⊔ C).relIndex (A ⊔ C) * (B ⊓ C).relIndex (A ⊓ C) = B.relIndex A := by
  have hmod : (B ⊔ C) ⊓ A = (A ⊓ C) ⊔ B := by
    rw [inf_comm, sup_comm B C, ← inf_sup_assoc_of_le C hBA]
  have hleft : B.relIndex ((B ⊔ C) ⊓ A) = (B ⊓ C).relIndex (A ⊓ C) := by
    rw [hmod, _root_.Subgroup.relIndex_sup_right, ← _root_.Subgroup.inf_relIndex_right,
      ← inf_assoc, inf_of_le_left hBA]
  have hright : (B ⊔ C).relIndex A = (B ⊔ C).relIndex (A ⊔ C) := by
    rw [← _root_.Subgroup.relIndex_sup_right A (B ⊔ C), ← sup_assoc, sup_eq_left.mpr hBA]
  simpa only [hleft, hright, inf_sup_self, mul_comm] using
    _root_.Subgroup.relIndex_inf_mul_relIndex B (B ⊔ C) A

/-- Intersecting with the range of a homomorphism computes relative indices by pullback:
$[A\cap f(H):B\cap f(H)]=[f^{-1}A:f^{-1}B]$. -/
theorem relIndex_inf_range {G H : Type*} [Group G] [Group H]
    (A B : _root_.Subgroup G) (f : H →* G) :
    (B ⊓ f.range).relIndex (A ⊓ f.range) = (B.comap f).relIndex (A.comap f) := by
  rw [_root_.Subgroup.relIndex_comap, _root_.Subgroup.map_comap_eq, inf_comm f.range A]
  rw [← _root_.Subgroup.inf_relIndex_right B (A ⊓ f.range),
    ← _root_.Subgroup.inf_relIndex_right (B ⊓ f.range) (A ⊓ f.range)]
  congr 1
  simp [inf_left_comm, inf_comm]

/-! ### Complementary subgroups

Two subgroups `B₁, B₂` of `G` with intersection `E` and join `G` split the index of `E`:
$[G:E]=[G:B_1][G:B_2]$. Childress compares the norm groups of two Kummer fields with
$P\,B_1$ and $P\,B_2$, where `P` is the principal subgroup: each norm group contains the
corresponding product, and each Kummer degree is the principal index of the *other* subgroup.
The two inclusions give two index inequalities whose product is an equality, so both are
equalities. -/

/-- Complementary subgroups split the index of their intersection. Used by
`index_sup_mul_index_sup_of_complementary`. -/
private theorem relIndex_mul_relIndex_of_complementary {G' : Type*} [CommGroup G']
    {E B₁ B₂ G : _root_.Subgroup G'} (hinf : B₁ ⊓ B₂ = E) (hsup : B₁ ⊔ B₂ = G) :
    B₁.relIndex G * B₂.relIndex G = E.relIndex G := by
  calc
    _ = B₂.relIndex G * B₁.relIndex G := mul_comm _ _
    _ = E.relIndex B₁ * B₁.relIndex G := by
      congr 1
      rw [← hinf, ← hsup, Subgroup.inf_relIndex_left, Subgroup.relIndex_sup_right]
    _ = E.relIndex G := Subgroup.relIndex_mul_relIndex E B₁ G
      (hinf ▸ inf_le_left) (hsup ▸ le_sup_left)

/-- The two product indices multiply to the product of the opposite principal-part indices.
This is the product equality used by `eq_sup_of_complementary`. -/
private theorem index_sup_mul_index_sup_of_complementary {G' : Type*} [CommGroup G']
    {P G E B₁ B₂ : _root_.Subgroup G'} (hinf : B₁ ⊓ B₂ = E) (hsup : B₁ ⊔ B₂ = G)
    (htop : P ⊔ G = ⊤) {s : ℕ} (hs : s ≠ 0) (hG : E.relIndex G = s ^ 2)
    (hP : (E ⊓ P).relIndex (G ⊓ P) = s) :
    (P ⊔ B₁).index * (P ⊔ B₂).index =
      (E ⊓ P).relIndex (B₂ ⊓ P) * (E ⊓ P).relIndex (B₁ ⊓ P) := by
  let a₁ := (P ⊔ B₁).index
  let a₂ := (P ⊔ B₂).index
  let c₁ := (B₁ ⊓ P).relIndex (G ⊓ P)
  let c₂ := (B₂ ⊓ P).relIndex (G ⊓ P)
  let d₁ := (E ⊓ P).relIndex (B₁ ⊓ P)
  let d₂ := (E ⊓ P).relIndex (B₂ ⊓ P)
  have hA₁ : a₁ * c₁ = B₁.relIndex G := by
    simpa only [a₁, c₁, sup_comm B₁ P, sup_comm G P, htop,
      Subgroup.relIndex_top_right] using
      relIndex_sup_mul_inf G B₁ P (hsup ▸ le_sup_left)
  have hA₂ : a₂ * c₂ = B₂.relIndex G := by
    simpa only [a₂, c₂, sup_comm B₂ P, sup_comm G P, htop,
      Subgroup.relIndex_top_right] using
      relIndex_sup_mul_inf G B₂ P (hsup ▸ le_sup_right)
  have hC₁ : d₁ * c₁ = s := by
    exact (Subgroup.relIndex_mul_relIndex (E ⊓ P) (B₁ ⊓ P) (G ⊓ P)
      (inf_le_inf (hinf ▸ inf_le_left) le_rfl)
      (inf_le_inf (hsup ▸ le_sup_left) le_rfl)).trans hP
  have hC₂ : d₂ * c₂ = s := by
    exact (Subgroup.relIndex_mul_relIndex (E ⊓ P) (B₂ ⊓ P) (G ⊓ P)
      (inf_le_inf (hinf ▸ inf_le_right) le_rfl)
      (inf_le_inf (hsup ▸ le_sup_right) le_rfl)).trans hP
  have hc₁ : c₁ ≠ 0 := right_ne_zero_of_mul (by rw [hC₁]; exact hs)
  have hc₂ : c₂ ≠ 0 := right_ne_zero_of_mul (by rw [hC₂]; exact hs)
  change a₁ * a₂ = d₂ * d₁
  apply Nat.mul_right_cancel (Nat.pos_of_ne_zero (mul_ne_zero hc₁ hc₂))
  calc
    a₁ * a₂ * (c₁ * c₂) = (a₁ * c₁) * (a₂ * c₂) := by ac_rfl
    _ = s ^ 2 := by
      rw [hA₁, hA₂, relIndex_mul_relIndex_of_complementary hinf hsup, hG]
    _ = (d₁ * c₁) * (d₂ * c₂) := by rw [hC₁, hC₂, pow_two]
    _ = d₂ * d₁ * (c₁ * c₂) := by ac_rfl

/-- **Complementary index counting.** Let `B₁ ⊓ B₂ = E` and `B₁ ⊔ B₂ = G` in a commutative
group, let `P ⊔ G = ⊤`, and suppose $[G:E]=s^2$ and $[G\cap P:E\cap P]=s\ne0$. If
$N_1\supseteq P\,B_1$ and $N_2\supseteq P\,B_2$ have indices $[B_2\cap P:E\cap P]$ and
$[B_1\cap P:E\cap P]$, then $N_1=P\,B_1$. This is the counting in Childress, *Class Field
Theory* (2009), Chapter VI, proof of Theorem 2.9, inequalities (∗) and (∗∗), with `P` the
principal idèles, `G` the idèles integral outside `S`, and $N_i$ the norm groups of the
complementary Kummer fields. -/
theorem eq_sup_of_complementary {G' : Type*} [CommGroup G']
    {P G E B₁ B₂ N₁ N₂ : _root_.Subgroup G'} (hinf : B₁ ⊓ B₂ = E) (hsup : B₁ ⊔ B₂ = G)
    (htop : P ⊔ G = ⊤) {s : ℕ} (hs : s ≠ 0) (hG : E.relIndex G = s ^ 2)
    (hP : (E ⊓ P).relIndex (G ⊓ P) = s) (h₁ : P ⊔ B₁ ≤ N₁) (h₂ : P ⊔ B₂ ≤ N₂)
    (hN₁ : N₁.index = (E ⊓ P).relIndex (B₂ ⊓ P))
    (hN₂ : N₂.index = (E ⊓ P).relIndex (B₁ ⊓ P)) :
    N₁ = P ⊔ B₁ := by
  have hprod := index_sup_mul_index_sup_of_complementary hinf hsup htop hs hG hP
  have hd₁ : (E ⊓ P).relIndex (B₁ ⊓ P) ≠ 0 :=
    left_ne_zero_of_mul (by
      rw [Subgroup.relIndex_mul_relIndex (E ⊓ P) (B₁ ⊓ P) (G ⊓ P)
        (inf_le_inf (hinf ▸ inf_le_left) le_rfl)
        (inf_le_inf (hsup ▸ le_sup_left) le_rfl), hP]
      exact hs)
  have hd₂ : (E ⊓ P).relIndex (B₂ ⊓ P) ≠ 0 :=
    left_ne_zero_of_mul (by
      rw [Subgroup.relIndex_mul_relIndex (E ⊓ P) (B₂ ⊓ P) (G ⊓ P)
        (inf_le_inf (hinf ▸ inf_le_right) le_rfl)
        (inf_le_inf (hsup ▸ le_sup_right) le_rfl), hP]
      exact hs)
  have ⟨ha₁, ha₂⟩ := mul_ne_zero_iff.mp (show
    (P ⊔ B₁).index * (P ⊔ B₂).index ≠ 0 by
      rw [hprod]; exact mul_ne_zero hd₂ hd₁)
  have hle₁ : (E ⊓ P).relIndex (B₂ ⊓ P) ≤ (P ⊔ B₁).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero ha₁) (hN₁ ▸ Subgroup.index_dvd_of_le h₁)
  have hle₂ : (E ⊓ P).relIndex (B₁ ⊓ P) ≤ (P ⊔ B₂).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero ha₂) (hN₂ ▸ Subgroup.index_dvd_of_le h₂)
  have heq : N₁.index = (P ⊔ B₁).index := by
    rw [hN₁]
    apply le_antisymm hle₁
    by_contra h
    have hlt : (E ⊓ P).relIndex (B₂ ⊓ P) < (P ⊔ B₁).index := Nat.lt_of_not_ge h
    have hstrict := Nat.mul_lt_mul_of_pos_right hlt (Nat.pos_of_ne_zero hd₁)
    have hweak := Nat.mul_le_mul_left (P ⊔ B₁).index hle₂
    rw [hprod] at hweak
    omega
  exact (eq_of_le_of_index_eq (P ⊔ B₁) N₁ h₁ heq.symm (hN₁ ▸ hd₂)).symm

end Subgroup

variable {M : Type*} [AddCommGroup M]

/-- Restriction to the torsion subgroup preserves the kernel of multiplication by nonzero n.
Used by `index_range_nsmul_eq_card_ker_mul_pow`. -/
private def nsmulTorsionKerEquiv (n : ℕ) (hn : n ≠ 0) :
    (nsmulAddMonoidHom (α := Submodule.torsion ℤ M) n).ker ≃
      (nsmulAddMonoidHom (α := M) n).ker where
  toFun x := ⟨x.1.1, congrArg Subtype.val x.2⟩
  invFun x := ⟨⟨x.1, ⟨⟨(n : ℤ), mem_nonZeroDivisors_iff_ne_zero.mpr
    (Int.natCast_ne_zero.mpr hn)⟩, by
      change (n : ℤ) • (x : M) = 0
      rw [natCast_zsmul]
      exact x.2⟩⟩, Subtype.ext x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- In a finitely generated abelian group, $[M:nM]=|M[n]|n^{\operatorname{rank}M}$.
This supplies the free-rank and torsion calculation in Milne, *Class Field Theory*,
Chapter VII, §6, construction preceding Lemma 6.2. -/
theorem index_range_nsmul_eq_card_ker_mul_pow [Module.Finite ℤ M] (n : ℕ) (hn : n ≠ 0) :
    (nsmulAddMonoidHom (α := M) n).range.index =
      Nat.card (nsmulAddMonoidHom (α := M) n).ker * n ^ Module.finrank ℤ M := by
  let T := Submodule.torsion ℤ M
  let F := M ⧸ T
  have : Finite T := Module.finite_of_fg_torsion T Submodule.torsion_isTorsion
  obtain ⟨s, hs⟩ := Module.projective_lifting_property T.mkQ LinearMap.id T.mkQ_surjective
  let e : (T × F) ≃ₗ[ℤ] M :=
    lequivProdOfRightSplitExact T.injective_subtype
      (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) hs
  have hp : (nsmulAddMonoidHom (α := T × F) n) =
      (nsmulAddMonoidHom (α := T) n).prodMap (nsmulAddMonoidHom (α := F) n) := rfl
  calc
    _ = (nsmulAddMonoidHom (α := T × F) n).range.index := by
      simpa only [AddEquiv.map_range_nsmulAddMonoidHom] using
        AddSubgroup.index_map_equiv (nsmulAddMonoidHom (α := T × F) n).range e.toAddEquiv
    _ = Nat.card (nsmulAddMonoidHom (α := T) n).ker * n ^ Module.finrank ℤ F := by
      rw [hp, AddMonoidHom.range_prodMap, AddSubgroup.index_prod,
        AddSubgroup.index_range, AddSubgroup.index_range_nsmul]
    _ = _ := by
      rw [Nat.card_congr (nsmulTorsionKerEquiv (M := M) n hn),
        finrank_quotient_eq_of_le_torsion (le_refl T)]

/-- Multiplicative form of `index_range_nsmul_eq_card_ker_mul_pow`:
$[G:G^n]=|G[n]|n^{\operatorname{rank}G}$. -/
theorem index_range_pow_eq_card_ker_mul_pow {G : Type*} [CommGroup G]
    [Module.Finite ℤ (Additive G)] (n : ℕ) (hn : n ≠ 0) :
    (powMonoidHom (α := G) n).range.index =
      Nat.card (powMonoidHom (α := G) n).ker * n ^ Module.finrank ℤ (Additive G) := by
  have h := index_range_nsmul_eq_card_ker_mul_pow (M := Additive G) n hn
  change (powMonoidHom (α := G) n).toAdditive.range.index =
    Nat.card (powMonoidHom (α := G) n).toAdditive.ker * _ at h
  rw [MonoidHom.coe_toAdditive_range, Subgroup.index_toAddSubgroup,
    MonoidHom.coe_toAdditive_ker] at h
  exact h

/-! ### Passage to finite-index subgroups

The subgroup index formula compares power images; the subgroup order formula compares
power kernels. Their common relative index cancels to give Milne's invariant ratio. -/

/-- Compare power indices through the image of a finite-index subgroup. Used by
`index_pow_mul_card_ker_of_finiteIndex`. -/
private theorem index_pow_eq_mul_relIndex {G : Type*} [CommGroup G]
    (H : Subgroup G) [H.FiniteIndex] (n : ℕ) :
    (powMonoidHom n : G →* G).range.index =
      (powMonoidHom n : H →* H).range.index * H.relIndex (powMonoidHom n : G →* G).ker := by
  let f := powMonoidHom (α := G) n
  have hle : H.map f ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact H.pow_mem hx n
  have hmap := Subgroup.relIndex_mul_index hle
  rw [Subgroup.relIndex, H.subgroupOf_map_powMonoidHom_eq_range n, H.index_map f] at hmap
  have hi := Subgroup.relIndex_mul_index (show H ≤ H ⊔ f.ker from le_sup_left)
  rw [Subgroup.relIndex_sup_left] at hi
  have hz : (H ⊔ f.ker).index ≠ 0 := (Subgroup.finiteIndex_of_le le_sup_left).index_ne_zero
  apply mul_left_cancel₀ hz
  rw [← hmap, ← hi]
  ac_rfl

/-- The cross-multiplied power-kernel and power-cokernel cardinality identity for a
finite-index subgroup. For finite kernels and cokernels, their ratio is unchanged.
Milne, *Class Field Theory*, Chapter VII, Proposition 6.8, applying the finite-module
invariance of the Herbrand quotient. -/
theorem index_pow_mul_card_ker_of_finiteIndex {G : Type*} [CommGroup G]
    (H : Subgroup G) [H.FiniteIndex] (n : ℕ) :
    (powMonoidHom n : G →* G).range.index *
      Nat.card (powMonoidHom n : H →* H).ker =
        (powMonoidHom n : H →* H).range.index *
          Nat.card (powMonoidHom n : G →* G).ker := by
  let f := powMonoidHom (α := G) n
  let e : H.subgroupOf f.ker ≃ (powMonoidHom n : H →* H).ker :=
    { toFun := fun x => ⟨⟨x.1.1, x.2⟩, Subtype.ext x.1.2⟩
      invFun := fun x => ⟨⟨x.1.1, congrArg Subtype.val x.2⟩, x.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard := (H.subgroupOf f.ker).card_mul_index
  rw [Nat.card_congr e] at hcard
  change Nat.card (powMonoidHom n : H →* H).ker * H.relIndex f.ker = Nat.card f.ker at hcard
  rw [index_pow_eq_mul_relIndex H n, mul_assoc, mul_comm (H.relIndex f.ker), hcard]

end SIC
