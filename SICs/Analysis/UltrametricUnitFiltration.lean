/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Analysis.UltrametricInverse
import Mathlib.Topology.Algebra.Group.Units

/-!
# Unit filtrations of complete ultrametric fields

Compact open lattices in a complete ultrametric field, the subgroups $1 + \varpi^i M$ of units
they define, and the multiplicative congruences of their successive quotients. This is the
filtration method in Serre, *Local class field theory*, Cassels–Fröhlich (1967), Chapter VI,
§1.4, Proposition 3.

## The argument

A compact open additive lattice has bounded norm and contains a small ball. A power of a
contracting scalar makes its elements small and sends products back into the lattice. Scaling
this lattice gives a decreasing sequence of closed additive subgroups. Their translates by one
are unit subgroups: multiplication follows from the product bound, and inversion follows by the
convergent geometric series. Compactness separates the levels, while multiplication raises a
level, so products and quotients linearize in successive quotients.
-/

noncomputable section

namespace SIC

/-- In an ultrametric field, an element within norm one of `1` has norm one. -/
theorem norm_one_add_of_norm_lt_one {E : Type*} [NontriviallyNormedField E]
    [IsUltrametricDist E] {a : E} (ha : ‖a‖ < 1) : ‖1 + a‖ = 1 := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm]
  · simpa using ha.le
  · simp [ne_of_gt ha]

/-! ### Scaled additive lattices -/

/-- A compact open additive lattice has a sufficiently small scalar multiple for the unit
filtration; used in `exists_unitSubgroup_tateTrivial`. -/
theorem exists_lattice_scale {E : Type*} [NontriviallyNormedField E]
    (π : E) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    (A : AddSubgroup E) (hAc : IsCompact (A : Set E))
    (hAo : IsOpen (A : Set E)) :
    ∃ k : ℕ,
      (∀ a ∈ A, ‖π ^ (k + 1) * a‖ < 1) ∧
      (∀ a ∈ A, ∀ b ∈ A, π ^ k * (a * b) ∈ A) := by
  obtain ⟨C₀, hC₀⟩ := hAc.isBounded.exists_norm_le
  let C := max 1 C₀
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hC : ∀ a ∈ A, ‖a‖ ≤ C := by
    intro a ha
    exact (hC₀ a ha).trans (le_max_right _ _)
  obtain ⟨ε, hεpos, hball⟩ := (Metric.isOpen_iff.mp hAo) 0 A.zero_mem
  have hsmall : ∀ z : E, ‖z‖ < ε → z ∈ A := by
    intro z hz
    apply hball
    simpa [Metric.mem_ball, dist_zero_left] using hz
  have hq : Filter.Tendsto (fun k : ℕ => ‖π‖ ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hπ0.le hπ1
  have ht : 0 < min (ε / (C * C)) (1 / C) :=
    lt_min (div_pos hεpos (mul_pos hCpos hCpos)) (div_pos zero_lt_one hCpos)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖π‖ ^ k < min (ε / (C * C)) (1 / C) :=
    (hq.eventually (eventually_lt_nhds ht)).exists
  have hkε : ‖π‖ ^ k * (C * C) < ε := by
    have := (lt_min_iff.mp hk).1
    exact (lt_div_iff₀ (mul_pos hCpos hCpos)).mp this
  have hk1 : ‖π‖ ^ k * C < 1 := by
    have := (lt_min_iff.mp hk).2
    exact (lt_div_iff₀ hCpos).mp this
  refine ⟨k, ?_, ?_⟩
  · intro a ha
    rw [norm_mul, norm_pow]
    have hqa : ‖π‖ ^ k * ‖a‖ < 1 :=
      (mul_le_mul_of_nonneg_left (hC a ha) (pow_nonneg (norm_nonneg _) _)).trans_lt hk1
    calc
      ‖π‖ ^ (k + 1) * ‖a‖ = ‖π‖ * (‖π‖ ^ k * ‖a‖) := by ring
      _ < 1 := by nlinarith [mul_lt_mul_of_pos_left hqa hπ0]
  · intro a ha b hb
    apply hsmall
    rw [norm_mul, norm_pow, norm_mul]
    have hprod : ‖a‖ * ‖b‖ ≤ C * C :=
      mul_le_mul (hC a ha) (hC b hb) (norm_nonneg _) hCpos.le
    exact (mul_le_mul_of_nonneg_left hprod (pow_nonneg (norm_nonneg _) _)).trans_lt hkε

/-- A compact open additive lattice with a chosen scale for Serre's unit filtration.
The scalar preserves the lattice, and products of two scaled elements gain a level.
Used in `exists_unitSubgroup_tateTrivial`. -/
structure UnitLattice (E : Type*) [NontriviallyNormedField E] where
  /-- The contracting scalar. -/
  π : E
  /-- The scalar is nonzero. -/
  π_ne : π ≠ 0
  /-- The scalar contracts the norm. -/
  π_lt_one : ‖π‖ < 1
  /-- The scale at which the unit filtration starts. -/
  k : ℕ
  /-- The additive lattice. -/
  A : AddSubgroup E
  /-- The scalar preserves the lattice. -/
  π_mul_mem : ∀ a ∈ A, π * a ∈ A
  /-- Products of lattice elements enter the scaled lattice. -/
  mul_mem : ∀ a ∈ A, ∀ b ∈ A, π ^ k * (a * b) ∈ A
  /-- The initial scaled lattice lies in the open unit ball. -/
  norm_lt_one : ∀ a ∈ A, ‖π ^ (k + 1) * a‖ < 1
  /-- The lattice is compact. -/
  Acompact : IsCompact (A : Set E)
  /-- The lattice is open. -/
  Aopen : IsOpen (A : Set E)

/-- Choose a scale for a compact open lattice stable under a contracting scalar, for
`exists_unitSubgroup_tateTrivial`. -/
noncomputable def UnitLattice.ofCompactOpen {E : Type*} [NontriviallyNormedField E]
    (π : E) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    (A : AddSubgroup E) (hAc : IsCompact (A : Set E))
    (hAo : IsOpen (A : Set E)) (hπA : ∀ a ∈ A, π * a ∈ A) : UnitLattice E := by
  let k := Classical.choose (exists_lattice_scale π hπ0 hπ1 A hAc hAo)
  let h := Classical.choose_spec (exists_lattice_scale π hπ0 hπ1 A hAc hAo)
  exact ⟨π, norm_pos_iff.mp hπ0, hπ1, k, A, hπA, h.2, h.1,
    hAc, hAo⟩

namespace UnitLattice

variable {E : Type*} [NontriviallyNormedField E] (D : UnitLattice E)

/-- The scaled additive lattice $\pi^{k+1+i}A$ at level `i`. -/
def scaledLevel (i : ℕ) : AddSubgroup E :=
  D.A.map (AddMonoidHom.mulLeft (D.π ^ (D.k + 1 + i)))

/-- Membership in a scaled additive lattice. -/
theorem mem_level (i : ℕ) (x : E) :
    x ∈ D.scaledLevel i ↔ ∃ a ∈ D.A, D.π ^ (D.k + 1 + i) * a = x := by
  rfl

/-- Successive scaled lattices decrease. -/
theorem scaledLevel_antitone : Antitone D.scaledLevel := by
  apply antitone_nat_of_succ_le
  intro i x hx
  rcases (D.mem_level (i + 1) x).mp hx with ⟨a, ha, rfl⟩
  apply (D.mem_level i _).mpr
  refine ⟨D.π * a, D.π_mul_mem a ha, ?_⟩
  rw [show D.k + 1 + (i + 1) = (D.k + 1 + i) + 1 by omega, pow_succ]
  ring

/-- Powers of the contracting scalar preserve the lattice. -/
theorem mul_pow_mem (n : ℕ) (a : E) (ha : a ∈ D.A) : D.π ^ n * a ∈ D.A := by
  induction n with
  | zero => simpa using ha
  | succ n ih =>
    rw [pow_succ, mul_comm (D.π ^ n) D.π, mul_assoc]
    exact D.π_mul_mem _ ih

/-- A product of two elements at one level lies in the next level. -/
theorem mul_level (i : ℕ) {x y : E} (hx : x ∈ D.scaledLevel i) (hy : y ∈ D.scaledLevel i) :
    x * y ∈ D.scaledLevel (i + 1) := by
  rcases (D.mem_level i x).mp hx with ⟨a, ha, rfl⟩
  rcases (D.mem_level i y).mp hy with ⟨b, hb, rfl⟩
  apply (D.mem_level (i + 1) _).mpr
  have hA : D.π ^ i * (D.π ^ D.k * (a * b)) ∈ D.A :=
    D.mul_pow_mem i _ (D.mul_mem a ha b hb)
  refine ⟨D.π ^ i * (D.π ^ D.k * (a * b)), hA, ?_⟩
  have ht : D.k + 1 + (i + 1) + (i + D.k) = 2 * (D.k + 1 + i) := by omega
  calc
    D.π ^ (D.k + 1 + (i + 1)) * (D.π ^ i * (D.π ^ D.k * (a * b))) =
        D.π ^ (D.k + 1 + (i + 1) + (i + D.k)) * (a * b) := by
          simp [pow_add, mul_assoc, mul_comm, mul_left_comm]
    _ = (D.π ^ (D.k + 1 + i) * a) * (D.π ^ (D.k + 1 + i) * b) := by
      rw [ht, pow_mul]
      ring

/-- Every element of a scaled lattice has norm below one. -/
theorem norm_level (i : ℕ) {x : E} (hx : x ∈ D.scaledLevel i) : ‖x‖ < 1 := by
  rcases (D.mem_level i x).mp hx with ⟨a, ha, rfl⟩
  have hpow : ‖D.π‖ ^ i ≤ 1 := pow_le_one₀ (norm_nonneg _) D.π_lt_one.le
  have hpow' : D.π ^ (D.k + 1 + i) * a = D.π ^ i * (D.π ^ (D.k + 1) * a) := by
    rw [pow_add]
    ring
  rw [hpow', norm_mul, norm_pow]
  exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans_lt
    (by simpa using D.norm_lt_one a ha)

end UnitLattice

/-- A closed multiplicatively stable small additive subgroup contains the inverse
correction; used in `UnitLattice.unitSubgroup`. -/
theorem one_add_inv_mem {E : Type*} [NontriviallyNormedField E] [CompleteSpace E]
    (B : AddSubgroup E) (hclosed : IsClosed (B : Set E))
    (hmul : ∀ a ∈ B, ∀ b ∈ B, a * b ∈ B)
    (hnorm : ∀ a ∈ B, ‖a‖ < 1)
    (x : Eˣ) (hx : (x : E) - 1 ∈ B) : ((x⁻¹ : Eˣ) : E) - 1 ∈ B := by
  let a : E := (x : E) - 1
  have haNorm : ‖-a‖ < 1 := by simpa using hnorm a hx
  have hsum : HasSum (fun n : ℕ => -a * (-a) ^ n) (-a * (1 + a)⁻¹) := by
    convert (hasSum_geometric_of_norm_lt_one haNorm).mul_left (-a) using 1; simp [a]
  have hpow : ∀ n : ℕ, (-a) ^ n * (-a) ∈ B := by
    intro n
    induction n with
    | zero => simpa [a] using B.neg_mem hx
    | succ n ih =>
      rw [pow_succ]
      exact hmul _ ih _ (B.neg_mem hx)
  have hpartial : ∀ n : ℕ, ∑ j ∈ Finset.range n, -a * (-a) ^ j ∈ B := by
    intro n
    apply B.sum_mem
    intro j hj
    rw [mul_comm]
    exact hpow j
  have hlim : -a * (1 + a)⁻¹ ∈ B :=
    hclosed.mem_of_tendsto hsum.tendsto_sum_nat (Filter.Eventually.of_forall hpartial)
  convert hlim using 1
  have hxa : (x : E) = 1 + a := by simp [a]
  rw [Units.val_inv_eq_inv_val, hxa]
  have hne : (1 + a : E) ≠ 0 := by simp [← hxa]
  field_simp
  ring

namespace UnitLattice

variable {E : Type*} [NontriviallyNormedField E] (D : UnitLattice E)

/-- Each scaled lattice is closed. -/
theorem scaledLevel_isClosed (i : ℕ) : IsClosed (D.scaledLevel i : Set E) := by
  change IsClosed ((fun a : E => D.π ^ (D.k + 1 + i) * a) '' (D.A : Set E))
  exact (Homeomorph.mulLeft₀ _ (pow_ne_zero _ D.π_ne)).isClosedMap _
    (D.A.isClosed_of_isOpen D.Aopen)

/-- Each scaled lattice is open. -/
theorem scaledLevel_isOpen (i : ℕ) : IsOpen (D.scaledLevel i : Set E) := by
  change IsOpen ((fun a : E => D.π ^ (D.k + 1 + i) * a) '' (D.A : Set E))
  exact (Homeomorph.mulLeft₀ _ (pow_ne_zero _ D.π_ne)).isOpenMap _ D.Aopen

variable [CompleteSpace E]

/-- The subgroup of units congruent to one modulo the scaled lattice at level `i`. -/
def unitSubgroup (i : ℕ) : Subgroup Eˣ where
  carrier := {x | (x : E) - 1 ∈ D.scaledLevel i}
  one_mem' := by
    change (1 : E) - 1 ∈ D.scaledLevel i
    simp
  mul_mem' := by
    intro x y hx hy
    have hxy : ((x : E) - 1) * ((y : E) - 1) ∈ D.scaledLevel i :=
      D.scaledLevel_antitone (Nat.le_succ i) (D.mul_level i hx hy)
    have heq : ((x : E) * (y : E) - 1) =
        ((x : E) - 1) + ((y : E) - 1) + ((x : E) - 1) * ((y : E) - 1) := by ring
    change ((x : E) * (y : E) - 1) ∈ D.scaledLevel i
    rw [heq]
    exact (D.scaledLevel i).add_mem ((D.scaledLevel i).add_mem hx hy) hxy
  inv_mem' := by
    intro x hx
    apply one_add_inv_mem (D.scaledLevel i) (D.scaledLevel_isClosed i) ?_ ?_ x hx
    · intro a ha b hb
      exact D.scaledLevel_antitone (Nat.le_succ i) (D.mul_level i ha hb)
    · intro a ha
      exact D.norm_level i ha

/-- Each unit filtration term is closed. -/
theorem unitSubgroup_isClosed (i : ℕ) : IsClosed (D.unitSubgroup i : Set Eˣ) := by
  change IsClosed ((fun x : Eˣ => (x : E) - 1) ⁻¹' (D.scaledLevel i : Set E))
  exact (D.scaledLevel_isClosed i).preimage (Units.continuous_val.sub continuous_const)

/-- Each unit filtration term is open. -/
theorem unitSubgroup_isOpen (i : ℕ) : IsOpen (D.unitSubgroup i : Set Eˣ) := by
  change IsOpen ((fun x : Eˣ => (x : E) - 1) ⁻¹' (D.scaledLevel i : Set E))
  exact (D.scaledLevel_isOpen i).preimage (Units.continuous_val.sub continuous_const)

/-- The unit filtration decreases. -/
theorem unitSubgroup_antitone : Antitone D.unitSubgroup := by
  intro i j hij x hx
  exact D.scaledLevel_antitone hij hx

/-- Every unit in this filtration has norm one. -/
theorem unitSubgroup_norm_eq_one [IsUltrametricDist E]
    (i : ℕ) {x : Eˣ} (hx : x ∈ D.unitSubgroup i) : ‖(x : E)‖ = 1 := by
  have ha : ‖(x : E) - 1‖ < 1 := D.norm_level i hx
  have hxp : (x : E) = 1 + ((x : E) - 1) := by ring
  rw [hxp]
  exact norm_one_add_of_norm_lt_one ha

end UnitLattice


namespace UnitLattice

variable {E : Type*} [NontriviallyNormedField E] (D : UnitLattice E)

/-- The intersection of all scaled lattice levels is zero. -/
theorem scaledLevel_separated (x : E) (hx : ∀ i : ℕ, x ∈ D.scaledLevel i) : x = 0 := by
  obtain ⟨C, hC⟩ := D.Acompact.isBounded.exists_norm_le
  have hbound : ∀ i : ℕ, ‖x‖ ≤ ‖D.π‖ ^ (D.k + 1 + i) * C := by
    intro i
    rcases (D.mem_level i x).mp (hx i) with ⟨a, ha, rfl⟩
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (hC a ha) (pow_nonneg (norm_nonneg _) _)
  have hlim : Filter.Tendsto (fun i : ℕ => ‖D.π‖ ^ (D.k + 1 + i) * C)
      Filter.atTop (nhds 0) := by
    have hq := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg D.π) D.π_lt_one
    convert hq.mul_const (‖D.π‖ ^ (D.k + 1) * C) using 1
    · funext i
      rw [pow_add]
      ring
    · simp
  have hxle : ‖x‖ ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hbound
  exact norm_eq_zero.mp (le_antisymm hxle (norm_nonneg x))

variable [CompleteSpace E]

/-- The intersection of the unit filtration terms is trivial. -/
theorem unitSubgroup_separated : ⨅ i, D.unitSubgroup i = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hx0 : (x : E) - 1 = 0 :=
    D.scaledLevel_separated _ (fun i => (Subgroup.mem_iInf.mp hx i))
  apply Units.ext
  exact sub_eq_zero.mp hx0

end UnitLattice

/-- A product of terms `1 + a` is additive modulo the next lattice level; used in both
quotient steps. -/
theorem prod_one_add_mod {E ι : Type*} [CommRing E]
    (B C : AddSubgroup E) (hCB : C ≤ B)
    (hmul : ∀ a ∈ B, ∀ b ∈ B, a * b ∈ C)
    (s : Finset ι) (f : ι → E) (hf : ∀ j ∈ s, f j ∈ B) :
    (∏ j ∈ s, (1 + f j)) - 1 - ∑ j ∈ s, f j ∈ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    have hfj : f j ∈ B := hf j (Finset.mem_insert_self ..)
    have hfs : ∀ a ∈ s, f a ∈ B := by
      intro a ha
      exact hf a (Finset.mem_insert_of_mem ha)
    have he := ih hfs
    have hsum : ∑ a ∈ s, f a ∈ B := B.sum_mem fun a ha => hfs a ha
    have hprodsub : (∏ a ∈ s, (1 + f a)) - 1 ∈ B := by
      have heq : (∏ a ∈ s, (1 + f a)) - 1 =
          ((∏ a ∈ s, (1 + f a)) - 1 - ∑ a ∈ s, f a) + ∑ a ∈ s, f a := by ring
      rw [heq]
      exact B.add_mem (hCB he) hsum
    have hcross : f j * ((∏ a ∈ s, (1 + f a)) - 1) ∈ C :=
      hmul _ hfj _ hprodsub
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    have heq : (1 + f j) * (∏ a ∈ s, (1 + f a)) - 1 -
        (f j + ∑ a ∈ s, f a) =
        ((∏ a ∈ s, (1 + f a)) - 1 - ∑ a ∈ s, f a) +
          f j * ((∏ a ∈ s, (1 + f a)) - 1) := by ring
    rw [heq]
    exact C.add_mem he hcross

/-- A difference in the next lattice level yields a unit quotient there; used in both
quotient steps. -/
theorem div_mod_of_sub_mem {E : Type*} [Field E]
    (B C : AddSubgroup E) (hCB : C ≤ B)
    (hmul : ∀ a ∈ B, ∀ b ∈ B, a * b ∈ C)
    (u z : Eˣ) (hzd : ((z⁻¹ : Eˣ) : E) - 1 ∈ B)
    (hdiff : (u : E) - (z : E) ∈ C) :
    (((u / z : Eˣ) : E) - 1) ∈ C := by
  have hcross : ((u : E) - (z : E)) * (((z⁻¹ : Eˣ) : E) - 1) ∈ C :=
    hmul _ (hCB hdiff) _ hzd
  have heq : (((u / z : Eˣ) : E) - 1) =
      ((u : E) - (z : E)) +
        ((u : E) - (z : E)) * (((z⁻¹ : Eˣ) : E) - 1) := by
    rw [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp [z.ne_zero]
    ring
  rw [heq]
  exact C.add_mem hdiff hcross


/-! ### Units near one and linearization -/

/-- The unit `1 + a` for an element of norm below one; used in both quotient steps. -/
def unitOneAdd {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E]
    (a : E) (ha : ‖a‖ < 1) : Eˣ :=
  Units.mk0 (1 + a) (by
    have hn : ‖(1 + a : E)‖ = 1 := norm_one_add_of_norm_lt_one ha
    intro h
    simp [h] at hn)

/-- The value of the unit `1 + a`; used in both quotient steps. -/
theorem unitOneAdd_val {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E]
    (a : E) (ha : ‖a‖ < 1) : (unitOneAdd a ha : E) = 1 + a := rfl

/-- A product of units linearizes modulo the next lattice level; used in the
degree-minus-one step. -/
theorem prod_units_mod {E ι : Type*} [Field E]
    (B C : AddSubgroup E) (hCB : C ≤ B)
    (hmul : ∀ a ∈ B, ∀ b ∈ B, a * b ∈ C)
    (s : Finset ι) (f : ι → Eˣ) (hf : ∀ j ∈ s, (f j : E) - 1 ∈ B) :
    ((∏ j ∈ s, f j : Eˣ) : E) - 1 - ∑ j ∈ s, ((f j : E) - 1) ∈ C := by
  convert prod_one_add_mod B C hCB hmul s (fun j => (f j : E) - 1) hf using 1; simp

/-- A quotient of units linearizes modulo the next lattice level; used in the
degree-minus-one step. -/
theorem div_unit_linear_mod {E : Type*} [Field E]
    (B C : AddSubgroup E) (hmul : ∀ a ∈ B, ∀ b ∈ B, a * b ∈ C)
    (u z : Eˣ) (hu : (u : E) - 1 ∈ B) (hz : (z : E) - 1 ∈ B)
    (hzi : ((z⁻¹ : Eˣ) : E) - 1 ∈ B) :
    (((u / z : Eˣ) : E) - 1) - ((u : E) - (z : E)) ∈ C := by
  have hdiff : (u : E) - (z : E) ∈ B := by
    convert B.sub_mem hu hz using 1; ring
  have hcross := hmul _ hdiff _ hzi
  have heq : (((u / z : Eˣ) : E) - 1) - ((u : E) - (z : E)) =
      ((u : E) - (z : E)) * (((z⁻¹ : Eˣ) : E) - 1) := by
    rw [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp [z.ne_zero]
  rw [heq]
  exact hcross

/-- Form a unit from an element of one scaled lattice level. -/
def UnitLattice.oneAdd {E : Type*} [NontriviallyNormedField E]
    [CompleteSpace E] [IsUltrametricDist E] (D : UnitLattice E) (i : ℕ) (a : E)
    (ha : a ∈ D.scaledLevel i) : Eˣ :=
  unitOneAdd a (D.norm_level i ha)

/-- The underlying field element of a unit formed from a scaled lattice element. -/
theorem UnitLattice.oneAdd_val {E : Type*} [NontriviallyNormedField E]
    [CompleteSpace E] [IsUltrametricDist E] (D : UnitLattice E) (i : ℕ) (a : E)
    (ha : a ∈ D.scaledLevel i) : (D.oneAdd i a ha : E) = 1 + a :=
  unitOneAdd_val _ _

/-- A unit formed from a scaled lattice element lies in the matching filtration term. -/
theorem UnitLattice.oneAdd_mem {E : Type*} [NontriviallyNormedField E]
    [CompleteSpace E] [IsUltrametricDist E] (D : UnitLattice E) (i : ℕ) (a : E)
    (ha : a ∈ D.scaledLevel i) : D.oneAdd i a ha ∈ D.unitSubgroup i := by
  change (D.oneAdd i a ha : E) - 1 ∈ D.scaledLevel i
  simpa only [D.oneAdd_val, add_sub_cancel_left] using ha


end SIC
