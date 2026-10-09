/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.RayClassGroup.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# The quotient construction of the ray class group

The ray class group `Cl_{𝔪∞₂}(𝒪_K)` as the quotient of the monoid of integral ray ideals by the
ray-principal congruence, with its exact presentation; every ray ideal contains a totally positive
element `≡ 1 (mod 𝔪)`, which supplies the inverses.

This module constructs the group whose interface `SICs.ClassField.RayClassGroup.Basic` states:
the ideal-theoretic ray class group `J^𝔪/P^𝔪` of [83, Neukirch (1999), Chapter VI, §1, p. 365],
for the modulus `𝔪∞₂` of [AFK25, Definition 2.1, `defn:rayclassgroup`], written on integral
representatives as in Milne, *Class Field Theory*, version 4.03 (2020), Chapter V,
Proposition 1.6: two integral ideals `𝔞, 𝔟` coprime to `𝔪` have the same ray class exactly when
`a𝔞 = b𝔟` for nonzero `a, b ∈ 𝒪_K` with `a ≡ b (mod 𝔪)` and `ρ₂(a)ρ₂(b) > 0`. This is
`RayIdeal.IsEquivalent`. Neukirch's convention makes idèle components positive at every real
place (the remark after his Definition (1.7)), so his `P^𝔪` asks for a totally positive
generator; the group here asks for positivity only at `∞₂`, so it is the quotient of his by the
classes of ideals with a generator `≡ 1 (mod 𝔪)` negative at `∞₁`.

## The argument

The integral ideals coprime to `𝔪` form the submonoid `rayIdeals K m` of `Ideal (𝒪_K)`, whose
type is `RayIdeal K m`, and `RayIdeal.IsEquivalent F m` is an equivalence relation and a
congruence on it, with witnesses given by pairs of generators with `RayCongruent F m a b`
(`SICs.ClassField.RayClassGroup.Basic`), hence a `Con`; its quotient `RayClassQuotient F m` is a
commutative monoid, and the quotient map is surjective with equality given by the relation.

Every class is invertible. Given a ray ideal `I`, coprimality `I + 𝔪 = 𝒪_K` gives `i ∈ I` with
`i ≡ 1 (mod 𝔪)`; adding a large multiple of the positive rational integer `N(I𝔪) ∈ I𝔪` makes
it totally positive without changing its class modulo `𝔪` or its membership in `I` (when
`𝔪 = 0` the ray ideal is `𝒪_K` itself and `i = 1`). Milne's proof uses the strong approximation
theorem for the signs; the integer shift replaces it. With such an `α ∈ I`, `(α) = IJ` for an
integral ideal `J` dividing `(α)`, hence coprime to `𝔪`, and `IJ = (α)` is ray-principal:
`IJ · (1) = 𝒪_K · (α)` with `α - 1 ∈ 𝔪` and `α` positive at `∞₂`. So `[I][J] = 1`, every
element of the quotient is a unit, and `commGroupOfIsUnit` makes the quotient a commutative
group with the same multiplication. Packaging the quotient map with the equality criterion gives
`rayClassQuotientPresentation`.

Finally, equality in the ordinary ideal class group admits coprime integral witnesses by
`exists_isCoprime_generators_mul_eq_of_class_eq`.  Choosing one ray ideal over each ordinary
class, a ray class is encoded by that ordinary class, the two witnesses modulo `m`, and their
signs at the real places.  These data form a finite type, and equality of the codes gives the
cross-multiplied witnesses for `RayIdeal.IsEquivalent`.  This proves Milne's finiteness theorem.
-/

noncomputable section

open NumberField

namespace SIC

universe u

variable {K : Type u} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
  (F : RealQuadraticFieldData K) {m : Ideal (NumberField.RingOfIntegers K)}

/-! ### The ray class congruence

`RayIdeal.IsEquivalent F m` as a congruence on the monoid of integral ray ideals. -/

variable (m) in
/-- **The ray-principal congruence** on the monoid of integral ray ideals coprime to `𝔪`: the
relation `RayIdeal.IsEquivalent F m`, whose quotient is `Cl_{𝔪∞₂}(𝒪_K)`
[AFK25, Definition 2.1, `defn:rayclassgroup`]. -/
def rayClassCon : Con (RayIdeal K m) where
  r := RayIdeal.IsEquivalent F m
  iseqv := ⟨RayIdeal.IsEquivalent.refl, RayIdeal.IsEquivalent.symm, RayIdeal.IsEquivalent.trans⟩
  mul' := RayIdeal.IsEquivalent.mul

/-! ### A totally positive element congruent to one in every ray ideal

The step of Milne, *Class Field Theory*, version 4.03 (2020), Chapter V, Proposition 1.6 that
produces integral representatives: an integral ideal coprime to `𝔪` contains a totally positive
element `≡ 1 (mod 𝔪)`. The element is found by the Chinese remainder theorem (coprimality) and
an integer shift in place of the strong approximation theorem. It provides an inverse for every
ray class. -/

/-- **A positive integer of a nonzero ideal makes any element totally positive**: for
`N ≠ 0` some `t ∈ N ∩ ℕ` has `ρ_w(i + t) > 0` at every real place `w`, since `N(N) ∈ N`
is a positive integer (`Ideal.absNorm_mem`) and the finitely many `ρ_w(i)` are bounded
below. It replaces the strong approximation theorem in the proof of Milne, *Class Field
Theory*, version 4.03 (2020), Chapter V, Proposition 1.6; used by
`RayIdeal.exists_mem_sub_one_mem_forall_pos`. -/
theorem exists_natCast_mem_forall_pos_add (N : Ideal (NumberField.RingOfIntegers K))
    (hN : N ≠ ⊥) (i : NumberField.RingOfIntegers K) :
    ∃ t : ℕ, (t : NumberField.RingOfIntegers K) ∈ N ∧
      ∀ w : InfinitePlace K,
        0 < realEmbeddingAt K w ((i + t : NumberField.RingOfIntegers K) : K) := by
  let n := Ideal.absNorm N
  have hn : 0 < n := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hN)
  obtain ⟨M, hM⟩ := Finite.exists_le
    (fun w : InfinitePlace K ↦ -realEmbeddingAt K w (i : K))
  obtain ⟨k, hk⟩ := exists_nat_gt M
  refine ⟨k * n, ?_, ?_⟩
  · rw [Nat.cast_mul]
    exact N.mul_mem_left (k : NumberField.RingOfIntegers K) (Ideal.absNorm_mem N)
  · intro w
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hw := (hM w).trans_lt hk
    simp only [map_add, map_mul, map_natCast, Nat.cast_mul]
    nlinarith

/-- **Every ray ideal contains a totally positive element congruent to one modulo `𝔪`**: the
representative step in the proof of Milne, *Class Field Theory*, version 4.03 (2020), Chapter V,
Proposition 1.6, with the signs arranged by adding a multiple of the positive integer
`N(I𝔪) ∈ I𝔪` (`Ideal.absNorm_mem`) instead of by the strong approximation theorem. From
`I + 𝔪 = 𝒪_K` (`Ideal.isCoprime_iff_exists`) take `i ∈ I`, `j ∈ 𝔪` with `i + j = 1`; then
`α = i + k·N(I𝔪)` lies in `I`, is `≡ 1 (mod 𝔪)`, and is positive at every real place once `k`
exceeds every `|ρ_w(i)|`; when `N(I𝔪) = 0`, `𝔪 = 0`, so `j = 0` and `α = i = 1`. -/
theorem RayIdeal.exists_mem_sub_one_mem_forall_pos (I : RayIdeal K m) :
    ∃ α : NumberField.RingOfIntegers K, α ∈ I.1 ∧ α - 1 ∈ m ∧
      ∀ w : InfinitePlace K, 0 < realEmbeddingAt K w (α : K) := by
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.mp I.2.2
  by_cases hm : m = ⊥
  · have hj0 : j = 0 := by simpa only [hm, Ideal.mem_bot] using hj
    have hi1 : i = 1 := by simpa only [hj0, add_zero] using hij
    refine ⟨1, hi1 ▸ hi, ?_, ?_⟩
    · simp
    · intro w
      simp only [map_one, zero_lt_one]
  · have hN : I.1 * m ≠ ⊥ := fun h ↦ hm ((Ideal.mul_eq_bot.mp h).resolve_left I.2.1)
    obtain ⟨t, ht, hpos⟩ := exists_natCast_mem_forall_pos_add (I.1 * m) hN i
    refine ⟨i + t, I.1.add_mem hi (Ideal.mul_le_left ht), ?_, hpos⟩
    have hi' : i - 1 ∈ m := by
      rw [← hij, sub_add_cancel_left]
      exact m.neg_mem hj
    convert m.add_mem hi' (Ideal.mul_le_right ht) using 1
    ring

/-- **Every ray ideal has an inverse up to ray-principal equivalence**: for `α ∈ I` totally
positive with `α ≡ 1 (mod 𝔪)` (`RayIdeal.exists_mem_sub_one_mem_forall_pos`), `(α) = IJ` for the
integral ideal `J` with `I ∣ (α)` (`Ideal.dvd_iff_le`), which is coprime to `𝔪` because `(α)` is
(`isCoprime_span_singleton_of_sub_mem`, `IsCoprime.of_mul_left_right`); then `IJ` is equivalent
to `𝒪_K` through the witnesses `a = α`, `b = 1`. -/
theorem RayIdeal.exists_mul_isEquivalent_one (I : RayIdeal K m) :
    ∃ J : RayIdeal K m, (I * J).IsEquivalent F m 1 := by
  obtain ⟨α, hαI, hαm, hαpos⟩ := I.exists_mem_sub_one_mem_forall_pos
  have hα0 : α ≠ 0 := cosetGenerator_ne_zero F (fun w _ ↦ hαpos w)
  have h1 : IsCoprime (Ideal.span {1}) m := isCoprime_span_singleton_one
  have hαcop := isCoprime_span_singleton_of_sub_mem h1 hαm
  obtain ⟨J₀, hJ₀⟩ := Ideal.dvd_iff_le.mpr
    ((Ideal.span_singleton_le_iff_mem I.1).mpr hαI)
  have hJ0 : J₀ ≠ ⊥ := by
    intro h
    apply hα0
    apply Ideal.span_singleton_eq_bot.mp
    rw [hJ₀, h, Ideal.mul_bot]
  have hJcop : IsCoprime J₀ m := (hJ₀ ▸ hαcop).of_mul_left_right
  refine ⟨⟨J₀, hJ0, hJcop⟩, α, 1, ⟨hαcop, hαm, ?_⟩, ?_⟩
  · intro w _
    simpa only [map_one, mul_one] using hαpos w
  · rw [Submonoid.coe_mul, RayIdeal.coe_one, Ideal.span_singleton_one,
      Ideal.mul_top, Ideal.top_mul]
    exact hJ₀.symm

/-- **Every element of the quotient by the ray class congruence is a unit**: the class of `I`
is inverted by the class of the `J` of `RayIdeal.exists_mul_isEquivalent_one`. -/
theorem isUnit_rayClassCon_quotient (A : (rayClassCon F m).Quotient) : IsUnit A := by
  induction A using Con.induction_on with
  | H I =>
    obtain ⟨J, hJ⟩ := I.exists_mul_isEquivalent_one F
    apply IsUnit.of_mul_eq_one (J : (rayClassCon F m).Quotient)
    rw [← Con.coe_mul, ← Con.coe_one]
    exact (Con.eq (rayClassCon F m)).mpr hJ

/-! ### The quotient group and its presentation

`RayClassQuotient F m` is the quotient monoid, made a commutative group by
`commGroupOfIsUnit`; its quotient map `RayClassQuotient.mk` is multiplicative and surjective,
and identifies two ideals exactly when they are ray-principally equivalent. -/

variable (m) in
/-- **The ray class group `Cl_{𝔪∞₂}(𝒪_K)` as a quotient**, `J^𝔪/P^𝔪` on integral
representatives [83, Neukirch (1999), Chapter VI, §1, p. 365]: the quotient of the monoid of
integral ray ideals by `rayClassCon F m`. -/
def RayClassQuotient : Type u := (rayClassCon F m).Quotient

/-- The commutative group structure of `RayClassQuotient F m`: the quotient monoid, in which
every element is a unit (`isUnit_rayClassCon_quotient`). -/
instance RayClassQuotient.instCommGroup : CommGroup (RayClassQuotient F m) :=
  commGroupOfIsUnit (M := (rayClassCon F m).Quotient) (isUnit_rayClassCon_quotient F)

variable (m) in
/-- The ray class of an integral ray ideal in `RayClassQuotient F m`. -/
def RayClassQuotient.mk (I : RayIdeal K m) : RayClassQuotient F m :=
  (rayClassCon F m).mk' I

/-- The quotient map represents ideal multiplication. -/
theorem RayClassQuotient.mk_mul (I J : RayIdeal K m) :
    RayClassQuotient.mk F m (I * J) = RayClassQuotient.mk F m I * RayClassQuotient.mk F m J :=
  map_mul (rayClassCon F m).mk' I J

/-- The quotient map is surjective. -/
theorem RayClassQuotient.mk_surjective : Function.Surjective (RayClassQuotient.mk F m) :=
  Con.mk'_surjective (c := rayClassCon F m)

/-- Two ideals have the same class exactly when they are ray-principally equivalent. -/
theorem RayClassQuotient.mk_eq_mk (I J : RayIdeal K m) :
    RayClassQuotient.mk F m I = RayClassQuotient.mk F m J ↔ I.IsEquivalent F m J :=
  Con.eq (rayClassCon F m)

/-- The ordinary ideal class of a ray ideal; used in the finite encoding of ray classes. -/
private noncomputable def rayIdealOrdinaryClass (I : RayIdeal K m) :
    ClassGroup (NumberField.RingOfIntegers K) :=
  ClassGroup.mk0 ⟨I.1, mem_nonZeroDivisors_of_ne_zero I.ne_bot⟩

/-- A canonical ray ideal over an ordinary class that occurs among ray ideals, and the unit ideal
otherwise; used in the finite encoding of ray classes. -/
private noncomputable def rayIdealClassRepresentative
    (c : ClassGroup (NumberField.RingOfIntegers K)) : RayIdeal K m :=
  by
    classical
    exact if h : ∃ I : RayIdeal K m, rayIdealOrdinaryClass I = c then h.choose else 1

omit [NumberField.IsTotallyReal K] in
/-- The canonical ray ideal over the ordinary class of `I` has the same ordinary class as `I`. -/
private theorem rayIdealOrdinaryClass_classRepresentative (I : RayIdeal K m) :
    rayIdealOrdinaryClass
        (rayIdealClassRepresentative (m := m) (rayIdealOrdinaryClass I)) =
      rayIdealOrdinaryClass I := by
  classical
  rw [rayIdealClassRepresentative, dite_eq_left ⟨I, rfl⟩]
  exact (Classical.choose_spec (⟨I, rfl⟩ :
    ∃ J : RayIdeal K m, rayIdealOrdinaryClass J = rayIdealOrdinaryClass I))

/-- Coprime integral generators comparing a ray ideal with the canonical ray ideal over its
ordinary class; used in the finite encoding of ray classes. -/
private structure RayClassFiniteWitness (I : RayIdeal K m) where
  /-- The generator multiplying `I`. -/
  a : NumberField.RingOfIntegers K
  /-- The generator multiplying the canonical ideal. -/
  b : NumberField.RingOfIntegers K
  /-- The first generator is nonzero. -/
  a_ne_zero : a ≠ 0
  /-- The second generator is nonzero. -/
  b_ne_zero : b ≠ 0
  /-- The first generator is coprime to the modulus. -/
  a_isCoprime : IsCoprime (Ideal.span {a}) m
  /-- The second generator is coprime to the modulus. -/
  b_isCoprime : IsCoprime (Ideal.span {b}) m
  /-- Multiplication by the generators identifies the two ideals. -/
  ideal_eq : Ideal.span {a} * I.1 =
    Ideal.span {b} *
      (rayIdealClassRepresentative (m := m) (rayIdealOrdinaryClass I)).1

/-- Chooses the coprime generators supplied by
`exists_isCoprime_generators_mul_eq_of_class_eq` for the finite encoding of a ray ideal. -/
private noncomputable def rayClassFiniteWitness (I : RayIdeal K m) :
    RayClassFiniteWitness I :=
  Classical.choice <| by
    let J := rayIdealClassRepresentative (m := m) (rayIdealOrdinaryClass I)
    obtain ⟨a, b, ha, hb, hacop, hbcop, hab⟩ :=
      exists_isCoprime_generators_mul_eq_of_class_eq I.ne_bot J.ne_bot I.isCoprime J.isCoprime
        (rayIdealOrdinaryClass_classRepresentative I).symm
    exact ⟨⟨a, b, ha, hb, hacop, hbcop, hab⟩⟩

/-- A chosen integral ray-ideal representative of a quotient class. -/
private noncomputable def rayClassRepresentative (A : RayClassQuotient F m) : RayIdeal K m :=
  Function.surjInv (RayClassQuotient.mk_surjective F) A

/-- The chosen representative maps back to its quotient class. -/
private theorem rayClassRepresentative_mk (A : RayClassQuotient F m) :
    RayClassQuotient.mk F m (rayClassRepresentative F A) = A :=
  Function.rightInverse_surjInv (RayClassQuotient.mk_surjective F) A

/-- The finite product of ordinary classes, two residue classes, and two sign vectors used to
separate ray classes when `m ≠ ⊥`. -/
private abbrev RayClassFiniteCode :=
  ClassGroup (NumberField.RingOfIntegers K) ×
    (NumberField.RingOfIntegers K ⧸ m) ×
    (NumberField.RingOfIntegers K ⧸ m) ×
    (InfinitePlace K → Bool) × (InfinitePlace K → Bool)

/-- The positivity vector of an integral generator at the infinite places. -/
private def rayClassGeneratorSigns (a : NumberField.RingOfIntegers K) : InfinitePlace K → Bool :=
  fun w ↦ decide (0 < realEmbeddingAt K w (a : K))

/-- Encodes a ray class by an ordinary class, two generator residues, and their sign vectors. -/
private noncomputable def rayClassFiniteCode (A : RayClassQuotient F m) :
    RayClassFiniteCode (K := K) (m := m) :=
  let I := rayClassRepresentative F A
  let h := rayClassFiniteWitness I
  (rayIdealOrdinaryClass I, Ideal.Quotient.mk m h.a, Ideal.Quotient.mk m h.b,
    rayClassGeneratorSigns h.a, rayClassGeneratorSigns h.b)

/-- Nonzero real numbers with the same positivity bit have positive product. -/
private theorem mul_pos_of_pos_decide_eq {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : decide (0 < x) = decide (0 < y)) : 0 < x * y := by
  have hpos : 0 < x ↔ 0 < y := decide_eq_decide.mp hxy
  rw [mul_pos_iff]
  by_cases hxpos : 0 < x
  · exact Or.inl ⟨hxpos, hpos.mp hxpos⟩
  · exact Or.inr ⟨lt_of_le_of_ne (not_lt.mp hxpos) hx,
      lt_of_le_of_ne (not_lt.mp (hpos.not.mp hxpos)) hy⟩

variable (m) in
/-- **The exact presentation of the quotient**: `RayClassQuotient F m` with its quotient map
realizes `Cl_{𝔪∞₂}(𝒪_K)` of [AFK25, Definition 2.1, `defn:rayclassgroup`], whose interface
`RayClassGroupPresentation` carries the source tag. -/
def rayClassQuotientPresentation : RayClassGroupPresentation F m (RayClassQuotient F m) where
  classOf := RayClassQuotient.mk F m
  classOf_mul := RayClassQuotient.mk_mul F
  classOf_surjective := RayClassQuotient.mk_surjective F
  class_eq_iff := RayClassQuotient.mk_eq_mk F

/-- The finite code separates quotient classes; used by `RayClassQuotient.instFinite`. -/
private theorem rayClassFiniteCode_injective :
    Function.Injective (rayClassFiniteCode (m := m) F) := by
  intro A B hcode
  let I := rayClassRepresentative F A
  let J := rayClassRepresentative F B
  let hI := rayClassFiniteWitness I
  let hJ := rayClassFiniteWitness J
  have hclass : rayIdealOrdinaryClass I = rayIdealOrdinaryClass J :=
    congrArg (fun c : RayClassFiniteCode (K := K) (m := m) ↦ c.1) hcode
  have ha : Ideal.Quotient.mk m hI.a = Ideal.Quotient.mk m hJ.a :=
    congrArg (fun c : RayClassFiniteCode (K := K) (m := m) ↦ c.2.1) hcode
  have hb : Ideal.Quotient.mk m hI.b = Ideal.Quotient.mk m hJ.b :=
    congrArg (fun c : RayClassFiniteCode (K := K) (m := m) ↦ c.2.2.1) hcode
  have hsignA : rayClassGeneratorSigns hI.a = rayClassGeneratorSigns hJ.a :=
    congrArg (fun c : RayClassFiniteCode (K := K) (m := m) ↦ c.2.2.2.1) hcode
  have hsignB : rayClassGeneratorSigns hI.b = rayClassGeneratorSigns hJ.b :=
    congrArg (fun c : RayClassFiniteCode (K := K) (m := m) ↦ c.2.2.2.2) hcode
  rw [← rayClassRepresentative_mk F A, ← rayClassRepresentative_mk F B]
  apply (RayClassQuotient.mk_eq_mk F I J).mpr
  refine ⟨hJ.a * hI.b, hI.a * hJ.b, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [← Ideal.span_singleton_mul_span_singleton]
    exact hJ.a_isCoprime.mul_left hI.b_isCoprime
  · have ha' : hJ.a - hI.a ∈ m := by
      simpa only [neg_sub] using
        m.neg_mem ((Ideal.Quotient.mk_eq_mk_iff_sub_mem hI.a hJ.a).mp ha)
    exact m.mul_sub_mul_mem ha'
      ((Ideal.Quotient.mk_eq_mk_iff_sub_mem hI.b hJ.b).mp hb)
  · intro w _
    have haI : realEmbeddingAt K w (hI.a : K) ≠ 0 :=
      realEmbeddingAt_coe_ne_zero hI.a_ne_zero w
    have haJ : realEmbeddingAt K w (hJ.a : K) ≠ 0 :=
      realEmbeddingAt_coe_ne_zero hJ.a_ne_zero w
    have hbI : realEmbeddingAt K w (hI.b : K) ≠ 0 :=
      realEmbeddingAt_coe_ne_zero hI.b_ne_zero w
    have hbJ : realEmbeddingAt K w (hJ.b : K) ≠ 0 :=
      realEmbeddingAt_coe_ne_zero hJ.b_ne_zero w
    have hapos : 0 < realEmbeddingAt K w (hJ.a : K) *
        realEmbeddingAt K w (hI.a : K) :=
      mul_pos_of_pos_decide_eq haJ haI (congrFun hsignA w).symm
    have hbpos : 0 < realEmbeddingAt K w (hI.b : K) *
        realEmbeddingAt K w (hJ.b : K) :=
      mul_pos_of_pos_decide_eq hbI hbJ (congrFun hsignB w)
    simpa only [map_mul, mul_mul_mul_comm] using mul_pos hapos hbpos
  · simp only [← Ideal.span_singleton_mul_span_singleton]
    calc
      I.1 * (Ideal.span {hI.a} * Ideal.span {hJ.b}) =
          (Ideal.span {hI.a} * I.1) * Ideal.span {hJ.b} := by ac_rfl
      _ = (Ideal.span {hI.b} *
            (rayIdealClassRepresentative (m := m) (rayIdealOrdinaryClass I)).1) *
            Ideal.span {hJ.b} := by rw [hI.ideal_eq]
      _ = (Ideal.span {hJ.b} *
            (rayIdealClassRepresentative (m := m) (rayIdealOrdinaryClass J)).1) *
            Ideal.span {hI.b} := by rw [hclass]; ac_rfl
      _ = (Ideal.span {hJ.a} * J.1) * Ideal.span {hI.b} := by rw [hJ.ideal_eq]
      _ = J.1 * (Ideal.span {hJ.a} * Ideal.span {hI.b}) := by ac_rfl


/-- **Finiteness of the ray class group**, Milne, *Class Field Theory*, version 4.03 (2020),
Chapter V, Theorem 1.7: ordinary ideal classes, residues modulo `m`, and the finitely many real
signs give a finite separating family of data for `RayClassQuotient F m`. -/
noncomputable instance RayClassQuotient.instFinite : Finite (RayClassQuotient F m) := by
  by_cases hm : m = ⊥
  · subst m
    apply Finite.of_injective (fun _ : RayClassQuotient F ⊥ ↦ ())
    intro A B _
    exact @Subsingleton.elim _
      (rayClassQuotientPresentation F ⊥).subsingleton_of_modulus_bot A B
  · let _ : NeZero m := ⟨hm⟩
    exact Finite.of_injective (rayClassFiniteCode F) (rayClassFiniteCode_injective F)

end SIC

end
