/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Reciprocity.ArtinMap
import SICs.FieldTheory.NormSigns

/-!
# Reciprocity for cyclotomic extensions

The norm character of fractional ideals modulo `n`, the Artin map of a cyclotomic extension
`K(ζ_n)/K` as the power map by that character, and the vanishing of the Artin map of `K(ζ_n)/K`
and of its subextensions on principal ideals congruent to one and totally positive.

This is Childress, *Class Field Theory* (2009), Chapter V, proof of Theorem 2.1(ii) for
`ℚ(ζ_m)/ℚ` and `F(ζ_m)/F`, and Exercise 5.6 for the subextensions of `F(ζ_m)/F`; Milne, *Class
Field Theory*, version 4.03 (2020), Chapter V, Example 3.2, describes the Artin map of
`ℚ(ζ_m)/ℚ`. Childress passes from `ℚ(ζ_m)` to `F(ζ_m)` through the consistency property; here
the Frobenius computation over `K` (`IsFrobeniusAt.apply_of_pow_eq_one`) gives the general
case directly.

## The argument

For `S` containing the primes dividing `n`, every prime `v ∉ S` has absolute norm prime to `n`,
and $\chi_{S,n}(J) = \prod_{v\notin S}(N v)^{\operatorname{ord}_v J}$ is a homomorphism to
$(\mathbb Z/n\mathbb Z)^\times$. At a prime $v\notin S$ the Artin map is Frobenius, which raises
a primitive `n`th root of unity `ζ` to the power `N v`; by multiplicativity
$\psi^S(J)(\zeta) = \zeta^{\chi_{S,n}(J)}$ for every fractional ideal `J`.

Let `α` be congruent to one modulo `m`, where `n ∣ m`, and totally positive. Write
$\alpha = a/b$ with $a, b\in\mathcal O_K$ and `b` coprime to `m`. Then $a - b\in n\mathcal O_K$
(`FinitePlace.sub_mem_of_units_map_mem_rayUnitGroup`). The norm $N_{K/\mathbb Q}$ is the
determinant of multiplication on the free `ℤ`-module $\mathcal O_K$, and determinants commute
with reduction modulo `n` (`LinearMap.det_baseChange`), so $N a\equiv N b \pmod n$. Since `α`
is totally positive, $N\alpha > 0$, so $|N a| \equiv |N b| \pmod n$, both prime to `n`. The
absolute norm of a principal ideal is the absolute value of the norm of its generator, so
$\chi((\alpha)) = 1$ and $\psi^S((\alpha))$ fixes `ζ`. As `ζ` generates `K(ζ_n)`,
$\psi^S((\alpha)) = 1$. Restriction to a subextension (`artinMap_restrictNormal`) gives the same
for every intermediate field.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped nonZeroDivisors

namespace SIC

variable {K : Type*} [Field K] [NumberField K]

/-! ### The norm character

At a prime outside the modulus the character is its absolute norm modulo `n`. Prime
factorization extends this to every integral ideal coprime to the modulus; integral ratios
then prove triviality on principal congruent ideals. -/

variable (K) in
/-- The norm character modulo `n` away from `S`:
$\chi_{S,n}(J) = \prod_{v\notin S}(N v)^{\operatorname{ord}_v J}$ in
$(\mathbb Z/n\mathbb Z)^\times$, a prime whose norm is not prime to `n` contributing `1`.
Milne, *Class Field Theory*, Chapter V, Example 3.2, over an arbitrary number field. -/
def normCharacter (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ →* (ZMod n)ˣ :=
  FractionalIdeal.liftPrimes K S (fun v ↦
    if h : (Ideal.absNorm v.asIdeal).Coprime n then ZMod.unitOfCoprime _ h else 1)

/-- The norm character of a prime outside `S` whose norm is prime to `n` is that norm. -/
theorem normCharacter_primeFractionalIdeal (n : ℕ) {S : Finset (HeightOneSpectrum (𝓞 K))}
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) (hcop : (Ideal.absNorm v.asIdeal).Coprime n) :
    normCharacter K n S (primeFractionalIdeal K v) = ZMod.unitOfCoprime _ hcop := by
  change FractionalIdeal.liftPrimes K S (fun w : HeightOneSpectrum (𝓞 K) ↦
    if h : (Ideal.absNorm w.asIdeal).Coprime n then ZMod.unitOfCoprime _ h else 1)
      (primeFractionalIdeal K v) = ZMod.unitOfCoprime _ hcop
  rw [FractionalIdeal.liftPrimes_primeFractionalIdeal_of_notMem (K := K) S _ hv]
  split_ifs
  rfl

/-- The norm character ignores the primes in its excluded set. -/
@[simp]
theorem normCharacter_primeFractionalIdeal_of_mem (n : ℕ)
    {S : Finset (HeightOneSpectrum (𝓞 K))} {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) :
    normCharacter K n S (primeFractionalIdeal K v) = 1 := by
  exact FractionalIdeal.liftPrimes_primeFractionalIdeal_of_mem (K := K) S _ hv

/-- The norm of a totally positive global element is positive. This is the sign step in
`normCharacter_toPrincipalIdeal_eq_one`; conjugate complex embeddings have positive product. -/
private theorem norm_pos_of_unitEmbedding_mem_congruent (m : Ideal (𝓞 K)) (a : Kˣ)
    (ha : NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a ∈
      IdeleGroup.congruentSubgroup Set.univ m) :
    0 < Algebra.norm ℚ (a : K) := by
  have hreal (ψ : K →+* ℝ) : 0 < ψ (a : K) := by
    let φ : K →+* ℂ := Complex.ofRealHom.comp ψ
    have hφ : NumberField.ComplexEmbedding.IsReal φ := by
      apply NumberField.ComplexEmbedding.isReal_iff.mpr
      ext x
      simp [φ, NumberField.ComplexEmbedding.conjugate_coe_eq]
    let w : NumberField.InfinitePlace K := NumberField.InfinitePlace.mk φ
    have hw : w.IsReal := NumberField.InfinitePlace.isReal_mk_iff.mpr hφ
    have hpos := ((IdeleGroup.mem_congruentSubgroup_univ_iff m _).mp ha).1 w hw
    rw [IdeleGroup.infiniteComponent_unitEmbedding] at hpos
    have heq : NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        (algebraMap K w.Completion (a : K)) = ψ (a : K) := by
      apply Complex.ofReal_injective
      rw [NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
      simp only [NumberField.InfinitePlace.Completion.algebraMap_apply,
        NumberField.InfinitePlace.Completion.extensionEmbedding_coe]
      rw [NumberField.InfinitePlace.embedding_mk_eq_of_isReal hφ]
      rfl
    simp only [Units.coe_map] at hpos
    change 0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
      (algebraMap K w.Completion (a : K)) at hpos
    rwa [heq] at hpos
  exact norm_pos_of_forall_realEmbedding_pos a.ne_zero hreal

/-- Taking absolute values preserves a congruence when the two integers have the same sign.
This is the final sign calculation in `normCharacter_toPrincipalIdeal_eq_one`. -/
private theorem natAbs_eq_mod_of_pos_ratio (n : ℕ) (x y : ℤ) (q : ℚ) (hq : 0 < q)
    (hxy : (x : ℚ) = q * (y : ℚ)) (hmod : (x : ZMod n) = (y : ZMod n)) :
    ((x.natAbs : ℕ) : ZMod n) = ((y.natAbs : ℕ) : ZMod n) := by
  by_cases hy : 0 ≤ y
  · have hxQ : (0 : ℚ) ≤ (x : ℚ) := by
      rw [hxy]
      exact mul_nonneg hq.le (by exact_mod_cast hy)
    have hx : 0 ≤ x := by exact_mod_cast hxQ
    have hxabs := congrArg (fun z : ℤ => (z : ZMod n)) (Int.natAbs_of_nonneg hx)
    have hyabs := congrArg (fun z : ℤ => (z : ZMod n)) (Int.natAbs_of_nonneg hy)
    simpa only [Int.cast_natCast] using hxabs.trans (hmod.trans hyabs.symm)
  · have hyneg : y < 0 := lt_of_not_ge hy
    have hxQ : (x : ℚ) < 0 := by
      rw [hxy]
      exact mul_neg_of_pos_of_neg hq (by exact_mod_cast hyneg)
    have hxneg : x < 0 := by exact_mod_cast hxQ
    have hxabsInt : ((x.natAbs : ℕ) : ℤ) = -x := by
      simpa only [Int.natAbs_neg] using Int.natAbs_of_nonneg (neg_nonneg.mpr hxneg.le)
    have hyabsInt : ((y.natAbs : ℕ) : ℤ) = -y := by
      simpa only [Int.natAbs_neg] using Int.natAbs_of_nonneg (neg_nonneg.mpr hyneg.le)
    have hxabs := congrArg (fun z : ℤ => (z : ZMod n)) hxabsInt
    have hyabs := congrArg (fun z : ℤ => (z : ZMod n)) hyabsInt
    have hxabs' : ((x.natAbs : ℕ) : ZMod n) = -(x : ZMod n) := by
      simpa only [Int.cast_natCast, Int.cast_neg] using hxabs
    have hyabs' : ((y.natAbs : ℕ) : ZMod n) = -(y : ZMod n) := by
      simpa only [Int.cast_natCast, Int.cast_neg] using hyabs
    rw [hxabs', hyabs', hmod]

/-- On an integral ideal prime to `m`, the norm character is its absolute norm modulo `n`.
This is the prime-factorization step of `normCharacter_toPrincipalIdeal_eq_one`. -/
private theorem normCharacter_integral_of_coprime (n : ℕ) (m : Ideal (𝓞 K))
    (hm0 : m ≠ ⊥) (hm : m ≤ Ideal.span {(n : 𝓞 K)})
    (I : Ideal (𝓞 K)) (hI0 : I ≠ ⊥) (hIm : IsCoprime I m) :
    ((normCharacter K n (FinitePlace.modulusSupport m)
        (Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K)
          (FractionalIdeal.coeIdeal_ne_zero.mpr hI0)) : (ZMod n)ˣ) : ZMod n) =
      Ideal.absNorm I := by
  let P : Ideal (𝓞 K) → Prop := fun I => ∀ (hI0 : I ≠ ⊥) (_ : IsCoprime I m),
    ((normCharacter K n (FinitePlace.modulusSupport m)
        (Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K)
          (FractionalIdeal.coeIdeal_ne_zero.mpr hI0)) : (ZMod n)ˣ) : ZMod n) =
      Ideal.absNorm I
  suffices hP : P I from hP hI0 hIm
  refine induction_on_prime_coprime m P ?_ ?_ I hI0 hIm
  · intro hJ0 _
    have htop : (Units.mk0 ((⊤ : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hJ0)) = 1 := by
      apply Units.ext
      simp
    rw [htop, map_one]
    simp
  · intro J Q hQ0 hQprime hQcop hJ0 hJcop ih hQJ0 _
    let v : HeightOneSpectrum (𝓞 K) := ⟨Q, hQprime, hQ0⟩
    have hv : v ∉ FinitePlace.modulusSupport m := by
      intro hv
      have hqzero := (FinitePlace.isCoprime_iff_modulusExponent_eq_zero hm0 v).mp hQcop
      exact (FinitePlace.mem_modulusSupport.mp hv) hqzero
    have hn : (n : 𝓞 K) ∉ v.asIdeal := by
      intro hn
      apply hv
      exact FinitePlace.mem_modulusSupport_of_le hm0
        (hm.trans ((Ideal.span_singleton_le_iff_mem v.asIdeal).mpr hn))
    have hQN := (absNorm_coprime_iff_natCast_notMem v).mpr hn
    have hmul : (Units.mk0 ((Q * J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hQJ0)) =
        (primeFractionalIdeal K v) *
          Units.mk0 (J : FractionalIdeal (𝓞 K)⁰ K)
            (FractionalIdeal.coeIdeal_ne_zero.mpr hJ0) := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_mk0, coe_primeFractionalIdeal,
        FractionalIdeal.coeIdeal_mul]
      rfl
    rw [hmul, map_mul, normCharacter_primeFractionalIdeal n hv hQN]
    simp only [Units.val_mul, ZMod.coe_unitOfCoprime, Ideal.absNorm.map_mul,
      Nat.cast_mul]
    exact congrArg ((Ideal.absNorm Q : ZMod n) * ·) (ih hJ0 hJcop)

/-- For an integral element `α` coprime to `m`, the character of `(α)` is `|N α|` modulo `n`.
This is the principal-ideal instance of `normCharacter_integral_of_coprime`. -/
private theorem normCharacter_span_singleton_eq_absNorm (n : ℕ) (m : Ideal (𝓞 K))
    (hm0 : m ≠ ⊥) (hm : m ≤ Ideal.span {(n : 𝓞 K)})
    (α : 𝓞 K) (hα0 : α ≠ 0) (hαcop : IsCoprime (Ideal.span {α}) m) :
    ((normCharacter K n (FinitePlace.modulusSupport m)
        (Units.mk0 ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
          (FractionalIdeal.coeIdeal_ne_zero.mpr (by simpa using hα0))) : (ZMod n)ˣ) : ZMod n) =
      (Algebra.norm ℤ α).natAbs := by
  simpa only [Ideal.absNorm_span_singleton] using
    normCharacter_integral_of_coprime n m hm0 hm (Ideal.span {α}) (by simpa using hα0) hαcop

/-- A principal congruent idèle admits an integral ratio whose numerator and denominator
are coprime to the modulus and congruent modulo it. Used by
`normCharacter_toPrincipalIdeal_eq_one`. -/
private theorem exists_integral_ratio_of_congruent (m : Ideal (𝓞 K)) (hm0 : m ≠ ⊥)
    (a : Kˣ)
    (ha : NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a ∈
      IdeleGroup.congruentSubgroup Set.univ m) :
    ∃ α β : 𝓞 K, α ≠ 0 ∧ β ≠ 0 ∧ (a : K) * (β : K) = (α : K) ∧
      α - β ∈ m ∧ IsCoprime (Ideal.span {α}) m ∧ IsCoprime (Ideal.span {β}) m := by
  have hlocal (v : HeightOneSpectrum (𝓞 K))
      (hv : v ∈ FinitePlace.modulusSupport m) : v.valuation K (a : K) = 1 := by
    have hvexp := FinitePlace.mem_modulusSupport.mp hv
    have hunit := ((IdeleGroup.mem_congruentSubgroup_univ_iff m _).mp ha).2 v hvexp
    rw [IdeleGroup.finiteComponent_unitEmbedding] at hunit
    exact ((FinitePlace.units_map_mem_higherUnitGroup_iff v _ a).mp hunit).1
  obtain ⟨α, β, hβ0, hab, hβcop⟩ :=
    exists_integral_ratio_coprime_modulus m hm0 a (fun v hv =>
      (hlocal v (FinitePlace.mem_modulusSupport_of_le hm0 hv)).le)
  have hsub : α - β ∈ m := by
    apply FinitePlace.sub_mem_of_units_map_mem_rayUnitGroup hm0 hab
    intro v hv
    have hunit := ((IdeleGroup.mem_congruentSubgroup_univ_iff m _).mp ha).2 v hv
    simpa only [IdeleGroup.finiteComponent_unitEmbedding] using hunit
  have hα0 : α ≠ 0 := by
    intro hzero
    have hβK : (β : K) ≠ 0 := (map_ne_zero_iff _
      (IsFractionRing.injective (𝓞 K) K)).mpr hβ0
    have hαK : (α : K) = 0 := by simp [hzero]
    rw [hαK] at hab
    exact (mul_ne_zero a.ne_zero hβK) hab
  exact ⟨α, β, hα0, hβ0, hab, hsub,
    isCoprime_span_singleton_of_sub_mem hβcop hsub, hβcop⟩

/-- The numerator and denominator of a positive integral ratio have congruent absolute
norms modulo `n` when they are congruent modulo an ideal contained in `(n)`.
Used by `normCharacter_toPrincipalIdeal_eq_one`. -/
private theorem natAbs_norm_congruent_of_ratio (n : ℕ) (m : Ideal (𝓞 K))
    (hm : m ≤ Ideal.span {(n : 𝓞 K)}) (a : Kˣ) (α β : 𝓞 K)
    (hab : (a : K) * (β : K) = (α : K)) (hsub : α - β ∈ m)
    (hpos : 0 < Algebra.norm ℚ (a : K)) :
    (((Algebra.norm ℤ α).natAbs : ℕ) : ZMod n) =
      (((Algebra.norm ℤ β).natAbs : ℕ) : ZMod n) := by
  have hnorm : (Algebra.norm ℤ α : ZMod n) = (Algebra.norm ℤ β : ZMod n) :=
    norm_eq_mod_of_sub_mem_span n α β (hm hsub)
  have hratioNorm : (Algebra.norm ℤ α : ℚ) =
      Algebra.norm ℚ (a : K) * (Algebra.norm ℤ β : ℚ) := by
    calc
      (Algebra.norm ℤ α : ℚ) = Algebra.norm ℚ (α : K) := Algebra.coe_norm_int α
      _ = Algebra.norm ℚ ((a : K) * (β : K)) := by rw [hab]
      _ = Algebra.norm ℚ (a : K) * Algebra.norm ℚ (β : K) := map_mul _ _ _
      _ = Algebra.norm ℚ (a : K) * (Algebra.norm ℤ β : ℚ) := by
        rw [Algebra.coe_norm_int β]
  exact natAbs_eq_mod_of_pos_ratio n _ _ _ hpos hratioNorm hnorm

/-- The norm character vanishes on the principal ideals of totally positive elements congruent to
one modulo a multiple `m` of `n`. Childress, *Class Field Theory*, Chapter V, proof of
Theorem 2.1(ii). -/
theorem normCharacter_toPrincipalIdeal_eq_one (n : ℕ) (m : Ideal (𝓞 K)) (hm0 : m ≠ ⊥)
    (hm : m ≤ Ideal.span {(n : 𝓞 K)}) (a : Kˣ)
    (ha : NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a ∈
      IdeleGroup.congruentSubgroup Set.univ m) :
    normCharacter K n (FinitePlace.modulusSupport m) (toPrincipalIdeal (𝓞 K) K a) = 1 := by
  obtain ⟨α, β, hα0, hβ0, hab, hsub, hαcop, hβcop⟩ :=
    exists_integral_ratio_of_congruent m hm0 a ha
  have hαideal0 : Ideal.span {α} ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hα0
  have hβideal0 : Ideal.span {β} ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hβ0
  have hAbs := natAbs_norm_congruent_of_ratio n m hm a α β hab hsub
    (norm_pos_of_unitEmbedding_mem_congruent m a ha)
  have hUnits : normCharacter K n (FinitePlace.modulusSupport m)
        (Units.mk0 ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
          (FractionalIdeal.coeIdeal_ne_zero.mpr hαideal0)) =
      normCharacter K n (FinitePlace.modulusSupport m)
        (Units.mk0 ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
          (FractionalIdeal.coeIdeal_ne_zero.mpr hβideal0)) := by
    apply Units.ext
    simpa only [normCharacter_span_singleton_eq_absNorm n m hm0 hm α hα0 hαcop,
      normCharacter_span_singleton_eq_absNorm n m hm0 hm β hβ0 hβcop] using hAbs
  have hprincipal : toPrincipalIdeal (𝓞 K) K a *
      Units.mk0 ((Ideal.span {β} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hβideal0) =
      Units.mk0 ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hαideal0) := by
    apply Units.ext
    simp only [Units.val_mul, coe_toPrincipalIdeal, Units.val_mk0,
      FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    exact congrArg (FractionalIdeal.spanSingleton (𝓞 K)⁰) hab
  have hprod := congrArg (normCharacter K n (FinitePlace.modulusSupport m)) hprincipal
  rw [map_mul, hUnits] at hprod
  exact mul_right_cancel (hprod.trans (one_mul _).symm)

/-! ### Cyclotomic reciprocity

Frobenius raises a primitive root of unity to the prime norm. Multiplicativity gives the
Artin action on all ideals, and principal vanishing makes the Artin map trivial on the
cyclotomic field and its subextensions. -/

variable {M : Type*} [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M]

/-- Frobenius at $\mathfrak p\nmid n$ acts on the `n`th roots of unity as the power
$N\mathfrak p$: its image under `IsPrimitiveRoot.autToPow` is $N\mathfrak p \bmod n$. Milne,
*Class Field Theory*, Chapter V, Example 3.2. -/
theorem autToPow_frobeniusAt {n : ℕ} [NeZero n] {ζ : M} (hζ : IsPrimitiveRoot ζ n)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (n : 𝓞 K) ∉ v.asIdeal) :
    ((hζ.autToPow K (frobeniusAt M v) : (ZMod n)ˣ) : ZMod n) = Ideal.absNorm v.asIdeal := by
  have hpow : ζ ^ (hζ.autToPow K (frobeniusAt M v) : ZMod n).val =
      ζ ^ Ideal.absNorm v.asIdeal := by
    rw [hζ.autToPow_spec K]
    exact (isFrobeniusAt_frobeniusAt v
      (FinitePlace.PrimeAbove.place (L := M) v
        (Classical.arbitrary _)).asIdeal).apply_of_pow_eq_one hζ.pow_eq_one hv
  have hmodpow : ζ ^ (Ideal.absNorm v.asIdeal % n) =
      ζ ^ Ideal.absNorm v.asIdeal := by
    rw [hζ.eq_orderOf, pow_mod_orderOf]
  have heq := hζ.pow_inj (ZMod.val_lt _)
    (Nat.mod_lt _ (NeZero.pos n)) (hpow.trans hmodpow.symm)
  have hmod : (((hζ.autToPow K (frobeniusAt M v) : ZMod n)).val : ZMod n) =
      (Ideal.absNorm v.asIdeal : ZMod n) := by
    apply (ZMod.natCast_eq_natCast_iff _ _ n).mpr
    rw [heq]
    exact Nat.mod_modEq _ _
  simpa only [ZMod.natCast_zmod_val] using hmod

/-- **The Artin map of a cyclotomic extension** raises a primitive `n`th root of unity to the
norm character: $\psi^S(J)(\zeta) = \zeta^{\chi_{S,n}(J)}$ when `S` contains the primes dividing
`n`. Milne, *Class Field Theory*, Chapter V, Example 3.2; Childress, *Class Field Theory*,
Chapter V, proof of Theorem 2.1(ii). -/
theorem artinMap_apply_of_isPrimitiveRoot {n : ℕ} {ζ : M} (hζ : IsPrimitiveRoot ζ n)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    artinMap M S J ζ = ζ ^ ((normCharacter K n S J : (ZMod n)ˣ) : ZMod n).val := by
  by_cases hn0 : n = 0
  · subst n
    have hSall (v : HeightOneSpectrum (𝓞 K)) : v ∈ S := hS v (by simp)
    have hArt : artinMap M S = 1 := by
      apply FractionalIdeal.monoidHom_ext
      intro v
      exact artinMap_primeFractionalIdeal_of_mem (hSall v)
    have hNorm : normCharacter K 0 S = 1 := by
      apply FractionalIdeal.monoidHom_ext
      intro v
      exact normCharacter_primeFractionalIdeal_of_mem 0 (hSall v)
    simp [hArt, hNorm]
  have : NeZero n := ⟨hn0⟩
  have hhom : (hζ.autToPow K).comp (artinMap M S) = normCharacter K n S := by
    apply FractionalIdeal.monoidHom_ext
    intro v
    by_cases hv : v ∈ S
    · simp only [MonoidHom.comp_apply, artinMap_primeFractionalIdeal_of_mem hv,
        map_one, normCharacter_primeFractionalIdeal_of_mem n hv]
    have hn : (n : 𝓞 K) ∉ v.asIdeal := fun h => hv (hS v h)
    have hcop := (absNorm_coprime_iff_natCast_notMem v).mpr hn
    rw [MonoidHom.comp_apply, artinMap_primeFractionalIdeal_of_notMem hv,
      normCharacter_primeFractionalIdeal n hv hcop]
    apply Units.ext
    change (hζ.autToPow K (frobeniusAt M v) : ZMod n) =
      (ZMod.unitOfCoprime (Ideal.absNorm v.asIdeal) hcop : ZMod n)
    simpa only [ZMod.coe_unitOfCoprime] using autToPow_frobeniusAt hζ v hn
  have h := congrArg (fun f : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* (ZMod n)ˣ => f J) hhom
  change hζ.autToPow K (artinMap M S J) = normCharacter K n S J at h
  rw [← h, hζ.autToPow_spec K]

/-- **Cyclotomic reciprocity**: the Artin map of `K(ζ_n)/K` vanishes on the principal ideals of
totally positive elements congruent to one modulo a multiple `m` of `n`. Childress, *Class Field
Theory*, Chapter V, proof of Theorem 2.1(ii). -/
theorem IsCyclotomicExtension.artinMap_toPrincipalIdeal_eq_one (n : ℕ)
    [IsCyclotomicExtension {n} K M] (m : Ideal (𝓞 K)) (hm0 : m ≠ ⊥)
    (hm : m ≤ Ideal.span {(n : 𝓞 K)}) (a : Kˣ)
    (ha : NumberField.IdeleGroup.unitEmbedding (𝓞 K) K a ∈
      IdeleGroup.congruentSubgroup Set.univ m) :
    artinMap M (FinitePlace.modulusSupport m) (toPrincipalIdeal (𝓞 K) K a) = 1 := by
  have hn : n ≠ 0 := by
    intro hzero
    subst n
    exact hm0 (le_bot_iff.mp (by simpa using hm))
  let : NeZero n := ⟨hn⟩
  have hS (v : HeightOneSpectrum (𝓞 K)) (hn : (n : 𝓞 K) ∈ v.asIdeal) :
      v ∈ FinitePlace.modulusSupport m := by
    exact FinitePlace.mem_modulusSupport_of_le hm0
      (hm.trans ((Ideal.span_singleton_le_iff_mem v.asIdeal).mpr hn))
  apply IsCyclotomicExtension.algEquiv_eq_of_apply_eq {n} K M
  intro t ht ht0
  have htn : t = n := Set.mem_singleton_iff.mp ht
  subst t
  let ζ := IsCyclotomicExtension.zeta n K M
  have hζ : IsPrimitiveRoot ζ n := IsCyclotomicExtension.zeta_spec n K M
  refine ⟨ζ, hζ, ?_⟩
  rw [artinMap_apply_of_isPrimitiveRoot hζ _ hS,
    normCharacter_toPrincipalIdeal_eq_one n m hm0 hm a ha]
  change ζ ^ (1 : ZMod n).val = ζ
  rw [show (1 : ZMod n) = ((1 : ℕ) : ZMod n) by simp, ZMod.val_natCast,
    hζ.eq_orderOf, pow_mod_orderOf, pow_one]

/-- Cyclotomic reciprocity for $E(\zeta)/E$ also kills principal congruence ideals in every
subfield `T` of `E(ζ)`; Childress, *Class Field Theory*, Chapter V, Exercise 5.6. -/
theorem artinMap_principal_eq_one_of_le_adjoin {E Ω : Type*}
    [Field E] [NumberField E] [Field Ω] [NumberField Ω] [Algebra E Ω]
    [IsAbelianGalois E Ω] {M : ℕ} [NeZero M] {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ M) (m : Ideal (𝓞 E)) (hm0 : m ≠ ⊥)
    (hmM : m ≤ Ideal.span {(M : 𝓞 E)})
    (hram : FinitePlace.ramifiedSet E Ω ⊆ FinitePlace.modulusSupport m)
    (T : IntermediateField E Ω) (hTC : T ≤ IntermediateField.adjoin E {ζ})
    (a : Eˣ)
    (ha : NumberField.IdeleGroup.unitEmbedding (𝓞 E) E a ∈
      IdeleGroup.congruentSubgroup Set.univ m) :
    artinMap T (FinitePlace.modulusSupport m) (toPrincipalIdeal (𝓞 E) E a) = 1 := by
  let C : IntermediateField E Ω := IntermediateField.adjoin E {ζ}
  let _ : IsCyclotomicExtension {M} E C :=
    hζ.intermediateField_adjoin_isCyclotomicExtension E
  exact (artinMap_eq_one_iff_mem_fixingSubgroup
    (FinitePlace.modulusSupport m) hram T _).mpr
      (IntermediateField.fixingSubgroup_le hTC
        ((artinMap_eq_one_iff_mem_fixingSubgroup
          (FinitePlace.modulusSupport m) hram C _).mp
          (IsCyclotomicExtension.artinMap_toPrincipalIdeal_eq_one M m hm0 hmM a ha)))


end SIC
