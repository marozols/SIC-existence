/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.Frobenius.SummandProducts
import SICs.Dilogarithm.Valuation.CyclicTranslation
import SICs.Dilogarithm.Valuation.Multiplier

/-!
# Translation invariance along one of two torsion lines

A finite quantum dilogarithm with unit values, on a metric group whose `p`-primary part is
`(ℤ/p^s)²`, whose products over the cyclic summands of order `p^s` other than those through two
given torsion lines `⟨a⟩`, `⟨b⟩` are invariant modulo `𝔪` under the `p`-torsion, is invariant
modulo `𝔪` under translation by `a` or by `b`.

This module formalizes the metric-group part of [RW26b, Radchenko, Wheeler (2026b), Section 7,
proof of Theorem 7]: everything after the products over the summands `L` have been shown
invariant (which the source deduces from Theorem 4 and Proposition 3(ii) at the inverse image of
`L`). The lattice part, which identifies `G_{I,η}[p^∞] = p^{-s}I/I` with the lines `U_𝔭`, `U_𝔮`
and supplies the hypothesis, belongs to the pseudolattice layer.

## The argument

*Separation on each coset.* On a coset `c + G[p^∞]`, the reduction of `E` is a function on
`(ℤ/p^s)²` into the residue field, of characteristic `p`, whose products over the admissible
summands are invariant under the `p`-torsion; Lemma 6 (`mul_eq_mul_of_prod_summand_invariant`)
gives `E(x + a + b)E(x) ≡ E(x + a)E(x + b)`, and iterating, `E(c + ia + jb)E(c) ≡
E(c + ia)E(c + jb)`.

*One coordinate is constant on each coset.* `E` takes unit values and `E`, `E⁻¹` are
Fourier-integral (`FiniteQuantumDilog.isFourierIntegral`, `isFourierIntegral_inv`, from `v(λ) = 1`),
so Lemma 1(iii) (`MetricGroup.forall_or_forall_of_separated`) makes the reduction on each coset
of `G[p]` constant along `a` or along `b`.

*The same line on every coset.* Suppose the reduction is nonconstant along `b` on the coset of
`x₁` and nonconstant along `a` on the coset of `x₂`, so on these cosets it depends only on the `a`-
and only on the `b`-coordinate respectively. Put `h = x₂ - x₁`. Then
`R_h(x₁ + ua + vb) ≡ E(x₂ + vb)/E(x₁ + ua)`, with both factors nonconstant. `R_h` and `R_h⁻¹`
have unit values and integral Fourier transforms by the identity (15) and its transform
(`FiniteQuantumDilog.fourier_translationRatio`, `fourier_div_translationRatio`), and the display
is separated, so Lemma 1(iii) applied to `R_h` makes one factor constant, a contradiction. Hence
one line leaves the reduction invariant on every coset where it is nonconstant, and both do on
the others.
-/

open scoped NNReal

namespace SIC

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {L : Type*} [Field L]

namespace FiniteQuantumDilog

variable {M : MetricGroup G L} (E : FiniteQuantumDilog M) (v : Valuation L ℝ≥0)

/-! ### Theorem 7 for a metric group

From invariant products over the summands to invariance along `a` or `b`. -/

omit [Fintype G] [DecidableEq G] in
/-- Iterating a vanishing mixed difference separates the two torsion coordinates.
Used by `translation_invariant_of_summands`. -/
private theorem separated_of_mixed {k : Type*} [Field k] (f : G → k)
    (hf : ∀ x, f x ≠ 0) {a b : G}
    (hm : ∀ x, f (x + a + b) * f x = f (x + a) * f (x + b))
    (c : G) (i j : ℕ) :
    f (c + i • a + j • b) * f c = f (c + i • a) * f (c + j • b) := by
  have hi (i : ℕ) (x : G) :
      f (x + i • a + b) * f x = f (x + i • a) * f (x + b) := by
    induction i with
    | zero => simpa only [zero_smul, add_zero] using (mul_comm (f (x + b)) (f x))
    | succ i ih =>
      have h := hm (x + i • a)
      have h' := ih
      have heq :
          f (x + (i + 1) • a + b) * f (x + i • a) =
            f (x + (i + 1) • a) * f (x + i • a + b) := by
        convert h using 1 <;> congr 1 <;> simp only [succ_nsmul] <;> abel_nf
      apply (mul_left_cancel₀ (hf (x + i • a)))
      calc
        f (x + i • a) * (f (x + (i + 1) • a + b) * f x) =
            f (x + (i + 1) • a + b) * f (x + i • a) * f x := by ring
        _ = f (x + (i + 1) • a) * (f (x + i • a + b) * f x) := by rw [heq]; ring
        _ = f (x + i • a) *
            (f (x + (i + 1) • a) * f (x + b)) := by rw [h']; ring
  induction j with
  | zero =>
      simp only [zero_smul, add_zero]
  | succ j ih =>
    have h := hi i (c + j • b)
    have heq :
        f (c + i • a + (j + 1) • b) * f (c + j • b) =
          f (c + i • a + j • b) * f (c + (j + 1) • b) := by
      simpa only [succ_nsmul, add_assoc, add_comm, add_left_comm] using h
    apply (mul_left_cancel₀ (hf (c + j • b)))
    calc
      f (c + j • b) * (f (c + i • a + (j + 1) • b) * f c) =
          f (c + i • a + (j + 1) • b) * f (c + j • b) * f c := by ring
      _ = f (c + i • a + j • b) * f c * f (c + (j + 1) • b) := by rw [heq]; ring
      _ = f (c + j • b) * (f (c + i • a) * f (c + (j + 1) • b)) := by
        rw [ih]; ring

omit [Fintype G] [DecidableEq G] in
/-- The quotient of two separated functions is separated. Used by
`translation_invariant_of_summands` for a translation ratio. -/
private theorem separated_div {k : Type*} [Field k] (f d : G → k)
    {a b : G} (c : G) (hfsep : ∀ i j : ℕ,
      f (c + i • a + j • b) * f c = f (c + i • a) * f (c + j • b))
    (hdsep : ∀ i j : ℕ,
      d (c + i • a + j • b) * d c = d (c + i • a) * d (c + j • b))
    (i j : ℕ) :
    (f (c + i • a + j • b) / d (c + i • a + j • b)) * (f c / d c) =
      (f (c + i • a) / d (c + i • a)) * (f (c + j • b) / d (c + j • b)) := by
  rw [div_mul_div_comm, div_mul_div_comm, hfsep i j, hdsep i j]

/-- The product condition on cyclic summands used to pass from Theorem 4 and distribution
to the metric-group part of Theorem 7. -/
private def SummandProductsInvariant (p s : ℕ) (a b : G) : Prop :=
  ∀ z : G, addOrderOf z = p ^ s → (∀ n : ℕ, p ^ (s - 1) • z ≠ n • a) →
    (∀ n : ℕ, p ^ (s - 1) • z ≠ n • b) → ∀ x u : G, p • u = 0 →
      v (∏ m ∈ Finset.range (p ^ s), E (x + u + m • z) -
        ∏ m ∈ Finset.range (p ^ s), E (x + m • z)) < 1

omit [AddCommGroup G] [Fintype G] [DecidableEq G] in
/-- Reduction modulo the valuation ideal commutes with a finite product of integral values.
Used by `residue_summand_products`. -/
private theorem residue_prod (n : ℕ) (F : ℕ → L) (hF : ∀ m, v (F m) ≤ 1)
    (hP : v (∏ m ∈ Finset.range n, F m) ≤ 1) :
    (IsLocalRing.residue v.valuationSubring)
        (⟨∏ m ∈ Finset.range n, F m, hP⟩ : v.valuationSubring) =
      ∏ m ∈ Finset.range n,
        (IsLocalRing.residue v.valuationSubring)
          (⟨F m, hF m⟩ : v.valuationSubring) := by
  rw [← map_prod]
  congr 1
  apply Subtype.ext
  simp

/-- The summand-product hypothesis descends to products in the residue field on each
coset of the primary subgroup. Used by `separation_on_coset`. -/
private theorem residue_summand_products {p : ℕ} [Fact p.Prime]
    (hunit : ∀ x, v (E x) = 1) {s : ℕ}
    (e : (Fin 2 → ZMod (p ^ s)) →+ G) (he : Function.Injective e)
    {a b : G} (aa bb : Fin 2 → ZMod (p ^ s))
    (haa : e aa = a) (hbb : e bb = b)
    (hL : E.SummandProductsInvariant v p s a b) :
    let R := v.valuationSubring
    let g : G → IsLocalRing.ResidueField R :=
      fun x => (IsLocalRing.residue R) (⟨E x, (hunit x).le⟩ : R)
    ∀ (c : G) (z : Fin 2 → ZMod (p ^ s)), addOrderOf z = p ^ s →
      (∀ n : ℕ, p ^ (s - 1) • z ≠ n • aa) →
      (∀ n : ℕ, p ^ (s - 1) • z ≠ n • bb) →
      ∀ (x u : Fin 2 → ZMod (p ^ s)), p • u = 0 →
        ∏ m ∈ Finset.range (p ^ s), g (c + e (x + u + m • z)) =
          ∏ m ∈ Finset.range (p ^ s), g (c + e (x + m • z)) := by
  classical
  intro R g c z hz hza hzb x u hu
  have hprodVal (c : G) (x u z : Fin 2 → ZMod (p ^ s)) :
      v (∏ m ∈ Finset.range (p ^ s), E (c + e (x + u + m • z))) ≤ 1 := by
    rw [map_prod]
    simp [hunit]
  have hzG : addOrderOf (e z) = p ^ s := (addOrderOf_injective e he z).trans hz
  have hzaG (n : ℕ) : p ^ (s - 1) • e z ≠ n • a := by
    intro h
    exact hza n (he (by simpa only [map_nsmul, haa] using h))
  have hzbG (n : ℕ) : p ^ (s - 1) • e z ≠ n • b := by
    intro h
    exact hzb n (he (by simpa only [map_nsmul, hbb] using h))
  have huG : p • e u = 0 := by rw [← map_nsmul, hu, map_zero]
  have hval := hL (e z) hzG hzaG hzbG (c + e x) (e u) huG
  have hval' : v ((∏ m ∈ Finset.range (p ^ s), E (c + e (x + u + m • z))) -
      ∏ m ∈ Finset.range (p ^ s), E (c + e (x + m • z))) < 1 := by
    simpa only [map_add, map_nsmul, add_assoc, add_comm, add_left_comm] using hval
  have hright : v (∏ m ∈ Finset.range (p ^ s), E (c + e (x + m • z))) ≤ 1 := by
    simpa only [add_zero] using hprodVal c x 0 z
  have hred := (valuation_residue_eq_iff v (hprodVal c x u z)
    hright).mpr hval'
  calc
    (∏ m ∈ Finset.range (p ^ s), g (c + e (x + u + m • z))) =
        (IsLocalRing.residue R)
          (⟨∏ m ∈ Finset.range (p ^ s), E (c + e (x + u + m • z)),
            hprodVal c x u z⟩ : R) := by
      simpa only [g] using (residue_prod v (p ^ s) (fun m => E (c + e (x + u + m • z)))
        (fun m => (hunit _).le) (hprodVal c x u z)).symm
    _ = (IsLocalRing.residue R)
          (⟨∏ m ∈ Finset.range (p ^ s), E (c + e (x + m • z)), hright⟩ : R) := hred
    _ = ∏ m ∈ Finset.range (p ^ s), g (c + e (x + m • z)) := by
      simpa only [g] using residue_prod v (p ^ s) (fun m => E (c + e (x + m • z)))
        (fun m => (hunit _).le) hright

/-- Invariant summand products give the separated reduction identity on every coset.
This is the Lemma 6 step used by `translation_invariant_of_summands`. -/
private theorem separation_on_coset {p : ℕ} [Fact p.Prime] (hvp : v (p : L) < 1)
    (hunit : ∀ x, v (E x) = 1) {s : ℕ} (hs : 1 ≤ s)
    (e : (Fin 2 → ZMod (p ^ s)) →+ G) (he : Function.Injective e)
    (hH : ∀ (x : G) (n : ℕ), p ^ n • x = 0 → x ∈ Set.range e)
    {a b : G} (ha : p • a = 0) (hb : p • b = 0)
    (hL : E.SummandProductsInvariant v p s a b)
    (c : G) (i j : ℕ) :
    v (E (c + i • a + j • b) * E c - E (c + i • a) * E (c + j • b)) < 1 := by
  classical
  let R := v.valuationSubring
  let k := IsLocalRing.ResidueField R
  let g : G → k := fun x => (IsLocalRing.residue R) (⟨E x, (hunit x).le⟩ : R)
  have : CharP k p := valuation_residue_charP v hvp
  have hg (x : G) : g x ≠ 0 := by
    intro hx
    have h := (valuation_residue_eq_zero_iff v (hunit x).le).mp hx
    exact (lt_irrefl (1 : ℝ≥0)) ((hunit x).symm ▸ h)
  obtain ⟨aa, haa⟩ := hH a 1 (by simpa using ha)
  obtain ⟨bb, hbb⟩ := hH b 1 (by simpa using hb)
  have haa0 : p • aa = 0 := he (by simpa only [map_nsmul, haa, map_zero] using ha)
  have hbb0 : p • bb = 0 := he (by simpa only [map_nsmul, hbb, map_zero] using hb)
  have hlines := E.residue_summand_products v hunit e he aa bb haa hbb hL
  have hmixed (c : G) : g (c + a + b) * g c = g (c + a) * g (c + b) := by
    let f : (Fin 2 → ZMod (p ^ s)) → k := fun x => g (c + e x)
    have hf (x : Fin 2 → ZMod (p ^ s)) : f x ≠ 0 := hg _
    have h := mul_eq_mul_of_prod_summand_invariant hs haa0 hbb0 f hf
      (fun z hz hza hzb x u hu => hlines c z hz hza hzb x u hu) 0
    simpa only [f, map_add, map_zero, zero_add, add_zero, haa, hbb, add_assoc] using h
  have hsep (c : G) (i j : ℕ) :
      g (c + i • a + j • b) * g c = g (c + i • a) * g (c + j • b) :=
    separated_of_mixed g hg hmixed c i j
  have hvalMul (x y : G) : v (E x * E y) ≤ 1 := by
    rw [map_mul, hunit x, hunit y]
    norm_num
  have hredMul (x y : G) :
      (IsLocalRing.residue R) (⟨E x * E y, hvalMul x y⟩ : R) = g x * g y := by
    calc
      _ = (IsLocalRing.residue R) ((⟨E x, (hunit x).le⟩ : R) *
          (⟨E y, (hunit y).le⟩ : R)) := rfl
      _ = _ := by rw [map_mul]
  have hsepVal (c : G) (i j : ℕ) :
      v (E (c + i • a + j • b) * E c - E (c + i • a) * E (c + j • b)) < 1 := by
    apply (valuation_residue_eq_iff v (hvalMul _ _) (hvalMul _ _)).mp
    rw [hredMul, hredMul]
    exact hsep c i j
  exact hsepVal c i j

/-- Fourier integrality of `E` and `E⁻¹` makes the reduction constant in one torsion
coordinate on each coset. This is the Lemma 1(iii) step used by
`translation_invariant_of_summands`. -/
private theorem constant_on_each_coset {p : ℕ} [Fact p.Prime] (hvp : v (p : L) < 1)
    (hunit : ∀ x, v (E x) = 1) {s : ℕ} (hs : 1 ≤ s)
    (e : (Fin 2 → ZMod (p ^ s)) →+ G) (he : Function.Injective e)
    (hH : ∀ (x : G) (n : ℕ), p ^ n • x = 0 → x ∈ Set.range e)
    {a b : G} (ha : p • a = 0) (hb : p • b = 0)
    (hab : ∀ i j : ZMod p, i.val • a + j.val • b = 0 → i = 0 ∧ j = 0)
    (hsepVal : ∀ (c : G) (i j : ℕ),
      v (E (c + i • a + j • b) * E c - E (c + i • a) * E (c + j • b)) < 1) :
    let R := v.valuationSubring
    let g : G → IsLocalRing.ResidueField R :=
      fun x => (IsLocalRing.residue R) (⟨E x, (hunit x).le⟩ : R)
    ∀ c : G, (∀ i : ℕ, g (c + i • a) = g c) ∨
      ∀ j : ℕ, g (c + j • b) = g c := by
  classical
  let R := v.valuationSubring
  let g : G → IsLocalRing.ResidueField R :=
    fun x => (IsLocalRing.residue R) (⟨E x, (hunit x).le⟩ : R)
  have hgeq (x y : G) : g x = g y ↔ v (E x - E y) < 1 :=
    valuation_residue_eq_iff v (hunit x).le (hunit y).le
  have hfiE : M.IsFourierIntegral v E := E.isFourierIntegral v hvp (fun x => (hunit x).le)
  have hfiInv : M.IsFourierIntegral v (fun x => (E x)⁻¹) :=
    E.isFourierIntegral_inv v hvp hunit
  change ∀ c : G, (∀ i : ℕ, g (c + i • a) = g c) ∨
    ∀ j : ℕ, g (c + j • b) = g c
  intro c
  rcases hfiE.forall_or_forall_of_separated hvp hs e he hH hunit hfiInv ha hb hab c
    (hsepVal c) with hca | hcb
  · exact Or.inl (fun i => (hgeq _ _).mpr (hca i))
  · exact Or.inr (fun j => (hgeq _ _).mpr (hcb j))

/-- Reduction of a translation ratio is the quotient of the reductions. Used by
`translation_ratio_separated` and `translation_invariant_of_summands`. -/
private theorem residue_translation_ratio (hunit : ∀ x, v (E x) = 1) (h t : G)
    (hQunit : v (E (h + t) / E t) = 1) :
    (IsLocalRing.residue v.valuationSubring)
      (⟨E (h + t) / E t, hQunit.le⟩ : v.valuationSubring) =
      (IsLocalRing.residue v.valuationSubring)
        (⟨E (h + t), (hunit (h + t)).le⟩ : v.valuationSubring) /
        (IsLocalRing.residue v.valuationSubring)
          (⟨E t, (hunit t).le⟩ : v.valuationSubring) := by
  let R := v.valuationSubring
  have hQinv : v (E t)⁻¹ ≤ 1 := by
    rw [map_inv₀, hunit]
    norm_num
  have heq : (⟨E (h + t) / E t, hQunit.le⟩ : R) =
      (⟨E (h + t), (hunit (h + t)).le⟩ : R) *
        (⟨(E t)⁻¹, hQinv⟩ : R) := by
    apply Subtype.ext
    simp [div_eq_mul_inv]
  rw [heq, map_mul, valuation_residue_inv_eq v (hunit t).le hQinv (E.ne_zero t)]
  rfl

/-- A separated residue remains separated after taking a translation ratio.
Used for the comparison of cosets in `translation_invariant_of_summands`. -/
private theorem translation_ratio_separated (hunit : ∀ x, v (E x) = 1)
    {a b : G} (c₁ c₂ : G)
    (hsep : let R := v.valuationSubring
      let g : G → IsLocalRing.ResidueField R :=
        fun x => (IsLocalRing.residue R) (⟨E x, (hunit x).le⟩ : R)
      ∀ (c : G) (i j : ℕ),
        g (c + i • a + j • b) * g c = g (c + i • a) * g (c + j • b))
    (i j : ℕ) :
    let h := c₂ - c₁
    let Q : G → L := fun t => E (h + t) / E t
    v (Q (c₁ + i • a + j • b) * Q c₁ -
      Q (c₁ + i • a) * Q (c₁ + j • b)) < 1 := by
  classical
  let R := v.valuationSubring
  let k := IsLocalRing.ResidueField R
  let g : G → k := fun x => (IsLocalRing.residue R) (⟨E x, (hunit x).le⟩ : R)
  change ∀ (c : G) (i j : ℕ),
    g (c + i • a + j • b) * g c = g (c + i • a) * g (c + j • b) at hsep
  let h : G := c₂ - c₁
  let Q : G → L := fun t => E (h + t) / E t
  let q : G → k := fun t => g (h + t) / g t
  have hQunit (t : G) : v (Q t) = 1 := by
    change v (E (h + t) / E t) = 1
    rw [map_div₀, hunit, hunit]
    norm_num
  have hQred (t : G) :
      (IsLocalRing.residue R) (⟨Q t, (hQunit t).le⟩ : R) = q t := by
    simpa only [Q, q, g] using E.residue_translation_ratio v hunit h t (hQunit t)
  have hshiftSep (i j : ℕ) :
      g (h + (c₁ + i • a + j • b)) * g (h + c₁) =
        g (h + (c₁ + i • a)) * g (h + (c₁ + j • b)) := by
    convert hsep c₂ i j using 1 <;> congr 1 <;> dsimp [h] <;> abel_nf
  have hQsep (i j : ℕ) :
      q (c₁ + i • a + j • b) * q c₁ =
        q (c₁ + i • a) * q (c₁ + j • b) := by
    simpa only [q] using separated_div (fun t => g (h + t)) g c₁
      hshiftSep (hsep c₁) i j
  have hQvalMul (x y : G) : v (Q x * Q y) ≤ 1 := by
    rw [map_mul, hQunit x, hQunit y]
    norm_num
  have hQredMul (x y : G) :
      (IsLocalRing.residue R) (⟨Q x * Q y, hQvalMul x y⟩ : R) = q x * q y := by
    calc
      _ = (IsLocalRing.residue R) ((⟨Q x, (hQunit x).le⟩ : R) *
          (⟨Q y, (hQunit y).le⟩ : R)) := rfl
      _ = _ := by rw [map_mul, hQred, hQred]
  apply (valuation_residue_eq_iff v (hQvalMul _ _) (hQvalMul _ _)).mp
  rw [hQredMul, hQredMul]
  exact hQsep i j

omit [Fintype G] [DecidableEq G] in
/-- Two cosets depending on different coordinates cannot have a translation ratio constant in
one coordinate. Used by `same_line_on_all_cosets`. -/
private theorem opposite_cosets_impossible {k : Type*} [Field k] (g : G → k)
    (hg : ∀ x, g x ≠ 0) {a b c₁ c₂ : G}
    (hconstA : g (c₁ + a) = g c₁) (hconstB : g (c₂ + b) = g c₂)
    (hbadA : g (c₂ + a) ≠ g c₂) (hbadB : g (c₁ + b) ≠ g c₁)
    (hcomp : g (c₂ + a) / g (c₁ + a) = g c₂ / g c₁ ∨
      g (c₂ + b) / g (c₁ + b) = g c₂ / g c₁) : False := by
  rcases hcomp with hqa | hqb
  · rw [hconstA] at hqa
    exact hbadA ((div_left_inj' (hg c₁)).mp hqa)
  · rw [hconstB] at hqb
    apply hbadB
    have hinv : (g (c₁ + b))⁻¹ = (g c₁)⁻¹ :=
      mul_left_cancel₀ (hg c₂) (by simpa only [div_eq_mul_inv] using hqb)
    exact inv_injective hinv

/-- The Fourier-integral translation ratio rules out two cosets selecting opposite
torsion directions. Used by `same_line_on_all_cosets`. -/
private theorem compare_cosets_via_ratio {p : ℕ} [Fact p.Prime] (hvp : v (p : L) < 1)
    (hunit : ∀ x, v (E x) = 1) {s : ℕ} (hs : 1 ≤ s)
    (e : (Fin 2 → ZMod (p ^ s)) →+ G) (he : Function.Injective e)
    (hH : ∀ (x : G) (n : ℕ), p ^ n • x = 0 → x ∈ Set.range e)
    {a b : G} (ha : p • a = 0) (hb : p • b = 0)
    (hab : ∀ i j : ZMod p, i.val • a + j.val • b = 0 → i = 0 ∧ j = 0)
    (g : G → IsLocalRing.ResidueField v.valuationSubring)
    (hgdef : g = fun x => (IsLocalRing.residue v.valuationSubring)
      (⟨E x, (hunit x).le⟩ : v.valuationSubring))
    (hg : ∀ x, g x ≠ 0)
    (hsep : ∀ (c : G) (i j : ℕ),
      g (c + i • a + j • b) * g c = g (c + i • a) * g (c + j • b))
    (c₁ c₂ : G) (hconstA : g (c₁ + a) = g c₁)
    (hconstB : g (c₂ + b) = g c₂)
    (hbadA : g (c₂ + a) ≠ g c₂) (hbadB : g (c₁ + b) ≠ g c₁) : False := by
  classical
  let R := v.valuationSubring
  let k := IsLocalRing.ResidueField R
  let h : G := c₂ - c₁
  have hshift (t : G) : h + (c₁ + t) = c₂ + t := by dsimp [h]; abel_nf
  have hbase : h + c₁ = c₂ := by dsimp [h]; abel_nf
  have hh : h ≠ 0 := by
    intro hzero
    have hc : c₂ = c₁ := sub_eq_zero.mp hzero
    apply hbadA
    rw [hc]
    exact hconstA
  let Q : G → L := fun t => E (h + t) / E t
  let q : G → k := fun t => g (h + t) / g t
  have hQunit (t : G) : v (Q t) = 1 := by
    change v (E (h + t) / E t) = 1
    rw [map_div₀, hunit, hunit]
    norm_num
  have hQred (t : G) :
      (IsLocalRing.residue R) (⟨Q t, (hQunit t).le⟩ : R) = q t := by
    simpa only [Q, q, hgdef] using E.residue_translation_ratio v hunit h t (hQunit t)
  have hQeq (x y : G) : q x = q y ↔ v (Q x - Q y) < 1 := by
    rw [← hQred, ← hQred]
    exact valuation_residue_eq_iff v (hQunit x).le (hQunit y).le
  have hQsepVal (i j : ℕ) := E.translation_ratio_separated v hunit c₁ c₂ (by
      simpa only [hgdef] using hsep) i j
  obtain ⟨hfiQ, hfiInvQ⟩ := E.translationRatio_fourierIntegral v hh hQunit
  have hcomp : g (c₂ + a) / g (c₁ + a) = g c₂ / g c₁ ∨
      g (c₂ + b) / g (c₁ + b) = g c₂ / g c₁ := by
    rcases hfiQ.forall_or_forall_of_separated hvp hs e he hH hQunit hfiInvQ
      ha hb hab c₁ hQsepVal with hQa | hQb
    · left
      have hqa : q (c₁ + a) = q c₁ := (hQeq _ _).mpr (by simpa only [one_nsmul] using hQa 1)
      change g (h + (c₁ + a)) / g (c₁ + a) = g (h + c₁) / g c₁ at hqa
      simpa only [hshift a, hbase] using hqa
    · right
      have hqb : q (c₁ + b) = q c₁ := (hQeq _ _).mpr (by simpa only [one_nsmul] using hQb 1)
      change g (h + (c₁ + b)) / g (c₁ + b) = g (h + c₁) / g c₁ at hqb
      simpa only [hshift b, hbase] using hqb
  exact opposite_cosets_impossible g hg hconstA hconstB hbadA hbadB hcomp


/-- The translation ratio excludes opposite coordinate choices on two cosets. This is
the comparison step in `translation_invariant_of_summands`. -/
private theorem same_line_on_all_cosets {p : ℕ} [Fact p.Prime] (hvp : v (p : L) < 1)
    (hunit : ∀ x, v (E x) = 1) {s : ℕ} (hs : 1 ≤ s)
    (e : (Fin 2 → ZMod (p ^ s)) →+ G) (he : Function.Injective e)
    (hH : ∀ (x : G) (n : ℕ), p ^ n • x = 0 → x ∈ Set.range e)
    {a b : G} (ha : p • a = 0) (hb : p • b = 0)
    (hab : ∀ i j : ZMod p, i.val • a + j.val • b = 0 → i = 0 ∧ j = 0)
    (g : G → IsLocalRing.ResidueField v.valuationSubring)
    (hgdef : g = fun x => (IsLocalRing.residue v.valuationSubring)
      (⟨E x, (hunit x).le⟩ : v.valuationSubring))
    (hg : ∀ x, g x ≠ 0)
    (hgeq : ∀ x y : G, g x = g y ↔ v (E x - E y) < 1)
    (hsep : ∀ (c : G) (i j : ℕ),
      g (c + i • a + j • b) * g c = g (c + i • a) * g (c + j • b))
    (hlocal : ∀ c : G,
      (∀ i : ℕ, g (c + i • a) = g c) ∨ ∀ j : ℕ, g (c + j • b) = g c) :
    (∀ x, v (E (x + a) - E x) < 1) ∨ ∀ x, v (E (x + b) - E x) < 1 := by
  classical
  let R := v.valuationSubring
  let k := IsLocalRing.ResidueField R
  by_contra hn
  obtain ⟨hna, hnb⟩ := not_or.mp hn
  obtain ⟨c₂, hc₂⟩ := not_forall.mp hna
  obtain ⟨c₁, hc₁⟩ := not_forall.mp hnb
  have hbadA : g (c₂ + a) ≠ g c₂ := fun h => hc₂ ((hgeq _ _).mp h)
  have hbadB : g (c₁ + b) ≠ g c₁ := fun h => hc₁ ((hgeq _ _).mp h)
  have hconstA : ∀ i : ℕ, g (c₁ + i • a) = g c₁ := by
    rcases hlocal c₁ with hA | hB
    · exact hA
    · exact (hbadB (by simpa only [one_nsmul] using hB 1)).elim
  have hconstB : ∀ j : ℕ, g (c₂ + j • b) = g c₂ := by
    rcases hlocal c₂ with hA | hB
    · exact (hbadA (by simpa only [one_nsmul] using hA 1)).elim
    · exact hB
  exact E.compare_cosets_via_ratio v hvp hunit hs e he hH ha hb hab g hgdef hg hsep
    c₁ c₂ (by simpa only [one_nsmul] using hconstA 1)
    (by simpa only [one_nsmul] using hconstB 1) hbadA hbadB

/-- **[RW26b, Radchenko, Wheeler (2026b), Section 7, Theorem 7], metric-group form**: let the
values of `E` be units at a valuation with `v(p) < 1`, let the `p`-primary part of `G` be the
image of an injective `e : (ℤ/p^s)² → G`, and let `a, b ∈ G[p]` be independent. If for every
`z` of order `p^s` with `p^{s-1}z ∉ ⟨a⟩ ∪ ⟨b⟩` the products `∏_{m<p^s} E(x + mz)` are invariant
modulo `𝔪` under translation by `G[p]`, then the reduction of `E` is invariant under translation
by `a` or by `b`, the same for every argument. -/
theorem translation_invariant_of_summands {p : ℕ} [Fact p.Prime] (hvp : v (p : L) < 1)
    (hunit : ∀ x, v (E x) = 1) {s : ℕ} (hs : 1 ≤ s) (e : (Fin 2 → ZMod (p ^ s)) →+ G)
    (he : Function.Injective e) (hH : ∀ (x : G) (n : ℕ), p ^ n • x = 0 → x ∈ Set.range e)
    {a b : G} (ha : p • a = 0) (hb : p • b = 0)
    (hab : ∀ i j : ZMod p, i.val • a + j.val • b = 0 → i = 0 ∧ j = 0)
    (hL : ∀ z : G, addOrderOf z = p ^ s → (∀ n : ℕ, p ^ (s - 1) • z ≠ n • a) →
      (∀ n : ℕ, p ^ (s - 1) • z ≠ n • b) → ∀ x u : G, p • u = 0 →
        v (∏ m ∈ Finset.range (p ^ s), E (x + u + m • z) -
          ∏ m ∈ Finset.range (p ^ s), E (x + m • z)) < 1) :
    (∀ x, v (E (x + a) - E x) < 1) ∨ ∀ x, v (E (x + b) - E x) < 1 := by
  classical
  let R := v.valuationSubring
  let k := IsLocalRing.ResidueField R
  let g : G → k := fun x => (IsLocalRing.residue R) (⟨E x, (hunit x).le⟩ : R)
  have : CharP k p := valuation_residue_charP v hvp
  have hg (x : G) : g x ≠ 0 := by
    intro hx
    have h := (valuation_residue_eq_zero_iff v (hunit x).le).mp hx
    exact (lt_irrefl (1 : ℝ≥0)) ((hunit x).symm ▸ h)
  have hgeq (x y : G) : g x = g y ↔ v (E x - E y) < 1 :=
    valuation_residue_eq_iff v (hunit x).le (hunit y).le
  have hsepVal (c : G) (i j : ℕ) :=
    E.separation_on_coset v hvp hunit hs e he hH ha hb hL c i j
  have hvalMul (x y : G) : v (E x * E y) ≤ 1 := by
    rw [map_mul, hunit x, hunit y]
    norm_num
  have hredMul (x y : G) :
      (IsLocalRing.residue R) (⟨E x * E y, hvalMul x y⟩ : R) = g x * g y := by
    calc
      _ = (IsLocalRing.residue R) ((⟨E x, (hunit x).le⟩ : R) *
          (⟨E y, (hunit y).le⟩ : R)) := rfl
      _ = _ := by rw [map_mul]
  have hsep (c : G) (i j : ℕ) :
      g (c + i • a + j • b) * g c = g (c + i • a) * g (c + j • b) := by
    have h := (valuation_residue_eq_iff v (hvalMul _ _) (hvalMul _ _)).mpr
      (hsepVal c i j)
    rwa [hredMul, hredMul] at h
  have hlocal := E.constant_on_each_coset v hvp hunit hs e he hH ha hb hab hsepVal
  exact E.same_line_on_all_cosets v hvp hunit hs e he hH ha hb hab g rfl hg hgeq
    hsep hlocal

end FiniteQuantumDilog

end SIC
