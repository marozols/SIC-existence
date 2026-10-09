/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.NumberTheory.Multiplicity

/-!
# Independent residues modulo integers prime to a given integer

Primes at which an integer has prescribed prime-power order, moduli prime to a given integer at
which an integer has order divisible by `n`, and moduli carrying a residue independent of the
residues of finitely many given integers.

This module follows Childress, *Class Field Theory* (2009), Chapter V, Lemmas 2.3–2.6, the
elementary number theory behind Artin's auxiliary fields (Lemma 2.8). Lemma 2.6 is formalized in
the form its consumer uses: for every integer `a > 1` and every `n > 0` there are a modulus `m`
prime to a given `N` and a residue `t` such that $a^it^j\equiv 1 \pmod m$ forces $n\mid i$ and
$n\mid j$. This is the content of Lemma 2.6(ii) and (iii) used in the proof of Lemma 2.8(ii):
independence of $\langle a\rangle$ and $\langle t\rangle$ together with orders divisible by `n`.
The family version provides one modulus and one residue for finitely many integers at once,
which replaces the pairwise coprime moduli $m_1,\dots,m_r$ of Childress's proof of
Proposition 2.2.

## The argument

*Lemma 2.3.* For a prime `q`, `r > 1` and `a > 1`, put $x = a^{q^{r-1}}$ and
$t = 1+x+\cdots+x^{q-1}$. A prime `p ∣ t` with `p ∤ x-1` has $a^{q^r}\equiv 1$ and
$a^{q^{r-1}}\not\equiv 1 \pmod p$, so the order of `a` modulo `p` is $q^r$. A prime dividing
both `t` and `x-1` divides `q`. The sum is greater than `q`, while $q^2\nmid t$: if $q\mid t$,
Fermat's theorem gives $q\mid x-1$; for odd `q`, the binomial expansion gives the exact
`q`-adic valuation one. For `q = 2`, write $x=y^2$; then $t=1+y^2$ is not divisible by four.
Thus `t` has a prime factor other than `q`.

*Corollary 2.4.* Apply Lemma 2.3 with exponent $r+N+2$. The resulting order exceeds `N` and
is at most the modulus `p`, so $p>N$ and $q^r$ divides that order.

*Lemma 2.5.* Factor `n` into prime powers and choose, for each, a prime from Corollary 2.4 not
dividing `N` nor the primes already chosen; their product `d` is prime to `N`, and the order of
`a` modulo `d` is divisible by each prime power, as reduction to each prime factor shows.

*Lemma 2.6.* Choose `d` for `N` by Lemma 2.5 and `d'` for `N d`, put `m = d d'`, and let `t` be
the residue with $t\equiv 1\pmod d$ and $t\equiv a\pmod{d'}$ (Chinese remainder theorem). If
$a^it^j\equiv 1\pmod m$, then modulo `d` we get $a^i\equiv 1$, so $n\mid i$, and modulo `d'` we
get $a^{i+j}\equiv 1$, so $n\mid i+j$. Childress takes $t\equiv a\pmod d$, $t\equiv 1\pmod{d'}$
with `d'` adapted to the order of `a` modulo `d`; the variant above needs only Lemma 2.5 twice.

*Several integers.* Induct on the finite family: given `M` and `t` for the family, apply
Lemma 2.6 to the new integer with `N M` in place of `N`, and combine the two residues by the
Chinese remainder theorem modulo the product of the coprime moduli. Each condition only
involves one of the two factors.
-/

namespace SIC

open Finset

/-! ### Primes with prescribed prime-power order -/

/-- The square modulo four needed for `exists_prime_orderOf_eq_pow` when the prime is two. -/
private theorem four_not_dvd_one_add_sq (y : ℕ) : ¬ 4 ∣ 1 + y ^ 2 := by
  intro hd
  have hz : ∀ z : ZMod 4, 1 + z ^ 2 ≠ 0 := by decide
  apply hz (y : ZMod 4)
  simpa using (ZMod.natCast_eq_zero_iff (1 + y ^ 2) 4).mpr hd

/-- The geometric-sum identity used in `exists_prime_orderOf_eq_pow`. -/
private theorem geom_sum_mul_sub_one (q x : ℕ) (hx : 1 ≤ x) :
    (∑ i ∈ range q, x ^ i) * (x - 1) + 1 = x ^ q := by
  simpa [Nat.sub_add_cancel hx] using geom_sum_mul_add (x - 1) q

/-- A prime dividing the geometric sum at its own exponent divides the base minus one;
this is the Frobenius step in `exists_prime_orderOf_eq_pow`. -/
private theorem prime_dvd_geom_sum_imp_dvd_sub_one (q x : ℕ) (hq : q.Prime) (hx : 1 < x)
    (ht : q ∣ ∑ i ∈ range q, x ^ i) : q ∣ x - 1 := by
  have hgeom := geom_sum_mul_sub_one q x hx.le
  have ht0 : ((∑ i ∈ range q, x ^ i : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr ht
  have hcast : (x : ZMod q) ^ q = 1 := by
    have h := congrArg (fun z : ℕ => (z : ZMod q)) hgeom
    simpa [ht0] using h.symm
  have hx1 : (x : ZMod q) = 1 := by
    simpa only [@ZMod.pow_card q ⟨hq⟩] using hcast
  have hsub : ((x - 1 : ℕ) : ZMod q) = 0 := by
    have h : x - 1 + 1 = x := Nat.sub_add_cancel hx.le
    have h' := congrArg (fun z : ℕ => (z : ZMod q)) h
    simp only [Nat.cast_add, Nat.cast_one, hx1] at h'
    simpa only [add_eq_right] using h'
  exact (ZMod.natCast_eq_zero_iff _ _).mp hsub

/-- For odd `q`, the geometric sum has `q`-adic valuation one when `q ∣ x-1`;
this is the odd-prime step in `exists_prime_orderOf_eq_pow`. -/
private theorem prime_sq_not_dvd_geom_sum_of_dvd_sub_one (q x : ℕ) (hq : q.Prime)
    (hqodd : Odd q) (hx : 1 ≤ x) (hqx : q ∣ x - 1) :
    ¬ q ^ 2 ∣ ∑ i ∈ range q, x ^ i := by
  have hqxZ : (q : ℤ) ∣ (x : ℤ) - 1 := by
    have hsub : ((x - 1 : ℕ) : ℤ) = (x : ℤ) - 1 := by omega
    rw [← hsub]
    exact_mod_cast hqx
  have hnxZ : ¬ (q : ℤ) ∣ (x : ℤ) := by
    intro hd
    have h1 : (q : ℤ) ∣ (1 : ℤ) := by
      have h := dvd_sub hd hqxZ
      simpa using h
    exact hq.not_dvd_one (Int.natCast_dvd_natCast.mp h1)
  have hem := emultiplicity_geom_sum₂_eq_one (p := q) (x := (x : ℤ)) (y := 1)
    (Nat.prime_iff_prime_int.mp hq) hqodd hqxZ hnxZ
  have hm : emultiplicity (q : ℤ) (∑ i ∈ range q, (x : ℤ) ^ i) = 1 := by
    simpa using hem
  have hnot := (emultiplicity_eq_coe.mp hm).2
  intro hq2
  apply hnot
  simpa using (show (q : ℤ) ^ 2 ∣ (∑ i ∈ range q, (x : ℤ) ^ i) by
    exact_mod_cast hq2)

/-- The geometric sum at a prime exponent of a prime power has no square of that
prime as a factor; used by `exists_prime_orderOf_eq_pow`. -/
private theorem prime_sq_not_dvd_geom_sum (q y : ℕ) (hq : q.Prime) (hy : 1 < y) :
    ¬ q ^ 2 ∣ ∑ i ∈ range q, (y ^ q) ^ i := by
  by_cases hq2 : q = 2
  · subst q
    simpa [Finset.sum_range_succ, add_comm] using four_not_dvd_one_add_sq y
  · have hx : 1 < y ^ q := one_lt_pow₀ hy hq.ne_zero
    by_cases hqt : q ∣ ∑ i ∈ range q, (y ^ q) ^ i
    · exact prime_sq_not_dvd_geom_sum_of_dvd_sub_one q (y ^ q) hq
        (hq.odd_of_ne_two hq2) hx.le
        (prime_dvd_geom_sum_imp_dvd_sub_one q (y ^ q) hq hx hqt)
    · intro hq2t
      exact hqt ((dvd_pow_self q (by decide : 2 ≠ 0)).trans hq2t)

/-- The geometric sum is larger than its prime exponent when its base exceeds one;
used by `exists_prime_orderOf_eq_pow`. -/
private theorem prime_lt_geom_sum (q x : ℕ) (hq : q.Prime) (hx : 1 < x) :
    q < ∑ i ∈ range q, x ^ i := by
  have hsum := Finset.sum_lt_sum (s := range q)
    (f := fun _ : ℕ => (1 : ℕ)) (g := fun i => x ^ i)
    (by intro i hi; exact one_le_pow₀ (by omega : 1 ≤ x))
    ⟨1, mem_range.mpr hq.one_lt, by simpa using hx⟩
  simpa using hsum

/-- A number greater than `q` but not divisible by `q²` has a prime factor other
than `q`; used by `exists_prime_orderOf_eq_pow`. -/
private theorem prime_factor_ne_of_sq_not_dvd (q t : ℕ) (hq : q.Prime) (hgt : q < t)
    (hnot : ¬ q ^ 2 ∣ t) :
    ∃ p : ℕ, p.Prime ∧ p ≠ q ∧ p ∣ t := by
  have ht0 : t ≠ 0 := by omega
  obtain ⟨e, b, hqb, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd ht0 q hq.ne_one
  have he : e ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ e := by omega
    apply hnot
    rw [heq]
    exact (pow_dvd_pow q h2).trans (dvd_mul_right _ _)
  have hb : b ≠ 1 := by
    intro hb1
    rcases e with _ | e
    · have ht : t = 1 := by simpa [hb1] using heq
      have := hq.one_lt
      omega
    rcases e with _ | e
    · have ht : t = q := by simpa [hb1] using heq
      omega
    · omega
  obtain ⟨p, hp, hpb⟩ := Nat.ne_one_iff_exists_prime_dvd.mp hb
  refine ⟨p, hp, ?_, ?_⟩
  · intro h
    subst p
    exact hqb hpb
  · rw [heq]
    exact dvd_mul_of_dvd_right hpb _

/-- A prime factor `p ≠ q` of the geometric sum does not divide `x-1`;
used by `exists_prime_orderOf_eq_pow`. -/
private theorem prime_factor_geom_sum_not_dvd_sub_one (q x p : ℕ) (hq : q.Prime)
    (hp : p.Prime) (hx : 1 ≤ x) (hpq : p ≠ q)
    (hpt : p ∣ ∑ i ∈ range q, x ^ i) : ¬ p ∣ x - 1 := by
  intro hpx
  have hpxZ : (p : ℤ) ∣ (x : ℤ) - 1 := by
    have hsub : ((x - 1 : ℕ) : ℤ) = (x : ℤ) - 1 := by omega
    rw [← hsub]
    exact_mod_cast hpx
  have hptZ : (p : ℤ) ∣ (∑ i ∈ range q, (x : ℤ) ^ i) := by
    exact_mod_cast hpt
  have hpd : (p : ℤ) ∣ (q : ℤ) := by
    have h := (dvd_geom_sum₂_iff_of_dvd_sub (n := q) (x := (x : ℤ)) (y := 1)
      (p := (p : ℤ)) hpxZ).mp (by simpa using hptZ)
    simpa using h
  have hpqd : p ∣ q := Int.natCast_dvd_natCast.mp hpd
  exact hpq ((hq.eq_one_or_self_of_dvd p hpqd).resolve_left hp.ne_one)

/-- **Childress, Lemma 2.3**: for a prime `q`, `r > 1`, and `a > 1`, there is a prime `p` at
which `a` has multiplicative order exactly $q^r$. Childress, *Class Field Theory*, Chapter V,
Lemma 2.3. -/
theorem exists_prime_orderOf_eq_pow {q r a : ℕ} (hq : q.Prime) (hr : 1 < r) (ha : 1 < a) :
    ∃ p : ℕ, p.Prime ∧ orderOf (a : ZMod p) = q ^ r := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, r = k + 2 := ⟨r - 2, by omega⟩
  let y := a ^ (q ^ k)
  let x := a ^ (q ^ (k + 1))
  have hy : 1 < y := one_lt_pow₀ ha (pow_ne_zero k hq.ne_zero)
  have hxy : x = y ^ q := by simp [x, y, pow_succ, pow_mul]
  have hx : 1 < x := by rw [hxy]; exact one_lt_pow₀ hy hq.ne_zero
  let t := ∑ i ∈ range q, x ^ i
  have htgt : q < t := prime_lt_geom_sum q x hq hx
  have htno : ¬ q ^ 2 ∣ t := by
    simpa [t, hxy] using prime_sq_not_dvd_geom_sum q y hq hy
  obtain ⟨p, hp, hpq, hpt⟩ := prime_factor_ne_of_sq_not_dvd q t hq htgt htno
  have hpx : ¬ p ∣ x - 1 := prime_factor_geom_sum_not_dvd_sub_one q x p hq hp hx.le hpq hpt
  have hgeom : t * (x - 1) + 1 = x ^ q := geom_sum_mul_sub_one q x hx.le
  have hfinx : (x : ZMod p) ^ q = 1 := by
    have ht0 : (t : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpt
    have h := congrArg (fun z : ℕ => (z : ZMod p)) hgeom
    simpa [ht0] using h.symm
  have hnotx : (x : ZMod p) ≠ 1 := by
    intro h
    have hcast : ((x - 1 : ℕ) : ZMod p) + 1 = (x : ZMod p) := by
      simpa using congrArg (fun z : ℕ => (z : ZMod p)) (Nat.sub_add_cancel hx.le)
    have hzero : ((x - 1 : ℕ) : ZMod p) = 0 := by
      simpa only [h, add_eq_right] using hcast
    exact hpx ((ZMod.natCast_eq_zero_iff _ _).mp hzero)
  have hxcast : (x : ZMod p) = (a : ZMod p) ^ q ^ (k + 1) := by simp [x]
  have hnot : (a : ZMod p) ^ q ^ (k + 1) ≠ 1 := by rwa [← hxcast]
  have hfin : (a : ZMod p) ^ q ^ (k + 1 + 1) = 1 := by
    simpa [hxcast, pow_succ, pow_mul] using hfinx
  exact ⟨p, hp, by simpa only [← Nat.add_assoc, one_add_one_eq_two] using
    (orderOf_eq_prime_pow (hp := ⟨hq⟩) hnot hfin)⟩

/-- **Childress, Corollary 2.4**: for a prime `q`, any `r`, and `a > 1`, there are arbitrarily
large primes `p` prime to `a` at which $q^r$ divides the order of `a`. Childress, *Class Field
Theory*, Chapter V, Corollary 2.4. -/
theorem exists_prime_pow_dvd_orderOf {q a : ℕ} (hq : q.Prime) (r : ℕ) (ha : 1 < a) (N : ℕ) :
    ∃ p : ℕ, p.Prime ∧ N < p ∧ a.Coprime p ∧ q ^ r ∣ orderOf (a : ZMod p) := by
  obtain ⟨p, hp, horder⟩ := exists_prime_orderOf_eq_pow hq
    (r := r + N + 2) (by omega) ha
  have : NeZero p := ⟨hp.ne_zero⟩
  have hlarge : N < q ^ (r + N + 2) := by
    have h := Nat.lt_two_pow_self (n := N + 1)
    have hqpow := Nat.pow_le_pow_left hq.two_le (N + 1)
    have hexp : N + 1 ≤ r + N + 2 := by omega
    exact lt_of_lt_of_le (by omega : N < 2 ^ (N + 1))
      (hqpow.trans (Nat.pow_le_pow_right hq.pos hexp))
  have hcop : a.Coprime p :=
    (ZMod.isUnit_iff_coprime a p).mp
      ((orderOf_pos_iff.mp (by rw [horder]; exact pow_pos hq.pos _)).isUnit)
  refine ⟨p, hp, ?_, hcop, ?_⟩
  · have hbound : orderOf (a : ZMod p) ≤ p := by
      simpa [ZMod.card] using (orderOf_le_card_univ (x := (a : ZMod p)))
    exact lt_of_lt_of_le hlarge (horder ▸ hbound)
  · rw [horder]
    exact pow_dvd_pow q (by omega)

/-! ### Moduli with prescribed order divisibility -/

/-- Reduction from a modulus `m` to a divisor `d` makes the order of an integer divide
its order modulo `m`; used by `exists_coprime_dvd_orderOf`. -/
private theorem orderOf_natCast_dvd_of_dvd {d m a : ℕ} (h : d ∣ m) :
    orderOf (a : ZMod d) ∣ orderOf (a : ZMod m) := by
  simpa using orderOf_map_dvd (ZMod.castHom h (ZMod d)).toMonoidHom (a : ZMod m)

/-- **Childress, Lemma 2.5**: for `n > 0`, `a > 1`, and `N ≠ 0`, some modulus `d` prime to `N`
and to `a` has `n` dividing the order of `a` modulo `d`. Childress, *Class Field Theory*,
Chapter V, Lemma 2.5, with the finite set of excluded primes given by the prime factors of `N`. -/
theorem exists_coprime_dvd_orderOf {n a N : ℕ} (hn : 0 < n) (ha : 1 < a) (hN : N ≠ 0) :
    ∃ d : ℕ, 0 < d ∧ d.Coprime N ∧ a.Coprime d ∧ n ∣ orderOf (a : ZMod d) := by
  suffices H : ∀ k : ℕ, 0 < k → ∀ M : ℕ, M ≠ 0 →
      ∃ d : ℕ, 0 < d ∧ d.Coprime M ∧ a.Coprime d ∧ k ∣ orderOf (a : ZMod d) from
    H n hn N hN
  intro k
  induction k using Nat.recOnPosPrimePosCoprime with
  | zero =>
      intro hk
      omega
  | one =>
      intro hk M hM
      exact ⟨1, by omega, by simp, by simp, one_dvd _⟩
  | prime_pow p e hp he =>
      intro hk M hM
      obtain ⟨d, hd, hlarge, had, horder⟩ := exists_prime_pow_dvd_orderOf hp e ha M
      refine ⟨d, hd.pos, ?_, had, horder⟩
      exact (hd.coprime_iff_not_dvd).mpr (by
        intro h
        exact (not_lt_of_ge (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) h)) hlarge)
  | coprime k l hk hl hkl ihk ihl =>
      intro hprod M hM
      obtain ⟨d, hd, hdM, had, hod⟩ := ihk (by omega) M hM
      obtain ⟨e, he, heMd, hae, hoe⟩ := ihl (by omega) (M * d)
        (mul_ne_zero hM (by omega))
      have heM : e.Coprime M := heMd.of_dvd_right (dvd_mul_right M d)
      have hed : e.Coprime d := heMd.of_dvd_right (dvd_mul_left d M)
      refine ⟨d * e, by positivity, hdM.mul_left heM, had.mul_right hae, ?_⟩
      apply hkl.mul_dvd_of_dvd_of_dvd
      · exact hod.trans (orderOf_natCast_dvd_of_dvd (d := d) (m := d * e)
          (dvd_mul_right d e))
      · exact hoe.trans (orderOf_natCast_dvd_of_dvd (d := e) (m := d * e)
          (dvd_mul_left e d))

/-! ### Independent residues

A unit `t` modulo `M` is independent of the residue of `a` to order `n` when
$a^it^j\equiv 1\pmod M$ forces $n\mid i$ and $n\mid j$. If `a` is not a unit modulo `M`, the
condition is vacuous. -/

/-- The unit `t` modulo `M` is **independent of `a` to order `n`**: for the unit `u` with
$u\equiv a\pmod M$, $u^it^j = 1$ forces $n\mid i$ and $n\mid j$. This is the consequence of
Childress's conditions that `n` divide the orders of `a` and `t` and that
$\langle a\rangle\cap\langle t\rangle = 1$ (Childress, *Class Field Theory*, Chapter V,
Lemma 2.6(ii), (iii)), in the form used in the proof of Lemma 2.8(ii). -/
def IsIndependentResidue {M : ℕ} (n a : ℕ) (t : (ZMod M)ˣ) : Prop :=
  ∀ u : (ZMod M)ˣ, (u : ZMod M) = a → ∀ i j : ℤ, u ^ i * t ^ j = 1 →
    (n : ℤ) ∣ i ∧ (n : ℤ) ∣ j

/-- The unit-level Chinese remainder equivalence used by the independent-residue
constructions. -/
private def crtUnits {d e : ℕ} (h : d.Coprime e) :
    (ZMod d)ˣ × (ZMod e)ˣ ≃* (ZMod (d * e))ˣ :=
  ((Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits).symm

/-- The first projection of `crtUnits`, used by `exists_isIndependentResidue` and its
finite-family version. -/
private theorem crtUnits_left {d e : ℕ} (h : d.Coprime e)
    (u : (ZMod d)ˣ) (v : (ZMod e)ˣ) :
    ZMod.unitsMap (dvd_mul_right d e) (crtUnits h (u, v)) = u := by
  apply Units.ext
  change (ZMod.castHom (dvd_mul_right d e) (ZMod d))
    ((crtUnits h (u, v) : (ZMod (d * e))ˣ) : ZMod (d * e)) = (u : ZMod d)
  have hh := (ZMod.chineseRemainder h).apply_symm_apply ((u : ZMod d), (v : ZMod e))
  change (((ZMod.chineseRemainder h).symm ((u : ZMod d), (v : ZMod e))).cast : ZMod d) = u
  simpa [ZMod.chineseRemainder] using congrArg Prod.fst hh

/-- The second projection of `crtUnits`, used by `exists_isIndependentResidue` and its
finite-family version. -/
private theorem crtUnits_right {d e : ℕ} (h : d.Coprime e)
    (u : (ZMod d)ˣ) (v : (ZMod e)ˣ) :
    ZMod.unitsMap (dvd_mul_left e d) (crtUnits h (u, v)) = v := by
  apply Units.ext
  change (ZMod.castHom (dvd_mul_left e d) (ZMod e))
    ((crtUnits h (u, v) : (ZMod (d * e))ˣ) : ZMod (d * e)) = (v : ZMod e)
  have hh := (ZMod.chineseRemainder h).apply_symm_apply ((u : ZMod d), (v : ZMod e))
  change (((ZMod.chineseRemainder h).symm ((u : ZMod d), (v : ZMod e))).cast : ZMod e) = v
  simpa [ZMod.chineseRemainder] using congrArg Prod.snd hh

/-- **Childress, Lemma 2.6**, in the form used by Artin's lemma: for `n > 0`, `a > 1`, and
`N ≠ 0`, there are a modulus `m` prime to `N` and a unit `t` modulo `m` independent of `a` to
order `n`: $a^it^j\equiv 1\pmod m$ forces $n\mid i$ and $n\mid j$. This is clauses (i)–(iii)
of Childress, *Class Field Theory*, Chapter V, Lemma 2.6, as consumed in the proof of
Lemma 2.8(ii); the residue `t` is built by a variant of Childress's construction (see the module
docstring). -/
theorem exists_isIndependentResidue {n a N : ℕ} (hn : 0 < n) (ha : 1 < a) (hN : N ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ m.Coprime N ∧ ∃ t : (ZMod m)ˣ, IsIndependentResidue n a t := by
  obtain ⟨d, hd, hdN, had, hdo⟩ := exists_coprime_dvd_orderOf hn ha hN
  obtain ⟨e, he, heNd, hae, heo⟩ := exists_coprime_dvd_orderOf hn ha
    (mul_ne_zero hN (by omega : d ≠ 0)) (N := N * d)
  have hde : d.Coprime e := (heNd.of_dvd_right (dvd_mul_left d N)).symm
  let ue : (ZMod e)ˣ := ZMod.unitOfCoprime a hae
  let t : (ZMod (d * e))ˣ := crtUnits hde (1, ue)
  refine ⟨d * e, by positivity, hdN.mul_left
    (heNd.of_dvd_right (dvd_mul_right N d)), t, ?_⟩
  intro u hu i j hrel
  let ud : (ZMod d)ˣ := ZMod.unitOfCoprime a had
  have hud : ZMod.unitsMap (dvd_mul_right d e) u = ud := by
    apply Units.ext
    change (ZMod.castHom (dvd_mul_right d e) (ZMod d)) (u : ZMod (d * e)) =
      (ud : ZMod d)
    rw [hu]
    simp [ud]
  have hue : ZMod.unitsMap (dvd_mul_left e d) u = ue := by
    apply Units.ext
    change (ZMod.castHom (dvd_mul_left e d) (ZMod e)) (u : ZMod (d * e)) =
      (ue : ZMod e)
    rw [hu]
    simp [ue]
  have hdi : ud ^ i = 1 := by
    have h := congrArg (ZMod.unitsMap (dvd_mul_right d e)) hrel
    simpa [hud, t, crtUnits_left hde] using h
  have hei : ue ^ (i + j) = 1 := by
    have h := congrArg (ZMod.unitsMap (dvd_mul_left e d)) hrel
    simpa [hue, t, crtUnits_right hde, zpow_add] using h
  have hudo : n ∣ orderOf ud := by
    rw [← orderOf_units]
    simpa [ud] using hdo
  have hueo : n ∣ orderOf ue := by
    rw [← orderOf_units]
    simpa [ue] using heo
  have hudoZ : (n : ℤ) ∣ (orderOf ud : ℤ) := by exact_mod_cast hudo
  have hueoZ : (n : ℤ) ∣ (orderOf ue : ℤ) := by exact_mod_cast hueo
  have hni : (n : ℤ) ∣ i := hudoZ.trans ((orderOf_dvd_iff_zpow_eq_one).mpr hdi)
  have hnij : (n : ℤ) ∣ i + j := hueoZ.trans ((orderOf_dvd_iff_zpow_eq_one).mpr hei)
  exact ⟨hni, by simpa using dvd_sub hnij hni⟩

/-- Independence survives reduction to a factor modulus; used by
`exists_isIndependentResidue_of_finset`. -/
private theorem independent_of_unitsMap {d m n a : ℕ} (hd : d ∣ m)
    {t : (ZMod m)ˣ} (hind : IsIndependentResidue n a (ZMod.unitsMap hd t)) :
    IsIndependentResidue n a t := by
  intro u hu i j hrel
  apply hind (ZMod.unitsMap hd u)
  · change (ZMod.castHom hd (ZMod d)) (u : ZMod m) = (a : ZMod d)
    rw [hu]
    simp
  · simpa using congrArg (ZMod.unitsMap hd) hrel

/-- **Independent residues for finitely many integers**: for `n > 0`, integers `a i > 1`
indexed by a finite set, and `N ≠ 0`, there are a modulus `M` prime to `N` and a unit `t` modulo
`M` such that for each `i`, $a_i^jt^k\equiv 1\pmod M$ forces $n\mid j$ and $n\mid k$. This
replaces the pairwise coprime moduli of Childress, *Class Field Theory*, Chapter V, proof of
Proposition 2.2, by their product, with `t` assembled by the Chinese remainder theorem from
`exists_isIndependentResidue`. -/
theorem exists_isIndependentResidue_of_finset {ι : Type*} (T : Finset ι) {a : ι → ℕ}
    (ha : ∀ i ∈ T, 1 < a i) {n N : ℕ} (hn : 0 < n) (hN : N ≠ 0) :
    ∃ M : ℕ, 0 < M ∧ M.Coprime N ∧ ∃ t : (ZMod M)ˣ, ∀ i ∈ T, IsIndependentResidue n (a i) t := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      exact ⟨1, by omega, by simp, 1, by simp⟩
  | @insert i S hi ih =>
      have haS : ∀ j ∈ S, 1 < a j := by
        intro j hj
        exact ha j (Finset.mem_insert_of_mem hj)
      obtain ⟨M, hM, hMN, t, ht⟩ := ih haS
      have hai : 1 < a i := ha i (Finset.mem_insert_self i S)
      obtain ⟨m, hm, hmNM, s, hs⟩ := exists_isIndependentResidue hn hai
        (mul_ne_zero hN (by omega : M ≠ 0)) (N := N * M)
      have hMm : M.Coprime m :=
        (hmNM.of_dvd_right (dvd_mul_left M N)).symm
      let t' : (ZMod (M * m))ˣ := crtUnits hMm (t, s)
      refine ⟨M * m, by positivity, hMN.mul_left
        (hmNM.of_dvd_right (dvd_mul_right N M)), t', ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · have hr : ZMod.unitsMap (dvd_mul_left m M) t' = s := crtUnits_right hMm t s
        exact independent_of_unitsMap (dvd_mul_left m M) (hr ▸ hs)
      · have hl : ZMod.unitsMap (dvd_mul_right M m) t' = t := crtUnits_left hMm t s
        exact independent_of_unitsMap (dvd_mul_right M m) (hl ▸ ht j hj)

end SIC
