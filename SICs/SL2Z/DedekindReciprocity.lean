/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.SL2Z.Rademacher

/-!
# Dedekind's reciprocity law

Dedekind's reciprocity law and the value `𝔰(n, n²-1)`.

This file proves the reciprocity law for the Dedekind sums of `SICs.SL2Z.Rademacher`: for coprime
positive integers `h` and `k`,

```text
𝔰(h,k) + 𝔰(k,h) = -1/4 + (h/k + k/h + 1/(hk))/12.
```

It is the one classical arithmetic input of `SICs.SL2Z.RademacherWord`, which identifies the
Rademacher class invariant `Ψ(M)` with the accumulator the word cocycle produces.

## The argument

The proof followed here is the first of the four in [88, Rademacher and Grosswald (1972), Chapter
2], a variant due to the authors of one of Dieter's. Everything happens in `ℚ`; no roots of unity,
cotangent sums, or contour integrals are needed, which is why this proof was chosen over the other
three.

Two preliminary facts carry the argument. The first is the *distribution law*
`dedekindSawtooth_sum_div` ([88, Rademacher and Grosswald (1972), Lemma 1]): summing the sawtooth
over a full residue system recovers a single sawtooth,

```text
Σ_{λ mod k} ((λ + x)/k) = ((x)).
```

The second is the value at first argument `1`, `dedekindSum_one_left` ([88, Rademacher and Grosswald
(1972), Lemma 2]): `𝔰(1,k) = -1/4 + 1/(6k) + k/12`, which is a direct summation of `((μ/k))²`.

Write `z(μ,v) = μ/k + v/h`. Applying the distribution law to each of the two Dedekind sums turns
`S = 𝔰(h,k) + 𝔰(k,h)` into a single double sum over `μ mod k` and `v mod h`,

```text
S = Σ_μ Σ_v ((z)) · (((μ/k)) + ((v/h))).
```

The two sawtooth factors on the right may then be replaced by their affine parts `μ/k - 1/2` and
`v/h - 1/2`: the two differ only in the terms with `μ = 0` and with `v = 0`, and those corrections
are multiples of `Σ_v ((v/h))` and `Σ_μ ((μ/k))`, both zero by the distribution law at `x = 0`.
So `S = Σ_μ Σ_v ((z))·(z - 1)`, and expanding the square of the difference gives

```text
Σ_μ Σ_v (z - 1 - ((z)))² = S₁ - 2S + S₃,
```

with `S₁ = Σ_μ Σ_v (z - 1)²` and `S₃ = Σ_μ Σ_v ((z))²`. Each of the three sums is then elementary:

* `S₁` is a polynomial sum, `hk/6 + h/(6k) + k/(6h) + 1/2`.
* `S₃` is `𝔰(1,hk)`: as `(μ,v)` runs over its range, `hμ + kv` runs over a full residue system
  modulo `hk`, since `h` and `k` are coprime. This is `crt_sum`, the one place coprimality is
  used besides the next item.
* The left-hand side is `hk/4 + 3/4`. Here `z` is an integer only at `μ = v = 0` -- if `z` were
  the integer `1` then `k ∣ hμ`, so `μ = 0` and `v = h`, which is out of range -- so away from
  the origin `z - 1 - ((z)) = ⌊z⌋ - 1/2`, and `0 ≤ z < 2` forces `⌊z⌋ ∈ {0,1}` and the square to
  be `1/4`. At the origin the value is `1`, contributing the extra `3/4`.

Solving for `S` gives the law. The `hk` terms cancel between `S₁`, `S₃`, and the left-hand side,
which is what makes the answer a sum of reciprocals.

Two steps reorganize [88]'s bookkeeping without changing its content. Where the book suppresses
the `μ = 0` and `v = 0` summands and recombines them afterwards, they are carried here as the two
corrections above, each a multiple of a sawtooth sum over a full residue system and so zero. And
where the book expands the left-hand side and argues that a residual double sum of
`⌊z⌋(⌊z⌋ - 1)` vanishes, the summand is evaluated pointwise instead. Both versions rest on the
same observation, that `⌊z⌋ ∈ {0,1}` on the range of summation.

The file closes with the one special value the project needs, `𝔰(n, n²-1)`: reciprocity pairs it
with `𝔰(n²-1, n)`, which is `-𝔰(1,n)` because `n² - 1 ≡ -1 (mod n)` and `𝔰` is odd in its first
argument.

## Main declarations

- `dedekindSawtooth_sum_div`: the distribution law, [88, Rademacher and Grosswald (1972), Lemma 1].
- `dedekindSum_one_left`: `𝔰(1,k)` in closed form, [88, Rademacher and Grosswald (1972), Lemma 2].
- `dedekindSum_reciprocity`: the reciprocity law, [88, Rademacher and Grosswald (1972), Theorem 1].
- `dedekindSum_reciprocity_mul`: the same law cleared of denominators, [88, Rademacher and Grosswald
  (1972), equation (35)].
- `dedekindSum_reciprocity_signed`: the law for nonzero coprime integers of either sign, derived
  from `dedekindSum_reciprocity` and the sign identities for Dedekind sums.
- `dedekindSum_self_sq_sub_one`: `𝔰(n, n²-1)`, the value the principal family uses.

## References

- [88] H. Rademacher and E. Grosswald, "Dedekind Sums", Carus Mathematical Monographs 16,
  Mathematical Association of America, 1972, Chapter 2, Section A
- [86] H. Rademacher, "Zur Theorie der Dedekindschen Summen", Math. Z. 63:445--463, 1955,
  equation (3)
-/

namespace SIC

open Finset

/-! ### Elementary summation lemmas

Closed forms for the polynomial sums that the Dedekind-sum computations reduce to, over a range
and over an interval. These private helpers evaluate the polynomial terms in the distribution
law and reciprocity proof below. -/

/-- The closed form for the sum of the first `n` naturals. -/
private lemma sum_range_id_cast (n : ℕ) :
    ∑ i ∈ Finset.range n, (i : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The closed form for the sum of the first `n` squares. -/
private lemma sum_range_sq (n : ℕ) :
    ∑ i ∈ Finset.range n, (i : ℚ) ^ 2 = (n : ℚ) * ((n : ℚ) - 1) * (2 * (n : ℚ) - 1) / 6 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- A sum of a quadratic function over `range k`, in closed form. -/
private lemma sum_range_quadratic (k : ℕ) (A B C : ℚ) :
    ∑ i ∈ Finset.range k, (A * (i : ℚ) ^ 2 + B * (i : ℚ) + C) =
      A * ((k : ℚ) * ((k : ℚ) - 1) * (2 * (k : ℚ) - 1) / 6) + B * ((k : ℚ) * ((k : ℚ) - 1) / 2) +
        C * (k : ℚ) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_range_sq, sum_range_id_cast, Finset.sum_const, Finset.card_range]
  ring

/-- A sum of a quadratic function over `Ico a b`, in closed form. -/
private lemma sum_Ico_quadratic (a b : ℕ) (hab : a ≤ b) (A B C : ℚ) :
    ∑ r ∈ Finset.Ico a b, (A * (r : ℚ) ^ 2 + B * (r : ℚ) + C) =
      A * (∑ i ∈ Finset.range b, (i : ℚ) ^ 2 - ∑ i ∈ Finset.range a, (i : ℚ) ^ 2) +
        B * (∑ i ∈ Finset.range b, (i : ℚ) - ∑ i ∈ Finset.range a, (i : ℚ)) +
        C * ((b : ℚ) - (a : ℚ)) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_Ico_eq_sub (fun i => (i : ℚ) ^ 2) hab, Finset.sum_Ico_eq_sub (fun i => (i : ℚ)) hab,
    Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hab]
  ring

/-! ### Shifting a sum over a full residue range

A function on `ℤ` with period `k` has the same sum over `{0, …, k-1}` as over any translate of
that range. This is what lets the distribution law below be reduced to the case `0 ≤ x < 1`. -/

section Shift

variable (k : ℕ) (g : ℤ → ℚ)

/-- One-step form of `sum_range_shift_of_periodic`: for a function of period `k`, adding `1` to
the argument permutes the range `{0, …, k-1}` cyclically. -/
private lemma sum_range_succ_shift_of_periodic (hg : ∀ n : ℤ, g (n + k) = g n) :
    ∑ i ∈ range k, g ((i : ℤ) + 1) = ∑ i ∈ range k, g (i : ℤ) := by
  have h1 : ∑ i ∈ range (k + 1), g (i : ℤ) = ∑ i ∈ range k, g ((i : ℤ) + 1) + g 0 := by
    rw [Finset.sum_range_succ' (fun i => g (i : ℤ)) k]
    push_cast
    ring_nf
  have h2 : ∑ i ∈ range (k + 1), g (i : ℤ) = ∑ i ∈ range k, g (i : ℤ) + g (k : ℤ) := by
    rw [Finset.sum_range_succ]
  rw [show g (k : ℤ) = g 0 by simpa using hg 0, h1] at h2
  exact add_right_cancel h2

/-- A function of period `k` sums to the same value over `{0, …, k-1}` and over any translate
`{m, …, m+k-1}` of it. Used by `dedekindSawtooth_sum_div`. -/
private lemma sum_range_shift_of_periodic (hg : ∀ n : ℤ, g (n + k) = g n) (m : ℤ) :
    ∑ i ∈ range k, g ((i : ℤ) + m) = ∑ i ∈ range k, g (i : ℤ) := by
  induction m using Int.induction_on with
  | zero => simp
  | succ j ih =>
      have key := sum_range_succ_shift_of_periodic k (fun n => g (n + j))
        (fun n => by simpa [add_right_comm] using hg (n + j))
      calc ∑ i ∈ range k, g ((i : ℤ) + (j + 1))
          = ∑ i ∈ range k, g ((i : ℤ) + 1 + j) := by
            refine Finset.sum_congr rfl fun i _ => ?_; ring_nf
        _ = ∑ i ∈ range k, g ((i : ℤ) + j) := key
        _ = ∑ i ∈ range k, g (i : ℤ) := ih
  | pred j ih =>
      have key := sum_range_succ_shift_of_periodic k (fun n => g (n + (-j - 1)))
        (fun n => by simpa [add_right_comm] using hg (n + (-j - 1)))
      calc ∑ i ∈ range k, g ((i : ℤ) + (-j - 1))
          = ∑ i ∈ range k, g ((i : ℤ) + 1 + (-j - 1)) := key.symm
        _ = ∑ i ∈ range k, g ((i : ℤ) + -j) := by
            refine Finset.sum_congr rfl fun i _ => ?_; ring_nf
        _ = ∑ i ∈ range k, g (i : ℤ) := ih

end Shift

/-! ### The distribution law

[88, Rademacher and Grosswald (1972), Lemma 1]: the sawtooth summed over a full residue system is
again a sawtooth. Proved first for `0 ≤ x < 1`, where every argument `(i+x)/k` lies in `[0,1)` and
the sum is a polynomial one, then in general by translating `x` into that range with
`sum_range_shift_of_periodic`. -/

/-- The sawtooth of a proper fraction of naturals. The `j = 0` case of
`dedekindSawtooth_natCast_div_of_bounds`. -/
private lemma dedekindSawtooth_natCast_div_natCast {k i : ℕ} (hi0 : 0 < i) (hik : i < k) :
    dedekindSawtooth ((i : ℚ) / (k : ℚ)) = (i : ℚ) / (k : ℚ) - 1 / 2 := by
  simpa using dedekindSawtooth_natCast_div_of_bounds (a := i) (b := k) (j := 0)
    (hi0.trans hik) (by omega) (by omega) (by omega)

/-- The case `x = 0` of `dedekindSawtooth_sum_div`, and the fact the argument uses most often:
the sawtooth sums to zero over a full residue system. -/
private lemma dedekindSawtooth_sum_range_div_self (k : ℕ) (hk : 0 < k) :
    ∑ i ∈ range k, dedekindSawtooth ((i : ℚ) / (k : ℚ)) = 0 := by
  have hkQ : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hk]
  have h0 : dedekindSawtooth (((0 : ℕ) : ℚ) / (k : ℚ)) = 0 := by simp [dedekindSawtooth]
  have hstep : ∑ i ∈ Finset.Ico 1 k, dedekindSawtooth ((i : ℚ) / (k : ℚ)) =
      ∑ i ∈ Finset.Ico 1 k, ((0 : ℚ) * (i : ℚ) ^ 2 + (1 / (k : ℚ)) * (i : ℚ) + (-(1 / 2))) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.mp hi
    rw [dedekindSawtooth_natCast_div_natCast hi1 hi2]
    ring
  rw [h0, zero_add, hstep, sum_Ico_quadratic 1 k hk]
  simp only [sum_range_sq, sum_range_id_cast]
  push_cast
  field_simp
  ring

/-- The case `0 < x < 1` of `dedekindSawtooth_sum_div`: every argument `(i+x)/k` then lies
strictly inside `(0,1)`, so each sawtooth is the argument itself less `1/2`. -/
private lemma dedekindSawtooth_sum_div_of_pos_of_lt_one (k : ℕ) (hk : 0 < k) {x : ℚ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    ∑ i ∈ range k, dedekindSawtooth (((i : ℚ) + x) / (k : ℚ)) = dedekindSawtooth x := by
  have hkQ : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  have hstep : ∑ i ∈ range k, dedekindSawtooth (((i : ℚ) + x) / (k : ℚ)) =
      ∑ i ∈ range k, ((0 : ℚ) * (i : ℚ) ^ 2 + (1 / (k : ℚ)) * (i : ℚ) + (x / (k : ℚ) - 1 / 2)) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi0 : (0 : ℚ) ≤ (i : ℚ) := by positivity
    have hib1 : (i : ℚ) + 1 ≤ (k : ℚ) := by
      exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    have hz0 : 0 < ((i : ℚ) + x) / (k : ℚ) := div_pos (by linarith) hkQ
    have hf : Int.fract (((i : ℚ) + x) / (k : ℚ)) = ((i : ℚ) + x) / (k : ℚ) :=
      Int.fract_eq_self.mpr ⟨hz0.le, (div_lt_one hkQ).mpr (by linarith)⟩
    rw [dedekindSawtooth_of_fract_ne_zero (by rw [hf]; exact hz0.ne'), hf]
    ring
  have hxf : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx0.le, hx1⟩
  rw [hstep, sum_range_quadratic,
    dedekindSawtooth_of_fract_ne_zero (by rw [hxf]; exact hx0.ne'), hxf]
  field_simp
  ring

/-- **The distribution law for the sawtooth.** For `k > 0` and any rational `x`,

```text
Σ_{λ mod k} ((λ + x)/k) = ((x)).
```

See [88, Rademacher and Grosswald (1972), Lemma 1, p. 4]. -/
@[source "88, Lemma 1, p. 4"]
lemma dedekindSawtooth_sum_div (k : ℕ) (hk : 0 < k) (x : ℚ) :
    ∑ i ∈ range k, dedekindSawtooth (((i : ℚ) + x) / (k : ℚ)) = dedekindSawtooth x := by
  have hkQ : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  set y : ℚ := Int.fract x with hy
  set m : ℤ := ⌊x⌋ with hm
  have hsaw : dedekindSawtooth y = dedekindSawtooth x := by
    have h := dedekindSawtooth_add_intCast x (-m)
    rw [show x + ((-m : ℤ) : ℚ) = y by rw [hy, Int.fract]; push_cast; ring] at h
    exact h
  set g : ℤ → ℚ := fun n => dedekindSawtooth (((n : ℚ) + y) / (k : ℚ)) with hg
  have hgper : ∀ n : ℤ, g (n + k) = g n := by
    intro n
    change dedekindSawtooth ((((n + k : ℤ) : ℚ) + y) / (k : ℚ)) = _
    rw [show (((n + k : ℤ) : ℚ) + y) / (k : ℚ) = ((n : ℚ) + y) / (k : ℚ) + ((1 : ℤ) : ℚ) by
      push_cast; field_simp; ring]
    exact dedekindSawtooth_add_intCast _ 1
  have hlhs : ∑ i ∈ range k, dedekindSawtooth (((i : ℚ) + x) / (k : ℚ)) =
      ∑ i ∈ range k, g ((i : ℤ) + m) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    change _ = dedekindSawtooth (((((i : ℤ) + m : ℤ)) + y : ℚ) / (k : ℚ))
    congr 2
    rw [hy, Int.fract]
    push_cast
    ring
  rw [hlhs, sum_range_shift_of_periodic k g hgper m, ← hsaw]
  rcases eq_or_lt_of_le (Int.fract_nonneg x) with h | h
  · have hy0 : y = 0 := by rw [hy]; exact h.symm
    rw [hy0]
    have hz : ∑ i ∈ range k, g (i : ℤ) =
        ∑ i ∈ range k, dedekindSawtooth ((i : ℚ) / (k : ℚ)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      change dedekindSawtooth ((((i : ℕ) : ℚ) + y) / (k : ℚ)) = _
      rw [hy0, add_zero]
    rw [hz, dedekindSawtooth_sum_range_div_self k hk,
      dedekindSawtooth_of_den_eq_one (by norm_num)]
  · have hz : ∑ i ∈ range k, g (i : ℤ) =
        ∑ i ∈ range k, dedekindSawtooth (((i : ℚ) + y) / (k : ℚ)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      change dedekindSawtooth ((((i : ℕ) : ℚ) + y) / (k : ℚ)) = _
      norm_num
    rw [hz]
    exact dedekindSawtooth_sum_div_of_pos_of_lt_one k hk h (Int.fract_lt_one x)

/-! ### The Dedekind sum at first argument `1`

[88, Rademacher and Grosswald (1972), Lemma 2]: `𝔰(1,k)` is the sum of `((μ/k))²`, hence a
polynomial sum. Both the reciprocity proof's `S₃` and its final arithmetic use this value. -/

/-- The `a = 1` case of `dedekindSum_eq_sum_range`, in which the two sawtooth factors coincide. -/
private lemma dedekindSum_one_eq_sum_range (n : ℕ) (hn0 : 0 < n) :
    dedekindSum 1 (n : ℤ) = ∑ r ∈ range n, dedekindSawtooth ((r : ℚ) / (n : ℚ)) ^ 2 := by
  rw [dedekindSum_eq_sum_range 1 n hn0]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [show (r : ℚ) * ((1 : ℤ) : ℚ) / (n : ℚ) = (r : ℚ) / (n : ℚ) by push_cast; ring]
  ring

/-- **The Dedekind sum at first argument `1`**: for `k > 0`,

```text
𝔰(1,k) = -1/4 + 1/(6k) + k/12.
```

See [88, Rademacher and Grosswald (1972), Lemma 2, eq. (5), p. 5]. -/
@[source "88, Lemma 2, p. 5"]
lemma dedekindSum_one_left (n : ℕ) (hn0 : 0 < n) :
    dedekindSum 1 (n : ℤ) = -1 / 4 + 1 / (6 * (n : ℚ)) + (n : ℚ) / 12 := by
  have hnQ : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn0
  rw [dedekindSum_eq_sum_Ico]
  have hstep : ∑ r ∈ Finset.Ico 1 n,
      dedekindSawtooth ((r : ℚ) / (n : ℚ)) * dedekindSawtooth ((r : ℚ) * ((1 : ℤ) : ℚ) / (n : ℚ)) =
      ∑ r ∈ Finset.Ico 1 n,
        ((1 / (n : ℚ) ^ 2) * (r : ℚ) ^ 2 + (-(1 / (n : ℚ))) * (r : ℚ) + 1 / 4) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    obtain ⟨hr1, hr2⟩ := Finset.mem_Ico.mp hr
    rw [show (r : ℚ) * ((1 : ℤ) : ℚ) / (n : ℚ) = (r : ℚ) / (n : ℚ) by push_cast; ring,
      dedekindSawtooth_natCast_div_natCast hr1 hr2]
    field_simp
    ring
  rw [hstep, sum_Ico_quadratic 1 n hn0]
  simp only [sum_range_sq, sum_range_id_cast]
  push_cast
  field_simp
  ring

/-! ### The lattice reindexing

Coprimality of `h` and `k` enters exactly here: as `μ` runs modulo `k` and `v` modulo `h`, the
combination `hμ + kv` runs over a full residue system modulo `hk`. Since `μ/k + v/h` is
`(hμ + kv)/(hk)`, any function of period `1` therefore has the same double sum over the two
ranges as its single sum over `{0, …, hk-1}`. -/

/-- Reindexing a double sum over `{0,…,k-1} × {0,…,h-1}` as a single sum over `{0,…,hk-1}`, for a
function `F` of period `1`. The map `(μ,v) ↦ (hμ + kv) mod hk` is injective on the product by
coprimality, hence bijective onto `{0,…,hk-1}` for cardinality reasons. -/
private lemma crt_sum {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hcop : Nat.Coprime h k)
    (F : ℚ → ℚ) (hF : ∀ (x : ℚ) (n : ℤ), F (x + (n : ℚ)) = F x) :
    ∑ ρ ∈ range (h * k), F ((ρ : ℚ) / ((h : ℚ) * (k : ℚ))) =
      ∑ μ ∈ range k, ∑ v ∈ range h, F ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ)) := by
  classical
  have hhk : 0 < h * k := Nat.mul_pos hh hk
  have hhQ : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  set φ : ℕ × ℕ → ℕ := fun p => (h * p.1 + k * p.2) % (h * k) with hφ
  have hinj : Set.InjOn φ ↑(range k ×ˢ range h) := by
    rintro ⟨μ₁, v₁⟩ hp₁ ⟨μ₂, v₂⟩ hp₂ heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hp₁ hp₂
    obtain ⟨hμ₁, hv₁⟩ := hp₁
    obtain ⟨hμ₂, hv₂⟩ := hp₂
    have hmod : Nat.ModEq (h * k) (h * μ₁ + k * v₁) (h * μ₂ + k * v₂) := heq
    have hdvd : ((h * k : ℕ) : ℤ) ∣ ((h * μ₂ + k * v₂ : ℕ) : ℤ) - ((h * μ₁ + k * v₁ : ℕ) : ℤ) :=
      Nat.modEq_iff_dvd.mp hmod
    push_cast at hdvd
    have hcopZ : IsCoprime (k : ℤ) (h : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
    have hd2 : (k : ℤ) ∣ (h : ℤ) * ((μ₂ : ℤ) - (μ₁ : ℤ)) + (k : ℤ) * ((v₂ : ℤ) - (v₁ : ℤ)) := by
      have hd := (Dvd.intro_left (h : ℤ) rfl : (k : ℤ) ∣ (h : ℤ) * (k : ℤ)).trans hdvd
      rwa [show (h : ℤ) * (μ₂ : ℤ) + (k : ℤ) * (v₂ : ℤ) -
        ((h : ℤ) * (μ₁ : ℤ) + (k : ℤ) * (v₁ : ℤ)) =
        (h : ℤ) * ((μ₂ : ℤ) - (μ₁ : ℤ)) + (k : ℤ) * ((v₂ : ℤ) - (v₁ : ℤ)) by ring] at hd
    have hkA : (k : ℤ) ∣ (h : ℤ) * ((μ₂ : ℤ) - (μ₁ : ℤ)) := by
      simpa using dvd_sub hd2 (Dvd.intro ((v₂ : ℤ) - (v₁ : ℤ)) rfl)
    have hμ₁Z : (μ₁ : ℤ) < (k : ℤ) := by exact_mod_cast hμ₁
    have hμ₂Z : (μ₂ : ℤ) < (k : ℤ) := by exact_mod_cast hμ₂
    have hA : (μ₂ : ℤ) - (μ₁ : ℤ) = 0 :=
      Int.eq_zero_of_abs_lt_dvd (hcopZ.dvd_of_dvd_mul_left hkA) (by rw [abs_lt]; omega)
    have hμeq : μ₁ = μ₂ := by omega
    subst hμeq
    have hkB : ((k : ℤ) * (h : ℤ)) ∣ (k : ℤ) * ((v₂ : ℤ) - (v₁ : ℤ)) := by
      rw [show (h : ℤ) * (μ₁ : ℤ) + (k : ℤ) * (v₂ : ℤ) -
        ((h : ℤ) * (μ₁ : ℤ) + (k : ℤ) * (v₁ : ℤ)) = (k : ℤ) * ((v₂ : ℤ) - (v₁ : ℤ)) by ring,
        mul_comm (h : ℤ) (k : ℤ)] at hdvd
      exact hdvd
    have hv₁Z : (v₁ : ℤ) < (h : ℤ) := by exact_mod_cast hv₁
    have hv₂Z : (v₂ : ℤ) < (h : ℤ) := by exact_mod_cast hv₂
    have hB : (v₂ : ℤ) - (v₁ : ℤ) = 0 :=
      Int.eq_zero_of_abs_lt_dvd
        ((mul_dvd_mul_iff_left (show (k : ℤ) ≠ 0 by exact_mod_cast hk.ne')).mp hkB)
        (by rw [abs_lt]; omega)
    have hveq : v₁ = v₂ := by omega
    subst hveq
    rfl
  have hsub : Finset.image φ (range k ×ˢ range h) ⊆ range (h * k) := by
    intro x hx
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (Nat.mod_lt _ hhk)
  have hcard : (range (h * k)).card ≤ (Finset.image φ (range k ×ˢ range h)).card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range,
      Finset.card_range, Finset.card_range]
    exact le_of_eq (Nat.mul_comm h k)
  rw [← Finset.eq_of_subset_of_card_le hsub hcard, Finset.sum_image hinj, Finset.sum_product]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun v _ => ?_
  set q : ℕ := (h * μ + k * v) / (h * k) with hq
  have hmd : φ (μ, v) + (h * k) * q = h * μ + k * v := Nat.mod_add_div _ _
  have hcastQ : ((φ (μ, v) : ℕ) : ℚ) =
      (h : ℚ) * (μ : ℚ) + (k : ℚ) * (v : ℚ) - (h : ℚ) * (k : ℚ) * (q : ℚ) := by
    have hc := congrArg (fun n : ℕ => (n : ℚ)) hmd
    simp only [Nat.cast_add, Nat.cast_mul] at hc
    linarith
  rw [hcastQ, show ((h : ℚ) * (μ : ℚ) + (k : ℚ) * (v : ℚ) - (h : ℚ) * (k : ℚ) * (q : ℚ)) /
      ((h : ℚ) * (k : ℚ)) = ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ)) + ((-(q : ℤ) : ℤ) : ℚ) by
    push_cast
    field_simp
    ring, hF]

/-! ### The three sums

With `z(μ,v) = μ/k + v/h` over `μ < k` and `v < h`, the proof needs `Σ (z-1)²`, `Σ ((z))²`, and
`Σ (z - 1 - ((z)))²`. The first is a polynomial sum, the second is `𝔰(1,hk)` by the lattice
reindexing, and the third is constant off the origin. -/

section Sums

variable {h k : ℕ}

/-- Away from `μ = v = 0`, the point `z = μ/k + v/h` is not an integer. If it were, then
`0 < z < 2` forces `z = 1`, so `k ∣ hμ`, hence `μ = 0` by coprimality and `v = h`, contradicting
`v < h`. -/
private lemma lattice_fract_ne_zero {μ v : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hcop : Nat.Coprime h k) (hμ : μ < k) (hv : v < h) (hne : ¬(μ = 0 ∧ v = 0)) :
    Int.fract ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ)) ≠ 0 := by
  have hhQ : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  intro hfr
  obtain ⟨n, hn⟩ := Int.fract_eq_zero_iff.mp hfr
  have hZ : (h : ℤ) * (μ : ℤ) + (k : ℤ) * (v : ℤ) = n * ((h : ℤ) * (k : ℤ)) := by
    have hQ : (h : ℚ) * (μ : ℚ) + (k : ℚ) * (v : ℚ) = (n : ℚ) * ((h : ℚ) * (k : ℚ)) := by
      field_simp at hn
      linarith [hn]
    exact_mod_cast hQ
  have hhZ : (0 : ℤ) < (h : ℤ) := by exact_mod_cast hh
  have hkZ : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have hμZ : (μ : ℤ) < (k : ℤ) := by exact_mod_cast hμ
  have hvZ : (v : ℤ) < (h : ℤ) := by exact_mod_cast hv
  have hμ0 : (0 : ℤ) ≤ (μ : ℤ) := Int.natCast_nonneg μ
  have hv0 : (0 : ℤ) ≤ (v : ℤ) := Int.natCast_nonneg v
  have hpos : 0 < (h : ℤ) * (μ : ℤ) + (k : ℤ) * (v : ℤ) := by
    rcases Nat.eq_zero_or_pos μ with rfl | hμp
    · have hvp : (0 : ℤ) < (v : ℤ) := by exact_mod_cast (by omega : 0 < v)
      positivity
    · have : (0 : ℤ) < (μ : ℤ) := by exact_mod_cast hμp
      nlinarith
  have hlt : (h : ℤ) * (μ : ℤ) + (k : ℤ) * (v : ℤ) < 2 * ((h : ℤ) * (k : ℤ)) := by nlinarith
  have hn1 : n = 1 := by nlinarith
  rw [hn1, one_mul] at hZ
  have hdvd : (k : ℤ) ∣ (h : ℤ) * (μ : ℤ) := ⟨(h : ℤ) - (v : ℤ), by linarith [hZ]⟩
  have hcopZ : IsCoprime (k : ℤ) (h : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  have hμ0' : (μ : ℤ) = 0 :=
    Int.eq_zero_of_abs_lt_dvd (hcopZ.dvd_of_dvd_mul_left hdvd) (by rw [abs_lt]; omega)
  have hvh : (v : ℤ) = (h : ℤ) :=
    mul_left_cancel₀ hkZ.ne' (by rw [hμ0'] at hZ; linarith : (k : ℤ) * (v : ℤ) = (k : ℤ) * (h : ℤ))
  omega

/-- Away from `μ = v = 0`, the summand of the `T`-sum is `1/4`: with `z = μ/k + v/h` not an
integer, `z - 1 - ((z)) = ⌊z⌋ - 1/2`, and `0 ≤ z < 2` leaves `⌊z⌋ ∈ {0,1}`. -/
private lemma lattice_sub_sawtooth_sq {μ v : ℕ} (hh : 0 < h) (hk : 0 < k)
    (hcop : Nat.Coprime h k) (hμ : μ < k) (hv : v < h) (hne : ¬(μ = 0 ∧ v = 0)) :
    ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ) - 1 -
      dedekindSawtooth ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ))) ^ 2 = 1 / 4 := by
  have hhQ : (0 : ℚ) < (h : ℚ) := by exact_mod_cast hh
  have hkQ : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  have hμQ : (μ : ℚ) < (k : ℚ) := by exact_mod_cast hμ
  have hvQ : (v : ℚ) < (h : ℚ) := by exact_mod_cast hv
  set z : ℚ := (μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ) with hzdef
  have hz0 : 0 ≤ z := by rw [hzdef]; positivity
  have hz2 : z < 2 := by
    have h1 : (μ : ℚ) / (k : ℚ) < 1 := (div_lt_one hkQ).mpr hμQ
    have h2 : (v : ℚ) / (h : ℚ) < 1 := (div_lt_one hhQ).mpr hvQ
    rw [hzdef]; linarith
  rw [dedekindSawtooth_of_fract_ne_zero (lattice_fract_ne_zero hh hk hcop hμ hv hne), Int.fract]
  have hfl0 : 0 ≤ ⌊z⌋ := Int.floor_nonneg.mpr hz0
  have hfl2 : ⌊z⌋ < 2 := Int.floor_lt.mpr (by exact_mod_cast hz2)
  have hfl : ⌊z⌋ = 0 ∨ ⌊z⌋ = 1 := by omega
  rcases hfl with h1 | h1 <;> rw [h1, hzdef] <;> push_cast <;> ring

/-- The `T`-sum `Σ_μ Σ_v (z - 1 - ((z)))²`, which equals `hk/4 + 3/4`: every summand is `1/4`
except the one at the origin, where `z = 0` and the summand is `1`. -/
private lemma reciprocity_sumT (hh : 0 < h) (hk : 0 < k) (hcop : Nat.Coprime h k) :
    ∑ μ ∈ range k, ∑ v ∈ range h,
        ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ) - 1 -
          dedekindSawtooth ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ))) ^ 2 =
      (h : ℚ) * (k : ℚ) / 4 + 3 / 4 := by
  have hpt : ∀ μ ∈ range k,
      ∑ v ∈ range h, ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ) - 1 -
          dedekindSawtooth ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ))) ^ 2 =
        (h : ℚ) / 4 + (if μ = 0 then 3 / 4 else 0) := by
    intro μ hμ
    have hμk : μ < k := Finset.mem_range.mp hμ
    rcases eq_or_ne μ 0 with rfl | hμ0
    · rw [ite_eq_left rfl, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hh]
      have h00 : (((0 : ℕ) : ℚ) / (k : ℚ) + ((0 : ℕ) : ℚ) / (h : ℚ) - 1 -
          dedekindSawtooth (((0 : ℕ) : ℚ) / (k : ℚ) + ((0 : ℕ) : ℚ) / (h : ℚ))) ^ 2 = 1 := by
        norm_num [dedekindSawtooth]
      have hrest : ∑ v ∈ Finset.Ico 1 h, (((0 : ℕ) : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ) - 1 -
          dedekindSawtooth (((0 : ℕ) : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ))) ^ 2 =
          ((h : ℚ) - 1) / 4 := by
        rw [Finset.sum_congr rfl (fun v hv => lattice_sub_sawtooth_sq hh hk hcop hμk
            (Finset.mem_Ico.mp hv).2 (by have h1v := (Finset.mem_Ico.mp hv).1; omega)),
          Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hh]
        push_cast
        ring
      rw [h00, hrest]
      ring
    · rw [ite_eq_right hμ0,
        Finset.sum_congr rfl (fun v hv => lattice_sub_sawtooth_sq hh hk hcop hμk
          (Finset.mem_range.mp hv) (by simp [hμ0])),
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, Finset.sum_ite_eq' (range k) 0 (fun _ => (3 : ℚ) / 4),
    ite_eq_left (Finset.mem_range.mpr hk)]
  ring

/-- The `S₁`-sum `Σ_μ Σ_v (z - 1)²`, evaluated by two applications of `sum_range_quadratic`. -/
private lemma reciprocity_sumS1 (hh : 0 < h) (hk : 0 < k) :
    ∑ μ ∈ range k, ∑ v ∈ range h, ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ) - 1) ^ 2 =
      (h : ℚ) * (k : ℚ) / 6 + (h : ℚ) / (6 * (k : ℚ)) + (k : ℚ) / (6 * (h : ℚ)) + 1 / 2 := by
  have hhQ : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have inner : ∀ μ ∈ range k,
      ∑ v ∈ range h, ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ) - 1) ^ 2 =
        ((h : ℚ) / (k : ℚ) ^ 2) * (μ : ℚ) ^ 2 + (-(((h : ℚ) + 1) / (k : ℚ))) * (μ : ℚ) +
          (((h : ℚ) - 1) * (2 * (h : ℚ) - 1) / (6 * (h : ℚ)) + 1) := by
    intro μ _
    rw [show (∑ v ∈ range h, ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ) - 1) ^ 2) =
        ∑ v ∈ range h, ((1 / (h : ℚ) ^ 2) * (v : ℚ) ^ 2 +
          (2 * ((μ : ℚ) / (k : ℚ) - 1) / (h : ℚ)) * (v : ℚ) + ((μ : ℚ) / (k : ℚ) - 1) ^ 2)
      from Finset.sum_congr rfl fun v _ => by ring, sum_range_quadratic]
    field_simp
    ring
  rw [Finset.sum_congr rfl inner, sum_range_quadratic]
  field_simp
  ring

/-- The `S₃`-sum `Σ_μ Σ_v ((z))²`, which is `𝔰(1,hk)` by the lattice reindexing `crt_sum`. -/
private lemma reciprocity_sumS3 (hh : 0 < h) (hk : 0 < k) (hcop : Nat.Coprime h k) :
    ∑ μ ∈ range k, ∑ v ∈ range h,
        dedekindSawtooth ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ)) ^ 2 =
      -1 / 4 + 1 / (6 * ((h : ℚ) * (k : ℚ))) + (h : ℚ) * (k : ℚ) / 12 := by
  have hhk : 0 < h * k := Nat.mul_pos hh hk
  have hcrt := crt_sum hh hk hcop (fun z => dedekindSawtooth z ^ 2)
    (fun x n => by rw [dedekindSawtooth_add_intCast])
  rw [← hcrt, show ((h : ℚ) * (k : ℚ)) = ((h * k : ℕ) : ℚ) by push_cast; ring,
    ← dedekindSum_one_eq_sum_range (h * k) hhk, dedekindSum_one_left (h * k) hhk]

end Sums

/-! ### The reciprocity law

The double sum `Σ_μ Σ_v ((z))·(z-1)` is `𝔰(h,k) + 𝔰(k,h)`, and the expansion of
`Σ (z - 1 - ((z)))²` then determines it from the three sums above. -/

section Reciprocity

variable {h k : ℕ}

/-- `𝔰(h,k) + 𝔰(k,h)` as the double sum `Σ_μ Σ_v ((z))·(z-1)`, `z = μ/k + v/h`. The distribution
law turns each Dedekind sum into a double sum with one sawtooth factor `((μ/k))` or `((v/h))`;
those factors may then be replaced by `μ/k - 1/2` and `v/h - 1/2`, since the corrections at
`μ = 0` and at `v = 0` are multiples of sawtooth sums over full residue systems, hence zero. -/
private lemma reciprocity_sumS (hh : 0 < h) (hk : 0 < k) :
    dedekindSum (h : ℤ) (k : ℤ) + dedekindSum (k : ℤ) (h : ℤ) =
      ∑ μ ∈ range k, ∑ v ∈ range h,
        dedekindSawtooth ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ)) *
          ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ) - 1) := by
  have hhQ : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hfirst : dedekindSum (h : ℤ) (k : ℤ) =
      ∑ μ ∈ range k, ∑ v ∈ range h,
        dedekindSawtooth ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ)) *
          dedekindSawtooth ((μ : ℚ) / (k : ℚ)) := by
    rw [dedekindSum_eq_sum_range (h : ℤ) k hk]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [show (μ : ℚ) * (((h : ℕ) : ℤ) : ℚ) / (k : ℚ) = (μ : ℚ) * (h : ℚ) / (k : ℚ) by
        push_cast; ring,
      ← dedekindSawtooth_sum_div h hh ((μ : ℚ) * (h : ℚ) / (k : ℚ)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [show ((v : ℚ) + (μ : ℚ) * (h : ℚ) / (k : ℚ)) / (h : ℚ) =
      (μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ) by field_simp; ring]
    ring
  have hsecond : dedekindSum (k : ℤ) (h : ℤ) =
      ∑ μ ∈ range k, ∑ v ∈ range h,
        dedekindSawtooth ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ)) *
          dedekindSawtooth ((v : ℚ) / (h : ℚ)) := by
    rw [dedekindSum_eq_sum_range (k : ℤ) h hh, Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [show (v : ℚ) * (((k : ℕ) : ℤ) : ℚ) / (h : ℚ) = (v : ℚ) * (k : ℚ) / (h : ℚ) by
        push_cast; ring,
      ← dedekindSawtooth_sum_div k hk ((v : ℚ) * (k : ℚ) / (h : ℚ)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [show ((μ : ℚ) + (v : ℚ) * (k : ℚ) / (h : ℚ)) / (k : ℚ) =
      (μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ) by field_simp]
    ring
  have hE1 : ∀ μ ∈ range k,
      ∑ v ∈ range h, dedekindSawtooth ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ)) *
          dedekindSawtooth ((μ : ℚ) / (k : ℚ)) =
        ∑ v ∈ range h, dedekindSawtooth ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ)) *
          ((μ : ℚ) / (k : ℚ) - 1 / 2) := by
    intro μ hμ
    rcases eq_or_ne μ 0 with rfl | hμ0
    · rw [show dedekindSawtooth (((0 : ℕ) : ℚ) / (k : ℚ)) = 0 by simp [dedekindSawtooth],
        ← Finset.sum_mul, ← Finset.sum_mul,
        show ∑ v ∈ range h, dedekindSawtooth (((0 : ℕ) : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ)) =
          ∑ v ∈ range h, dedekindSawtooth ((v : ℚ) / (h : ℚ)) from
            Finset.sum_congr rfl fun v _ => by norm_num,
        dedekindSawtooth_sum_range_div_self h hh]
      ring
    · rw [dedekindSawtooth_natCast_div_natCast (Nat.pos_of_ne_zero hμ0) (Finset.mem_range.mp hμ)]
  have hE2 : ∑ μ ∈ range k, ∑ v ∈ range h,
        dedekindSawtooth ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ)) *
          dedekindSawtooth ((v : ℚ) / (h : ℚ)) =
      ∑ μ ∈ range k, ∑ v ∈ range h,
        dedekindSawtooth ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ)) * ((v : ℚ) / (h : ℚ) - 1 / 2) := by
    have hinner : ∀ μ ∈ range k,
        ∑ v ∈ range h, dedekindSawtooth ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ)) *
            dedekindSawtooth ((v : ℚ) / (h : ℚ)) =
          (∑ v ∈ range h, dedekindSawtooth ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ)) *
            ((v : ℚ) / (h : ℚ) - 1 / 2)) + dedekindSawtooth ((μ : ℚ) / (k : ℚ)) * (1 / 2) := by
      intro μ _
      have hIco : ∑ v ∈ Finset.Ico 1 h,
            dedekindSawtooth ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ)) *
              dedekindSawtooth ((v : ℚ) / (h : ℚ)) =
          ∑ v ∈ Finset.Ico 1 h, dedekindSawtooth ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ)) *
            ((v : ℚ) / (h : ℚ) - 1 / 2) :=
        Finset.sum_congr rfl fun v hv => by
          rw [dedekindSawtooth_natCast_div_natCast (Finset.mem_Ico.mp hv).1
            (Finset.mem_Ico.mp hv).2]
      simp only [Finset.range_eq_Ico]
      rw [Finset.sum_eq_sum_Ico_succ_bot hh, Finset.sum_eq_sum_Ico_succ_bot hh, hIco,
        show dedekindSawtooth (((0 : ℕ) : ℚ) / (h : ℚ)) = 0 by simp [dedekindSawtooth],
        show dedekindSawtooth ((μ : ℚ) / (k : ℚ) + ((0 : ℕ) : ℚ) / (h : ℚ)) =
          dedekindSawtooth ((μ : ℚ) / (k : ℚ)) by norm_num]
      push_cast
      ring
    rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, ← Finset.sum_mul,
      dedekindSawtooth_sum_range_div_self k hk, zero_mul, add_zero]
  rw [hfirst, hsecond, Finset.sum_congr rfl hE1, hE2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

/-- The reciprocity law for natural-number arguments; `dedekindSum_reciprocity` is the form the
project uses. -/
private lemma dedekindSum_reciprocity_nat (hh : 0 < h) (hk : 0 < k) (hcop : Nat.Coprime h k) :
    dedekindSum (h : ℤ) (k : ℤ) + dedekindSum (k : ℤ) (h : ℤ) =
      -1 / 4 + ((h : ℚ) / (k : ℚ) + (k : ℚ) / (h : ℚ) + 1 / ((h : ℚ) * (k : ℚ))) / 12 := by
  have hexp : ∑ μ ∈ range k, ∑ v ∈ range h,
        ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ) - 1 -
          dedekindSawtooth ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ))) ^ 2 =
      (∑ μ ∈ range k, ∑ v ∈ range h, ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ) - 1) ^ 2) -
        2 * (∑ μ ∈ range k, ∑ v ∈ range h,
          dedekindSawtooth ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ)) *
            ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ) - 1)) +
        ∑ μ ∈ range k, ∑ v ∈ range h,
          dedekindSawtooth ((μ : ℚ) / (k : ℚ) + (v : ℚ) / (h : ℚ)) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [reciprocity_sumS hh hk]
  linear_combination (hexp + reciprocity_sumS1 hh hk + reciprocity_sumS3 hh hk hcop -
    reciprocity_sumT hh hk hcop) / 2

end Reciprocity

/-- **Dedekind's reciprocity law.** For coprime positive integers `h` and `k`,

```text
𝔰(h,k) + 𝔰(k,h) = -1/4 + (h/k + k/h + 1/(hk))/12.
```

See [88, Rademacher and Grosswald (1972), Theorem 1, eq. (4), p. 4] and
[86, Rademacher (1955), eq. (3)]. The proof formalized here is the first of the four in
[88, Rademacher and Grosswald (1972), Chapter 2]; see the module docstring. -/
@[source "88, Theorem 1, p. 4" "86, equation (3), p. 445"]
theorem dedekindSum_reciprocity {h k : ℤ} (hh : 0 < h) (hk : 0 < k) (hcop : IsCoprime h k) :
    dedekindSum h k + dedekindSum k h =
      -1 / 4 + ((h : ℚ) / (k : ℚ) + (k : ℚ) / (h : ℚ) + 1 / ((h : ℚ) * (k : ℚ))) / 12 := by
  obtain ⟨H, rfl⟩ := Int.eq_ofNat_of_zero_le hh.le
  obtain ⟨K, rfl⟩ := Int.eq_ofNat_of_zero_le hk.le
  rw [dedekindSum_reciprocity_nat (by exact_mod_cast hh) (by exact_mod_cast hk)
    (Nat.isCoprime_iff_coprime.mp hcop)]
  push_cast
  ring

/-- **Reciprocity cleared of denominators.** For coprime positive integers `h` and `k`,

```text
12hk·𝔰(h,k) + 12hk·𝔰(k,h) = -3hk + h² + k² + 1.
```

See [88, Rademacher and Grosswald (1972), equation (35), p. 27], where it is derived from
`dedekindSum_reciprocity` exactly as here. This is the form the word walk uses, since it is
polynomial in the matrix entries. -/
@[source "88, equation (35), p. 27"]
lemma dedekindSum_reciprocity_mul {h k : ℤ} (hh : 0 < h) (hk : 0 < k) (hcop : IsCoprime h k) :
    12 * (h : ℚ) * (k : ℚ) * (dedekindSum h k + dedekindSum k h) =
      -3 * (h : ℚ) * (k : ℚ) + (h : ℚ) ^ 2 + (k : ℚ) ^ 2 + 1 := by
  have hhQ : (h : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hh.ne'
  have hkQ : (k : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hk.ne'
  rw [dedekindSum_reciprocity hh hk hcop]
  field_simp
  ring

/-- **Signed reciprocity.** For nonzero coprime integers `a` and `k` of either sign,
`12·sgn(k)·𝔰(a,k) + 12·sgn(a)·𝔰(k,a) = -3·sgn(ak) + a/k + k/a + 1/(ak)`.
This follows from `dedekindSum_reciprocity` by `dedekindSum_neg_left` and
`dedekindSum_neg_right`. See [88, Rademacher and Grosswald (1972), Chapter 2,
the reciprocity theorem]. -/
theorem dedekindSum_reciprocity_signed {a k : ℤ}
    (ha : a ≠ 0) (hk : k ≠ 0) (hcop : IsCoprime a k) :
    12 * (Int.sign k : ℚ) * dedekindSum a k +
      12 * (Int.sign a : ℚ) * dedekindSum k a =
      -3 * (Int.sign (a * k) : ℚ) +
      (a : ℚ) / (k : ℚ) + (k : ℚ) / (a : ℚ) + 1 / ((a : ℚ) * (k : ℚ)) := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · rcases lt_or_gt_of_ne hk with hk | hk
    · obtain ⟨A, rfl⟩ : ∃ A : ℤ, a = -A := ⟨-a, by ring⟩
      obtain ⟨K, rfl⟩ : ∃ K : ℤ, k = -K := ⟨-k, by ring⟩
      have hA : 0 < A := by omega
      have hK : 0 < K := by omega
      have hc : IsCoprime A K := by simpa only [neg_neg] using hcop.neg_left.neg_right
      have hrec := dedekindSum_reciprocity hA hK hc
      simp [Int.sign_mul, Int.sign_eq_one_of_pos hA, Int.sign_eq_one_of_pos hK,
        dedekindSum_neg_left, dedekindSum_neg_right] at *
      linear_combination 12 * hrec
    · obtain ⟨A, rfl⟩ : ∃ A : ℤ, a = -A := ⟨-a, by ring⟩
      have hA : 0 < A := by omega
      have hc : IsCoprime A k := by simpa only [neg_neg] using hcop.neg_left
      have hrec := dedekindSum_reciprocity hA hk hc
      simp [Int.sign_mul, Int.sign_eq_one_of_pos hA, Int.sign_eq_one_of_pos hk,
        dedekindSum_neg_left, dedekindSum_neg_right] at *
      linear_combination -12 * hrec
  · rcases lt_or_gt_of_ne hk with hk | hk
    · obtain ⟨K, rfl⟩ : ∃ K : ℤ, k = -K := ⟨-k, by ring⟩
      have hK : 0 < K := by omega
      have hc : IsCoprime a K := by simpa only [neg_neg] using hcop.neg_right
      have hrec := dedekindSum_reciprocity ha hK hc
      simp [Int.sign_mul, Int.sign_eq_one_of_pos ha, Int.sign_eq_one_of_pos hK,
        dedekindSum_neg_left, dedekindSum_neg_right] at *
      linear_combination -12 * hrec
    · have hrec := dedekindSum_reciprocity ha hk hcop
      simp [Int.sign_mul, Int.sign_eq_one_of_pos ha, Int.sign_eq_one_of_pos hk] at *
      linear_combination 12 * hrec

/-! ### A special value

`𝔰(n, n²-1)`, the Dedekind sum that the principal rank-one family's stabilizer computation needs.
It is the standard application of reciprocity together with the oddness and first-argument
periodicity of `𝔰`. -/

/-- The Dedekind sum `𝔰(n, n² - 1)` for `n ≥ 2`:

```text
𝔰(n, n²-1) = (n³ - 3n² + 3) / (6(n² - 1)).
```

Reciprocity ([88, Rademacher and Grosswald (1972), Theorem 1, p. 4]) applied to the coprime pair
`(n, n²-1)` pairs this with `𝔰(n²-1, n)`, which is `-𝔰(1,n)` since `n² - 1 ≡ -1 (mod n)` and `𝔰` is
odd in its first argument ([88, Rademacher and Grosswald (1972), equation (33a), p. 26]); `𝔰(1,n)`
is then `dedekindSum_one_left`. -/ lemma dedekindSum_self_sq_sub_one (n : ℕ) (hn : 2 ≤ n) :
    dedekindSum (n : ℤ) ((n * n - 1 : ℕ) : ℤ) =
      ((n : ℚ) ^ 3 - 3 * (n : ℚ) ^ 2 + 3) / (6 * ((n * n - 1 : ℕ) : ℚ)) := by
  have hnn : 2 ≤ n * n := by nlinarith
  have hnpos : 0 < n := by omega
  have hγpos : 0 < n * n - 1 := by omega
  have hnZ : (0 : ℤ) < ((n : ℕ) : ℤ) := by exact_mod_cast hnpos
  have hγZ : (0 : ℤ) < ((n * n - 1 : ℕ) : ℤ) := by exact_mod_cast hγpos
  have hcast : ((n * n - 1 : ℕ) : ℤ) = (n : ℤ) * (n : ℤ) - 1 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ n * n)]; ring
  have hcop : IsCoprime ((n : ℕ) : ℤ) ((n * n - 1 : ℕ) : ℤ) :=
    ⟨(n : ℤ), -1, by rw [hcast]; ring⟩
  have hrec := dedekindSum_reciprocity hnZ hγZ hcop
  rw [show dedekindSum ((n * n - 1 : ℕ) : ℤ) ((n : ℕ) : ℤ) =
      -dedekindSum 1 ((n : ℕ) : ℤ) by
        rw [show ((n * n - 1 : ℕ) : ℤ) = (-1 : ℤ) + (n : ℤ) * (n : ℤ) by rw [hcast]; ring,
          dedekindSum_add_mul_right, dedekindSum_neg_left],
    dedekindSum_one_left n hnpos] at hrec
  have hnQ : ((n : ℕ) : ℚ) ≠ 0 := by positivity
  have hγQ : ((n * n - 1 : ℕ) : ℚ) = (n : ℚ) ^ 2 - 1 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ n * n)]; ring
  have hγQ0 : (n : ℚ) ^ 2 - 1 ≠ 0 := by
    rw [← hγQ]
    exact_mod_cast Nat.cast_ne_zero.mpr hγpos.ne'
  push_cast at hrec
  rw [hγQ] at hrec ⊢
  have hS : dedekindSum ((n : ℕ) : ℤ) ((n * n - 1 : ℕ) : ℤ) =
      (-1 / 4 + ((n : ℚ) / ((n : ℚ) ^ 2 - 1) + ((n : ℚ) ^ 2 - 1) / (n : ℚ) +
          1 / ((n : ℚ) * ((n : ℚ) ^ 2 - 1))) / 12) +
        (-1 / 4 + 1 / (6 * (n : ℚ)) + (n : ℚ) / 12) := by
    linarith [hrec]
  rw [hS]
  field_simp
  ring

end SIC
