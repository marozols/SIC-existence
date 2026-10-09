/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Admissible.ShiftArithmetic
import SICs.Quantum.RootsOfUnity

/-!
# Arithmetic of the twist function

The function `f_t` of Definition 5.10, the parity of its values, and their coprimality to `d̄`.

For an admissible tuple `t = (d,r,Q) ∼ (K,j,m,Q)`, [AFK25, Definition 5.10, `dfn:functionht`]
introduces

`f_t : ℤ/dℤ → ℤ/d̄ℤ`,   `f_t(x) = r(2x + d + d_j - 1)`,

and [AFK25, Definition 1.41, `def:fiducialdata`] requires a fiducial datum's twist `G` to satisfy
`Det(G) r(2λ + d_j - 1 + d) ≡ 1 (mod d̄)` for some shift `λ`. Comparing the two says exactly that
`Det(G⁻¹) = f_t(λ)`, which is the substitution made in the idempotency computation of [AFK25, Lemma
1.42, `lem:GhostFiducialIndependenceOfTransversal`]. The compatibility interface is in
`SICs.Ghost.CompatibleTwists`; this file proves the parts of [AFK25, Lemma 5.11, `lem:fdf`] that
interface needs: a twist compatible with `λ` exists exactly when `f_t(λ)` is coprime to `d̄`, and
the last statement of the lemma reduces this to coprimality of `2λ + d_j - 1` with `d`.

## The argument

Modulo `d`, `f_t(x) ≡ r(2x + d_j - 1)`, and `r` is coprime to `d` because it divides `d² - 1` by
the Diophantine equation `n r (d - r) = d² - 1` of [AFK25, Definition 1.21, `dfn:admissiblePair`].
So `f_t(x)` is coprime to `d` exactly when `2x + d_j - 1` is. For odd `d` this is already
coprimality to `d̄ = d`. For even `d` we have `d̄ = 2d`, and `f_t(x)` is odd: `n` and `r` divide
the odd number `d² - 1`, so both are odd, `d_j = n - 1` is even, and `2x + d + d_j - 1` is odd.
Here `n = d_j + 1` by [AFK25, Theorem 4.20(B), `thm:nrddjmrjm`].

## Main definitions

- `SIC.twistFnInt`: the integer-indexed `f_t(x) = r(2x + d + d_j - 1)`.

## Main results

- `SIC.AdmissiblePair.odd_twistFnInt_of_even`, `SIC.AdmissiblePair.isCoprime_twistFnInt_iff`:
  [AFK25, Lemma 5.11, `lem:fdf`], the parity of the values in even dimensions and the coprimality
  criterion.

## Notational and structural differences from [AFK25]

The paper attaches `f_t` to an admissible tuple. The arithmetic here depends only on the bare data
`(d, r, d_j)`, so `twistFnInt` takes those arguments directly, and the results are proved for an
`AdmissiblePair` together with the hypothesis `d_j + 1 = n`. That hypothesis holds for every
associated tuple by [AFK25, Theorem 4.20(A)(2), `thm:nrddjmrjm`]. The function is evaluated at an
integer representative of its argument, and its values are integers rather than residues modulo
`d̄`. The quotient-valued arbitrary-rank compatibility predicate and its link to this arithmetic
are in `SICs.Ghost.CompatibleTwists`.

Of [AFK25, Lemma 5.11, `lem:fdf`], the bijectivity statements and the inverse formula are not
needed and are not formalized.

## References

- [AFK25] Appleby, Flammia, Kopp, arXiv:2501.03970v2, Definitions 1.21, 1.41, and 5.10,
  Theorem 4.20, Lemma 5.11
-/

noncomputable section

namespace SIC

/-! ### The function `f_t` of [AFK25, Definition 5.10, `dfn:functionht`]

The paper's `f_t` is defined on `ℤ/dℤ`; here it is the affine integer formula, evaluated at an
integer representative of its argument. -/

/-- The integer-indexed form of the function `f_t` of [AFK25, Definition 5.10, `dfn:functionht`]:

`f_t(x) = r(2x + d + d_j - 1)`. -/
def twistFnInt (d r dj : ℕ) (x : ℤ) : ℤ :=
  (r : ℤ) * (2 * x + (d : ℤ) + (dj : ℤ) - 1)

/-! ### Odd values of `f_t` [AFK25, Lemma 5.11, `lem:fdf`]

In even dimensions `r` and `n = d_j + 1` are odd, so every value `r(2x + d + d_j - 1)` is odd. -/

namespace AdmissiblePair

/-- [AFK25, Lemma 5.11, `lem:fdf`](2): in even dimensions every value of `f_t` is odd. -/
@[source "AFK25, Lemma 5.11, p. 81, lem:fdf (2, odd values)"]
theorem odd_twistFnInt_of_even (p : AdmissiblePair) (dj : ℕ) (hdj : dj + 1 = p.n)
    (hd : Even p.d) (x : ℤ) : Odd (twistFnInt p.d p.r dj x) := by
  have hn2 : (p.n : ℤ) % 2 = 1 := Int.odd_iff.mp (by exact_mod_cast p.odd_n_of_even_d hd)
  have hd2 : (p.d : ℤ) % 2 = 0 := Int.even_iff.mp (by exact_mod_cast hd)
  have hdjz : (dj : ℤ) + 1 = (p.n : ℤ) := by exact_mod_cast hdj
  refine Odd.mul (by exact_mod_cast p.odd_r_of_even_d hd) ?_
  rw [Int.odd_iff]
  omega

end AdmissiblePair

/-! ### The twist condition of [AFK25, Definition 1.41, `def:fiducialdata`]

Rewriting the determinant congruence as `Det(G) f_t(λ) ≡ 1` isolates the exact arithmetic needed
for compatibility. Coprimality then characterizes when a compatible quotient twist exists. -/

/-- Congruent integers are simultaneously coprime to the modulus. -/
private theorem isCoprime_of_modEq {a b n : ℤ} (h : a ≡ b [ZMOD n]) (hb : IsCoprime b n) :
    IsCoprime a n := by
  obtain ⟨u, v, huv⟩ := hb
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp h
  exact ⟨u, v + u * k, by linear_combination huv - u * hk⟩

/-- The last statement of [AFK25, Lemma 5.11, `lem:fdf`]: `f_t(x)` is coprime to `d̄` if and only if
`2x + d_j - 1` is coprime to `d`. -/
@[source "AFK25, Lemma 5.11, p. 81, lem:fdf (coprimality)"]
theorem AdmissiblePair.isCoprime_twistFnInt_iff (p : AdmissiblePair) (dj : ℕ) (hdj : dj + 1 = p.n)
    (x : ℤ) :
    IsCoprime (twistFnInt p.d p.r dj x) (dbar p.d : ℤ) ↔
      IsCoprime (2 * x + (dj : ℤ) - 1) (p.d : ℤ) := by
  have hmod : twistFnInt p.d p.r dj x ≡ (p.r : ℤ) * (2 * x + (dj : ℤ) - 1) [ZMOD (p.d : ℤ)] :=
    Int.modEq_iff_dvd.mpr ⟨-(p.r : ℤ), by simp only [twistFnInt]; ring⟩
  constructor
  · intro h
    have h1 : IsCoprime (twistFnInt p.d p.r dj x) (p.d : ℤ) :=
      h.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr (dvd_dbar p.d))
    exact (isCoprime_of_modEq hmod.symm h1).of_mul_left_right
  · intro h
    have hr : IsCoprime ((p.r : ℤ)) ((p.d : ℤ)) := Nat.isCoprime_iff_coprime.mpr p.coprime_r_d
    have h1 : IsCoprime (twistFnInt p.d p.r dj x) (p.d : ℤ) :=
      isCoprime_of_modEq hmod (hr.mul_left h)
    rcases Nat.even_or_odd p.d with hd | hd
    · obtain ⟨m, hm⟩ := p.odd_twistFnInt_of_even dj hdj hd x
      have h2 : IsCoprime (twistFnInt p.d p.r dj x) (2 : ℤ) := ⟨1, -m, by linarith⟩
      rw [dbar_of_even hd]
      push_cast
      exact h2.mul_right h1
    · rw [dbar_of_odd hd]
      exact h1

end SIC

end
