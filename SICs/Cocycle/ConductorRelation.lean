/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Cocycle.ConductorDistribution
import SICs.Cocycle.ConductorLowering

/-!
# The orbit conductor relation for matrices of positive determinant

For `B ∈ G_f` with `BC = AB`, the product of real cocycle values over a fibre of `B` is grouped
by the `C`-orbits of characteristic classes. The result extends [72, Kopp (2024), Theorem 4.46,
`thm:cllr`], whose classes are fixed and hence have orbit length one.

An orbit decomposition uses a finite transversal of the classes `s` with `Bs ≡ r`. The relation
requires an irrational fixed point `α` of `C` with `j_C(α) > 0`, and the orientation
`j_B(α) > 0` omitted from the source's statement.

## The orientation `j_B(α) > 0`

The source's statement has no condition on the sign of `j_B(α)`, and without one it is false.
`-B` acts on the upper half plane as `B` does and conjugates `C` to the same matrix, so the left
side is unchanged when `B` is replaced by `-B`, while the right side becomes the product over
`Bs ≡ -r`, that is, over the negated characteristics. For `B = -I ∈ G_1` the statement would read
`ש^r_C(α) = ש^{-r}_C(α)`, whereas the quotient of the two is `U^{(1)}(r)^{∓2}` at a reduced `α`
([72, Kopp (2024), Proposition 7.20, `prop:almost`], `SICs.Cocycle.FixedPointQuotient`), a positive
real that is generally not `1`. The source's proof applies [72, Kopp (2024), Theorem 4.37,
`thm:shinconj`] with `R = C₀⁻¹`, whose sign
`s_R(C₀·α) = sgn j_{C₀}(α) = sgn j_B(α)` it drops. That sign is positive precisely when
`j_B(α) > 0`.

## Mathematical argument

[72, Kopp (2024), Lemma 4.44, `lem:Gforbits`] (`exists_eq_upperTriangular_mul_of_mem_Gf`) writes
`B = UR` with `U = [[a,b],[0,d]]`, `a, d > 0`, and `R ∈ SL₂(ℤ)`. Then `j_B(α) = d·j_R(α)`, so
`j_R(α) > 0`. Put `α' = R·α` and `C' = RCR⁻¹`: `C'` fixes `α'` with `j_{C'}(α') = j_C(α)`, and
`UC' = AU` from `BC = AB`. Transport the orbit decomposition of the classes over `r` to the
upper-triangular factor set under `R`. The upper-triangular orbit relation
`sfModularCocycleRealTotal_eq_prod_orbits_upperTriangular` gives

$$ש^{\mathbf r}_A(B\cdot\alpha) = ש^{\mathbf r}_A(U\cdot\alpha')
  = \prod_{y\in R'} ש^y_{(C')^{m'(y)}}(\alpha'),$$

and [72, Kopp (2024), Theorem 4.37, `thm:shinconj`] (`sfModularCocycleRealTotal_mul_mul_inv`) at
`R`, with `j_R(α) > 0`, turns each orbit factor into the corresponding factor at `C^{m(y)}`.
The characteristics `s(j,ℓ)` represent each class over `r` for `U` once (`[0,a) × [0,d)` is a
fundamental domain for `Uℤ²`), so any transversal for `B = UR` transports to the same classes.
When every class is fixed by `C`, all orbit lengths are one, which is the case stated by Kopp.

## Main declarations

- `IsPreimageTransversal`: representatives of the classes `s` with `Bs ≡ r (mod ℤ²)`.
- `isPreimageTransversal_upperTriangular`, `IsPreimageTransversal.image_ratVecAction_inv`:
  construct and transport the transversals used by the proof.
- `sfModularCocycleReal'_conj_pow`: transports an orbit factor under a change of basis.
- `sfModularCocycleRealTotal_eq_prod_orbits_of_mem_Gf`: the orbit conductor relation.

## References

- [72] G. S. Kopp, "The Shintani--Faddeev modular cocycle: Stark units from q-Pochhammer
  ratios," arXiv:2411.06763v3, Lemma 4.44 (`lem:Gforbits`), Theorem 4.37 (`thm:shinconj`), and
  Theorem 4.46 (`thm:cllr`)
- [RW26b] D. Radchenko and C. Wheeler, "Stark units for real quadratic fields and reciprocity
  laws," 4 October 2026, Appendix A, proof of Proposition 3
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### Transversals of the classes over `r`

The product in [72, Kopp (2024), Theorem 4.46, `thm:cllr`] runs over the classes `s ∈ ℚ²/ℤ²`
with `Bs ≡ r`. A finite set containing exactly one representative of each such class stands in for
that index set; any function of `s` that is constant on these classes has the same product over
every such set. -/

/-- **A transversal of the classes over `r`**: a finite set `S ⊆ ℚ²` containing exactly one
representative of each class `s ∈ ℚ²/ℤ²` with `Bs ≡ r (mod ℤ²)`. It represents the index set
`{s ∈ ℚ²/ℤ² : Bs - r ∈ ℤ²}` of the product in [72, Kopp (2024), Theorem 4.46, `thm:cllr`]. -/
structure IsPreimageTransversal (B : Mat(2, ℤ)) (r : Fin 2 → ℚ)
    (S : Finset (Fin 2 → ℚ)) : Prop where
  /-- Every member lies over `r`: `Bs - r ∈ ℤ²`. -/
  mem_preimage : ∀ s ∈ S, IsIntegralIndex (ratVecAction B s - r)
  /-- Members are pairwise incongruent modulo `ℤ²`. -/
  eq_of_isIntegralIndex_sub : ∀ s ∈ S, ∀ s' ∈ S, IsIntegralIndex (s - s') → s = s'
  /-- Every class over `r` has a member. -/
  exists_mem : ∀ s, IsIntegralIndex (ratVecAction B s - r) → ∃ s' ∈ S, IsIntegralIndex (s - s')

/-- A transversal also represents the classes over an integrally congruent characteristic;
used over the zero class by `prod_sfModularCocycleReal'_orbits_preimage_zero`. -/
theorem IsPreimageTransversal.of_isIntegralIndex_sub {B : Mat(2, ℤ)}
    {r r' : Fin 2 → ℚ} {S : Finset (Fin 2 → ℚ)}
    (hS : IsPreimageTransversal B r S) (hrr' : IsIntegralIndex (r - r')) :
    IsPreimageTransversal B r' S := by
  refine ⟨?_, hS.eq_of_isIntegralIndex_sub, ?_⟩
  · intro s hs
    convert isIntegralIndex_add (hS.mem_preimage s hs) hrr' using 1; module
  · intro s hs
    apply hS.exists_mem s
    convert isIntegralIndex_sub hs hrr' using 1; module

open scoped Classical in
/-- Two transversals of one fibre have the same nonintegral classes. This supplies the
representative change for the zero-class orbit decomposition. -/
theorem IsPreimageTransversal.congruent_nonintegral {B : Mat(2, ℤ)}
    {r : Fin 2 → ℚ} {S T : Finset (Fin 2 → ℚ)}
    (hS : IsPreimageTransversal B r S) (hT : IsPreimageTransversal B r T) :
    (∀ t ∈ T.filter (fun s => ¬ IsIntegralIndex s),
      ∃ s ∈ S.filter (fun s => ¬ IsIntegralIndex s), IsIntegralIndex (t - s)) ∧
    (∀ s ∈ S.filter (fun s => ¬ IsIntegralIndex s),
      ∃ t ∈ T.filter (fun s => ¬ IsIntegralIndex s), IsIntegralIndex (s - t)) := by
  classical
  constructor
  · intro t ht
    obtain ⟨htT, htni⟩ := Finset.mem_filter.mp ht
    obtain ⟨s, hsS, hts⟩ := hS.exists_mem t (hT.mem_preimage t htT)
    have hsni : ¬ IsIntegralIndex s := by
      intro hsi
      exact htni ((isIntegralIndex_iff_of_isIntegralIndex_sub hts).mpr hsi)
    exact ⟨s, Finset.mem_filter.mpr ⟨hsS, hsni⟩, hts⟩
  · intro s hs
    obtain ⟨hsS, hsni⟩ := Finset.mem_filter.mp hs
    obtain ⟨t, htT, hst⟩ := hT.exists_mem s (hS.mem_preimage s hsS)
    have htni : ¬ IsIntegralIndex t := by
      intro hti
      exact hsni ((isIntegralIndex_iff_of_isIntegralIndex_sub hst).mpr hti)
    exact ⟨t, Finset.mem_filter.mpr ⟨htT, htni⟩, hst⟩

/-- Congruent characteristics lie over the same characteristic. This is used by
`prod_orbitFactors_conj`. -/
private theorem isIntegralIndex_preimage_of_sub {B : Mat(2, ℤ)}
    {r s s' : Fin 2 → ℚ} (hs : IsIntegralIndex (ratVecAction B s - r))
    (hsub : IsIntegralIndex (s - s')) : IsIntegralIndex (ratVecAction B s' - r) := by
  have hBsub := isIntegralIndex_ratVecAction B hsub
  have h := isIntegralIndex_sub hs hBsub
  convert h using 1
  rw [ratVecAction_sub]
  module

/-- Kopp's conjugation law for a positive power that fixes a characteristic class. This
identifies the transported orbit factors in
`sfModularCocycleRealTotal_eq_prod_orbits_of_mem_Gf`. -/
theorem sfModularCocycleReal'_conj_pow {s : Fin 2 → ℚ} {C : SL(2, ℤ)} (n : ℕ)
    (hCn : C ^ n ∈ gammaSubgroup s) (M : SL(2, ℤ)) {α : ℝ}
    (hα : Irrational α) (hs : ¬ IsIntegralIndex s)
    (hfix : flt (C : Mat(2, ℤ)) α = α)
    (hjC : 0 < fltDenominator (C : Mat(2, ℤ)) α)
    (hjM : 0 < fltDenominator (M : Mat(2, ℤ)) α) :
    sfModularCocycleReal' (ratVecAction (M : Mat(2, ℤ)) s)
        ((M * C * M⁻¹) ^ n) (flt (M : Mat(2, ℤ)) α) =
      sfModularCocycleReal' s (C ^ n) α := by
  rw [conj_pow]
  rw [sfModularCocycleReal'_of_mem
    (mul_mul_inv_mem_gammaSubgroup_ratVecAction hCn M),
    sfModularCocycleReal'_of_mem hCn]
  exact sfModularCocycleRealTotal_mul_mul_inv hCn M hα hs
    (flt_pow_of_flt_eq_self hjC.ne' hfix n)
    (by rw [fltDenominator_pow_of_flt_eq_self hjC.ne' hfix]; positivity) hjM

/-- **The upper-triangular factors are distinct**: `(ℓ, j) ↦ s(j,ℓ)` is injective, since
`s(j,ℓ)₁ = (ℓ + r₁)/d` determines `ℓ` and then `s(j,ℓ)₀` determines `j`. -/
theorem sfUpperTriangularIndex_injective (r : Fin 2 → ℚ) (a d : ℕ) (b : ℤ) :
    Function.Injective fun p : Fin d × Fin a ↦ sfUpperTriangularIndex r a d b p.2 p.1 := by
  intro p q hpq
  apply sfUpperTriangularIndex_eq_of_sub_integral r (Fin.pos p.2) (Fin.pos p.1) b p q
  simpa only [hpq, sub_self] using
    (show IsIntegralIndex (0 : Fin 2 → ℚ) from fun _ => ⟨0, by simp⟩)

/-- Euclidean division supplies a finite residue and an integer quotient. This is used to build
the representative in `exists_sfUpperTriangularIndex_sub_integral`. -/
private theorem exists_int_mul_add_fin (n : ℕ) (hn : 0 < n) (k : ℤ) :
    ∃ q : ℤ, ∃ e : Fin n, q * n + e = k := by
  let e : Fin n := ⟨(k % (n : ℤ)).toNat, by
    have hnonneg := Int.emod_nonneg k (by positivity : (n : ℤ) ≠ 0)
    have hlt := Int.emod_lt_of_pos k (by positivity : (0 : ℤ) < n)
    omega⟩
  have he : (e : ℤ) = k % (n : ℤ) := by
    simp only [e]
    rw [Int.toNat_of_nonneg (Int.emod_nonneg k (by positivity))]
  exact ⟨k / n, e, by rw [he]; exact Int.ediv_mul_add_emod k n⟩

/-- Every characteristic over `r` is integrally congruent to an upper-triangular index. This is
the existence input for `isPreimageTransversal_upperTriangular`. -/
private theorem exists_sfUpperTriangularIndex_sub_integral (r : Fin 2 → ℚ) {a d : ℕ}
    (ha : 0 < a) (hd : 0 < d) (b : ℤ) (s : Fin 2 → ℚ)
    (hs : IsIntegralIndex (ratVecAction !![(a : ℤ), b; 0, (d : ℤ)] s - r)) :
    ∃ p : Fin d × Fin a,
      IsIntegralIndex (s - sfUpperTriangularIndex r a d b p.2 p.1) := by
  obtain ⟨k₀, hk₀⟩ := (isIntegralIndex_ratVecAction_sub_iff.mp hs) 0
  obtain ⟨k₁, hk₁⟩ := (isIntegralIndex_ratVecAction_sub_iff.mp hs) 1
  norm_num [Fin.sum_univ_two] at hk₀ hk₁
  obtain ⟨y, ell, hy⟩ := exists_int_mul_add_fin d hd k₁
  let t : ℤ := k₀ - b * y
  obtain ⟨q, j, hq⟩ := exists_int_mul_add_fin a ha (-t)
  let x : ℤ := -q
  have hx : t + (j : ℤ) = (a : ℤ) * x := by
    dsimp only [x]
    linarith
  refine ⟨(ell, j), fun i => ?_⟩
  fin_cases i
  · refine ⟨x, ?_⟩
    change s 0 -
      ((d : ℚ) * (r 0 - j) - b * (ell + r 1)) / (a * d) = (x : ℚ)
    field_simp
    have hxQ : (t : ℚ) + j = a * x := by exact_mod_cast hx
    have hyQ : (y : ℚ) * d + ell = k₁ := by exact_mod_cast hy
    dsimp only [t] at hxQ
    push_cast at hxQ
    linear_combination d * hk₀ - b * hk₁ + d * hxQ + b * hyQ
  · refine ⟨y, ?_⟩
    change s 1 - (ell + r 1) / d = (y : ℚ)
    field_simp
    have hyQ : (y : ℚ) * d + ell = k₁ := by exact_mod_cast hy
    ring_nf at hk₁ hyQ ⊢
    linarith

/-- **The upper-triangular factors form a transversal**: for `U = [[a,b],[0,d]]` with `a, d > 0`,
the characteristics `s(j,ℓ)`, `j < a`, `ℓ < d`, represent each class over `r` exactly once, because
`Us(j,ℓ) - r = (-j, ℓ)` (`sfUpperTriangularIndex_mem_preimage`) and the vectors `(-j, ℓ)` represent
`ℤ²/Uℤ²` exactly once. -/
theorem isPreimageTransversal_upperTriangular (r : Fin 2 → ℚ) {a d : ℕ} (ha : 0 < a)
    (hd : 0 < d) (b : ℤ) :
    IsPreimageTransversal !![(a : ℤ), b; 0, (d : ℤ)] r
      (Finset.univ.image fun p : Fin d × Fin a ↦ sfUpperTriangularIndex r a d b p.2 p.1) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hs
    exact isIntegralIndex_ratVecAction_sub_iff.2
      (sfUpperTriangularIndex_mem_preimage r b p.2 p.1)
  · intro s hs s' hs' hsub
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hs'
    subst s'
    exact congrArg (fun z => sfUpperTriangularIndex r a d b z.2 z.1)
      (sfUpperTriangularIndex_eq_of_sub_integral r ha hd b p q hsub)
  · intro s hs
    obtain ⟨p, hp⟩ := exists_sfUpperTriangularIndex_sub_integral r ha hd b s hs
    exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ p), hp⟩

/-- **Transversals transport along `SL₂(ℤ)`**: if `S` is a transversal of the classes over `r`
for `U`, then `R⁻¹S` is one for `UR`, since `(UR)(R⁻¹s) = Us` and `R⁻¹` preserves `ℤ²`. -/
theorem IsPreimageTransversal.image_ratVecAction_inv {U : Mat(2, ℤ)}
    {r : Fin 2 → ℚ} {S : Finset (Fin 2 → ℚ)} (hS : IsPreimageTransversal U r S) (R : SL(2, ℤ)) :
    IsPreimageTransversal (U * (R : Mat(2, ℤ))) r
      (S.image (ratVecAction ((R⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)))) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    rw [ratVecAction_mul, ratVecAction_ratVecAction_inv]
    exact hS.mem_preimage t ht
  · intro s hs s' hs' hsub
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp hs'
    have htt' : IsIntegralIndex (t - t') := by
      rw [← ratVecAction_sub] at hsub
      exact (isIntegralIndex_ratVecAction_iff (R⁻¹)).mp hsub
    exact congrArg _ (hS.eq_of_isIntegralIndex_sub t ht t' ht' htt')
  · intro s hs
    rw [ratVecAction_mul] at hs
    obtain ⟨t, ht, hst⟩ := hS.exists_mem _ hs
    refine ⟨ratVecAction ((R⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) t,
      Finset.mem_image_of_mem _ ht, ?_⟩
    apply (isIntegralIndex_ratVecAction_iff R).mp
    rw [ratVecAction_sub, ratVecAction_ratVecAction_inv]
    exact hst

/-! ### The relation for every matrix of positive determinant

The upper-triangular relation of `SICs.Cocycle.ConductorDistribution`, moved along the `SL₂(ℤ)`
factor of [72, Kopp (2024), Lemma 4.44, `lem:Gforbits`] by [72, Kopp (2024), Theorem 4.37,
`thm:shinconj`]. -/

/-- A characteristic over a nonintegral characteristic cannot itself be integral. This supplies
the domain hypothesis in `prod_orbitFactors_conj`. -/
private theorem not_isIntegralIndex_of_mem_preimage {B : Mat(2, ℤ)}
    {r s : Fin 2 → ℚ} (hr : ¬ IsIntegralIndex r)
    (hs : IsIntegralIndex (ratVecAction B s - r)) : ¬ IsIntegralIndex s := by
  intro hsint
  apply hr
  have h := isIntegralIndex_sub (isIntegralIndex_ratVecAction B hsint) hs
  convert h using 1
  module

/-- Factoring `B = UR` transports `BC = AB` to `U(RCR⁻¹) = AU`. This is the matrix step in
`sfModularCocycleRealTotal_eq_prod_orbits_of_mem_Gf` and
`prod_sfModularCocycleReal'_orbits_preimage_zero`. -/
theorem upperTriangular_semiconj_of_factor {B : Mat(2, ℤ)}
    {A C : SL(2, ℤ)} (a d : ℕ) (b : ℤ) (R : SL(2, ℤ))
    (hfac : B = !![(a : ℤ), b; 0, (d : ℤ)] * R)
    (hconj : B * (C : Mat(2, ℤ)) = (A : Mat(2, ℤ)) * B) :
    !![(a : ℤ), b; 0, (d : ℤ)] *
        ((R * C * R⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) =
      (A : Mat(2, ℤ)) * !![(a : ℤ), b; 0, (d : ℤ)] := by
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [hfac] at hconj
  have hRR : (R : Mat(2, ℤ)) *
      ((R⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
    rfl
  calc
    _ = ((!![(a : ℤ), b; 0, (d : ℤ)] * R) * C) * (R⁻¹ : SL(2, ℤ)) := by
      noncomm_ring
    _ = ((A : Mat(2, ℤ)) *
        (!![(a : ℤ), b; 0, (d : ℤ)] * R)) * (R⁻¹ : SL(2, ℤ)) := by rw [hconj]
    _ = ((A : Mat(2, ℤ)) * !![(a : ℤ), b; 0, (d : ℤ)]) *
        ((R : Mat(2, ℤ)) * (R⁻¹ : SL(2, ℤ))) := by noncomm_ring
    _ = _ := by rw [hRR, Matrix.mul_one]

/-- Positivity of `j_B(α)` descends to `j_R(α)` in an upper-triangular factorization `B = UR`.
This supplies the orientation hypothesis in `sfModularCocycleRealTotal_eq_prod_orbits_of_mem_Gf`
and `prod_sfModularCocycleReal'_orbits_preimage_zero`. -/
theorem fltDenominator_pos_of_upperTriangular_factor
    {B : Mat(2, ℤ)} (a d : ℕ) (b : ℤ) (R : SL(2, ℤ)) {α : ℝ}
    (hd : 0 < d) (hfac : B = !![(a : ℤ), b; 0, (d : ℤ)] * R)
    (hRden : fltDenominator (R : Mat(2, ℤ)) α ≠ 0)
    (hjB : 0 < fltDenominator B α) :
    0 < fltDenominator (R : Mat(2, ℤ)) α := by
  rw [hfac, fltDenominator_mul _ _ _ hRden, fltDenominator_upperTriangular] at hjB
  have hdR : (0 : ℝ) < d := by positivity
  exact pos_of_mul_pos_right hjB hdR.le

/-- The Möbius action of `B = [[a,b],[0,d]]R` is the upper-triangular action after `R`.
This rewrites the left side in `sfModularCocycleRealTotal_eq_prod_orbits_of_mem_Gf`. -/
private theorem flt_eq_upperTriangular_of_factor
    {B : Mat(2, ℤ)} (a d : ℕ) (b : ℤ) (R : SL(2, ℤ)) {α : ℝ}
    (hfac : B = !![(a : ℤ), b; 0, (d : ℤ)] * R)
    (hRden : fltDenominator (R : Mat(2, ℤ)) α ≠ 0) :
    flt B α = ((a : ℝ) * flt (R : Mat(2, ℤ)) α + b) / d := by
  rw [hfac, flt_mul _ _ _ hRden]
  simpa only [Int.cast_natCast] using
    flt_upperTriangular (K := ℝ) (a : ℤ) b (d : ℤ)
      (flt (R : Mat(2, ℤ)) α)

/-- A transversal and its orbit decomposition for `B = [[a,b],[0,d]]M` transport to the
canonical upper-triangular factor set. This supplies the orbit data in
`sfModularCocycleRealTotal_eq_prod_orbits_of_mem_Gf`. -/
private theorem orbitDecomp_upperTriangular_of_factor {B : Mat(2, ℤ)} {r : Fin 2 → ℚ}
    {C : SL(2, ℤ)} {S R : Finset (Fin 2 → ℚ)} {m : (Fin 2 → ℚ) → ℕ+}
    (hS : IsPreimageTransversal B r S) (hR : IsOrbitDecomposition C S R m)
    {a d : ℕ} (ha : 0 < a) (hd : 0 < d) (b : ℤ) (M : SL(2, ℤ))
    (hfac : B = !![(a : ℤ), b; 0, (d : ℤ)] * M) :
    IsOrbitDecomposition (M * C * M⁻¹)
      (Finset.univ.image fun p : Fin d × Fin a ↦ sfUpperTriangularIndex r a d b p.2 p.1)
      (R.image (ratVecAction (M : Mat(2, ℤ))))
      (fun t => m (ratVecAction ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) t)) := by
  classical
  let U : Mat(2, ℤ) := !![(a : ℤ), b; 0, (d : ℤ)]
  let T := Finset.univ.image fun p : Fin d × Fin a ↦
    sfUpperTriangularIndex r a d b p.2 p.1
  let S' := S.image (ratVecAction (M : Mat(2, ℤ)))
  have hmat : B * ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) = U := by
    rw [hfac]
    change (U * (M : Mat(2, ℤ))) * (M⁻¹ : SL(2, ℤ)) = U
    rw [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
    simp
  have hS' : IsPreimageTransversal U r S' := by
    have hh := hS.image_ratVecAction_inv (M⁻¹)
    rw [hmat] at hh
    simpa only [inv_inv, S'] using hh
  have hT : IsPreimageTransversal U r T := isPreimageTransversal_upperTriangular r ha hd b
  exact (hR.image_ratVecAction M).of_congruent_set
    (fun t ht => hS'.exists_mem t (hT.mem_preimage t ht))
    (fun s hs => hT.exists_mem s (hS'.mem_preimage s hs))

/-- Conjugation carries the product of orbit factors through a unimodular change of
coordinates. This is the final product comparison in
`sfModularCocycleRealTotal_eq_prod_orbits_of_mem_Gf`. -/
private theorem prod_orbitFactors_conj {B : Mat(2, ℤ)} {r : Fin 2 → ℚ}
    (hr : ¬ IsIntegralIndex r) {C : SL(2, ℤ)} {S R : Finset (Fin 2 → ℚ)}
    {m : (Fin 2 → ℚ) → ℕ+} (hS : IsPreimageTransversal B r S)
    (hR : IsOrbitDecomposition C S R m) {α : ℝ} (hα : Irrational α)
    (hfix : flt (C : Mat(2, ℤ)) α = α)
    (hjC : 0 < fltDenominator (C : Mat(2, ℤ)) α) (M : SL(2, ℤ))
    (hjM : 0 < fltDenominator (M : Mat(2, ℤ)) α) :
    ∏ y ∈ R.image (ratVecAction (M : Mat(2, ℤ))),
        sfModularCocycleReal' y ((M * C * M⁻¹) ^
          (m (ratVecAction ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) y) : ℕ))
          (flt (M : Mat(2, ℤ)) α) =
      ∏ y ∈ R, sfModularCocycleReal' y (C ^ (m y : ℕ)) α := by
  classical
  have hinj : Function.Injective (ratVecAction (M : Mat(2, ℤ))) := by
    intro s t hst
    have h := congrArg (ratVecAction ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))) hst
    simpa only [ratVecAction_inv_ratVecAction] using h
  rw [Finset.prod_image hinj.injOn]
  apply Finset.prod_congr rfl
  intro y hy
  obtain ⟨s, hs, hsy⟩ := hR.exists_mem y hy 0 (m y).pos
  have hpre : IsIntegralIndex (ratVecAction B y - r) :=
    isIntegralIndex_preimage_of_sub (hS.mem_preimage s hs) (by simpa using hsy)
  have hCn : C ^ (m y : ℕ) ∈ gammaSubgroup y :=
    mem_gammaSubgroup_of_isIntegralIndex (hR.period y hy)
  simpa only [ratVecAction_inv_ratVecAction] using
    sfModularCocycleReal'_conj_pow (m y : ℕ) hCn M hα
      (not_isIntegralIndex_of_mem_preimage hr hpre) hfix hjC hjM

/-- **The conductor relation along orbits, on the real line**: for `B ∈ G_f`, `f > 0`,
`C ∈ SL₂(ℤ)` with `BC = AB`, `r ∉ ℤ²`, `A ∈ Γ_r`, an irrational `α` with `C·α = α`,
`j_C(α) > 0` and `j_B(α) > 0`, a transversal `S` of the classes over `r`, and an orbit
decomposition `(R, m)` of those classes under `C`,

$$ש^{\mathbf r}_A(B\cdot\alpha) = \prod_{\mathbf y\in R} ש^{\mathbf y}_{C^{m(\mathbf y)}}(\alpha).$$

The nonzero orbits of [RW26b, Radchenko, Wheeler (2026b), Appendix A, proof of Proposition 3]
in the cocycle language of [72, Kopp (2024), Theorem 4.46, `thm:cllr`]. The source theorem is
the case `m ≡ 1`; its printed statement omits the necessary orientation `j_B(α) > 0`. -/
theorem sfModularCocycleRealTotal_eq_prod_orbits_of_mem_Gf {f : ℕ} (hf : 0 < f)
    {B : Mat(2, ℤ)} (hB : B ∈ Gf (f : ℤ)) {r : Fin 2 → ℚ}
    (hr : ¬ IsIntegralIndex r) {A C : SL(2, ℤ)}
    (hconj : B * (C : Mat(2, ℤ)) = (A : Mat(2, ℤ)) * B)
    (hA : A ∈ gammaSubgroup r)
    {α : ℝ} (hα : Irrational α) (hfix : flt (C : Mat(2, ℤ)) α = α)
    (hjC : 0 < fltDenominator (C : Mat(2, ℤ)) α)
    (hjB : 0 < fltDenominator B α) {S R : Finset (Fin 2 → ℚ)} {m : (Fin 2 → ℚ) → ℕ+}
    (hS : IsPreimageTransversal B r S) (hR : IsOrbitDecomposition C S R m) :
    sfModularCocycleRealTotal r A hA (flt B α) =
      ∏ y ∈ R, sfModularCocycleReal' y (C ^ (m y : ℕ)) α := by
  classical
  obtain ⟨a, d, b, M, had, _, _, hfac⟩ :=
    exists_eq_upperTriangular_mul_of_mem_Gf hf hB
  have hadpos : 0 < a * d := by simpa only [had] using hf
  have ha : 0 < a := Nat.pos_of_mul_pos_right hadpos
  have hd : 0 < d := Nat.pos_of_mul_pos_left hadpos
  let C' : SL(2, ℤ) := M * C * M⁻¹
  let α' : ℝ := flt (M : Mat(2, ℤ)) α
  have hMden := fltDenominator_ne_zero_of_irrational hα M
  have hα' : Irrational α' := Irrational.flt hα M
  have hjM := fltDenominator_pos_of_upperTriangular_factor a d b M hd hfac hMden hjB
  have hfix' : flt (C' : Mat(2, ℤ)) α' = α' :=
    flt_mul_mul_inv_of_flt_eq_self M hMden hjC.ne' hfix
  have hjC' : 0 < fltDenominator (C' : Mat(2, ℤ)) α' := by
    rw [fltDenominator_mul_mul_inv_of_flt_eq_self M hMden hjC.ne' hfix]
    exact hjC
  have hconj' := upperTriangular_semiconj_of_factor a d b M hfac hconj
  have hmain := sfModularCocycleRealTotal_eq_prod_orbits_upperTriangular
    hr ha hd b hconj' hA hα' hfix' hjC'
      (orbitDecomp_upperTriangular_of_factor hS hR ha hd b M hfac)
  rw [flt_eq_upperTriangular_of_factor a d b M hfac hMden]
  calc
    sfModularCocycleRealTotal r A hA (((a : ℝ) * α' + b) / d) =
        ∏ y ∈ R.image (ratVecAction (M : Mat(2, ℤ))),
          sfModularCocycleReal' y (C' ^
            (m (ratVecAction ((M⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) y) : ℕ)) α' := hmain
    _ = _ := prod_orbitFactors_conj hr hS hR hα hfix hjC M hjM

end SIC

end
