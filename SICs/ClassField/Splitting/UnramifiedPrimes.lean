/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Splitting.PrimeDegree

/-!
# Unramified primes of abelian extensions

A finite place `v` of `K` is unramified in a finite abelian extension `L` whenever the image of
the integral units $U_v$ in the idèle class group consists of norms from `L`.

This module follows Childress, *Class Field Theory* (2009), Chapter VI, Theorem 3.4, in the form
consumed by the ray class field (for $\iota_v(U_v)\subseteq N_{L/K}C_L$ the inertia group
$\operatorname{Art}_{L/K}(\iota_v(U_v))$ is trivial), by an induction on the degree through
intermediate fields of prime codegree in place of his reduction to the decomposition field. It
supplies the unramifiedness of ray class fields away from their modulus
(`rayNorm_ramificationIdx_one`).

## The argument

*Prime degree.* Let $[L:K] = p$ be prime and `w` a place of `L` above `v`, with ramification index
`e` and inertia degree `f`; then $ef = [L_w:K_v]$ divides `p`
(`FinitePlace.finrank_eq_ramificationIdx_mul_inertiaDeg`, `FinitePlace.finrank_dvd_finrank`). If
$f\ne1$, then $f = p$ and $e = 1$. If $f = 1$, the local norm $y = N_{L_w/K_v}(\pi_w)$ of a
uniformizer has valuation $\exp(-1)$ (`FinitePlace.valued_localNorm`), and $\iota_v(y)$ is the norm
of $\iota_w(\pi_w)$ (`IdeleClassGroup.norm_ofAdicCompletion`). With the hypothesis on $U_v$, the
whole of $K_v^\times = y^{\mathbb Z}U_v$ maps into norms (`FinitePlace.eq_top_of_unitGroup_le`), so
`v` splits completely (`FinitePlace.finrank_eq_one_of_finrank_prime`) and $e = 1$.

*Induction.* Choose `E` with $[L:E] = p$ prime. Restriction gives the
hypothesis for `E/K`, so `v` is unramified in `E` by induction. Local norms of units are units
(`FinitePlace.localNorm_mem_unitGroup_iff`). The tower law for the global Artin map carries the
norm-subgroup hypothesis to `L/E` at every place `w` of `E` above `v`, and ramification indices
multiply in towers.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped SIC.FinitePlace NumberField.LiesOver SIC.InfinitePlace

namespace SIC

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- **Unramifiedness in prime degree**: if `L/K` is Galois of prime degree and the image of
$U_v$ in $C_K$ lies in $N_{L/K}C_L$, then every `w` above `v` is unramified. Childress, *Class
Field Theory*, Chapter VI, proof of Theorem 3.4, for a cyclic extension of prime degree. -/
theorem FinitePlace.ramificationIdx_eq_one_of_finrank_prime [IsGalois K L]
    (hp : (Module.finrank K L).Prime) (v : HeightOneSpectrum (𝓞 K))
    (hv : (FinitePlace.unitGroup v).map (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v) ≤
      (IdeleClassGroup.norm (K := K) (L := L)).range)
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  let e := w.asIdeal.ramificationIdx (𝓞 K)
  let f := w.asIdeal.inertiaDeg (𝓞 K)
  have hdegree : Module.finrank (v.adicCompletion K) (w.adicCompletion L) = e * f :=
    FinitePlace.finrank_eq_ramificationIdx_mul_inertiaDeg v w
  have hdiv : e * f ∣ Module.finrank K L := by
    rw [← hdegree]
    exact FinitePlace.finrank_dvd_finrank v w
  by_cases hf : f = 1
  · obtain ⟨π, hπ⟩ := FinitePlace.exists_valued_eq_exp_neg_one w
    let y := FinitePlace.localNorm v w π
    have hy : Valued.v (y : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
      rw [FinitePlace.valued_localNorm]
      change Valued.v (π : w.adicCompletion L) ^ f = _
      rw [hf, pow_one]
      exact hπ
    let H := (IdeleClassGroup.norm (K := K) (L := L)).range.comap
      (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v)
    have hU : FinitePlace.unitGroup v ≤ H :=
      Subgroup.map_le_iff_le_comap.mp hv
    have hyH : y ∈ H := by
      change NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v y ∈
        (IdeleClassGroup.norm (K := K) (L := L)).range
      exact ⟨NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 L) L w π,
        IdeleClassGroup.norm_ofAdicCompletion v w π⟩
    have htop := FinitePlace.eq_top_of_unitGroup_le v hU hy hyH
    have hfull : (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v).range ≤
        (IdeleClassGroup.norm (K := K) (L := L)).range := by
      rw [← Subgroup.map_top, ← htop]
      exact Subgroup.map_le_iff_le_comap.mpr le_rfl
    have hlocal := FinitePlace.finrank_eq_one_of_finrank_prime hp v hfull w
    exact Nat.eq_one_of_mul_eq_one_right (hdegree ▸ hlocal)
  · have hfdiv : f ∣ Module.finrank K L :=
      (show f ∣ e * f from ⟨e, by simp [Nat.mul_comm]⟩).trans hdiv
    have hfeq : f = Module.finrank K L :=
      (hp.eq_one_or_self_of_dvd f hfdiv).resolve_left hf
    have hprod : e * f = Module.finrank K L := by
      rcases hp.eq_one_or_self_of_dvd (e * f) hdiv with h | h
      · have : f = 1 := Nat.eq_one_of_mul_eq_one_left h
        exact (hf this).elim
      · exact h
    exact (Nat.mul_eq_right (b := Module.finrank K L) hp.ne_zero).mp
      (by simpa [hfeq] using hprod)

/-! ### Passing the norm hypothesis to an intermediate field

The norm of a one-place idèle is the one-place idèle of the local norm. The global Artin tower
law therefore transports the subgroup hypothesis from `L/K` to `L/E`; this is the bridge used in
the induction step below.
-/

/-- If $\iota_v(H)\subseteq N_{L/K}C_L$ for a subgroup `H` of $K_v^\times$ at a finite place, then
$\iota_w(N_{E_w/K_v}^{-1}H)\subseteq N_{L/E}C_L$ for every intermediate field `E` and place `w`
of `E` above `v`. Childress, *Class Field Theory*, Chapter VI, proof of Theorem 3.4, by the
consistency property (Chapter V, Corollary 1.3). -/
private theorem map_comap_localNorm_le_range_norm [IsAbelianGalois K L]
    (E : IntermediateField K L) (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal] {H : Subgroup (v.adicCompletion K)ˣ}
    (hH : H.map (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v) ≤
      (IdeleClassGroup.norm (K := K) (L := L)).range) :
    (H.comap (FinitePlace.localNorm v w)).map
        (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 E) E w) ≤
      (IdeleClassGroup.norm (K := E) (L := L)).range := by
  rintro y ⟨x, hx, rfl⟩
  apply comap_norm_range_norm_le E
  change IdeleClassGroup.norm (K := K) (L := E) _ ∈
    (IdeleClassGroup.norm (K := K) (L := L)).range
  rw [IdeleClassGroup.norm_ofAdicCompletion v w]
  exact hH ⟨FinitePlace.localNorm v w x, hx, rfl⟩

/-- The prime-degree step above an unramified intermediate place. Used in
`FinitePlace.ramificationIdx_eq_one_of_map_le_range_norm`. -/
private theorem FinitePlace.ramificationIdx_eq_one_of_prime_tower
    [IsAbelianGalois K L] (E : IntermediateField K L)
    (hp : (Module.finrank E L).Prime) (v : HeightOneSpectrum (𝓞 K))
    (u : HeightOneSpectrum (𝓞 E)) [u.asIdeal.LiesOver v.asIdeal]
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver u.asIdeal]
    (hv : (FinitePlace.unitGroup v).map
      (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v) ≤
      (IdeleClassGroup.norm (K := K) (L := L)).range)
    (hbase : u.asIdeal.ramificationIdx (𝓞 K) = 1) :
    w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  have hunit : (FinitePlace.unitGroup v).comap (FinitePlace.localNorm v u) =
      FinitePlace.unitGroup u := by
    ext x
    exact FinitePlace.localNorm_mem_unitGroup_iff v u
  have hvL : (FinitePlace.unitGroup u).map
      (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 E) E u) ≤
      (IdeleClassGroup.norm (K := E) (L := L)).range := by
    rw [← hunit]
    exact map_comap_localNorm_le_range_norm E v u hv
  have htop := FinitePlace.ramificationIdx_eq_one_of_finrank_prime hp u hvL w
  rw [Ideal.ramificationIdx_tower (R := 𝓞 K) (S := 𝓞 E) (T := 𝓞 L)
    (q := u.asIdeal) (r := w.asIdeal), hbase, htop, one_mul]

/-- **Unramified primes**: if the image of the integral units $U_v$ in $C_K$ lies in
$N_{L/K}C_L$ for a finite abelian `L/K`, then every `w` above `v` is unramified. Childress,
*Class Field Theory*, Chapter VI, Theorem 3.4: $\operatorname{Art}_{L/K}(\iota_v(U_v))$ is the
inertia group, so it is trivial only if `v` is unramified. -/
theorem FinitePlace.ramificationIdx_eq_one_of_map_le_range_norm [IsAbelianGalois K L]
    (v : HeightOneSpectrum (𝓞 K))
    (hv : (FinitePlace.unitGroup v).map (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v) ≤
      (IdeleClassGroup.norm (K := K) (L := L)).range)
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  classical
  apply (IsAbelianGalois.induction_finrank_prime (K := K)
    (P := fun F [Field F] [Algebra K F] [FiniteDimensional K F] =>
      letI : NumberField F := NumberField.of_module_finite K F
      ∀ (v : HeightOneSpectrum (𝓞 K)),
        (FinitePlace.unitGroup v).map
          (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v) ≤
            (IdeleClassGroup.norm (K := K) (L := F)).range →
        ∀ (w : HeightOneSpectrum (𝓞 F)) [w.asIdeal.LiesOver v.asIdeal],
          w.asIdeal.ramificationIdx (𝓞 K) = 1)
    ?_ ?_ L) v hv w
  · intro F _ _ _ _
    refine (letI : NumberField F := NumberField.of_module_finite K F; ?_)
    intro hone v _ w _
    have hlocal : Module.finrank (v.adicCompletion K) (w.adicCompletion F) = 1 :=
      Nat.eq_one_of_dvd_one (by
        simpa only [hone] using FinitePlace.finrank_dvd_finrank v w)
    have hdegree := FinitePlace.finrank_eq_ramificationIdx_mul_inertiaDeg v w
    rw [hlocal] at hdegree
    exact Nat.eq_one_of_mul_eq_one_right hdegree.symm
  · intro F _ _ _ _
    refine (letI : NumberField F := NumberField.of_module_finite K F; ?_)
    intro E hp ih v hv w _
    let u : HeightOneSpectrum (𝓞 E) := FinitePlace.below (K := E) w
    have hu : u.asIdeal.LiesOver v.asIdeal :=
      FinitePlace.liesOver_below_of_liesOver (L := E) v w
    have hvE : (FinitePlace.unitGroup v).map
        (NumberField.IdeleClassGroup.ofAdicCompletion (𝓞 K) K v) ≤
        (IdeleClassGroup.norm (K := K) (L := E)).range :=
      hv.trans (IdeleClassGroup.range_norm_le_of_algHom E.val)
    have hbase : u.asIdeal.ramificationIdx (𝓞 K) = 1 := ih v hvE u
    exact FinitePlace.ramificationIdx_eq_one_of_prime_tower E hp v u w hv hbase

end SIC
