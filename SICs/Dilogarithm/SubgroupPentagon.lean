/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.FiveTerm.Conjugation

/-!
# The pentagon relation for subgroups

The pentagon relation for `(H, H^∨)`, obtained by summing the finite five-term relation over the
orthogonal complement `H^∨` supplied by `SICs.Dilogarithm.MetricGroup`.

This module follows [AFK26, Appleby, Flammia, Kopp (2026), Section 3, Theorem 3.1,
`thm:subgrouppentagon`], which deduces the relation from [RW26, Radchenko, Wheeler (2026),
Theorem 2, `thm:fg.equs`, equation (7), `eq:Fgpm.5term`]. It is stated first for any functions
`E`, `F⁻` on a metric group satisfying (7), then for the finite quantum dilogarithm `F^±_γ` of a
hyperbolic matrix at its attractive fixed point. Only the second identity of the theorem,
`eq:subgrouppentagon2`, is formalized: it is the one [AFK26, Appleby, Flammia, Kopp (2026),
Section 5, proof of Theorem 1.2,
`thm:tci`] uses for the explicit shift, and the first, `eq:subgrouppentagon1`, has no consumer.
The source's normalizations `1/√|H|` and `1/√|H^∨|` are cleared using `|H||H^∨| = |G|`, so that
no square root of `|H|` is needed in the coefficient field.
The source assumes `H` is proper; the same character-sum argument also covers `H = G`, so the
formal statement allows every subgroup.

## The argument

For `z ∈ G`, `∑_{u ∈ H^∨} ⟨z; u⟩ = (|G|/|H|) 1_{z ∈ H}`: write the indicator of `H^∨` as
`|H|⁻¹ ∑_{h ∈ H} ⟨u; h⟩` (a character of `H` sums to `0` unless it is trivial) and use
orthogonality on `G` (`MetricGroup.sum_bichar`). Multiply (7) at `(u, v)`, `v ≠ 0`, by `⟨y; u⟩`
and sum over `u ∈ H^∨`: the left side becomes
`|G|^{-1/2} ∑_x E(x)/F⁻(x + v) ∑_{u ∈ H^∨} ⟨x + y; u⟩`, which is
`(√|G|/|H|) ∑_{x ∈ H} E(x - y)/F⁻(x - y + v)`,
and the right side is `F⁻(v)⁻¹ ∑_{u ∈ H^∨} ⟨y; u⟩ E(u + v)/F⁻(u)`.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

variable {G : Type*} [AddCommGroup G] [Fintype G] {k : Type*} [Field k]

namespace MetricGroup

variable (M : MetricGroup G k)

/-! ### The pentagon relation for subgroups

Summing (7) over `H^∨` against `⟨y; ·⟩`. -/

open scoped Classical in
/-- Reindexes a sum restricted to `x + y ∈ H` as a sum over `H`; used by
`subgroupPentagon`. -/
private theorem sum_subgroup_translate (H : AddSubgroup G) (y : G) (f : G → k) :
    (∑ x with x + y ∈ H, f x) = ∑ x with x ∈ H, f (x - y) := by
  classical
  calc
    _ = ∑ x : G, if x + y ∈ H then f x else 0 := by rw [Finset.sum_filter]
    _ = ∑ x : G, if x ∈ H then f (x - y) else 0 := by
      apply Fintype.sum_equiv (Equiv.addRight y)
      intro x
      simp
    _ = ∑ x with x ∈ H, f (x - y) := by rw [Finset.sum_filter]

open scoped Classical in
/-- Summing the Fourier kernel against `⟨y;u⟩` on `H^∨` selects the translate
`H - y`; used by `subgroupPentagon`. -/
private theorem weighted_sum_orthogonal_bichar (H : AddSubgroup G) (y : G) (f : G → k) :
    (Nat.card H : k) *
        ∑ u with u ∈ M.orthogonal H,
          M.bichar y u * (M.sqrtCard⁻¹ * ∑ x, M.bichar x u * f x) =
      M.sqrtCard * ∑ x with x ∈ H, f (x - y) := by
  classical
  have hcore :
      (∑ u with u ∈ M.orthogonal H,
        M.bichar y u * ∑ x : G, M.bichar x u * f x) =
        ∑ x : G, f x * ∑ u with u ∈ M.orthogonal H, M.bichar (x + y) u := by
    calc
      _ = ∑ u with u ∈ M.orthogonal H,
            ∑ x : G, f x * M.bichar (x + y) u := by
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [M.bichar_add_left]
        ring_nf
      _ = _ := by
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
  calc
    _ = (Nat.card H : k) * M.sqrtCard⁻¹ *
          ∑ u with u ∈ M.orthogonal H,
            M.bichar y u * (∑ x : G, M.bichar x u * f x) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring_nf
    _ = M.sqrtCard⁻¹ * ∑ x : G,
          f x * ((Nat.card H : k) *
            ∑ u with u ∈ M.orthogonal H, M.bichar (x + y) u) := by
      rw [hcore]
      simp only [Finset.mul_sum]
      ring_nf
    _ = M.sqrtCard⁻¹ * ∑ x : G,
          f x * (if x + y ∈ H then (Fintype.card G : k) else 0) := by
      simp_rw [M.card_mul_sum_orthogonal_bichar H]
    _ = M.sqrtCard * ∑ x with x ∈ H, f (x - y) := by
      simp only [mul_ite, mul_zero, Finset.sum_ite, Finset.sum_const_zero, add_zero]
      rw [← Finset.sum_mul, sum_subgroup_translate H y f, ← M.sqrtCard_sq]
      field_simp [M.sqrtCard_ne_zero]

open scoped Classical in
/-- **The pentagon relation for a subgroup, in metric-group form** [AFK26, Appleby, Flammia,
Kopp (2026), Theorem 3.1, `thm:subgrouppentagon`, equation `eq:subgrouppentagon2`]: if `E`, `F⁻`
satisfy the finite five-term relation (7) for `v ≠ 0`, then for every subgroup `H`, `y ∈ G`, and
`v ≠ 0`,

$$\sqrt{|G|}\sum_{x\in H}\frac{E(x-y)}{F^-(x-y+v)}
  = \frac{|H|}{F^-(v)}\sum_{u\in H^\vee}\langle y;u\rangle\frac{E(u+v)}{F^-(u)}.$$

The source's normalization `|H|^{-1/2}` on the left and `|H^∨|^{-1/2}` on the right is cleared
with `|H||H^∨| = |G|`. The source's properness assumption on `H` is unnecessary. -/
theorem subgroupPentagon {E Fm : G → k}
    (hfive : ∀ u v, v ≠ 0 →
      M.sqrtCard⁻¹ * ∑ x, M.bichar x u * (E x / Fm (x + v)) = E (u + v) / (Fm u * Fm v))
    (H : AddSubgroup G) (y : G) {v : G} (hv : v ≠ 0) :
    M.sqrtCard * ∑ x with x ∈ H, E (x - y) / Fm (x - y + v) =
      (Nat.card H : k) * (Fm v)⁻¹ *
        ∑ u with u ∈ M.orthogonal H, M.bichar y u * (E (u + v) / Fm u) := by
  let f : G → k := fun x => E x / Fm (x + v)
  have hlocal (u : G) :
      E (u + v) / (Fm u * Fm v) =
        M.sqrtCard⁻¹ * ∑ x, M.bichar x u * f x := (hfive u v hv).symm
  have hsum :
      (Nat.card H : k) *
          ∑ u with u ∈ M.orthogonal H,
            M.bichar y u * (E (u + v) / (Fm u * Fm v)) =
        M.sqrtCard * ∑ x with x ∈ H, f (x - y) := by
    calc
      _ = (Nat.card H : k) *
            ∑ u with u ∈ M.orthogonal H,
              M.bichar y u * (M.sqrtCard⁻¹ * ∑ x, M.bichar x u * f x) := by
        simp_rw [hlocal]
      _ = _ := M.weighted_sum_orthogonal_bichar H y f
  calc
    _ = (Nat.card H : k) *
          ∑ u with u ∈ M.orthogonal H,
            M.bichar y u * (E (u + v) / (Fm u * Fm v)) := by
      simpa only [f] using hsum.symm
    _ = (Nat.card H : k) * (Fm v)⁻¹ *
          ∑ u with u ∈ M.orthogonal H,
            M.bichar y u * (E (u + v) / Fm u) := by
      have hfactor :
          (∑ u with u ∈ M.orthogonal H,
            M.bichar y u * (E (u + v) / (Fm u * Fm v))) =
          (Fm v)⁻¹ * ∑ u with u ∈ M.orthogonal H,
            M.bichar y u * (E (u + v) / Fm u) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring_nf
      rw [hfactor]
      ring_nf

end MetricGroup

open scoped Classical in
/-- **The pentagon relation for subgroups at a hyperbolic matrix** [AFK26, Appleby, Flammia, Kopp
(2026), Theorem 3.1, `thm:subgrouppentagon`, equation `eq:subgrouppentagon2`]: for the finite
quantum dilogarithm `F^±_γ` of `γ` at its attractive fixed point `τ`, given the finite five-term
relation (7), every subgroup `H ⊆ G`, `y ∈ G`, and `v ≠ 0` satisfy
`√N ∑_{x ∈ H} F⁺(x - y)/F⁻(x - y + v) = |H| F⁻(v)⁻¹ ∑_{u ∈ H^∨} ⟨y; u⟩ F⁺(u + v)/F⁻(u)`. -/
@[source "AFK26, Theorem 3.1, p. 5, thm:subgrouppentagon (eq:subgrouppentagon2)"]
theorem finiteDilogSubgroupPentagon {A : SL(2, ℤ)} {τ : ℝ} (h : IsAttractiveFixedPoint A τ)
    [NeZero (finiteDilogOrder A)] (hfive : FiniteDilogFiveTerm A τ)
    (H : AddSubgroup (finiteDilogGroup A)) (y : finiteDilogGroup A)
    {v : finiteDilogGroup A} (hv : v ≠ 0) :
    (Real.sqrt (finiteDilogOrder A) : ℂ) *
        ∑ x with x ∈ H,
          finiteDilogE A τ (x - y) / finiteDilogEMinus A τ (x - y + v) =
      (Nat.card H : ℂ) * (finiteDilogEMinus A τ v)⁻¹ *
        ∑ u with u ∈ (fixedMetricGroup A (finiteDilogOrder A)
            (det_sub_one_eq_neg_finiteDilogOrder h)).orthogonal H,
          fixedBicharacter A (finiteDilogOrder A) y u *
            (finiteDilogE A τ (u + v) / finiteDilogEMinus A τ u) := by
  let M := fixedMetricGroup A (finiteDilogOrder A)
    (det_sub_one_eq_neg_finiteDilogOrder h)
  have hfiveM : ∀ u v : finiteDilogGroup A, v ≠ 0 →
      M.sqrtCard⁻¹ * ∑ x,
        M.bichar x u * (finiteDilogE A τ x / finiteDilogEMinus A τ (x + v)) =
      finiteDilogE A τ (u + v) /
        (finiteDilogEMinus A τ u * finiteDilogEMinus A τ v) := by
    intro u v hv
    have huv : ((u : Fin 2 → ZMod (finiteDilogOrder A)),
        (v : Fin 2 → ZMod (finiteDilogOrder A))) ≠ (0, 0) := by
      intro heq
      exact hv (Subtype.ext (congrArg Prod.snd heq))
    simpa only [M, fixedMetricGroup_sqrtCard, fixedMetricGroup_bichar,
      inv_eq_one_div, AddSubgroup.coe_add] using hfive u u.property v v.property huv
  have hsub := M.subgroupPentagon
    (E := fun x : finiteDilogGroup A => finiteDilogE A τ x)
    (Fm := fun x : finiteDilogGroup A => finiteDilogEMinus A τ x) hfiveM H y hv
  dsimp only [M] at hsub
  rw [fixedMetricGroup_sqrtCard] at hsub
  simpa only [fixedMetricGroup_bichar, AddSubgroup.coe_add, AddSubgroup.coe_sub] using hsub

/-! ### The dual pair of multiples and torsion

[AFK26, Appleby, Flammia, Kopp (2026), Section 5, proof of Theorem 1.2, `thm:tci`], up to
equation (7), `eq:tccproof2`, for any `R` commuting with `γ`, fixing `τ`, with `j_R(τ) > 0`, and
fixing the multiples `nG` pointwise; at an admissible tuple, `R = L_{z,t}^{-1}` and `n = d`. Take
`H = nG`, so `H^∨ = G[n]` (`MetricGroup.orthogonal_range_nsmul`), and `v = y - Ry ≠ 0`; then
`y ∉ H`. For `x ∈ H`, `x - y + v = R(x - y)` and `x - y ≠ 0`, so by the symmetry
`F⁻(Rz) = F⁻(z)` (`finiteDilogEMinus_ratVecAction`) and `F⁺ = F⁻` off zero each summand on the
left of the subgroup pentagon relation is `1`: the relation reads
`√N |H| = |H| F⁻(v)⁻¹ ∑_{u ∈ G[n]} ⟨y;u⟩ F⁺(u + v)/F⁻(u)`. The term `u = 0` is
`√j_γ(τ) F⁺(v)`, and `√j_γ(τ) - √N = 1/√j_γ(τ)` (`sqrt_finiteDilogOrder_eq`), which gives
(7). -/

/-- If `R` fixes `nG` and `v = y - Ry` is nonzero, then `y` lies outside `nG`; used by
`finiteDilogTorsionSum_eq_zero`. -/
private theorem torsionShift_not_mem_multiples {A : SL(2, ℤ)} (R : SL(2, ℤ)) (n : ℕ)
    (hfix : ∀ x ∈ finiteDilogGroup A,
      residueMulVec R (finiteDilogOrder A) (n • x) = n • x)
    {y v : finiteDilogGroup A}
    (hv : (v : Fin 2 → ZMod (finiteDilogOrder A)) =
      y - residueMulVec R (finiteDilogOrder A) y) (hv0 : v ≠ 0) :
    y ∉ (nsmulAddMonoidHom n : finiteDilogGroup A →+ finiteDilogGroup A).range := by
  rintro ⟨z, hz⟩
  change n • z = y at hz
  have hyfix : residueMulVec R (finiteDilogOrder A) y = y := by
    rw [← hz]
    exact hfix z z.property
  apply hv0
  apply Subtype.ext
  have hv' : (v : Fin 2 → ZMod (finiteDilogOrder A)) = 0 := by
    rw [hv, hyfix, sub_self]
  exact hv'

/-- Each left summand of the subgroup pentagon is `1` for the pair `(nG,G[n])`; used by
`finiteDilogTorsionSum_eq_zero`. -/
private theorem torsionPentagon_summand {A : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint A τ) (R : SL(2, ℤ))
    (hcomm : R * A * R⁻¹ = A) (hR : flt (R : Mat(2, ℤ)) τ = τ)
    (hjR : 0 < fltDenominator (R : Mat(2, ℤ)) τ) (n : ℕ)
    (hfix : ∀ x ∈ finiteDilogGroup A,
      residueMulVec R (finiteDilogOrder A) (n • x) = n • x)
    {y v : finiteDilogGroup A}
    (hv : (v : Fin 2 → ZMod (finiteDilogOrder A)) =
      y - residueMulVec R (finiteDilogOrder A) y)
    (hyH : y ∉ (nsmulAddMonoidHom n : finiteDilogGroup A →+ finiteDilogGroup A).range)
    {x : finiteDilogGroup A}
    (hx : x ∈ (nsmulAddMonoidHom n : finiteDilogGroup A →+ finiteDilogGroup A).range) :
    finiteDilogE A τ (x - y) / finiteDilogEMinus A τ (x - y + v) = 1 := by
  have hxmem := hx
  obtain ⟨z, hz⟩ := hx
  change n • z = x at hz
  have hxfix : residueMulVec R (finiteDilogOrder A) x =
      (x : Fin 2 → ZMod (finiteDilogOrder A)) := by
    rw [← hz]
    exact hfix z z.property
  have hxy0 : (x - y : finiteDilogGroup A) ≠ 0 := by
    intro hxy
    apply hyH
    have hxy' : x = y := sub_eq_zero.mp hxy
    simpa only [← hxy'] using hxmem
  have hxy0' : ((x - y : finiteDilogGroup A) :
      Fin 2 → ZMod (finiteDilogOrder A)) ≠ 0 := by
    intro heq
    exact hxy0 (Subtype.ext heq)
  have hRsub (a b : Fin 2 → ZMod (finiteDilogOrder A)) :
      residueMulVec R (finiteDilogOrder A) (a - b) =
        residueMulVec R (finiteDilogOrder A) a -
          residueMulVec R (finiteDilogOrder A) b := Matrix.mulVec_sub _ a b
  have harg : (x : Fin 2 → ZMod (finiteDilogOrder A)) - y + v =
      residueMulVec R (finiteDilogOrder A)
        ((x : Fin 2 → ZMod (finiteDilogOrder A)) - y) := by
    rw [hRsub, hxfix, hv]
    abel
  change finiteDilogE A τ ((x : Fin 2 → ZMod (finiteDilogOrder A)) - y) /
    finiteDilogEMinus A τ ((x : Fin 2 → ZMod (finiteDilogOrder A)) - y + v) = 1
  rw [harg]
  change finiteDilogE A τ (x - y : finiteDilogGroup A) /
    finiteDilogEMinus A τ
      (residueMulVec R (finiteDilogOrder A) (x - y : finiteDilogGroup A)) = 1
  rw [finiteDilogEMinus_ratVecAction h R hcomm hR hjR (x - y),
    finiteDilogEMinus_of_ne_zero h hxy0']
  exact div_self (finiteDilogE_ne_zero h (x - y).property)

/-- The left side of the subgroup pentagon for `H=nG` is `|H|`; used by
`finiteDilogTorsionSum_eq_zero`. -/
private theorem torsionPentagon_left_sum {A : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint A τ) [NeZero (finiteDilogOrder A)] (R : SL(2, ℤ))
    (hcomm : R * A * R⁻¹ = A) (hR : flt (R : Mat(2, ℤ)) τ = τ)
    (hjR : 0 < fltDenominator (R : Mat(2, ℤ)) τ) (n : ℕ)
    (hfix : ∀ x ∈ finiteDilogGroup A,
      residueMulVec R (finiteDilogOrder A) (n • x) = n • x)
    {y v : finiteDilogGroup A}
    (hv : (v : Fin 2 → ZMod (finiteDilogOrder A)) =
      y - residueMulVec R (finiteDilogOrder A) y) (hv0 : v ≠ 0) :
    (∑ x : finiteDilogGroup A with x ∈
        (nsmulAddMonoidHom n : finiteDilogGroup A →+ finiteDilogGroup A).range,
      finiteDilogE A τ (x - y) / finiteDilogEMinus A τ (x - y + v)) =
        (Nat.card (nsmulAddMonoidHom n :
          finiteDilogGroup A →+ finiteDilogGroup A).range : ℂ) := by
  classical
  have hyH := torsionShift_not_mem_multiples R n hfix hv hv0
  calc
    _ = ∑ x : finiteDilogGroup A with x ∈
          (nsmulAddMonoidHom n : finiteDilogGroup A →+ finiteDilogGroup A).range,
          (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact torsionPentagon_summand h R hcomm hR hjR n hfix hv hyH
        (Finset.mem_filter.mp hx).2
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The subgroup pentagon for `H=nG`, after cancelling `|H|`; used by
`finiteDilogTorsionSum_eq_zero`. -/
private theorem torsionPentagon_minus_sum {A : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint A τ) [NeZero (finiteDilogOrder A)]
    (hfive : FiniteDilogFiveTerm A τ) (n : ℕ) {y v : finiteDilogGroup A} (hv0 : v ≠ 0)
    (hleftSum :
      (∑ x : finiteDilogGroup A with x ∈
          (nsmulAddMonoidHom n : finiteDilogGroup A →+ finiteDilogGroup A).range,
        finiteDilogE A τ (x - y) / finiteDilogEMinus A τ (x - y + v)) =
          (Nat.card (nsmulAddMonoidHom n :
            finiteDilogGroup A →+ finiteDilogGroup A).range : ℂ)) :
    (Real.sqrt (finiteDilogOrder A) : ℂ) = (finiteDilogEMinus A τ v)⁻¹ *
      ∑ u : finiteDilogGroup A with n • u = 0,
        fixedBicharacter A (finiteDilogOrder A) y u *
          (finiteDilogE A τ (u + v : finiteDilogGroup A) /
            finiteDilogEMinus A τ u) := by
  classical
  let G := finiteDilogGroup A
  let N := finiteDilogOrder A
  let H : AddSubgroup G := (nsmulAddMonoidHom n).range
  let M := fixedMetricGroup A N (det_sub_one_eq_neg_finiteDilogOrder h)
  have horth : M.orthogonal H = (nsmulAddMonoidHom n : G →+ G).ker :=
    M.orthogonal_range_nsmul n
  have hp := finiteDilogSubgroupPentagon h hfive H y hv0
  have hp' : (Real.sqrt N : ℂ) * (Nat.card H : ℂ) =
      (Nat.card H : ℂ) * (finiteDilogEMinus A τ v)⁻¹ *
        ∑ u : G with n • u = 0,
          fixedBicharacter A N y u *
            (finiteDilogE A τ (u + v : G) / finiteDilogEMinus A τ u) := by
    convert hp using 1
    · congr 1
      calc
        (Nat.card H : ℂ) = ∑ x : G with x ∈ H,
            finiteDilogE A τ (x - y) / finiteDilogEMinus A τ (x - y + v) := hleftSum.symm
        _ = _ := by
          apply Finset.sum_congr (by ext x; simp)
          intro x _
          rfl
    · congr 1
      apply Finset.sum_congr
      · ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        change n • u = 0 ↔ u ∈ M.orthogonal H
        rw [horth, AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
      · intro u _
        simp only [N, AddSubgroup.coe_add]
  apply mul_left_cancel₀ (M.card_subgroup_ne_zero H)
  calc
    (Nat.card H : ℂ) * (Real.sqrt N : ℂ) =
        (Real.sqrt N : ℂ) * (Nat.card H : ℂ) := mul_comm _ _
    _ = (Nat.card H : ℂ) * (finiteDilogEMinus A τ v)⁻¹ *
        ∑ u : G with n • u = 0,
          fixedBicharacter A N y u *
            (finiteDilogE A τ (u + v : G) / finiteDilogEMinus A τ u) := hp'
    _ = _ := by ring

/-- The zero term changes by `√N E(v)` when `F⁻(0)` is replaced by `E(0)`; used by
`torsionPentagon_sum_correction`. -/
private theorem torsionPentagon_zero_term {A : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint A τ) (y v : finiteDilogGroup A) :
    fixedBicharacter A (finiteDilogOrder A) y (0 : finiteDilogGroup A) *
        (finiteDilogE A τ (0 + v : finiteDilogGroup A) /
          finiteDilogEMinus A τ (0 : finiteDilogGroup A)) =
      fixedBicharacter A (finiteDilogOrder A) y (0 : finiteDilogGroup A) *
        (finiteDilogE A τ (0 + v : finiteDilogGroup A) /
          finiteDilogE A τ (0 : finiteDilogGroup A)) +
        (Real.sqrt (finiteDilogOrder A) : ℂ) * finiteDilogE A τ v := by
  have hzero : finiteDilogEMinus A τ (0 : finiteDilogGroup A) =
      (finiteDilogE A τ (0 : finiteDilogGroup A))⁻¹ := by
    simp [finiteDilogE_zero, finiteDilogEMinus_zero]
  have hroot : finiteDilogE A τ (0 : finiteDilogGroup A) -
      (finiteDilogE A τ (0 : finiteDilogGroup A))⁻¹ =
        (Real.sqrt (finiteDilogOrder A) : ℂ) := by
    change finiteDilogE A τ (0 : Fin 2 → ZMod (finiteDilogOrder A)) -
      (finiteDilogE A τ (0 : Fin 2 → ZMod (finiteDilogOrder A)))⁻¹ =
        (Real.sqrt (finiteDilogOrder A) : ℂ)
    rw [finiteDilogE_zero]
    exact_mod_cast (sqrt_finiteDilogOrder_eq h).symm
  have hb : fixedBicharacter A (finiteDilogOrder A) y (0 : finiteDilogGroup A) = 1 := by
    rw [fixedBicharacter_comm]
    exact fixedBicharacter_zero_left A (finiteDilogOrder A) y
  simp only [hb, one_mul, zero_add]
  rw [hzero, div_inv_eq_mul, div_eq_mul_inv]
  rw [← hroot]
  ring

/-- Only the zero torsion term distinguishes the `F⁻` and `E` denominators; used by
`finiteDilogTorsionSum_eq_zero`. -/
private theorem torsionPentagon_sum_correction {A : SL(2, ℤ)} {τ : ℝ}
    (h : IsAttractiveFixedPoint A τ) [NeZero (finiteDilogOrder A)] (n : ℕ)
    (y v : finiteDilogGroup A) :
    (∑ u : finiteDilogGroup A with n • u = 0,
      fixedBicharacter A (finiteDilogOrder A) y u *
        (finiteDilogE A τ (u + v : finiteDilogGroup A) / finiteDilogEMinus A τ u)) =
      (∑ u : finiteDilogGroup A with n • u = 0,
        fixedBicharacter A (finiteDilogOrder A) y u *
          (finiteDilogE A τ (u + v : finiteDilogGroup A) / finiteDilogE A τ u)) +
        (Real.sqrt (finiteDilogOrder A) : ℂ) * finiteDilogE A τ v := by
  classical
  calc
    _ = ∑ u : finiteDilogGroup A with n • u = 0,
          (fixedBicharacter A (finiteDilogOrder A) y u *
            (finiteDilogE A τ (u + v : finiteDilogGroup A) / finiteDilogE A τ u) +
            if u = 0 then (Real.sqrt (finiteDilogOrder A) : ℂ) * finiteDilogE A τ v
              else 0) := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : u = 0
      · subst u
        simpa only [ite_true] using torsionPentagon_zero_term h y v
      · simp only [hu, ite_false, add_zero]
        have hu' : (u : Fin 2 → ZMod (finiteDilogOrder A)) ≠ 0 := by
          intro heq
          exact hu (Subtype.ext heq)
        rw [finiteDilogEMinus_of_ne_zero h hu']
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp

/-- **[AFK26, Appleby, Flammia, Kopp (2026), Section 5, equation (7), `eq:tccproof2`]**: for `R`
commuting with `γ`, fixing `τ` with `j_R(τ) > 0`, and fixing every multiple `nx`, `x ∈ G`, and for
`y ∈ G` with `v = y - Ry ≠ 0`,
`∑_{u ∈ G[n]} ⟨y; u⟩ F⁺(u + v)/F⁺(u) = 0`. -/
theorem finiteDilogTorsionSum_eq_zero {A : SL(2, ℤ)} {τ : ℝ} (h : IsAttractiveFixedPoint A τ)
    [NeZero (finiteDilogOrder A)] (hfive : FiniteDilogFiveTerm A τ) {R : SL(2, ℤ)}
    (hcomm : R * A * R⁻¹ = A) (hR : flt (R : Mat(2, ℤ)) τ = τ)
    (hjR : 0 < fltDenominator (R : Mat(2, ℤ)) τ) (n : ℕ)
    (hfix : ∀ x ∈ finiteDilogGroup A,
      residueMulVec R (finiteDilogOrder A) (n • x) = n • x)
    {y v : finiteDilogGroup A}
    (hv : (v : Fin 2 → ZMod (finiteDilogOrder A)) =
      y - residueMulVec R (finiteDilogOrder A) y) (hv0 : v ≠ 0) :
    ∑ u : finiteDilogGroup A with n • u = 0,
      fixedBicharacter A (finiteDilogOrder A) y u *
        (finiteDilogE A τ (u + v : finiteDilogGroup A) / finiteDilogE A τ u) = 0 := by
  let G := finiteDilogGroup A
  let N := finiteDilogOrder A
  have hsum := torsionPentagon_minus_sum h hfive n hv0
    (torsionPentagon_left_sum h R hcomm hR hjR n hfix hv hv0)
  have hsplit := torsionPentagon_sum_correction h n y v
  have hv' : (v : Fin 2 → ZMod N) ≠ 0 := by
    intro heq
    exact hv0 (Subtype.ext heq)
  have hFmne := finiteDilogEMinus_ne_zero h v.property
  have hvalue :
      (∑ u : G with n • u = 0,
        fixedBicharacter A N y u *
          (finiteDilogE A τ (u + v : G) / finiteDilogEMinus A τ u)) =
            (Real.sqrt N : ℂ) * finiteDilogE A τ v := by
    calc
      _ = finiteDilogEMinus A τ v * ((finiteDilogEMinus A τ v)⁻¹ *
            ∑ u : G with n • u = 0,
              fixedBicharacter A N y u *
                (finiteDilogE A τ (u + v : G) / finiteDilogEMinus A τ u)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hFmne, one_mul]
      _ = _ := by rw [← hsum, finiteDilogEMinus_of_ne_zero h hv']; ring
  rw [hsplit] at hvalue
  linear_combination hvalue

end SIC
