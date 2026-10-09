/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.Pseudolattice.Homothety

/-!
# Nested pseudolattices

For pseudolattices `I ⊆ J` with admissible bases, the integer matrix `B` of positive determinant
carrying the characteristics on `I` to those on `J`, with `B·β_I = β_J` and `Bγ_I = γ_J B` for a
common period; sets of representatives of `J/I`; the periods of intermediate lattices; and the
existence of an admissible basis of every lattice between `I` and `n⁻¹I`.

This module supplies the lattice side of [RW26b, Radchenko, Wheeler (2026b), Proposition 3(ii)
and Appendix A]: there `J = ℤτ + ℤ` and `I = ℤ(nτ + k) + ℤm` after division by `β₂`, and the
matrix `[[n, k], [0, m]]` intertwines the period matrices `γ_I`, `γ_J`. Here the lattices keep
arbitrary admissible bases and `B` is any integer matrix with `B(τ_I, 1)ᵀ = j(τ_J, 1)ᵀ`; its
reduction to upper-triangular form is done once, in the cocycle layer
(`exists_eq_upperTriangular_mul_of_mem_Gf`). The consumer is
`SICs.Dilogarithm.Pseudolattice.Distribution`.

## The argument

*The inclusion matrix.* The vectors of `B.basis` are `β₂^Iτ_I` and `β₂^I` (`coe_basis`). Thus
`I ⊆ J` puts them in `J = β₂^J(ℤτ_J + ℤ)`, so
`M(τ_J, 1)ᵀ = (β₂^I/β₂^J)(τ_I, 1)ᵀ` for an integer `M` (`exists_pairMap_of_mem_span`), and its
adjugate `B` satisfies `B(τ_I, 1)ᵀ = (det M · β₂^J/β₂^I)(τ_J, 1)ᵀ`. Both bases are oriented and
both scales totally positive, so the orientation identity (`IsPairMap.det_mul_sub_eq`) makes
`det B = det M > 0`.

*Characteristics and fixed points.* With `x = β₂⟨⟨r, τ⟩⟩` on either basis, the covariance
`⟨⟨Br, B·τ⟩⟩ = det B ⟨⟨r, τ⟩⟩/j_B(τ)` (`fracSymplecticFormRat_ratVecAction`) gives
`r_J(x) = B r_I(x)`; the first place of `B·τ_I = τ_J` gives `B·β_I = β_J`, and
`j_B(β_I) = det B · ρ₁(β₂^J/β₂^I) > 0`. If `ε` is a period of both lattices,
`Bγ_I(τ_I, 1)ᵀ` and `γ_J B(τ_I, 1)ᵀ` are both `ε j (τ_J, 1)ᵀ`, so the integer matrices `Bγ_I` and
`γ_J B` agree (`IsPairMap.conj`).

*Intermediate lattices.* If `I ⊆ J` and `(ε - 1)J ⊆ I`, then `εy = y + (ε - 1)y ∈ J` for `y ∈ J`,
so a period of `I` is a period of every admissible basis of `J`. A lattice `J` with
`I ⊆ J ⊆ n⁻¹I` is free of rank two; among its primitive vectors some is totally positive (the
totally positive cone is open and contains `β₂^I`), and completing it to an oriented basis gives
an admissible basis. A set of representatives of `J/I` exists since `J/I` embeds in the finite
group `n⁻¹I/I`.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
variable {F : RealQuadraticFieldData K}

/-! ### Representatives of `J/I`

A finite set containing exactly one representative of each class of `J` modulo `I`. -/

/-- **A set of representatives of `J/I`**: a finite `T ⊆ J` meeting every class of `J` modulo
`I` exactly once. It stands for the subgroup `H = J/I ⊆ K/I` over which the product of
[RW26b, Radchenko, Wheeler (2026b), Proposition 3(ii), equation (11)] runs. -/
structure IsQuotientTransversal (I J : Submodule ℤ K) (T : Finset K) : Prop where
  /-- Every member lies in `J`. -/
  mem : ∀ t ∈ T, t ∈ J
  /-- Members are pairwise incongruent modulo `I`. -/
  eq_of_sub_mem : ∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ I → t = t'
  /-- Every class of `J` modulo `I` has a member. -/
  exists_mem : ∀ y ∈ J, ∃ t ∈ T, y - t ∈ I

/-- **Orbit representatives of a fibre** of `K/I → K/J` under multiplication by `ε`: a finite set
`Y` of lifts of `x` modulo `J` with lengths `m(y) ≥ 1` such that `ε^{m(y)}y ≡ y (mod I)` and the
points `εʲy`, `y ∈ Y`, `j < m(y)`, represent each class of `x + J` modulo `I` exactly once. It
is the set `ℛ_x` of one representative of each `ε`-orbit in `π⁻¹(x)`, with the orbit lengths
`r_y`, of [RW26b, Radchenko, Wheeler (2026b), Proposition 3(i)]. -/
structure IsOrbitTransversal (I J : Submodule ℤ K) (ε x : K) (Y : Finset K) (m : K → ℕ+) :
    Prop where
  /-- Every member lies over `x`: `y - x ∈ J`. -/
  sub_mem : ∀ y ∈ Y, y - x ∈ J
  /-- `ε^{m(y)}y ≡ y (mod I)`. -/
  period : ∀ y ∈ Y, ε ^ (m y : ℕ) * y - y ∈ I
  /-- Every class of `x + J` modulo `I` is that of some `εʲy` with `j < m(y)`. -/
  exists_pow : ∀ z, z - x ∈ J → ∃ y ∈ Y, ∃ j < (m y : ℕ), z - ε ^ j * y ∈ I
  /-- The points `εʲy` with `j < m(y)` are pairwise incongruent modulo `I`. -/
  pow_injective : ∀ y ∈ Y, ∀ y' ∈ Y, ∀ j < (m y : ℕ), ∀ j' < (m y' : ℕ),
    ε ^ j * y - ε ^ j' * y' ∈ I → y = y' ∧ j = j'

namespace PseudolatticeBasis

/-- The two displayed generators form a basis of a pseudolattice; this supplies the rank
calculation in `exists_isQuotientTransversal`. -/
def basis (B : PseudolatticeBasis F) :
    Module.Basis (Fin 2) ℤ B.submodule := by
  let v : Fin 2 → K := ![B.scale * B.tau, B.scale]
  have hv : LinearIndependent ℤ v := by
    apply (Fintype.linearIndependent_iff).2
    intro g hg i
    have hsum : (g 0 : K) * (B.scale * B.tau) + (g 1 : K) * B.scale = 0 := by
      simpa [v, Fin.sum_univ_two, zsmul_eq_mul] using hg
    have hlin : (g 0 : K) * B.tau + (g 1 : K) = 0 := by
      have hh : B.scale * ((g 0 : K) * B.tau + (g 1 : K)) = 0 := by
        convert hsum using 1; ring
      exact (mul_eq_zero.mp hh).resolve_left B.scale_ne_zero
    have hf := congrArg (realEmbeddingAt K F.place) hlin
    have ho := congrArg (realEmbeddingAt K F.otherPlace) hlin
    simp only [map_add, map_mul, map_intCast, map_zero] at hf ho
    have hg0R : (g 0 : ℝ) = 0 := by
      have hmul : (g 0 : ℝ) *
          (realEmbeddingAt K F.place B.tau - realEmbeddingAt K F.otherPlace B.tau) = 0 := by
        nlinarith [hf, ho]
      exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr B.other_lt.ne')
    have hg0 : g 0 = 0 := by exact_mod_cast hg0R
    have hg1 : g 1 = 0 := by
      simp only [hg0, Int.cast_zero, zero_mul, zero_add] at hlin
      exact_mod_cast hlin
    fin_cases i
    · exact hg0
    · exact hg1
  have hrange : Set.range v = {B.scale * B.tau, B.scale} := by
    ext x
    simp [v, or_comm]
  change Module.Basis (Fin 2) ℤ (Submodule.span ℤ {B.scale * B.tau, B.scale})
  rw [← hrange]
  exact Module.Basis.span hv

omit [NumberField K] [NumberField.IsTotallyReal K] in
/-- Transporting a basis across an equality of submodules preserves its ambient vectors. -/
private theorem basis_cast_coe {S T : Submodule ℤ K} (h : S = T)
    (b : Module.Basis (Fin 2) ℤ T) (i : Fin 2) :
    ((Eq.mpr (congrArg (fun U : Submodule ℤ K => Module.Basis (Fin 2) ℤ U) h) b i : S) : K) =
      (b i : K) := by
  cases h
  rfl

/-- The ambient vectors of a pseudolattice basis are `β₂τ` and `β₂`. -/
theorem coe_basis (B : PseudolatticeBasis F) (i : Fin 2) :
    (B.basis i : K) = ![B.scale * B.tau, B.scale] i := by
  let v : Fin 2 → K := ![B.scale * B.tau, B.scale]
  have hrange : Set.range v = {B.scale * B.tau, B.scale} := by
    ext x
    simp [v, or_comm]
  have hspan : B.submodule = Submodule.span ℤ (Set.range v) := by
    rw [hrange]
    rfl
  unfold PseudolatticeBasis.basis
  dsimp only [id]
  apply Eq.trans (basis_cast_coe hspan _ i)
  simp only [Module.Basis.coe_span_apply]

/-- **Representatives of `J/I` exist** for nested pseudolattices `I ⊆ J`: the quotient `J/I` is
finite. -/
theorem exists_isQuotientTransversal {B B' : PseudolatticeBasis F}
    (hle : B.submodule ≤ B'.submodule) :
    ∃ T : Finset K, IsQuotientTransversal B.submodule B'.submodule T := by
  classical
  let N : Submodule ℤ B'.submodule := B.submodule.comap B'.submodule.subtype
  have hrank : Module.finrank ℤ N = Module.finrank ℤ B'.submodule := by
    calc
      _ = Module.finrank ℤ B.submodule :=
        (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
      _ = 2 := by simpa using (Module.finrank_eq_card_basis (basis B))
      _ = _ := by simpa using (Module.finrank_eq_card_basis (basis B')).symm
  have : Module.Free ℤ B'.submodule := Module.Free.of_basis (basis B')
  have : Module.Finite ℤ B'.submodule := Module.Finite.of_basis (basis B')
  have : Finite (B'.submodule ⧸ N) := Submodule.finiteQuotientOfFreeOfRankEq N hrank
  let : Fintype (B'.submodule ⧸ N) := Fintype.ofFinite _
  let rep (q : B'.submodule ⧸ N) : K := (Quotient.out q).val
  let T : Finset K := Finset.univ.image rep
  refine ⟨T, ?_⟩
  constructor
  · intro t ht
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp ht
    exact (Quotient.out q).property
  · intro t ht t' ht' hsub
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨q', _, rfl⟩ := Finset.mem_image.mp ht'
    have hN : (Quotient.out q : B'.submodule) - Quotient.out q' ∈ N := by
      simpa [N, rep] using hsub
    have hq : q = q' := by
      have heq := (Submodule.Quotient.eq N).mpr hN
      simpa only [Submodule.Quotient.mk_out] using heq
    simp [hq]
  · intro y hy
    let q : B'.submodule ⧸ N := Submodule.Quotient.mk ⟨y, hy⟩
    refine ⟨rep q, Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩, ?_⟩
    have hq : (Submodule.Quotient.mk (Quotient.out q) : B'.submodule ⧸ N) =
        Submodule.Quotient.mk (⟨y, hy⟩ : B'.submodule) := by
      exact Submodule.Quotient.mk_out q
    have hN : (⟨y, hy⟩ : B'.submodule) - Quotient.out q ∈ N :=
      (Submodule.Quotient.eq N).mp hq.symm
    simpa [N, rep] using hN

/-! ### The inclusion matrix

`B(τ_I, 1)ᵀ = j(τ_J, 1)ᵀ` with `det B > 0`, carrying characteristics, fixed points, and period
matrices from `I` to `J`. -/

omit [NumberField K] [NumberField.IsTotallyReal K] in
/-- The adjugate reverses a pair map after dividing its determinant by the original scale;
this is the algebraic step in `exists_inclusionMatrix`. -/
private theorem pairMap_adjugate {τ τ' j : K} {A : Mat(2, ℤ)}
    (hj : j ≠ 0) (hA : IsPairMap A τ j τ') :
    IsPairMap A.adjugate τ' ((A.det : K) / j) τ := by
  have h0 := hA.first_row
  have h1 := hA.denominator_eq
  unfold IsPairMap fltDenominator at *
  rw [Matrix.adjugate_fin_two, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  constructor
  · field_simp [hj]
    push_cast
    linear_combination -(A 1 1 : K) * h0 + (A 0 1 : K) * h1
  · field_simp [hj]
    push_cast
    linear_combination (A 1 0 : K) * h0 - (A 0 0 : K) * h1

/-- **The inclusion matrix of nested pseudolattices** [RW26b, Radchenko, Wheeler (2026b),
Appendix A]: for `I ⊆ J` there is an integer `B` with `det B > 0` and
`B(τ_I, 1)ᵀ = (det B · β₂^J/β₂^I)(τ_J, 1)ᵀ`, the adjugate of the matrix expressing the basis of `I`
in that of `J`. -/
theorem exists_inclusionMatrix {B B' : PseudolatticeBasis F}
    (hle : B.submodule ≤ B'.submodule) :
    ∃ M : Mat(2, ℤ), 0 < M.det ∧
      IsPairMap M B.tau ((M.det : K) * B'.scale / B.scale) B'.tau := by
  have hfirst : B.scale * B.tau ∈ B'.submodule :=
    hle (Submodule.subset_span (by simp : B.scale * B.tau ∈ {B.scale * B.tau, B.scale}))
  have hsecond : B.scale ∈ B'.submodule :=
    hle (Submodule.subset_span (by simp : B.scale ∈ {B.scale * B.tau, B.scale}))
  obtain ⟨A, hA⟩ := exists_pairMap_of_mem_span B'.scale_ne_zero hfirst hsecond
  have hjf : 0 < realEmbeddingAt K F.place (B.scale / B'.scale) := by
    rw [map_div₀]
    exact div_pos B.scale_pos.1 B'.scale_pos.1
  have hjg : 0 < realEmbeddingAt K F.otherPlace (B.scale / B'.scale) := by
    rw [map_div₀]
    exact div_pos B.scale_pos.2 B'.scale_pos.2
  have hdR : 0 < (A.det : ℝ) := by
    have horient := hA.det_mul_sub_eq F
    have hprod : 0 < (A.det : ℝ) *
        (realEmbeddingAt K F.place B'.tau - realEmbeddingAt K F.otherPlace B'.tau) := by
      rw [horient]
      exact mul_pos (mul_pos hjf hjg) (sub_pos.mpr B.other_lt)
    exact (mul_pos_iff_of_pos_right (sub_pos.mpr B'.other_lt)).mp hprod
  have hd : 0 < A.det := by exact_mod_cast hdR
  have hAdj : A.adjugate.det = A.det := by
    simpa using (Matrix.det_adjugate A)
  refine ⟨A.adjugate, hAdj ▸ hd, ?_⟩
  rw [hAdj]
  convert pairMap_adjugate (div_ne_zero B.scale_ne_zero B'.scale_ne_zero) hA using 1
  field_simp [B.scale_ne_zero, B'.scale_ne_zero]

variable {B B' : PseudolatticeBasis F} {M : Mat(2, ℤ)}

/-- **The characteristic under an inclusion**: `r_J(x) = B r_I(x)` for the inclusion matrix `B`;
the integral form of `characteristic_eq_ratVecAction_of_isPairMap`. -/
theorem characteristic_eq_ratVecAction_of_inclusion (hdet : 0 < M.det)
    (hM : IsPairMap M B.tau ((M.det : K) * B'.scale / B.scale) B'.tau) (x : K) :
    B'.characteristic x = ratVecAction M (B.characteristic x) := by
  apply B'.characteristic_eq_of_eq
  have hd : (M.det : K) ≠ 0 := by exact_mod_cast hdet.ne'
  have hj : (M.det : K) * B'.scale / B.scale ≠ 0 :=
    div_ne_zero (mul_ne_zero hd B'.scale_ne_zero) B.scale_ne_zero
  have hcov := fracSymplecticFormRat_ratVecAction M
    (B.characteristic x) B.tau (hM.denominator_eq.symm ▸ hj)
  rw [hM.flt_eq hj, hM.denominator_eq,
    B.fracSymplecticFormRat_characteristic] at hcov
  calc
    _ = (M.det : K) * (x / B.scale) / ((M.det : K) * B'.scale / B.scale) := hcov
    _ = x / B'.scale := by field_simp [hd, B.scale_ne_zero, B'.scale_ne_zero]

/-- **The fixed point under an inclusion**: `β_J = B·β_I`. -/
theorem beta_eq_flt_of_inclusion (hdet : 0 < M.det)
    (hM : IsPairMap M B.tau ((M.det : K) * B'.scale / B.scale) B'.tau) :
    B'.beta = flt M B.beta := by
  have hj : (M.det : K) * B'.scale / B.scale ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (by exact_mod_cast hdet.ne') B'.scale_ne_zero)
      B.scale_ne_zero
  have hf := congrArg (realEmbeddingAt K F.place) (hM.flt_eq hj)
  simpa only [PseudolatticeBasis.beta, map_flt] using hf.symm

/-- **The Jacobi denominator of an inclusion is positive**: `j_B(β_I) > 0`, since it is the first
place of `det B · β₂^J/β₂^I`. -/
theorem fltDenominator_pos_of_inclusion (hdet : 0 < M.det)
    (hM : IsPairMap M B.tau ((M.det : K) * B'.scale / B.scale) B'.tau) :
    0 < fltDenominator M B.beta := by
  change 0 < fltDenominator M (realEmbeddingAt K F.place B.tau)
  rw [← map_fltDenominator, hM.denominator_eq, map_div₀, map_mul]
  have hd : 0 < (realEmbeddingAt K F.place) (M.det : K) := by
    simpa only [map_intCast] using (show (0 : ℝ) < (M.det : ℝ) from by exact_mod_cast hdet)
  exact div_pos (mul_pos hd B'.scale_pos.1) B.scale_pos.1

/-- **The inclusion matrix intertwines the period matrices**: `Bγ_I = γ_J B` for a common period
`ε` [RW26b, Radchenko, Wheeler (2026b), Appendix A], where it reads
`γ_I [[n,k],[0,m]] = [[n,k],[0,m]] γ_J`. -/
theorem IsPeriod.inclusionMatrix_mul {ε : K} (h : B.IsPeriod ε) (h' : B'.IsPeriod ε)
    (hM : IsPairMap M B.tau ((M.det : K) * B'.scale / B.scale) B'.tau) :
    M * (h.matrix : Mat(2, ℤ)) = (h'.matrix : Mat(2, ℤ)) * M := by
  exact (IsPairMap.conj B.beta_irrational hM h.isPairMap_matrix
    h'.isPairMap_matrix).symm

/-! ### Intermediate lattices

Periods pass to lattices between `I` and `(ε - 1)⁻¹I`, and every lattice between `I` and `n⁻¹I`
has an admissible basis. -/

/-- **A period passes to an intermediate lattice** [RW26b, Radchenko, Wheeler (2026b),
Proposition 3(ii)]: if `I ⊆ J` and `(ε - 1)J ⊆ I`, then `εJ ⊆ J`, so a period of `I` is a period
of `J`. -/
theorem IsPeriod.of_le {ε : K} (h : B.IsPeriod ε) (hle : B.submodule ≤ B'.submodule)
    (hJ : ∀ y ∈ B'.submodule, (ε - 1) * y ∈ B.submodule) : B'.IsPeriod ε := by
  have hmul (y : K) (hy : y ∈ B'.submodule) : ε * y ∈ B'.submodule := by
    have hdiff := hle (hJ y hy)
    convert B'.submodule.add_mem hy hdiff using 1; ring
  exact h.of_mul_mem hmul

/-- A lattice sandwiched between `I` and `n⁻¹I` has an integral basis of rank two; the
basis calculation used in `exists_submodule_eq`. -/
private theorem exists_integralBasis_of_sandwich {J : Submodule ℤ K}
    (hle : B.submodule ≤ J) {n : ℕ} (hn : n ≠ 0)
    (hJ : ∀ y ∈ J, (n : K) * y ∈ B.submodule) :
    Nonempty (Module.Basis (Fin 2) ℤ J) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hc : F.IsTotallyPositive ((n : K)⁻¹) := by
    constructor <;> simpa only [map_inv₀, map_natCast] using inv_pos.mpr hnpos
  let S := B.smul ((n : K)⁻¹) hc
  have hJsuper : J ≤ S.submodule := by
    intro y hy
    apply (B.mem_smul_submodule_iff hc y).mpr
    refine ⟨(n : K) * y, hJ y hy, ?_⟩
    field_simp [show (n : K) ≠ 0 from by exact_mod_cast hn]
  obtain ⟨m, bJ⟩ := Submodule.basisOfPidOfLE hJsuper (basis S)
  have hJfinite : Module.Finite ℤ J := Module.Finite.of_basis bJ
  have hSfinite : Module.Finite ℤ S.submodule := Module.Finite.of_basis (basis S)
  have hrank : Module.finrank ℤ J = 2 := by
    have hlow := Submodule.finrank_mono hle
    have hup := Submodule.finrank_mono hJsuper
    have hBrank : Module.finrank ℤ B.submodule = 2 := by
      simpa using (Module.finrank_eq_card_basis (basis B))
    have hSrank : Module.finrank ℤ S.submodule = 2 := by
      simpa using (Module.finrank_eq_card_basis (basis S))
    omega
  have hm : m = 2 := by
    have hb := Module.finrank_eq_card_basis bJ
    simpa [hrank] using hb.symm
  subst m
  exact ⟨bJ⟩

omit [NumberField K] [NumberField.IsTotallyReal K] in
/-- Bézout coefficients make a vector with coprime basis coordinates unimodular; this
supplies the primitive vector in `exists_positive_primitive`. -/
private theorem unimodular_basis_combo {J : Submodule ℤ K}
    (bJ : Module.Basis (Fin 2) ℤ J) (a b α β : ℤ)
    (hcoeff : a * α + b * β = 1) :
    Module.IsUnimodular ℤ (a • bJ 0 + b • bJ 1) := by
  let w : J := a • bJ 0 + b • bJ 1
  let φ : J →ₗ[ℤ] ℤ :=
    α • ((LinearMap.proj (R := ℤ) (φ := fun _ : Fin 2 => ℤ) 0).comp
      bJ.equivFun.toLinearMap) +
    β • ((LinearMap.proj (R := ℤ) (φ := fun _ : Fin 2 => ℤ) 1).comp
      bJ.equivFun.toLinearMap)
  have hwcoords : bJ.equivFun w = ![a, b] := by
    have hwsum : w = ∑ i : Fin 2, (![a, b] i) • bJ i := by
      simp [w, Fin.sum_univ_two]
    rw [hwsum, Module.Basis.equivFun_apply, bJ.repr_sum_self]
  have hφw : φ w = 1 := by
    simp only [φ, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, LinearEquiv.coe_coe, hwcoords]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      smul_eq_mul, mul_comm] using hcoeff
  exact ⟨φ, hφw⟩

/-- Positive integer multiples preserve total positivity in both directions; this is the
positivity step in `exists_positive_primitive`. -/
private theorem totallyPositive_of_nsmul {J : Submodule ℤ K} {v w : J} {d : ℕ}
    (hd : d ≠ 0) (hvw : v = (d : ℤ) • w)
    (hvpos : F.IsTotallyPositive (v : K)) : F.IsTotallyPositive (w : K) := by
  have hwval : (v : K) = (d : K) * (w : K) := by
    have := congrArg Subtype.val hvw
    simpa [zsmul_eq_mul] using this
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
  constructor
  · have hh := hvpos.1
    rw [hwval, map_mul, map_natCast] at hh
    exact (mul_pos_iff_of_pos_left hdpos).mp hh
  · have hh := hvpos.2
    rw [hwval, map_mul, map_natCast] at hh
    exact (mul_pos_iff_of_pos_left hdpos).mp hh

/-- A totally positive lattice vector has a totally positive primitive divisor; the
primitive vector used in `exists_submodule_eq`. -/
private theorem exists_positive_primitive {J : Submodule ℤ K}
    (bJ : Module.Basis (Fin 2) ℤ J) (v : J)
    (hvpos : F.IsTotallyPositive (v : K)) :
    ∃ w : J, F.IsTotallyPositive (w : K) ∧ Module.IsUnimodular ℤ w := by
  let a : ℤ := (bJ.repr v) 0
  let b : ℤ := (bJ.repr v) 1
  let d : ℕ := a.gcd b
  have hd : d ≠ 0 := by
    intro hd
    obtain ⟨ha, hb⟩ := Int.gcd_eq_zero_iff.mp hd
    have hz : bJ.repr v = 0 := by
      ext i
      fin_cases i
      · exact ha
      · exact hb
    have hv : v = 0 := bJ.repr.injective (by simpa using hz)
    apply hvpos.ne_zero
    exact congrArg Subtype.val hv
  have hdI : (d : ℤ) ≠ 0 := by exact_mod_cast hd
  obtain ⟨a', ha'⟩ := Int.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ := Int.gcd_dvd_right a b
  let w : J := a' • bJ 0 + b' • bJ 1
  have hvw : v = (d : ℤ) • w := by
    have hvrepr := bJ.sum_repr v
    simp only [Fin.sum_univ_two] at hvrepr
    calc
      v = a • bJ 0 + b • bJ 1 := hvrepr.symm
      _ = (d : ℤ) • w := by
        simpa only [w, smul_add, ← mul_smul] using
          congrArg₂ (fun x y : ℤ => x • bJ 0 + y • bJ 1) ha' hb'
  have hwpos : F.IsTotallyPositive (w : K) := totallyPositive_of_nsmul hd hvw hvpos
  have hcoeff : a' * a.gcdA b + b' * a.gcdB b = 1 := by
    apply mul_left_cancel₀ hdI
    calc
      (d : ℤ) * (a' * a.gcdA b + b' * a.gcdB b) =
          a * a.gcdA b + b * a.gcdB b := by linear_combination -(a.gcdA b) * ha' - (a.gcdB b) * hb'
      _ = (d : ℤ) := (Int.gcd_eq_gcd_ab a b).symm
      _ = (d : ℤ) * 1 := by ring
  have hwunimodular : Module.IsUnimodular ℤ w :=
    unimodular_basis_combo bJ a' b' (a.gcdA b) (a.gcdB b) hcoeff
  exact ⟨w, hwpos, hwunimodular⟩

omit [NumberField K] [NumberField.IsTotallyReal K] in
/-- The two values of a basis of `J` generate `J` as a submodule of `K`; this is used to
construct the admissible basis in `exists_admissible_of_positive_basis`. -/
private theorem span_eq_of_basis {J : Submodule ℤ K} (e : Module.Basis (Fin 2) ℤ J) :
    Submodule.span ℤ {(e 1 : K), (e 0 : K)} = J := by
  let p : K := (e 0 : J).val
  let q : K := (e 1 : J).val
  change Submodule.span ℤ {q, p} = J
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact (e 1).property
    · rw [Set.mem_singleton_iff.mp hx]
      exact (e 0).property
  · intro y hy
    let yy : J := ⟨y, hy⟩
    have hh := e.sum_repr yy
    simp only [Fin.sum_univ_two] at hh
    apply Submodule.mem_span_pair.mpr
    refine ⟨(e.repr yy) 1, (e.repr yy) 0, ?_⟩
    have hv := congrArg Subtype.val hh
    simpa [q, p, yy, zsmul_eq_mul, add_comm] using hv

/-- The ratio of an integral basis of `J` with totally positive second vector has distinct
real values, because `I ⊆ J` has an oriented basis; used in
`exists_admissible_of_positive_basis`. -/
private theorem orientation_ne_zero_of_positive_basis {J : Submodule ℤ K}
    (hle : B.submodule ≤ J) {p q : K} (hppos : F.IsTotallyPositive p)
    (hspan : Submodule.span ℤ {q, p} = J) :
    realEmbeddingAt K F.place (q / p) - realEmbeddingAt K F.otherPlace (q / p) ≠ 0 := by
  have hp0 : p ≠ 0 := hppos.ne_zero
  have hpair : Submodule.span ℤ {p * (q / p), p} = J := by
    simpa [mul_div_cancel₀ q hp0] using hspan
  have hfirst : B.scale * B.tau ∈ Submodule.span ℤ {p * (q / p), p} := by
    rw [hpair]
    exact hle (Submodule.subset_span (by simp :
      B.scale * B.tau ∈ {B.scale * B.tau, B.scale}))
  have hsecond : B.scale ∈ Submodule.span ℤ {p * (q / p), p} := by
    rw [hpair]
    exact hle (Submodule.subset_span (by simp :
      B.scale ∈ {B.scale * B.tau, B.scale}))
  obtain ⟨A, hA⟩ := exists_pairMap_of_mem_span hp0 hfirst hsecond
  have hOri := hA.det_mul_sub_eq F
  have hjf : 0 < realEmbeddingAt K F.place (B.scale / p) := by
    rw [map_div₀]
    exact div_pos B.scale_pos.1 hppos.1
  have hjg : 0 < realEmbeddingAt K F.otherPlace (B.scale / p) := by
    rw [map_div₀]
    exact div_pos B.scale_pos.2 hppos.2
  have hpos : 0 < (A.det : ℝ) *
      (realEmbeddingAt K F.place (q / p) - realEmbeddingAt K F.otherPlace (q / p)) := by
    rw [hOri]
    exact mul_pos (mul_pos hjf hjg) (sub_pos.mpr B.other_lt)
  intro hz
  have hzero : (A.det : ℝ) *
      (realEmbeddingAt K F.place (q / p) - realEmbeddingAt K F.otherPlace (q / p)) = 0 := by
    rw [hz, mul_zero]
  exact (not_lt_of_ge (le_of_eq hzero)) hpos

/-- A totally positive primitive vector extends to an admissible basis of a lattice
containing `I`; the orientation step in `exists_submodule_eq`. -/
private theorem exists_admissible_of_positive_basis {J : Submodule ℤ K}
    (hle : B.submodule ≤ J) (bJ : Module.Basis (Fin 2) ℤ J) {w : J}
    (hwpos : F.IsTotallyPositive (w : K))
    (hwunimodular : Module.IsUnimodular ℤ w) :
    ∃ B'' : PseudolatticeBasis F, B''.submodule = J := by
  have hrank : Module.finrank ℤ J = 2 := by
    simpa using (Module.finrank_eq_card_basis bJ)
  have hJfree : Module.Free ℤ J := Module.Free.of_basis bJ
  obtain ⟨e, he0⟩ := Module.IsUnimodular.exists_basis_zero_eq hrank hwunimodular
  let p : K := (e 0 : J).val
  let q : K := (e 1 : J).val
  have hppos : F.IsTotallyPositive p := by simpa only [p, he0] using hwpos
  have hp0 : p ≠ 0 := hppos.ne_zero
  have hspan : Submodule.span ℤ {q, p} = J := span_eq_of_basis e
  have hpair : Submodule.span ℤ {p * (q / p), p} = J := by
    simpa [mul_div_cancel₀ q hp0] using hspan
  let δ : ℝ := realEmbeddingAt K F.place (q / p) -
    realEmbeddingAt K F.otherPlace (q / p)
  have hδ : δ ≠ 0 := orientation_ne_zero_of_positive_basis hle hppos hspan
  by_cases hδpos : 0 < δ
  · refine ⟨⟨q / p, p, ?_, hppos⟩, ?_⟩
    · exact sub_pos.mp hδpos
    · change Submodule.span ℤ {p * (q / p), p} = J
      exact hpair
  · have hδneg : δ < 0 := lt_of_le_of_ne (le_of_not_gt hδpos) hδ
    have hspanneg : Submodule.span ℤ {-q, p} = J := by
      rw [span_pair_neg_left_eq, hspan]
    refine ⟨⟨(-q) / p, p, ?_, hppos⟩, ?_⟩
    · have hsign : realEmbeddingAt K F.place ((-q) / p) -
          realEmbeddingAt K F.otherPlace ((-q) / p) = -δ := by
        simp only [neg_div, map_neg]
        ring
      exact sub_pos.mp (by rw [hsign]; exact neg_pos.mpr hδneg)
    · change Submodule.span ℤ {p * ((-q) / p), p} = J
      simpa only [mul_div_cancel₀ (-q) hp0] using hspanneg
/-- **Every lattice between `I` and `n⁻¹I` has an admissible basis**: an oriented basis with
totally positive second vector, as [RW26b, Radchenko, Wheeler (2026b), Section 3] chooses for
every pseudolattice. -/
theorem exists_submodule_eq {J : Submodule ℤ K} (hle : B.submodule ≤ J) {n : ℕ} (hn : n ≠ 0)
    (hJ : ∀ y ∈ J, (n : K) * y ∈ B.submodule) :
    ∃ B'' : PseudolatticeBasis F, B''.submodule = J := by
  obtain ⟨bJ⟩ := exists_integralBasis_of_sandwich hle hn hJ
  let v : J := ⟨B.scale, hle (Submodule.subset_span
    (by simp : B.scale ∈ {B.scale * B.tau, B.scale}))⟩
  obtain ⟨w, hwpos, hwunimodular⟩ :=
    exists_positive_primitive bJ v (by simpa only [v] using B.scale_pos)
  exact exists_admissible_of_positive_basis hle bJ hwpos hwunimodular
end PseudolatticeBasis

end SIC
