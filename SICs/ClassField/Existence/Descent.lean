/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Reciprocity.Conjugation
import SICs.ClassField.Reciprocity.NormGroups

/-!
# Descent of class fields along abelian extensions

If `F/K` is finite abelian and a subgroup $W\le C_K$ pulls back to the norm group of an abelian
extension `N/F` that is Galois over `K`, then `W` is the norm group of an abelian extension of
`K` inside `N`.

This module follows Childress, *Class Field Theory* (2009), Chapter VI, Proposition 1.3 (the
Reduction Lemma), and the cyclic tower of the proof of Theorem 2.7 (p. 139). It supplies the
descent from $K(\zeta_n)$ in `exists_intermediateField_range_norm_eq`.

## The argument

*Abelian over a cyclic step.* Let $F\subseteq E\subseteq N$ with `E/F` cyclic, `N/E` abelian,
`N/F` Galois, and $\ker N_{E/F}\subseteq N_{N/E}C_N$. For $\tau\in\operatorname{Gal}(N/F)$ with
restriction $\sigma$ to `E` and $g = \operatorname{Art}_{N/E}(b)$,
$\tau g\tau^{-1} = \operatorname{Art}_{N/E}(\sigma b)$ (`globalArtin_restrictNormal_smul`), and
$\sigma(b)/b\in\ker N_{E/F}$ is killed by $\operatorname{Art}_{N/E}$; so
$\operatorname{Gal}(N/E)$ is central with cyclic quotient $\operatorname{Gal}(E/F)$, and
$\operatorname{Gal}(N/F)$ is abelian.

*Galois descent of fixed fields.* If `N/K` is Galois, `F/K` is Galois, `N/F` is abelian, and
$V\le C_F$ is stable under $\operatorname{Gal}(F/K)$, then conjugation by
$\operatorname{Gal}(N/K)$ preserves $\operatorname{Art}_{N/F}(V)$, so its fixed field is Galois
over `K`.

*Cyclic step.* With $W\le C_F$ stable under $\operatorname{Gal}(F/K)$ and
$N_{N/E}C_N = N_{E/F}^{-1}(W)$, the field `N` is abelian over `F`, its norm group
$N_{E/F}N_{N/E}C_N$ lies in `W`, and the fixed field `M` of $\operatorname{Art}_{N/F}(W)$ has norm
group `W` (`range_norm_fixedField`) and is Galois over `K`.

*Abelian descent.* Induct on $[F:K]$. If $[F:K]>1$, choose `F₁` with $[F:F_1]$ prime
(`exists_intermediateField_finrank_eq_prime`), so `F/F₁` is cyclic, and apply the cyclic step to
$W_1 = N_{F_1/K}^{-1}(W)$, which is stable under $\operatorname{Gal}(F_1/K)$ since
$N_{F_1/K}\circ\sigma = N_{F_1/K}$; then apply induction to the result over `F₁`. If $[F:K]=1$
the cyclic step applies directly. Childress descends along a fixed cyclic tower in $K(\zeta_n)$;
the induction chooses the tower one step at a time.
-/

noncomputable section

open IsDedekindDomain NumberField

namespace SIC

/-! ### Abelian extensions over cyclic steps -/

/-- **Central extensions of cyclic groups**: if `E/F` is cyclic, `N/E` abelian, `N/F` Galois,
and the Artin map of `N/E` kills $\ker N_{E/F}$, then `N/F` is abelian. Childress, *Class Field
Theory*, Chapter VI, proof of Proposition 1.3. -/
theorem isAbelianGalois_of_ker_norm_le {F E N : Type*} [Field F] [Field E] [Field N]
    [NumberField F] [NumberField E] [NumberField N] [Algebra F E] [Algebra E N] [Algebra F N]
    [IsScalarTower F E N] [IsGalois F N] [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)]
    [IsAbelianGalois E N]
    (h : (IdeleClassGroup.norm (K := F) (L := E)).ker ≤
      (IdeleClassGroup.norm (K := E) (L := N)).range) :
    IsAbelianGalois F N := by
  classical
  let f : (N ≃ₐ[F] N) →* (E ≃ₐ[F] E) := AlgEquiv.restrictNormalHom E
  have hker : f.ker ≤ Subgroup.center (N ≃ₐ[F] N) := by
    intro α hα
    rw [Subgroup.mem_center_iff]
    intro τ
    have hfix : ∀ x : E, α (algebraMap E N x) = algebraMap E N x := by
      intro x
      have hr : α.restrictNormal E = 1 := by
        change (AlgEquiv.restrictNormalHom E) α = 1 at hα
        exact hα
      simpa [hr] using (α.restrictNormal_commutes E x).symm
    let g : N ≃ₐ[E] N := { α with commutes' := hfix }
    obtain ⟨b, hb⟩ := globalArtin_surjective (K := E) (L := N) g
    have hdiff : (τ.restrictNormal E • b) * b⁻¹ ∈
        (IdeleClassGroup.norm (K := F) (L := E)).ker := by
      change IdeleClassGroup.norm (K := F) (L := E) ((τ.restrictNormal E • b) * b⁻¹) = 1
      rw [map_mul, map_inv]
      simp only [IdeleClassGroup.norm_smul, mul_inv_cancel]
    have heq : globalArtin N (τ.restrictNormal E • b) = globalArtin N b := by
      have hm : (τ.restrictNormal E • b) * b⁻¹ ∈ (globalArtin N).ker := by
        rw [ker_globalArtin (K := E) (L := N)]
        exact h hdiff
      change globalArtin N ((τ.restrictNormal E • b) * b⁻¹) = 1 at hm
      rw [map_mul, map_inv, mul_inv_eq_one] at hm
      exact hm
    have hc := globalArtin_restrictNormal_smul (F := F) (E := E) (L := N) τ b
    rw [heq, hb] at hc
    have hg : g.restrictScalars F = α := AlgEquiv.ext fun _ => rfl
    rw [hg] at hc
    calc
      τ * α = (τ * α * τ⁻¹) * τ := by group
      _ = α * τ := by rw [← hc]
  exact { is_comm.comm := (f.isMulCommutative_of_isCyclic_of_ker_le_center hker).is_comm.comm }

/-! ### Fixed fields of stable subgroups -/

/-- **Galois descent of fixed fields**: if $V\le C_F$ is stable under
$\operatorname{Gal}(F/K)$, the fixed field of $\operatorname{Art}_{N/F}(V)$ is Galois over `K`.
Childress, *Class Field Theory*, Chapter VI, proof of Proposition 1.3. -/
theorem isGalois_fixedField_map_globalArtin {K F N : Type*} [Field K] [Field F] [Field N]
    [NumberField F] [NumberField N] [Algebra K F] [Algebra F N] [Algebra K N]
    [IsScalarTower K F N] [IsGalois K N] [IsGalois K F] [IsAbelianGalois F N]
    {V : Subgroup (NumberField.IdeleClassGroup (𝓞 F) F)}
    (hV : ∀ σ : F ≃ₐ[K] F, ∀ x ∈ V, σ • x ∈ V) :
    IsGalois K (IntermediateField.fixedField (V.map (globalArtin (K := F) N))) := by
  classical
  let H : Subgroup (N ≃ₐ[F] N) := V.map (globalArtin N)
  let j : (N ≃ₐ[F] N) →* (N ≃ₐ[K] N) := AlgEquiv.restrictScalarsHom K
  let H' : Subgroup (N ≃ₐ[K] N) := H.map j
  have hn : H'.Normal := ⟨by
    intro g hg τ
    obtain ⟨a, ha, rfl⟩ := hg
    obtain ⟨x, hx, rfl⟩ := ha
    refine ⟨globalArtin N (τ.restrictNormal F • x),
      ⟨τ.restrictNormal F • x, hV _ _ hx, rfl⟩, ?_⟩
    exact globalArtin_restrictNormal_smul (F := K) (E := F) (L := N) τ x⟩
  have hfield : (IntermediateField.fixedField H).restrictScalars K =
      IntermediateField.fixedField H' := by
    apply IntermediateField.ext
    intro x
    simp only [IntermediateField.mem_restrictScalars, IntermediateField.mem_fixedField_iff]
    constructor
    · intro hx g hg
      obtain ⟨a, ha, rfl⟩ := hg
      exact hx a ha
    · intro hx a ha
      exact hx (j a) (Subgroup.mem_map_of_mem j ha)
  have hG : IsGalois K (IntermediateField.fixedField H') :=
    IsGalois.of_fixedField_normal_subgroup (hn := hn) H'
  change IsGalois K ((IntermediateField.fixedField H).restrictScalars K)
  rw [hfield]
  exact hG

/-! ### Descent -/

/-- **The Reduction Lemma**: for a cyclic step $F\subseteq E$ inside `N`, with `N/K` Galois,
`F/K` Galois, `N/E` abelian, $W\le C_F$ stable under $\operatorname{Gal}(F/K)$, and
$N_{N/E}C_N = N_{E/F}^{-1}(W)$, the subgroup `W` is the norm group of an abelian extension of `F`
inside `N` that is Galois over `K`. Childress, *Class Field Theory*, Chapter VI,
Proposition 1.3. -/
theorem exists_range_norm_eq_of_isCyclic {K F E N : Type*} [Field K] [Field F] [Field E]
    [Field N] [NumberField F] [NumberField E] [NumberField N] [Algebra K F] [Algebra F E]
    [Algebra E N] [Algebra F N] [Algebra K N] [IsScalarTower F E N] [IsScalarTower K F N]
    [IsGalois K N] [IsGalois K F] [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)] [IsAbelianGalois E N]
    {W : Subgroup (NumberField.IdeleClassGroup (𝓞 F) F)}
    (hW : ∀ σ : F ≃ₐ[K] F, ∀ x ∈ W, σ • x ∈ W)
    (hN : (IdeleClassGroup.norm (K := E) (L := N)).range =
      W.comap (IdeleClassGroup.norm (K := F) (L := E))) :
    ∃ M : IntermediateField F N, IsAbelianGalois F M ∧ IsGalois K M ∧
      (IdeleClassGroup.norm (K := F) (L := M)).range = W := by
  classical
  have hker : (IdeleClassGroup.norm (K := F) (L := E)).ker ≤
      (IdeleClassGroup.norm (K := E) (L := N)).range := by
    intro x hx
    rw [hN]
    change IdeleClassGroup.norm (K := F) (L := E) x ∈ W
    change IdeleClassGroup.norm (K := F) (L := E) x = 1 at hx
    rw [hx]
    exact W.one_mem
  have hA : IsAbelianGalois F N := by
    have : IsGalois F N := IsGalois.tower_top_of_isGalois K F N
    exact isAbelianGalois_of_ker_norm_le hker
  have hNW : (IdeleClassGroup.norm (K := F) (L := N)).range ≤ W := by
    rintro _ ⟨x, rfl⟩
    have hx : IdeleClassGroup.norm (K := E) (L := N) x ∈
        (IdeleClassGroup.norm (K := E) (L := N)).range := ⟨x, rfl⟩
    rw [hN] at hx
    change IdeleClassGroup.norm (K := F) (L := E)
      (IdeleClassGroup.norm (K := E) (L := N) x) ∈ W at hx
    simpa only [IdeleClassGroup.norm_norm] using hx
  let M : IntermediateField F N :=
    IntermediateField.fixedField (W.map (globalArtin N))
  refine ⟨M, ?_, ?_, ?_⟩
  · exact IsAbelianGalois.tower_bot F M N
  · exact isGalois_fixedField_map_globalArtin hW
  · exact range_norm_fixedField hNW

/-- The degree-one base case of `exists_range_norm_eq_of_isAbelianGalois`. -/
private theorem descent_of_finrank_one {K F N : Type*} [Field K] [Field F] [Field N]
    [NumberField K] [NumberField F] [NumberField N] [Algebra K F] [Algebra F N] [Algebra K N]
    [IsScalarTower K F N] [IsAbelianGalois K F] [IsGalois K N] [IsAbelianGalois F N]
    {W : Subgroup (NumberField.IdeleClassGroup (𝓞 K) K)}
    (hdegree : Module.finrank K F = 1)
    (hN : (IdeleClassGroup.norm (K := F) (L := N)).range =
      W.comap (IdeleClassGroup.norm (K := K) (L := F))) :
    ∃ M : IntermediateField K N, IsAbelianGalois K M ∧
      (IdeleClassGroup.norm (K := K) (L := M)).range = W := by
  classical
  have hcard : Nat.card (F ≃ₐ[K] F) = 1 := by
    rw [IsGalois.card_aut_eq_finrank, hdegree]
  have hcyc : IsCyclic (F ≃ₐ[K] F) :=
    @isCyclic_of_subsingleton _ _ (Nat.card_eq_one_iff_unique.mp hcard).1
  have hstab : ∀ σ : K ≃ₐ[K] K, ∀ x ∈ W, σ • x ∈ W := by
    intro σ x hx
    have hσ : σ = 1 := Subsingleton.elim σ 1
    simpa only [hσ, one_smul] using hx
  obtain ⟨M, hM, _, hnorm⟩ :=
    exists_range_norm_eq_of_isCyclic (K := K) (F := K) (E := F) (N := N) hstab hN
  exact ⟨M, hM, hnorm⟩

/-- Applies the cyclic reduction over an intermediate field; used by
`exists_range_norm_eq_of_isAbelianGalois`. -/
private theorem descent_cyclic_step {K F N : Type*} [Field K] [Field F] [Field N]
    [NumberField K] [NumberField F] [NumberField N] [Algebra K F] [Algebra F N] [Algebra K N]
    [IsScalarTower K F N] [IsAbelianGalois K F] [IsGalois K N] [IsAbelianGalois F N]
    (F₁ : IntermediateField K F) [IsCyclic (F ≃ₐ[F₁] F)]
    {W : Subgroup (NumberField.IdeleClassGroup (𝓞 K) K)}
    (hN : (IdeleClassGroup.norm (K := F) (L := N)).range =
      W.comap (IdeleClassGroup.norm (K := K) (L := F))) :
    ∃ M₁ : IntermediateField F₁ N, IsAbelianGalois F₁ M₁ ∧ IsGalois K M₁ ∧
      (IdeleClassGroup.norm (K := F₁) (L := M₁)).range =
        W.comap (IdeleClassGroup.norm (K := K) (L := F₁)) := by
  let W₁ : Subgroup (NumberField.IdeleClassGroup (𝓞 F₁) F₁) :=
    W.comap (IdeleClassGroup.norm (K := K) (L := F₁))
  have hstab : ∀ σ : F₁ ≃ₐ[K] F₁, ∀ x ∈ W₁, σ • x ∈ W₁ := by
    intro σ x hx
    exact IdeleClassGroup.smul_mem_comap_norm W σ hx
  have hN₁ : (IdeleClassGroup.norm (K := F) (L := N)).range =
      W₁.comap (IdeleClassGroup.norm (K := F₁) (L := F)) := by
    rw [hN]
    ext x
    change IdeleClassGroup.norm (K := K) (L := F) x ∈ W ↔
      IdeleClassGroup.norm (K := K) (L := F₁)
        (IdeleClassGroup.norm (K := F₁) (L := F) x) ∈ W
    rw [IdeleClassGroup.norm_norm]
  exact exists_range_norm_eq_of_isCyclic (K := K) (F := F₁) (E := F) (N := N) hstab hN₁

universe uN in
/-- **Descent along an abelian extension**: if `F/K` is finite abelian, `N/K` Galois, `N/F`
abelian, and $N_{N/F}C_N = N_{F/K}^{-1}(W)$, then `W` is the norm group of an abelian extension
of `K` inside `N`. Childress, *Class Field Theory*, Chapter VI, Proposition 1.3 along the cyclic
tower in the proof of Theorem 2.7. -/
theorem exists_range_norm_eq_of_isAbelianGalois {K F : Type*} {N : Type uN}
    [Field K] [Field F] [Field N]
    [NumberField K] [NumberField F] [NumberField N] [Algebra K F] [Algebra F N] [Algebra K N]
    [IsScalarTower K F N] [IsAbelianGalois K F] [IsGalois K N] [IsAbelianGalois F N]
    {W : Subgroup (NumberField.IdeleClassGroup (𝓞 K) K)}
    (hN : (IdeleClassGroup.norm (K := F) (L := N)).range =
      W.comap (IdeleClassGroup.norm (K := K) (L := F))) :
    ∃ M : IntermediateField K N, IsAbelianGalois K M ∧
      (IdeleClassGroup.norm (K := K) (L := M)).range = W := by
  classical
  apply (IsAbelianGalois.induction_finrank_prime (K := K)
    (P := fun E [Field E] [Algebra K E] [FiniteDimensional K E] =>
      letI : NumberField E := NumberField.of_module_finite K E
      ∀ (N : Type uN) [Field N] [NumberField N] [Algebra E N] [Algebra K N]
        [IsScalarTower K E N] [IsGalois K N] [IsAbelianGalois E N],
        (IdeleClassGroup.norm (K := E) (L := N)).range =
          W.comap (IdeleClassGroup.norm (K := K) (L := E)) →
        ∃ M : IntermediateField K N, IsAbelianGalois K M ∧
          (IdeleClassGroup.norm (K := K) (L := M)).range = W)
    ?_ ?_ F) N hN
  · intro E _ _ _ _
    refine (letI : NumberField E := NumberField.of_module_finite K E; ?_)
    intro hone N _ _ _ _ _ _ _ hN
    exact descent_of_finrank_one hone hN
  · intro E _ _ _ _ F₁ hp ih
    refine (letI : NumberField E := NumberField.of_module_finite K E; ?_)
    intro N _ _ _ _ _ _ _ hN
    have hcard : Nat.card (E ≃ₐ[F₁] E) = Module.finrank F₁ E :=
      IsGalois.card_aut_eq_finrank F₁ E
    have hcyc : IsCyclic (E ≃ₐ[F₁] E) :=
      @isCyclic_of_prime_card _ _ _ ⟨hp⟩ hcard
    obtain ⟨M₁, hA₁, hG₁, hnorm₁⟩ := descent_cyclic_step F₁ hN
    obtain ⟨M₂, hA₂, hnorm₂⟩ := ih M₁ hnorm₁
    let f : M₁ →ₐ[K] N := (IsScalarTower.toAlgHom F₁ M₁ N).restrictScalars K
    let M : IntermediateField K N := M₂.map f
    have hAM : IsAbelianGalois K M :=
      IsAbelianGalois.of_algHom (M₂.equivMap f).symm.toAlgHom
    have hnorm : (IdeleClassGroup.norm (K := K) (L := M)).range = W :=
      (IdeleClassGroup.range_norm_congr (M₂.equivMap f)).symm.trans hnorm₂
    exact ⟨M, hAM, hnorm⟩

end SIC
