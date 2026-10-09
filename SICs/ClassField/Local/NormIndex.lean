/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Local.UnitCohomology
import SICs.ClassField.Completion.InfiniteDecomposition
import Mathlib.RingTheory.Complex
import Mathlib.Algebra.Order.Ring.Units
import SICs.GroupCohomology.Hilbert90

/-!
# The norm index of a cyclic local extension

For a Galois extension of number fields `L/K` and a place `w` of `L` above `v` with $L_w/K_v$
cyclic, $h(L_w^\times) = [L_w : K_v]$ and $[K_v^\times : N_{L_w/K_v} L_w^\times] = [L_w : K_v]$, at
finite and at infinite places.

At finite places this is Milne, *Class Field Theory*, version 4.03 (2020), Chapter III,
Lemma 2.5, with Hilbert's Theorem 90; it is Serre, *Local class field theory*, in J. W. S. Cassels
and A. Fröhlich (eds.), *Algebraic Number Theory* (1967), Chapter VI, §1.4, Corollaries 1 and 2,
read through $\widehat H^0$ instead of $H^2$. At an infinite place the extension is $\mathbb C /
\mathbb R$ or trivial, and the norms from $\mathbb C^\times$ are the positive reals (Milne,
Chapter I, 1.6; Serre, Chapter VI, §2.9). These local
Herbrand quotients are the factors of $h(I_{L,S}) = \prod_{v \in S} n_v$ in Milne, Chapter VII,
Proposition 2.7.

## The argument

At a finite place, the valuation sequence $1 \to U_w \to L_w^\times \to \mathbb Z \to 0$
(`SICs.ClassField.Local.ValuationSequence`) is exact with $h(U_w) = 1$
(`SICs.ClassField.Local.UnitCohomology`) and $h(\mathbb Z) = |G| = [L_w : K_v]$, so
$h(L_w^\times) = [L_w : K_v]$ by multiplicativity. By Hilbert's Theorem 90,
$\widehat H^{-1}(G, L_w^\times) = 0$, so the order of
$\widehat H^0(G, L_w^\times) \cong K_v^\times / N L_w^\times$ is $h(L_w^\times)$.

At an infinite place, $[L_w : K_v]$ is `1` or `2`. In degree one the norm is the identity. In
degree two $K_v \cong \mathbb R$ and $L_w \cong \mathbb C$, the norm of `z` is $z \bar z > 0$, and
every positive real `a` is the norm of $\sqrt a \in K_v$, so the norms are the index-two subgroup of
positive elements. The Galois group then has order at most two, hence is cyclic, and Hilbert's
Theorem 90 again gives $h(L_w^\times) = [K_v^\times : N L_w^\times]$.
-/

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField SIC.FinitePlace

namespace SIC

/-! ### Finite places -/

namespace FinitePlace

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [IsGalois K L] [IsCyclic (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)]

/-- For cyclic $L_w/K_v$ at a finite place, $h(L_w^\times) = [L_w : K_v]$. Milne, *Class Field
Theory*, Chapter III, Lemma 2.5; Serre, *Local class field theory*, in Cassels–Fröhlich (1967),
Chapter VI, §1.4, Corollary 1. -/
theorem herbrandQuotient_units_adicCompletion :
    Representation.herbrandQuotient
        (Representation.ofMulDistribMulAction
          (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
          (w.adicCompletion L)ˣ) =
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  rw [Representation.herbrandQuotient_eq_mul
    (Representation.Subrepresentation.subtype_injective (unitGroupSubrep v w))
    (unitsValuationHom_surjective v w)
    (exact_unitGroupSubrep_unitsValuationHom v w)
    (hasHerbrandQuotient_unitGroupSubrep v w)
    Representation.hasHerbrandQuotient_trivial,
    herbrandQuotient_unitGroupSubrep, Representation.herbrandQuotient_trivial, one_mul,
    Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]

/-- **The local norm index**: for cyclic $L_w/K_v$ at a finite place,
$[K_v^\times : N_{L_w/K_v} L_w^\times] = [L_w : K_v]$. Milne, *Class Field Theory*, Chapter III,
Lemma 2.5 with Hilbert's Theorem 90; Serre, *Local class field theory*, in Cassels–Fröhlich
(1967), Chapter VI, §1.4, Corollary 2. -/
theorem card_quotient_range_localNorm :
    Nat.card ((v.adicCompletion K)ˣ ⧸ (localNorm v w).range) =
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  have h := herbrandQuotient_units_adicCompletion v w
  rw [Representation.herbrandQuotient_units] at h
  exact_mod_cast h

end FinitePlace

/-! ### Infinite places -/

namespace InfinitePlace

open scoped NumberField.LiesOver SIC.InfinitePlace

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  (v : NumberField.InfinitePlace K) (w : NumberField.InfinitePlace L) [w.LiesOver v]

omit [NumberField K] [NumberField L] in
/-- In the ramified infinite case, the algebraic norm becomes the complex squared modulus under
the real and complex completion isomorphisms. Used in `card_quotient_range_localNorm`. -/
private theorem norm_real_of_ramified (hw : w.IsRamified K) (x : w.Completion) :
    (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
      (NumberField.InfinitePlace.IsRamified.liesOver_isReal_under w v hw))
      (Algebra.norm v.Completion x) =
      Complex.normSq
        ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw.isComplex) x) := by
  let e := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
    (NumberField.InfinitePlace.IsRamified.liesOver_isReal_under w v hw)
  let f := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw.isComplex
  have : NumberField.ComplexEmbedding.LiesOver
      (NumberField.InfinitePlace.Completion.extensionEmbedding w)
      (NumberField.InfinitePlace.Completion.extensionEmbedding v) :=
    NumberField.InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal w
      (NumberField.InfinitePlace.IsRamified.liesOver_isReal_under w v hw)
  have hcomm : RingHom.comp (algebraMap ℝ ℂ) (e : v.Completion →+* ℝ) =
      RingHom.comp (f : w.Completion →+* ℂ)
        (algebraMap v.Completion w.Completion) := by
    ext y
    change (e y : ℂ) = f ((algebraMap v.Completion w.Completion) y)
    rw [show (e y : ℂ) = NumberField.InfinitePlace.Completion.extensionEmbedding v y from
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply _ _]
    exact (NumberField.InfinitePlace.Completion.liesOver_extensionEmbedding_apply
      (w := w) (v := v)
      (φ := NumberField.InfinitePlace.Completion.extensionEmbedding w) (x := y)).symm
  have h := Algebra.norm_eq_of_equiv_equiv e f hcomm x
  apply_fun e at h
  simpa [e, f, Algebra.norm_complex_apply] using h

omit [NumberField K] [NumberField L] in
/-- At a ramified infinite place, every local norm is positive under the real completion
isomorphism. Used in `mem_range_localNorm_iff_pos`. -/
private theorem localNorm_pos_of_ramified (hw : w.IsRamified K) (y : w.Completionˣ) :
    0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
      (NumberField.InfinitePlace.IsRamified.liesOver_isReal_under w v hw))
      ((localNorm v w y : v.Completionˣ) : v.Completion) := by
  rw [localNorm_val, norm_real_of_ramified v w hw]
  exact Complex.normSq_pos.mpr ((map_ne_zero _).mpr y.ne_zero)

omit [NumberField K] [NumberField L] in
/-- At a ramified infinite place, every positive real unit is the norm of its square root.
Used in `mem_range_localNorm_iff_pos`. -/
private theorem mem_localNorm_range_of_pos (hw : w.IsRamified K) (x : v.Completionˣ)
    (hx : 0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
      (NumberField.InfinitePlace.IsRamified.liesOver_isReal_under w v hw))
      (x : v.Completion)) : x ∈ (localNorm v w).range := by
  let e := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
    (NumberField.InfinitePlace.IsRamified.liesOver_isReal_under w v hw)
  let z : v.Completion := e.symm (Real.sqrt (e (x : v.Completion)))
  have hz : z ≠ 0 := by
    intro hz
    have hz' : Real.sqrt (e (x : v.Completion)) = 0 := by
      simpa [z] using congrArg e hz
    exact (Real.sqrt_pos.2 hx).ne' hz'
  let u : v.Completionˣ := Units.mk0 z hz
  have hu : u ^ 2 = x := by
    apply Units.ext
    apply e.injective
    change e (z ^ 2) = e (x : v.Completion)
    rw [map_pow]
    rw [show e z = Real.sqrt (e (x : v.Completion)) by simp [z]]
    exact Real.sq_sqrt hx.le
  exact ⟨Units.map (NumberField.LiesOver.completionMap (v := v) (w := w)) u,
    by simp [hw.finrank_eq_two v, hu]⟩

omit [NumberField K] [NumberField L] in
/-- At an unramified infinite place, the norm is surjective. Milne, *Class Field Theory*,
Chapter I, §1.6. -/
theorem localNorm_surjective_of_unramified (hw : w.IsUnramified K) :
    Function.Surjective (localNorm v w) := by
  intro x
  refine ⟨Units.map (NumberField.LiesOver.completionMap (v := v) (w := w)) x, ?_⟩
  simp [hw.finrank_eq_one v]

omit [NumberField K] [NumberField L] in
/-- At a ramified infinite place, a unit is a norm exactly when it is positive under the real
completion isomorphism. Milne, *Class Field Theory*, Chapter I, §1.6. -/
theorem mem_range_localNorm_iff_pos (hw : w.IsRamified K) (x : v.Completionˣ) :
    x ∈ (localNorm v w).range ↔
      0 < (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
        (NumberField.InfinitePlace.IsRamified.liesOver_isReal_under w v hw))
        (x : v.Completion) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact localNorm_pos_of_ramified v w hw y
  · exact mem_localNorm_range_of_pos v w hw x

omit [NumberField K] [NumberField L] in
/-- **The local norm index at an infinite place**: $[K_v^\times : N_{L_w/K_v} L_w^\times] =
[L_w : K_v]$, which is `2` for $\mathbb C/\mathbb R$ and `1` otherwise. Milne, *Class Field
Theory*, Chapter I, 1.6; Serre, *Local class field theory*, in Cassels–Fröhlich (1967),
Chapter VI, §2.9. -/
theorem card_quotient_range_localNorm :
    Nat.card (v.Completionˣ ⧸ (localNorm v w).range) =
      Module.finrank v.Completion w.Completion := by
  rcases w.isUnramified_or_isRamified K with hw | hw
  · rw [(localNorm v w).range_eq_top_of_surjective
      (localNorm_surjective_of_unramified v w hw)]
    simpa [Subgroup.index] using (show (⊤ : Subgroup v.Completionˣ).index = 1 by simp).trans
      (hw.finrank_eq_one v).symm
  · let e := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
      (NumberField.InfinitePlace.IsRamified.liesOver_isReal_under w v hw)
    have hindex : (localNorm v w).range.index = 2 := by
      have hrange : (localNorm v w).range =
          (Units.posSubgroup ℝ).comap (Units.map e) := by
        ext x
        exact mem_range_localNorm_iff_pos v w hw x
      rw [hrange, Subgroup.index_comap_of_surjective _]
      · exact Units.index_posSubgroup ℝ
      · intro x
        refine ⟨Units.map e.symm x, ?_⟩
        apply Units.ext
        simp [Units.map]
    exact hindex.trans (hw.finrank_eq_two v).symm

omit [NumberField K] [NumberField L] in
/-- The Galois group of an extension of infinite completions has order at most two, so it is
cyclic. -/
theorem isCyclic_algEquiv_completion :
    IsCyclic (w.Completion ≃ₐ[v.Completion] w.Completion) := by
  have hcard : Nat.card (w.Completion ≃ₐ[v.Completion] w.Completion) ≤ 2 := by
    rw [← Fintype.card_eq_nat_card]
    refine (AlgEquiv.card_le).trans ?_
    rcases w.isUnramified_or_isRamified K with hw | hw
    · rw [hw.finrank_eq_one v]
      omega
    · rw [hw.finrank_eq_two v]
  have hpos : 0 < Nat.card (w.Completion ≃ₐ[v.Completion] w.Completion) := Nat.card_pos
  have h : Nat.card (w.Completion ≃ₐ[v.Completion] w.Completion) = 1 ∨
      Nat.card (w.Completion ≃ₐ[v.Completion] w.Completion) = 2 := by omega
  apply isCyclic_of_card_dvd_prime (p := 2)
  rcases h with h | h
  · simp only [h, one_dvd]
  · simp only [h, dvd_refl]

omit [NumberField K] [NumberField L] in
/-- For Galois `L/K`, $h(L_w^\times) = [L_w : K_v]$ at an infinite place. Milne, *Class Field
Theory*, Chapter VII, Proposition 2.7 (the infinite factors). -/
theorem herbrandQuotient_units_completion [IsGalois K L] :
    Representation.herbrandQuotient
        (Representation.ofMulDistribMulAction (w.Completion ≃ₐ[v.Completion] w.Completion)
          w.Completionˣ) =
      Module.finrank v.Completion w.Completion := by
  let _ : IsCyclic (w.Completion ≃ₐ[v.Completion] w.Completion) :=
    isCyclic_algEquiv_completion v w
  rw [Representation.herbrandQuotient_units]
  exact_mod_cast card_quotient_range_localNorm v w

end InfinitePlace

end SIC
