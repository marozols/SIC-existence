/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import SICs.ClassField.Completion.Norm
import SICs.ClassField.Completion.PlacesAbove
import SICs.ClassField.Completion.WeakApproximation

/-!
# The completed base change at a finite place

The isomorphism $K_v \otimes_K L \cong \prod_{w \mid v} L_w$ for a finite extension of number
fields `L/K` and a finite place `v` of `K`, with the degree formula
$\sum_{w \mid v} [L_w : K_v] = [L : K]$ and the norm formula
$N_{L/K}(x) = \prod_{w \mid v} N_{L_w/K_v}(x)$.

This is [83, Neukirch (1999), Chapter II, Proposition 8.3 and Corollary 8.4] at a finite place,
proved as in Serre, *Local Fields*, Chapter II, §3, Theorem 1(iii) and Proposition 4.

## The argument

The canonical map sends $a \otimes x$ to $(a x)_{w \mid v}$.

*Surjectivity.* By weak approximation, `L` is dense in $\prod_{w \mid v} L_w$; the image of the
finite-dimensional $K_v$-space $K_v \otimes_K L$ is closed and contains `L`, so it is everything.

*Injectivity.* Write $\mathfrak p$ for the prime of `v` and choose $b_1, \dots, b_n \in \mathcal
O_L$ whose residues form a basis of $\mathcal O_L / \mathfrak p \mathcal O_L$ over
$\mathcal O_K / \mathfrak p$; then $n = [L : K]$ by the fiber dimension formula. Suppose
$\sum_i a_i b_i = 0$ in every $L_w$, not all $a_i = 0$. Scaling,
all $|a_i|_v \le 1$ with equality for some $i$. Choose $c_i \in \mathcal O_K$ with
$|a_i - c_i|_v < 1$. Then $y = \sum_i c_i b_i \in \mathcal O_L$ equals
$\sum_i (c_i - a_i) b_i$ in each $L_w$, so $\operatorname{ord}_w(y) \ge e_w$ for every
$w \mid v$, because the completion map multiplies orders by the ramification index. Hence
$y \in \prod_{w \mid v} w^{e_w} = \mathfrak p \mathcal O_L$, so the residues of the $c_i$ vanish,
that is, every $c_i \in \mathfrak p$ and every $|a_i|_v < 1$: a contradiction. Thus the images
of the $b_i$ in the product of local completions are independent over $K_v$, so the $b_i$ are
independent over $K$. They form a basis of `L`, and the $1 \otimes b_i$ form a basis of
$K_v \otimes_K L$. This is the reduction modulo $\mathfrak p$ of Serre's Proposition 4; it
replaces the local degree formula $[L_w : K_v] = e_w f_w$ that Serre uses for injectivity.

The degree and norm formulas then follow from the general results of
`SICs.FieldTheory.BaseChange`.
-/

noncomputable section

open IsDedekindDomain NumberField
open scoped TensorProduct SIC.FinitePlace

namespace SIC

namespace FinitePlace

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [NumberField K] [NumberField L]
  (v : HeightOneSpectrum (𝓞 K))

/-- The canonical map $K_v \otimes_K L \to \prod_{w \mid v} L_w$,
$a \otimes x \mapsto (a x)_{w \mid v}$. -/
def baseChangeAlgHom :
    v.adicCompletion K ⊗[K] L →ₐ[v.adicCompletion K]
      ∀ w : PrimeAbove (L := L) v, (PrimeAbove.place v w).adicCompletion L :=
  baseChangePi fun w ↦ IsScalarTower.toAlgHom K L ((PrimeAbove.place v w).adicCompletion L)

/-- Evaluation of `baseChangeAlgHom` on a pure tensor. -/
@[simp]
theorem baseChangeAlgHom_tmul (a : v.adicCompletion K) (x : L) (w : PrimeAbove (L := L) v) :
    baseChangeAlgHom v (a ⊗ₜ x) w =
      algebraMap (v.adicCompletion K) ((PrimeAbove.place v w).adicCompletion L) a *
        algebraMap L ((PrimeAbove.place v w).adicCompletion L) x := by
  exact baseChangePi_tmul _ a x w

/-- The canonical map $K_v \otimes_K L \to \prod_{w \mid v} L_w$ is surjective. Serre,
*Local Fields*, Chapter II, §3, proof of Theorem 1(iii). -/
theorem baseChangeAlgHom_surjective : Function.Surjective (baseChangeAlgHom (L := L) v) := by
  apply surjective_of_denseRange_tmul (baseChangeAlgHom (L := L) v).toLinearMap
  convert denseRange_algebraMap_pi (PrimeAbove.place (L := L) v)
    (PrimeAbove.place_injective v) using 1
  ext x w
  simp

/-- A local norm bound detects membership of an integer in a prime power.
Used in `mem_map_of_norm`. -/
private theorem mem_pow_of_norm {L : Type*} [Field L] [NumberField L]
    (w : HeightOneSpectrum (𝓞 L)) (y : 𝓞 L) (n : ℕ)
    (h : ‖NumberField.FinitePlace.embedding w (algebraMap (𝓞 L) L y)‖ ≤
      (WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero w)
        (WithZero.exp (-(n : ℤ))) : ℝ)) : y ∈ w.asIdeal ^ n := by
  rw [NumberField.FinitePlace.norm_embedding_int] at h
  apply (w.intValuation_le_pow_iff_mem y n).mp
  apply (WithZeroMulInt.toNNReal_strictMono
    (HeightOneSpectrum.one_lt_absNorm_nnreal w)).le_iff_le.mp
  exact_mod_cast h

/-- Bounds at every place over `v` put an integer in the extended prime ideal.
Used in `no_integral_relation`. -/
private theorem mem_map_of_norm (v : HeightOneSpectrum (𝓞 K)) (y : 𝓞 L)
    (h : ∀ w : SIC.FinitePlace.PrimeAbove (L := L) v,
      ‖NumberField.FinitePlace.embedding (SIC.FinitePlace.PrimeAbove.place v w)
        (algebraMap (𝓞 L) L y)‖ ≤
      (WithZeroMulInt.toNNReal
        (HeightOneSpectrum.absNorm_ne_zero (SIC.FinitePlace.PrimeAbove.place v w))
        (WithZero.exp (-(w.1.ramificationIdx (𝓞 K) : ℤ))) : ℝ)) :
    y ∈ Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal := by
  have hfactor : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal =
      ∏ w : SIC.FinitePlace.PrimeAbove (L := L) v,
        w.1 ^ w.1.ramificationIdx (𝓞 K) := by
    rw [Ideal.map_algebraMap_eq_finsetProd_pow v.ne_bot]
    exact (Finset.prod_set_coe (v.asIdeal.primesOver (𝓞 L))).symm
  rw [hfactor]
  have hprod := IsDedekindDomain.HeightOneSpectrum.inf_pow_eq_prod
    (s := Finset.univ)
    (f := SIC.FinitePlace.PrimeAbove.place (L := L) v)
    (e := fun w : SIC.FinitePlace.PrimeAbove (L := L) v => w.1.ramificationIdx (𝓞 K))
    (by intro i hi j hj hij; exact (SIC.FinitePlace.PrimeAbove.place_injective v).ne hij)
  change (Finset.univ.inf fun i : SIC.FinitePlace.PrimeAbove (L := L) v =>
    i.1 ^ i.1.ramificationIdx (𝓞 K)) =
    ∏ i : SIC.FinitePlace.PrimeAbove (L := L) v,
      i.1 ^ i.1.ramificationIdx (𝓞 K) at hprod
  rw [← hprod]
  simp only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true]
  rw [Submodule.mem_iInf]
  intro w
  exact mem_pow_of_norm (SIC.FinitePlace.PrimeAbove.place v w) y _ (h w)

/-- The norm threshold at `w` equals the threshold at `v` raised to `e_w f_w`.
Used in `no_integral_relation`. -/
private theorem threshold_eq (v : HeightOneSpectrum (𝓞 K))
    (w : SIC.FinitePlace.PrimeAbove (L := L) v) :
    ((Ideal.absNorm v.asIdeal : ℝ)⁻¹) ^
      (w.1.ramificationIdx (𝓞 K) * w.1.inertiaDeg (𝓞 K)) =
    (WithZeroMulInt.toNNReal
      (HeightOneSpectrum.absNorm_ne_zero (SIC.FinitePlace.PrimeAbove.place v w))
      (WithZero.exp (-(w.1.ramificationIdx (𝓞 K) : ℤ))) : ℝ) := by
  rw [WithZeroMulInt.toNNReal_neg_apply
    (HeightOneSpectrum.absNorm_ne_zero (SIC.FinitePlace.PrimeAbove.place v w))
    WithZero.exp_ne_zero]
  change _ = ((Ideal.absNorm w.1 : ℝ) ^
    (-(w.1.ramificationIdx (𝓞 K) : ℤ)))
  rw [zpow_neg, zpow_natCast]
  rw [← inv_pow, mul_comm, pow_mul]
  congr 1
  rw [inv_pow, ← Nat.cast_pow, Ideal.absNorm_pow_inertiaDeg v.asIdeal w.1]

attribute [local instance] Ideal.Quotient.field

/-- An index set for a basis of the residue quotient of the ring of integers.
Used in `residueBasis`. -/
private abbrev ResidueIndex (v : HeightOneSpectrum (𝓞 K)) :=
  Module.Free.ChooseBasisIndex (𝓞 K ⧸ v.asIdeal)
    (𝓞 L ⧸ Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal)

/-- A chosen basis of the residue quotient over the residue field at `v`. Used in `liftedBasis`. -/
private noncomputable def residueBasis (v : HeightOneSpectrum (𝓞 K)) :
    Module.Basis (ResidueIndex (L := L) v) (𝓞 K ⧸ v.asIdeal)
      (𝓞 L ⧸ Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal) :=
  Module.Free.chooseBasis _ _

/-- Integral representatives of the residue basis.
Used in `liftedBasis` and `no_integral_relation`. -/
private noncomputable def residueLift (v : HeightOneSpectrum (𝓞 K))
    (i : ResidueIndex (L := L) v) : 𝓞 L :=
  (Ideal.Quotient.mk_surjective (residueBasis v i)).choose

/-- Each integral representative reduces to its chosen residue basis vector.
Used in `no_integral_relation`. -/
private theorem residueLift_mk (v : HeightOneSpectrum (𝓞 K))
    (i : ResidueIndex (L := L) v) :
    Ideal.Quotient.mk (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal)
      (residueLift v i) = residueBasis v i :=
  (Ideal.Quotient.mk_surjective (residueBasis v i)).choose_spec

/-- The residue quotient has degree `[L : K]` over the residue field.
This is Mathlib's fiber dimension formula after identifying the quotient with the fiber at `v`;
Mathlib's `Ideal.finrank_quotient_map` states the same but is deprecated in the pinned version.
Used in `residueIndex_card`. -/
private theorem finrank_residueQuotient
    (v : HeightOneSpectrum (𝓞 K)) :
    Module.finrank (𝓞 K ⧸ v.asIdeal)
      (𝓞 L ⧸ Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal) =
    Module.finrank K L := by
  let p := v.asIdeal
  let q := Ideal.map (algebraMap (𝓞 K) (𝓞 L)) p
  let eκ : (𝓞 K ⧸ p) ≃ₐ[𝓞 K] p.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom (𝓞 K) (𝓞 K ⧸ p) p.ResidueField)
      p.bijective_algebraMap_quotient_residueField
  let e : (𝓞 L ⧸ q) ≃+* p.Fiber (𝓞 L) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (𝓞 L) p).toRingEquiv.trans
      (((Algebra.TensorProduct.congr (AlgEquiv.refl : 𝓞 L ≃ₐ[𝓞 K] 𝓞 L) eκ).trans
        (Algebra.TensorProduct.comm (𝓞 K) (𝓞 L) p.ResidueField)).toRingEquiv)
  have he_mk (x : 𝓞 L) : e (Ideal.Quotient.mk q x) =
      (1 : p.ResidueField) ⊗ₜ[𝓞 K] x := by
    change (Algebra.TensorProduct.comm (𝓞 K) (𝓞 L) p.ResidueField)
      ((Algebra.TensorProduct.map (AlgHom.id (𝓞 K) (𝓞 L)) (eκ : (𝓞 K ⧸ p) →ₐ[𝓞 K] p.ResidueField))
        ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot (𝓞 L) p)
          (Ideal.Quotient.mk q x))) = _
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one,
      Algebra.TensorProduct.comm_tmul]
  have heq : Module.finrank (𝓞 K ⧸ p) (𝓞 L ⧸ q) =
      Module.finrank p.ResidueField (p.Fiber (𝓞 L)) := by
    apply Algebra.finrank_eq_of_equiv_equiv eκ.toRingEquiv e
    apply RingHom.ext
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hquot : (algebraMap (𝓞 K ⧸ p) (𝓞 L ⧸ q)) (Ideal.Quotient.mk p r) =
        Ideal.Quotient.mk q ((algebraMap (𝓞 K) (𝓞 L)) r) := rfl
    simp only [RingHom.comp_apply]
    rw [hquot]
    change (algebraMap p.ResidueField (p.Fiber (𝓞 L)))
      (eκ (Ideal.Quotient.mk p r)) = e (Ideal.Quotient.mk q ((algebraMap (𝓞 K) (𝓞 L)) r))
    rw [he_mk]
    change eκ (Ideal.Quotient.mk p r) ⊗ₜ[𝓞 K] (1 : 𝓞 L) =
      (1 : p.ResidueField) ⊗ₜ[𝓞 K] ((algebraMap (𝓞 K) (𝓞 L)) r)
    rw [show eκ (Ideal.Quotient.mk p r) = algebraMap (𝓞 K) p.ResidueField r from rfl]
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul r
  rw [heq, Ideal.finrank_fiber_eq_finrank]
  exact (IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L).symm

/-- The integral lift of a relation differs from it by its approximation errors at `w`.
Used in `lifted_sum_mem_map`. -/
private theorem lifted_sum_at_place (v : HeightOneSpectrum (𝓞 K))
    (a : ResidueIndex (L := L) v → v.adicCompletion K)
    (c : ResidueIndex (L := L) v → 𝓞 K)
    (hrel : ∀ w : PrimeAbove (L := L) v,
      ∑ i, algebraMap (v.adicCompletion K) ((PrimeAbove.place v w).adicCompletion L) (a i) *
        algebraMap L ((PrimeAbove.place v w).adicCompletion L)
          (algebraMap (𝓞 L) L (residueLift v i)) = 0)
    (w : PrimeAbove (L := L) v) :
    algebraMap L ((PrimeAbove.place v w).adicCompletion L)
      (algebraMap (𝓞 L) L (∑ i, c i • residueLift v i)) =
    ∑ i, algebraMap (v.adicCompletion K) ((PrimeAbove.place v w).adicCompletion L)
        (algebraMap (𝓞 K) (v.adicCompletion K) (c i) - a i) *
      algebraMap L ((PrimeAbove.place v w).adicCompletion L)
        (algebraMap (𝓞 L) L (residueLift v i)) := by
  have hbase : algebraMap L ((PrimeAbove.place v w).adicCompletion L)
      (algebraMap (𝓞 L) L (∑ i, c i • residueLift v i)) =
    ∑ i, algebraMap (v.adicCompletion K) ((PrimeAbove.place v w).adicCompletion L)
        (algebraMap (𝓞 K) (v.adicCompletion K) (c i)) *
      algebraMap L ((PrimeAbove.place v w).adicCompletion L)
        (algebraMap (𝓞 L) L (residueLift v i)) := by
    simp only [map_sum, Algebra.smul_def, map_mul]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    rw [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
      IsScalarTower.algebraMap_apply (𝓞 K) K L,
      ← IsScalarTower.algebraMap_apply K L ((PrimeAbove.place v w).adicCompletion L),
      IsScalarTower.algebraMap_apply K (v.adicCompletion K)
        ((PrimeAbove.place v w).adicCompletion L),
      ← IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K)]
  rw [hbase]
  simp only [map_sub, sub_mul, Finset.sum_sub_distrib, hrel w, sub_zero]

/-- Approximation errors force the integral lift of a relation into the extended prime ideal.
Used in `no_integral_relation`. -/
private theorem lifted_sum_mem_map
    (v : HeightOneSpectrum (𝓞 K))
    (a : ResidueIndex (L := L) v → v.adicCompletion K)
    (c : ResidueIndex (L := L) v → 𝓞 K)
    (hc : ∀ i, ‖a i - algebraMap (𝓞 K) (v.adicCompletion K) (c i)‖ <
      (Ideal.absNorm v.asIdeal : ℝ)⁻¹)
    (hrel : ∀ w : PrimeAbove (L := L) v,
      ∑ i, algebraMap (v.adicCompletion K) ((PrimeAbove.place v w).adicCompletion L) (a i) *
        algebraMap L ((PrimeAbove.place v w).adicCompletion L)
          (algebraMap (𝓞 L) L (residueLift v i)) = 0) :
    (∑ i, c i • residueLift v i) ∈
      Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal := by
  apply mem_map_of_norm v (∑ i, c i • residueLift v i)
  intro w
  let E := (SIC.FinitePlace.PrimeAbove.place v w).adicCompletion L
  let e := w.1.ramificationIdx (𝓞 K)
  let f := w.1.inertiaDeg (𝓞 K)
  let t : ℝ := (Ideal.absNorm v.asIdeal : ℝ)⁻¹
  change ‖algebraMap L E (algebraMap (𝓞 L) L (∑ i, c i • residueLift v i))‖ ≤ _
  rw [lifted_sum_at_place v a c hrel w]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (by positivity)
  intro i hi
  have hdiff : ‖algebraMap (𝓞 K) (v.adicCompletion K) (c i) - a i‖ < t := by
    simpa only [norm_sub_rev] using hc i
  have hmap :
      ‖algebraMap (v.adicCompletion K) E
          (algebraMap (𝓞 K) (v.adicCompletion K) (c i) - a i)‖ ≤ t ^ (e * f) := by
    change ‖SIC.FinitePlace.completionMap v
      (SIC.FinitePlace.PrimeAbove.place v w) _‖ ≤ _
    rw [SIC.FinitePlace.completionMap_norm]
    change ‖algebraMap (𝓞 K) (v.adicCompletion K) (c i) - a i‖ ^ (e * f) ≤
      t ^ (e * f)
    exact pow_le_pow_left₀ (norm_nonneg _) hdiff.le _
  have hb : ‖algebraMap L E
      (algebraMap (𝓞 L) L (residueLift v i))‖ ≤ 1 :=
    NumberField.FinitePlace.norm_le_one L (SIC.FinitePlace.PrimeAbove.place v w)
      (residueLift v i)
  calc
    ‖algebraMap (v.adicCompletion K) E
        (algebraMap (𝓞 K) (v.adicCompletion K) (c i) - a i) *
      algebraMap L E (algebraMap (𝓞 L) L (residueLift v i))‖ =
        ‖algebraMap (v.adicCompletion K) E
          (algebraMap (𝓞 K) (v.adicCompletion K) (c i) - a i)‖ *
        ‖algebraMap L E (algebraMap (𝓞 L) L (residueLift v i))‖ := norm_mul _ _
    _ ≤ t ^ (e * f) * 1 := by gcongr
    _ = _ := by simpa only [mul_one] using threshold_eq v w

/-- A normalized relation vanishing at every completion contradicts independence modulo `v`.
This follows Serre, *Local Fields*, Chapter II, §3, Proposition 4; used in `localLI`. -/
private theorem no_integral_relation
    (v : HeightOneSpectrum (𝓞 K))
    (a : ResidueIndex (L := L) v → v.adicCompletion K)
    (ha : ∀ i, ‖a i‖ ≤ 1) (j : ResidueIndex (L := L) v) (haj : a j = 1)
    (hrel : ∀ w : SIC.FinitePlace.PrimeAbove (L := L) v,
      ∑ i, algebraMap (v.adicCompletion K)
        ((SIC.FinitePlace.PrimeAbove.place v w).adicCompletion L) (a i) *
        algebraMap L ((SIC.FinitePlace.PrimeAbove.place v w).adicCompletion L)
          (algebraMap (𝓞 L) L (residueLift v i)) = 0) : False := by
  classical
  choose c hc using fun i => exists_integral_approx v (ha i)
  let y : 𝓞 L := ∑ i, c i • residueLift v i
  have hyP : y ∈ Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal := by
    simpa only [y] using lifted_sum_mem_map v a c hc hrel
  let q := Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal
  have hy0 : Ideal.Quotient.mk q y = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hyP
  have hres : (∑ i, (Ideal.Quotient.mk v.asIdeal (c i)) • residueBasis v i) = 0 := by
    calc
      (∑ i, (Ideal.Quotient.mk v.asIdeal (c i)) • residueBasis v i) =
        Ideal.Quotient.mk q y := by
          simp only [y, map_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [← residueLift_mk v i]
          change (Ideal.Quotient.mk v.asIdeal (c i)) •
            (Ideal.Quotient.mk q (residueLift v i)) =
            Ideal.Quotient.mk q ((algebraMap (𝓞 K) (𝓞 L)) (c i) * residueLift v i)
          exact Ideal.Quotient.mk_smul_mk_quotient_map_quotient (c i) (residueLift v i)
      _ = 0 := hy0
  have hc0 : Ideal.Quotient.mk v.asIdeal (c j) = 0 :=
    (Fintype.linearIndependent_iff.mp (residueBasis v).linearIndependent) _ hres j
  have hcP : c j ∈ v.asIdeal := (Ideal.Quotient.eq_zero_iff_mem).mp hc0
  have hcn : ‖algebraMap (𝓞 K) (v.adicCompletion K) (c j)‖ < 1 :=
    (NumberField.FinitePlace.norm_lt_one_iff_mem K v (c j)).mpr hcP
  have happroxj : ‖(1 : v.adicCompletion K) -
      algebraMap (𝓞 K) (v.adicCompletion K) (c j)‖ <
      (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by simpa only [haj] using hc j
  have ht1 : (Ideal.absNorm v.asIdeal : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v)
  have hcontra := IsUltrametricDist.norm_add_le_max
    ((1 : v.adicCompletion K) - algebraMap (𝓞 K) (v.adicCompletion K) (c j))
    (algebraMap (𝓞 K) (v.adicCompletion K) (c j))
  have hlt : max
      ‖(1 : v.adicCompletion K) - algebraMap (𝓞 K) (v.adicCompletion K) (c j)‖
      ‖algebraMap (𝓞 K) (v.adicCompletion K) (c j)‖ < 1 :=
    max_lt (happroxj.trans ht1) hcn
  simp only [sub_add_cancel, norm_one] at hcontra
  exact (not_lt_of_ge hcontra) hlt

/-- The images of the tensor basis are linearly independent in the product of completions.
Used in `baseChangeAlgHom_injective`. -/
private theorem localLI
    (v : HeightOneSpectrum (𝓞 K)) :
    LinearIndependent (v.adicCompletion K)
      (fun i : ResidueIndex (L := L) v =>
        SIC.FinitePlace.baseChangeAlgHom v
          ((1 : v.adicCompletion K) ⊗ₜ[K] (algebraMap (𝓞 L) L (residueLift v i)))) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hsum i
  by_contra hgi
  let s : Finset (ResidueIndex (L := L) v) := Finset.univ.filter (fun j => g j ≠ 0)
  have hs : s.Nonempty := ⟨i, by simp [s, hgi]⟩
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun k => ‖g k‖) hs
  have hgj : g j ≠ 0 := (Finset.mem_filter.mp hj).2
  let a k := g k / g j
  have ha k : ‖a k‖ ≤ 1 := by
    by_cases hgk : g k = 0
    · simp [a, hgk]
    · have hk : k ∈ s := by simp [s, hgk]
      have hle := hmax k hk
      dsimp [a]
      rw [norm_div]
      exact (div_le_one (norm_pos_iff.mpr hgj)).mpr hle
  have haj : a j = 1 := div_self hgj
  have hsum' : ∑ k, a k • SIC.FinitePlace.baseChangeAlgHom v
          ((1 : v.adicCompletion K) ⊗ₜ[K] (algebraMap (𝓞 L) L (residueLift v k))) = 0 := by
    have h := congrArg (fun z => (g j)⁻¹ • z) hsum
    simpa only [Finset.smul_sum, smul_smul, inv_mul_eq_div, inv_smul_smul, smul_zero, a]
      using h
  have hrel (w : SIC.FinitePlace.PrimeAbove (L := L) v) :
      ∑ k, algebraMap (v.adicCompletion K)
          ((SIC.FinitePlace.PrimeAbove.place v w).adicCompletion L) (a k) *
        algebraMap L ((SIC.FinitePlace.PrimeAbove.place v w).adicCompletion L)
          (algebraMap (𝓞 L) L (residueLift v k)) = 0 := by
    have hw := congrArg (fun z => z w) hsum'
    simpa [SIC.FinitePlace.baseChangeAlgHom_tmul, Pi.mul_apply, Algebra.smul_def] using hw
  exact (no_integral_relation v a ha j haj hrel).elim

/-- The integral residue lifts are independent over `K`. Used in `liftedBasis`. -/
private theorem residueLift_linearIndependent
    (v : HeightOneSpectrum (𝓞 K)) :
    LinearIndependent K (fun i : ResidueIndex (L := L) v =>
      algebraMap (𝓞 L) L (residueLift v i)) := by
  let f : L →ₗ[K] (∀ w : PrimeAbove (L := L) v,
      (PrimeAbove.place v w).adicCompletion L) :=
    ((baseChangeAlgHom v).restrictScalars K).toLinearMap.comp
      Algebra.TensorProduct.includeRight.toLinearMap
  apply LinearIndependent.of_comp f
  convert (localLI (L := L) v).restrict_scalars' K using 1
  funext i
  rfl

/-- The residue basis has `[L : K]` vectors. Used in `liftedBasis`. -/
private theorem residueIndex_card
    (v : HeightOneSpectrum (𝓞 K)) :
    Fintype.card (ResidueIndex (L := L) v) = Module.finrank K L := by
  rw [← Module.finrank_eq_card_basis (residueBasis v)]
  exact finrank_residueQuotient v

/-- The integral residue lifts form a `K`-basis of `L`. Used in `baseChangeAlgHom_injective`. -/
private noncomputable def liftedBasis
    (v : HeightOneSpectrum (𝓞 K)) : Module.Basis (ResidueIndex (L := L) v) K L := by
  letI : Fintype (ResidueIndex (L := L) v) := Fintype.ofFinite _
  exact basisOfLinearIndependentOfCardEqFinrank'
    (fun i => algebraMap (𝓞 L) L (residueLift v i))
    (residueLift_linearIndependent v) (residueIndex_card v)

/-- The canonical map $K_v \otimes_K L \to \prod_{w \mid v} L_w$ is injective. Serre,
*Local Fields*, Chapter II, §3, Proposition 4, reduced modulo the prime of `v`. -/
theorem baseChangeAlgHom_injective : Function.Injective (baseChangeAlgHom (L := L) v) := by
  let b := liftedBasis (L := L) v
  let bt := Algebra.TensorProduct.basis (v.adicCompletion K) b
  apply LinearMap.injective_of_linearIndependent (f := (baseChangeAlgHom (L := L) v).toLinearMap)
    bt.span_eq
  convert localLI (L := L) v using 1
  funext i
  change baseChangeAlgHom v (bt i) = _
  rw [Algebra.TensorProduct.basis_apply]
  simp [b, liftedBasis]

/-- The decomposition $K_v \otimes_K L \cong \prod_{w \mid v} L_w$ at a finite place.
[83, Neukirch (1999), Chapter II, Proposition 8.3]. -/
@[source "83, Chapter II, Proposition 8.3, p. 164 (finite place)"]
def baseChangeEquiv :
    v.adicCompletion K ⊗[K] L ≃ₐ[v.adicCompletion K]
      ∀ w : PrimeAbove (L := L) v, (PrimeAbove.place v w).adicCompletion L :=
  AlgEquiv.ofBijective (baseChangeAlgHom v)
    ⟨baseChangeAlgHom_injective v, baseChangeAlgHom_surjective v⟩

/-- The decomposition sends $1 \otimes x$ to the diagonal image of `x`. -/
@[simp]
theorem baseChangeEquiv_one_tmul (x : L) (w : PrimeAbove (L := L) v) :
    baseChangeEquiv v ((1 : v.adicCompletion K) ⊗ₜ x) w =
      algebraMap L ((PrimeAbove.place v w).adicCompletion L) x := by
  change baseChangeAlgHom v ((1 : v.adicCompletion K) ⊗ₜ x) w = _
  simp

/-- The local degrees above a finite place add up to the global degree:
$\sum_{w \mid v} [L_w : K_v] = [L : K]$. [83, Neukirch (1999), Chapter II, Corollary 8.4]. -/
@[source "83, Chapter II, Corollary 8.4, p. 164 (degree, finite place)"]
theorem sum_finrank_primeAbove :
    ∑ w : PrimeAbove (L := L) v,
        Module.finrank (v.adicCompletion K) ((PrimeAbove.place v w).adicCompletion L) =
      Module.finrank K L := by
  exact (finrank_eq_sum_of_algEquiv (baseChangeEquiv v)).symm

/-- The norm of `x ∈ L` is the product of its local norms above a finite place:
$N_{L/K}(x) = \prod_{w \mid v} N_{L_w/K_v}(x)$ in $K_v$.
[83, Neukirch (1999), Chapter II, Corollary 8.4]. -/
@[source "83, Chapter II, Corollary 8.4, p. 164 (norm, finite place)"]
theorem algebraMap_norm_eq_prod (x : L) :
    algebraMap K (v.adicCompletion K) (Algebra.norm K x) =
      ∏ w : PrimeAbove (L := L) v, Algebra.norm (v.adicCompletion K)
        (algebraMap L ((PrimeAbove.place v w).adicCompletion L) x) := by
  simpa only [baseChangeEquiv_one_tmul] using
    algebraMap_norm_eq_prod_of_algEquiv (baseChangeEquiv v) x

end FinitePlace

end SIC
