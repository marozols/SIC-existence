/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.FieldTheory.Kummer.Basic
import SICs.FieldTheory.GaloisDescent
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-!
# The Kummer pairing

The pairing of radicands with Galois characters, and its kernel, the base-field nth powers.

This follows Milne, *Fields and Galois Theory*, version 5.10 (2022), the argument preceding
Theorem 5.30, and *Class Field Theory*, version 4.03 (2020), Chapter VII, Appendix A.3.
The latter cites Theorem 5.29 of *Fields and Galois Theory*; this is Theorem 5.30 in the
pinned version 5.10.

## The argument

If $a=\alpha^n\in K^\times$, pair its class with an automorphism by
$\sigma\alpha/\alpha\in\mu_n$. Base-field roots of unity make this independent of the chosen
root and multiplicative in both arguments. Its kernel is the base-field nth powers, by Galois
descent.
-/

noncomputable section
namespace SIC

variable (K : Type*) [Field K] (n : ℕ) (L : Type*) [Field L] [Algebra K L]
/-! ### Power maps and chosen roots

The nth-power map on $K^\times$ takes values in $B(L)$. A chosen root of each radicand
will define the pairing; the root-choice lemma later removes dependence on this choice. -/

/-- Base-field nth powers as radicands in $L$; the denominator of the Kummer power classes.
Milne, *Fields and Galois Theory*, proof of Theorem 5.30. -/
def kummerPow : Kˣ →* kummerRadicands K n L :=
  (powMonoidHom n).codRestrict _ fun a ↦
    ⟨algebraMap K L (a : K), by simp⟩

/-- The power map into the radicands subgroup is the ordinary nth-power map. -/
@[simp] theorem kummerPow_coe (a : Kˣ) : (kummerPow K n L a).val = a ^ n := rfl

variable {K L n} [NeZero n]

/-- A chosen unit root of a radicand; used only to construct `kummerPairing`. -/
private def radicandRoot (a : kummerRadicands K n L) : Lˣ :=
  Units.mk0 a.property.choose (by
    intro hx
    apply a.val.ne_zero
    apply (algebraMap K L).injective
    simpa [hx, NeZero.ne n] using a.property.choose_spec.symm)

/-- The chosen unit root has its prescribed nth power. -/
private theorem radicandRoot_pow (a : kummerRadicands K n L) :
    radicandRoot a ^ n = Units.map (algebraMap K L : K →* L) a.val := by
  exact Units.ext a.property.choose_spec

/-- Automorphisms fix base-field units; used by the pairing and its kernel. -/
private theorem smul_unitsMap (σ : Gal(L/K)) (a : Kˣ) :
    σ • Units.map (algebraMap K L : K →* L) a =
      Units.map (algebraMap K L : K →* L) a := by
  exact Units.ext (σ.commutes a)

/-! ### The Kummer pairing

For a chosen root $\alpha$, the quotient $\sigma\alpha/\alpha$ lies in $\mu_n(L)$.
The primitive root identifies these roots of unity with $\mu_n(K)$. Any other root is a
base-field root of unity times $\alpha$, so this quotient is independent of its choice.
Automorphisms fix these quotients, giving multiplicativity in the automorphism variable. -/

/-- The quotient $\sigma\alpha/\alpha$ as a root of unity in $L$; used by `pairingValue`. -/
private def rootRatio (a : kummerRadicands K n L) (σ : Gal(L/K)) : rootsOfUnity n L :=
  ⟨σ • radicandRoot a / radicandRoot a, by
    rw [mem_rootsOfUnity, div_pow, ← smul_pow', radicandRoot_pow, smul_unitsMap, div_self']⟩

/-- Transport the root quotient to $\mu_n(K)$; used by `kummerPairing`. -/
private def pairingValue {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (a : kummerRadicands K n L) (σ : Gal(L/K)) : rootsOfUnity n K :=
  (rootsOfUnityEquivOfPrimitiveRoots (algebraMap K L).injective
    ⟨ζ, (mem_primitiveRoots (NeZero.pos n)).2 hζ⟩).symm (rootRatio a σ)

/-- The transported pairing value is $\sigma\alpha/\alpha$ for the chosen root. -/
private theorem pairingValue_spec {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (a : kummerRadicands K n L) (σ : Gal(L/K)) :
    Units.map (algebraMap K L : K →* L) (pairingValue hζ a σ).val =
      σ • radicandRoot a / radicandRoot a := by
  apply Units.ext
  exact rootsOfUnityEquivOfPrimitiveRoots_symm_apply (algebraMap K L).injective
    ⟨ζ, (mem_primitiveRoots (NeZero.pos n)).2 hζ⟩ (rootRatio a σ)

/-- The pairing value is independent of the chosen root; used by `kummerPairing_apply`. -/
private theorem pairingValue_spec_of_root {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (a : kummerRadicands K n L) (α : Lˣ)
    (hα : α ^ n = Units.map (algebraMap K L : K →* L) a.val) (σ : Gal(L/K)) :
    Units.map (algebraMap K L : K →* L) (pairingValue hζ a σ).val = σ • α / α := by
  rw [pairingValue_spec]
  have heq : ((radicandRoot a : Lˣ) : L) ^ n = (α : L) ^ n :=
    congrArg Units.val ((radicandRoot_pow a).trans hα.symm)
  obtain ⟨i, _, hi⟩ := exists_base_mul_of_pow_eq hζ (NeZero.pos n) heq
  apply Units.ext
  simp only [Units.val_div_eq_div_val, AlgEquiv.smul_units_def, Units.coe_map,
    MonoidHom.coe_coe]
  rw [hi, map_mul, σ.commutes]
  exact mul_div_mul_left _ _
    ((map_ne_zero (algebraMap K L)).2 (pow_ne_zero _ (hζ.ne_zero (NeZero.ne n))))

/-- The pairing is multiplicative in the automorphism; used by `kummerPairing`. -/
private theorem pairingValue_mul_aut {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (a : kummerRadicands K n L) (σ τ : Gal(L/K)) :
    pairingValue hζ a (σ * τ) = pairingValue hζ a σ * pairingValue hζ a τ := by
  apply Subtype.ext
  apply Units.map_injective (f := (algebraMap K L : K →* L)) (algebraMap K L).injective
  simp only [Subgroup.coe_mul, map_mul, pairingValue_spec, mul_smul]
  have hτ := pairingValue_spec hζ a τ
  have hfixed := smul_unitsMap σ (pairingValue hζ a τ).val
  rw [hτ, smul_div'] at hfixed
  rw [← hfixed, mul_comm]
  exact (div_mul_div_cancel _ _ _).symm

/-- The Kummer pairing $a\mapsto(\sigma\mapsto\sigma\alpha/\alpha)$, where $\alpha^n=a$.
Milne, *Fields and Galois Theory*, argument preceding Theorem 5.30. -/
def kummerPairing {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    kummerRadicands K n L →* (Gal(L/K) →* rootsOfUnity n K) where
  toFun a :=
    { toFun := pairingValue hζ a
      map_one' := by
        apply Subtype.ext
        apply Units.map_injective (f := (algebraMap K L : K →* L)) (algebraMap K L).injective
        simp [pairingValue_spec]
      map_mul' := pairingValue_mul_aut hζ a }
  map_one' := by
    apply MonoidHom.ext
    intro σ
    apply Subtype.ext
    apply Units.map_injective (f := (algebraMap K L : K →* L)) (algebraMap K L).injective
    have h := pairingValue_spec_of_root hζ 1 1 (by simp) σ
    simpa using h
  map_mul' a b := by
    apply MonoidHom.ext
    intro σ
    apply Subtype.ext
    apply Units.map_injective (f := (algebraMap K L : K →* L)) (algebraMap K L).injective
    have hα : (radicandRoot a * radicandRoot b) ^ n =
        Units.map (algebraMap K L : K →* L) (a * b).val := by
      simp [mul_pow, radicandRoot_pow]
    change Units.map (algebraMap K L : K →* L) (pairingValue hζ (a * b) σ).val =
      Units.map (algebraMap K L : K →* L)
        ((pairingValue hζ a σ).val * (pairingValue hζ b σ).val)
    rw [pairingValue_spec_of_root hζ (a * b) _ hα, map_mul,
      pairingValue_spec, pairingValue_spec, smul_mul', mul_div_mul_comm]

/-- The Kummer pairing evaluated using any specified nth root $\alpha$ of $a$ is
$\sigma\alpha/\alpha$. Milne, *Fields and Galois Theory*, argument preceding Theorem 5.30. -/
theorem kummerPairing_apply {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (a : kummerRadicands K n L) (α : Lˣ)
    (hα : α ^ n = Units.map (algebraMap K L : K →* L) a.val) (σ : Gal(L/K)) :
    Units.map (algebraMap K L : K →* L) ((kummerPairing hζ a σ).val) = σ • α / α :=
  pairingValue_spec_of_root hζ a α hα σ

/-! ### The kernel

A radicand pairs trivially precisely when its root is fixed, hence belongs to $K$ by Galois
descent. -/

variable [FiniteDimensional K L] [IsGalois K L]

/-- The kernel of the Kummer pairing is $K^{\times n}$ inside $B(L)$.
Milne, *Fields and Galois Theory*, exact sequence preceding Theorem 5.30. -/
theorem ker_kummerPairing {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    (kummerPairing (L := L) hζ).ker = (kummerPow K n L).range := by
  apply Subgroup.ext
  intro a
  constructor
  · intro ha
    have hfixed : radicandRoot a ∈ FixedPoints.subgroup Gal(L/K) Lˣ := by
      rw [FixedPoints.mem_subgroup]
      intro σ
      have h := kummerPairing_apply hζ a (radicandRoot a) (radicandRoot_pow a) σ
      have htriv : kummerPairing hζ a σ = 1 := congrArg (fun f => f σ) ha
      rw [htriv, OneMemClass.coe_one, map_one] at h
      exact div_eq_one.mp h.symm
    rw [← range_unitsMap_algebraMap] at hfixed
    obtain ⟨b, hb⟩ := hfixed
    refine ⟨b, Subtype.ext ?_⟩
    apply Units.map_injective (f := (algebraMap K L : K →* L)) (algebraMap K L).injective
    simpa only [kummerPow_coe, map_pow, hb] using radicandRoot_pow a
  · rintro ⟨b, rfl⟩
    apply MonoidHom.ext
    intro σ
    apply Subtype.ext
    apply Units.map_injective (f := (algebraMap K L : K →* L)) (algebraMap K L).injective
    have h := kummerPairing_apply hζ (kummerPow K n L b)
      (Units.map (algebraMap K L : K →* L) b) (by simp) σ
    simpa only [smul_unitsMap, div_self', MonoidHom.one_apply, OneMemClass.coe_one,
      map_one] using h

/-! ### Enough roots of unity

If a group is killed by $n$, every $K^\times$-valued character of it takes values in $\mu_n$, so
a primitive nth root of unity supplies the roots of unity that finite abelian character duality
needs. -/

/-- A primitive nth root supplies enough roots of unity for the exponent of a group killed
by $n$. This bridges primitive-root hypotheses to Mathlib's character-duality API. -/
theorem hasEnoughRootsOfUnity_exponent {G : Type*} [Monoid G] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (hexp : ∀ g : G, g ^ n = 1) :
    HasEnoughRootsOfUnity K (Monoid.exponent G) := by
  have : HasEnoughRootsOfUnity K n := ⟨⟨ζ, hζ⟩, inferInstance⟩
  exact HasEnoughRootsOfUnity.of_dvd K (Monoid.exponent_dvd_of_forall_pow_eq_one hexp)

end SIC
