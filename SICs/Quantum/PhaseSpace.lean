/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Quantum.RootsOfUnity
import SICs.MatrixNotation
import Mathlib.Data.ZMod.Units
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Integer phase space, residues, and transversals

Integer and residue phase space, canonical representatives, transversals, negation, and symplectic
matrix arithmetic.

The integer and residue indices of [AFK25, Section 3.1, equation (3.1)] are related by
coordinatewise reduction. Canonical representatives and complete transversals let later
operator sums choose their indices. An integral matrix scales the symplectic pairing by
its determinant; a determinant coprime to the modulus therefore permutes residue classes
and transports transversals. These statements use no displacement operators.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

/-! ### Integer phase-space representatives

Integer phase space is related explicitly to its reductions modulo `d` and `dbar d`.  A transversal
then records one representative of every displacement class without choosing it canonically. -/

/-- The integer phase space used for displacement indices in [AFK25].

Using functions on `Fin 2` rather than pairs makes the action of a `2 × 2` twist matrix
literal matrix--vector multiplication. -/
abbrev IntPhaseSpace := Fin 2 → ℤ

/-- Phase space modulo `n`. In particular, normalized ghost overlaps are naturally indexed by
`PhaseSpaceMod (dbar d)`, while a displacement sum is indexed by `PhaseSpaceMod d`. -/
abbrev PhaseSpaceMod (n : ℕ) := Fin 2 → ZMod n

/-- Reduce an integer phase-space point coordinatewise modulo `n`. -/
def intPhaseSpaceMod (n : ℕ) (p : IntPhaseSpace) : PhaseSpaceMod n :=
  fun i => (p i : ZMod n)

/-- Negation of an integer phase-space point negates its residue. -/
lemma intPhaseSpaceMod_neg (d : ℕ) (p : IntPhaseSpace) :
    intPhaseSpaceMod d (-p) = -(intPhaseSpaceMod d p) := by
  funext i
  simp [intPhaseSpaceMod]

/-- An integer phase-space point is zero modulo `d` exactly when both of its coordinates are
divisible by `d`. -/
lemma intPhaseSpaceMod_eq_zero_iff_dvd (d : ℕ) (p : IntPhaseSpace) :
    intPhaseSpaceMod d p = 0 ↔ (d : ℤ) ∣ p 0 ∧ (d : ℤ) ∣ p 1 := by
  constructor
  · intro h
    constructor
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mp
      simpa only [intPhaseSpaceMod, Pi.zero_apply] using congrFun h 0
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mp
      simpa only [intPhaseSpaceMod, Pi.zero_apply] using congrFun h 1
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mpr h0
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mpr h1

/-- Congruent integer phase-space points differ by `d` times an integer phase-space point. -/
lemma exists_eq_add_smul_of_intPhaseSpaceMod_eq (d : ℕ) {p p' : IntPhaseSpace}
    (h : intPhaseSpaceMod d p' = intPhaseSpaceMod d p) :
    ∃ a : IntPhaseSpace, p' = p + (d : ℤ) • a := by
  have hdvd : ∀ i, (d : ℤ) ∣ p' i - p i := fun i =>
    Int.ModEq.dvd ((ZMod.intCast_eq_intCast_iff _ _ _).mp (congrFun h i)).symm
  refine ⟨fun i => (p' i - p i) / (d : ℤ), ?_⟩
  funext i
  have hcancel := Int.mul_ediv_cancel' (hdvd i)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linarith

/-- The canonical integer representative of a phase-space point, with both coordinates reduced
into `{0, …, d - 1}` when `d` is positive. -/
def canonicalIntPhaseSpaceRep (d : ℕ) (p : IntPhaseSpace) : IntPhaseSpace :=
  fun i => p i % (d : ℤ)

/-- Every coordinate of a canonical integer representative is nonnegative when `d` is positive. -/
lemma canonicalIntPhaseSpaceRep_nonneg {d : ℕ} (hd : 0 < d) (p : IntPhaseSpace) (i : Fin 2) :
    0 ≤ canonicalIntPhaseSpaceRep d p i :=
  Int.emod_nonneg _ (by exact_mod_cast hd.ne')

/-- Every coordinate of a canonical integer representative is strictly below a positive `d`. -/
lemma canonicalIntPhaseSpaceRep_lt {d : ℕ} (hd : 0 < d) (p : IntPhaseSpace) (i : Fin 2) :
    canonicalIntPhaseSpaceRep d p i < (d : ℤ) :=
  Int.emod_lt_of_pos _ (by exact_mod_cast hd)

/-- A canonical integer representative has the same coordinatewise remainder as its source. -/
lemma canonicalIntPhaseSpaceRep_emod (d : ℕ) (p : IntPhaseSpace) (i : Fin 2) :
    canonicalIntPhaseSpaceRep d p i % (d : ℤ) = p i % (d : ℤ) :=
  Int.emod_emod_of_dvd _ dvd_rfl

/-- Canonical integer representatives have the same residue as their source points. -/
lemma intPhaseSpaceMod_canonicalIntPhaseSpaceRep (d : ℕ) (p : IntPhaseSpace) :
    intPhaseSpaceMod d (canonicalIntPhaseSpaceRep d p) = intPhaseSpaceMod d p := by
  funext i
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr (canonicalIntPhaseSpaceRep_emod d p i)

/-- Congruent integer phase-space points have the same canonical integer representative. -/
lemma canonicalIntPhaseSpaceRep_eq_of_mod_eq (d : ℕ) {p p' : IntPhaseSpace}
    (h : intPhaseSpaceMod d p' = intPhaseSpaceMod d p) :
    canonicalIntPhaseSpaceRep d p' = canonicalIntPhaseSpaceRep d p := by
  funext i
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mp (congrFun h i)

/-- Taking the canonical integer representative twice changes nothing. -/
@[simp]
lemma canonicalIntPhaseSpaceRep_idem (d : ℕ) (p : IntPhaseSpace) :
    canonicalIntPhaseSpaceRep d (canonicalIntPhaseSpaceRep d p) =
      canonicalIntPhaseSpaceRep d p := by
  funext i
  exact canonicalIntPhaseSpaceRep_emod d p i

/-- A complete set of representatives for `ℤ² / dℤ²`, represented as a section of the
coordinatewise residue map.

This functional presentation gives exactly one integer representative of every residue class. It is
the form in which `ghostFiducialMatrix` and `AdmissibleTuple.shiftConvolutionSum` take the source's
"any set of coset representatives of `ℤ²/dℤ²`". -/
structure PhaseSpaceTransversal (d : ℕ) where
  /-- The chosen integer representative of each residue class. -/
  repr : PhaseSpaceMod d → IntPhaseSpace
  /-- Each chosen point represents the residue class at which it is indexed. -/
  residue_repr : ∀ q, intPhaseSpaceMod d (repr q) = q

/-- The canonical phase-space transversal whose coordinates lie in `{0, ..., d - 1}`. -/
noncomputable def canonicalPhaseSpaceTransversal (d : ℕ) [NeZero d] :
    PhaseSpaceTransversal d where
  repr q i := (q i).val
  residue_repr q := by
    funext i
    simp [intPhaseSpaceMod]

/-- The canonical transversal represents the zero residue by the origin. -/
@[simp]
lemma canonicalPhaseSpaceTransversal_repr_zero (d : ℕ) [NeZero d] :
    (canonicalPhaseSpaceTransversal d).repr 0 = 0 := by
  funext i
  simp [canonicalPhaseSpaceTransversal]

/-- The canonical transversal represents the residue of an integer point by its canonical
integer representative. -/
lemma canonicalPhaseSpaceTransversal_repr_mod (d : ℕ) [NeZero d] (p : IntPhaseSpace) :
    (canonicalPhaseSpaceTransversal d).repr (intPhaseSpaceMod d p) =
      canonicalIntPhaseSpaceRep d p := by
  funext i
  change ((((p i : ZMod d)).val : ℕ) : ℤ) = p i % (d : ℤ)
  rw [ZMod.val_intCast]

/-- The canonical representative in `Fin d` of an integer. -/
def intToFin (d : ℕ) [NeZero d] (a : ℤ) : Fin d :=
  (ZMod.finEquiv d).symm (a : ZMod d)

/-- Converting the integer value of a canonical representative back to `Fin d` recovers the
original representative. -/
@[simp]
lemma intToFin_finVal (d : ℕ) [NeZero d] (a : Fin d) :
    intToFin d (a.val : ℤ) = a := by
  apply (ZMod.finEquiv d).injective
  unfold intToFin
  rw [RingEquiv.apply_symm_apply, Int.cast_natCast]
  rw [← ZMod.natCast_zmod_val ((ZMod.finEquiv d) a)]
  congr
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ d => rfl

/-- An integer has canonical representative zero in `Fin d` exactly when it is zero modulo `d`. -/
lemma intToFin_eq_zero_iff (d : ℕ) [NeZero d] (a : ℤ) :
    intToFin d a = 0 ↔ (a : ZMod d) = 0 := by
  constructor
  · intro h
    have := congrArg (ZMod.finEquiv d) h
    simpa only [intToFin, RingEquiv.apply_symm_apply, map_zero] using this
  · intro h
    apply (ZMod.finEquiv d).injective
    simpa only [intToFin, RingEquiv.apply_symm_apply, map_zero]

/-- Casting an integer's canonical representative to `ZMod d` gives the original residue class. -/
@[simp]
lemma intToFin_cast (d : ℕ) [NeZero d] (a : ℤ) :
    ((intToFin d a).val : ZMod d) = (a : ZMod d) := by
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      change (((a : ZMod (n + 1)).val : ℕ) : ZMod (n + 1)) =
        (a : ZMod (n + 1))
      exact ZMod.natCast_zmod_val (a : ZMod (n + 1))

/-- Convert an integer phase-space point to its pair of canonical `Fin d` representatives. -/
def intPhaseSpaceToFin (d : ℕ) [NeZero d] (p : IntPhaseSpace) : Fin d × Fin d :=
  (intToFin d (p 0), intToFin d (p 1))

/-- Regard a pair of canonical `Fin d` representatives as an integer phase-space point. -/
def finPhaseSpaceToInt {d : ℕ} (p : Fin d × Fin d) : IntPhaseSpace :=
  ![(p.1.val : ℤ), (p.2.val : ℤ)]

/-- Passing a pair of canonical representatives through integer phase space and back is the
identity. -/
@[simp]
lemma intPhaseSpaceToFin_finPhaseSpaceToInt (d : ℕ) [NeZero d]
    (p : Fin d × Fin d) :
    intPhaseSpaceToFin d (finPhaseSpaceToInt p) = p := by
  ext <;> simp [intPhaseSpaceToFin, finPhaseSpaceToInt]

/-- Negation commutes with taking canonical `Fin d` representatives. -/
lemma intToFin_neg (d : ℕ) [NeZero d] (a : ℤ) :
    intToFin d (-a) = -(intToFin d a) := by
  unfold intToFin
  rw [Int.cast_neg, map_neg]

/-- Negation commutes with taking canonical `Fin d` phase-space representatives. -/
lemma intPhaseSpaceToFin_neg (d : ℕ) [NeZero d] (p : IntPhaseSpace) :
    intPhaseSpaceToFin d (-p) =
      (-(intPhaseSpaceToFin d p).1, -(intPhaseSpaceToFin d p).2) := by
  simp [intPhaseSpaceToFin, intToFin_neg]

/-- An integer phase-space point has canonical representative zero exactly when it is zero
coordinatewise modulo `d`. -/
lemma intPhaseSpaceToFin_eq_zero_iff (d : ℕ) [NeZero d] (p : IntPhaseSpace) :
    intPhaseSpaceToFin d p = 0 ↔ intPhaseSpaceMod d p = 0 := by
  constructor
  · intro h
    funext i
    fin_cases i
    · have h₀ := congrArg Prod.fst h
      exact (intToFin_eq_zero_iff d (p 0)).mp (by
        simpa only [intPhaseSpaceToFin, Prod.fst_zero] using h₀)
    · have h₁ := congrArg Prod.snd h
      exact (intToFin_eq_zero_iff d (p 1)).mp (by
        simpa only [intPhaseSpaceToFin, Prod.snd_zero] using h₁)
  · intro h
    apply Prod.ext
    · apply (intToFin_eq_zero_iff d (p 0)).mpr
      have h₀ := congrFun h 0
      simpa only [intPhaseSpaceMod, Pi.zero_apply] using h₀
    · apply (intToFin_eq_zero_iff d (p 1)).mpr
      have h₁ := congrFun h 1
      simpa only [intPhaseSpaceMod, Pi.zero_apply] using h₁

/-- The residue class of an integer phase-space point is determined by its canonical `Fin d`
representative. -/
lemma intPhaseSpaceMod_eq_of_intPhaseSpaceToFin_eq {d : ℕ} [NeZero d]
    {r : IntPhaseSpace} {p : Fin d × Fin d} (h : intPhaseSpaceToFin d r = p) :
    intPhaseSpaceMod d r = intPhaseSpaceMod d (finPhaseSpaceToInt p) := by
  subst h
  funext i
  fin_cases i <;>
    simp [intPhaseSpaceMod, finPhaseSpaceToInt, intPhaseSpaceToFin]

/-- Congruent integer phase-space points have the same canonical `Fin d` representatives. -/
lemma intPhaseSpaceToFin_eq_of_mod_eq {d : ℕ} [NeZero d]
    {p p' : IntPhaseSpace} (h : intPhaseSpaceMod d p' = intPhaseSpaceMod d p) :
    intPhaseSpaceToFin d p' = intPhaseSpaceToFin d p := by
  apply Prod.ext
  · apply (ZMod.finEquiv d).injective
    simpa only [intPhaseSpaceToFin, intToFin, RingEquiv.apply_symm_apply,
      intPhaseSpaceMod] using congrFun h 0
  · apply (ZMod.finEquiv d).injective
    simpa only [intPhaseSpaceToFin, intToFin, RingEquiv.apply_symm_apply,
      intPhaseSpaceMod] using congrFun h 1

/-! ### Negating canonical residues -/

/-- The canonical residue of `-x` modulo `d`. This represents negation in integer phase space. -/
def negRes (d : ℕ) (x : ℤ) : ℤ := (-x) % (d : ℤ)


/-- The canonical residue of zero is zero. -/
lemma negRes_zero (d : ℕ) : negRes d 0 = 0 := by simp [negRes]

/-- For `0 < x < d`, the canonical residue of `-x` is `d - x`. -/
lemma negRes_eq_sub {d : ℕ} (x : ℤ) (hx0 : 0 < x) (hxd : x < (d : ℤ)) :
    negRes d x = (d : ℤ) - x := by
  unfold negRes
  rw [Int.neg_emod]
  have hnd : ¬ (d : ℤ) ∣ x := fun h ↦ absurd (Int.le_of_dvd hx0 h) (by omega)
  rw [ite_eq_right hnd, Int.emod_eq_of_lt hx0.le hxd]
  simp



/-! ### Symplectic pairing and matrix actions -/

/-- The integral symplectic form `⟨p,q⟩ = p₂q₁ - p₁q₂` used in the representative-change
laws for displacement operators and candidate ghost overlaps. This is the discrete symplectic
form of [AFK25, Definition 3.1, equation (3.1)], restricted to `p, q ∈ ℤ²`. -/
def intSymplecticForm (p q : IntPhaseSpace) : ℤ :=
  p 1 * q 0 - p 0 * q 1
/-- An integer `2 × 2` matrix scales the symplectic form by its determinant. -/
theorem intSymplecticForm_matrix_mulVec
    (G : Mat(2, ℤ)) (p q : IntPhaseSpace) :
    intSymplecticForm (Matrix.mulVec G p) (Matrix.mulVec G q) =
      G.det * intSymplecticForm p q := by
  simp only [intSymplecticForm, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.det_fin_two]
  ring

/-- Reduction modulo `d` commutes with integer matrix-vector multiplication. -/
lemma intPhaseSpaceMod_matrix_mulVec (d : ℕ) (G : Mat(2, ℤ))
    (p : IntPhaseSpace) :
    intPhaseSpaceMod d (Matrix.mulVec G p) =
      Matrix.mulVec (G.map (Int.castRingHom (ZMod d))) (intPhaseSpaceMod d p) := by
  funext i
  exact (Int.castRingHom (ZMod d)).map_mulVec G p i

/-- Equality of integer phase-space points modulo `dbar d` implies equality modulo `d`. -/
theorem intPhaseSpaceMod_eq_of_dbar_eq {d : ℕ} {p p' : IntPhaseSpace}
    (h : intPhaseSpaceMod (dbar d) p' = intPhaseSpaceMod (dbar d) p) :
    intPhaseSpaceMod d p' = intPhaseSpaceMod d p := by
  funext i
  rw [← sub_eq_zero]
  change (p' i : ZMod d) - (p i : ZMod d) = 0
  rw [← Int.cast_sub]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).2
  have hdvd : (d : ℤ) ∣ (dbar d : ℤ) := by
    exact_mod_cast dvd_dbar d
  apply dvd_trans hdvd
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (dbar d)).1
  rw [Int.cast_sub]
  have hi := congrFun h i
  simpa only [intPhaseSpaceMod, sub_eq_zero] using hi

/-- Integer matrix-vector multiplication preserves congruence of phase-space points modulo `d`. -/
theorem intPhaseSpaceMod_matrix_mulVec_eq {d : ℕ}
    (G : Mat(2, ℤ)) {p p' : IntPhaseSpace}
    (h : intPhaseSpaceMod d p' = intPhaseSpaceMod d p) :
    intPhaseSpaceMod d (Matrix.mulVec G p') =
      intPhaseSpaceMod d (Matrix.mulVec G p) := by
  rw [intPhaseSpaceMod_matrix_mulVec, intPhaseSpaceMod_matrix_mulVec, h]

/-- An integer matrix whose determinant is coprime to `d` acts injectively on `(ℤ/dℤ)²` after
reduction modulo `d`. -/
theorem mulVec_map_intCast_injective {d : ℕ} {G : Mat(2, ℤ)}
    (hG : IsCoprime G.det (d : ℤ)) :
    Function.Injective (G.map (Int.castRingHom (ZMod d))).mulVec := by
  have hdet : IsUnit (G.map (Int.castRingHom (ZMod d))).det := by
    change IsUnit ((Int.castRingHom (ZMod d)).mapMatrix G).det
    rw [← (Int.castRingHom (ZMod d)).map_det]
    exact (ZMod.coe_int_isUnit_iff_isCoprime G.det d).mpr hG.symm
  exact Matrix.mulVec_injective_of_isUnit
    ((G.map (Int.castRingHom (ZMod d))).isUnit_iff_isUnit_det.mpr hdet)

/-- An integer coprime to `dbar d` is coprime to `d`, since `d ∣ dbar d`. -/
theorem isCoprime_of_isCoprime_dbar {d : ℕ} {a : ℤ} (h : IsCoprime a (dbar d : ℤ)) :
    IsCoprime a (d : ℤ) :=
  h.of_isCoprime_of_dvd_right (by exact_mod_cast dvd_dbar d)

/-- An integer twist whose determinant is coprime to `dbar d` preserves nonzero phase-space
residues modulo `d`. -/
theorem intPhaseSpaceMod_matrix_mulVec_ne_zero {d : ℕ}
    (G : Mat(2, ℤ)) (hG : IsCoprime G.det (dbar d : ℤ))
    {p : IntPhaseSpace} (hp : intPhaseSpaceMod d p ≠ 0) :
    intPhaseSpaceMod d (Matrix.mulVec G p) ≠ 0 := by
  intro hzero
  apply hp
  apply mulVec_map_intCast_injective (isCoprime_of_isCoprime_dbar hG)
  rw [Matrix.mulVec_zero, ← intPhaseSpaceMod_matrix_mulVec]
  exact hzero

/-! ### Integer matrices permute residues and transversals

An integer matrix `G` whose determinant is coprime to `d` permutes `(ℤ/dℤ)²`, fixing `0`. Applied
to the representatives of a complete transversal, it therefore produces another complete
transversal, whose representative of the class `Gq` is `G` times the representative of `q`. The
idempotency argument for a twisted ghost candidate moves its convolution sums along this
permutation. -/

/-- The permutation `q ↦ Gq` of `(ℤ/dℤ)²` induced by an integer matrix whose determinant is
coprime to `d`. -/
noncomputable def phaseSpaceModMulVecEquiv {d : ℕ} [NeZero d] (G : Mat(2, ℤ))
    (hG : IsCoprime G.det (d : ℤ)) : PhaseSpaceMod d ≃ PhaseSpaceMod d :=
  Equiv.ofBijective (G.map (Int.castRingHom (ZMod d))).mulVec
    (Finite.injective_iff_bijective.mp (mulVec_map_intCast_injective hG))

/-- The permutation `phaseSpaceModMulVecEquiv` is matrix multiplication by `G` modulo `d`. -/
lemma phaseSpaceModMulVecEquiv_apply {d : ℕ} [NeZero d] (G : Mat(2, ℤ))
    (hG : IsCoprime G.det (d : ℤ)) (q : PhaseSpaceMod d) :
    phaseSpaceModMulVecEquiv G hG q = (G.map (Int.castRingHom (ZMod d))).mulVec q :=
  rfl

/-- Reducing `Gp` modulo `d` is the permutation `phaseSpaceModMulVecEquiv` applied to the class
of `p`. -/
lemma intPhaseSpaceMod_mulVec_eq_mulVecEquiv {d : ℕ} [NeZero d]
    (G : Mat(2, ℤ)) (hG : IsCoprime G.det (d : ℤ)) (p : IntPhaseSpace) :
    intPhaseSpaceMod d (Matrix.mulVec G p) =
      phaseSpaceModMulVecEquiv G hG (intPhaseSpaceMod d p) :=
  intPhaseSpaceMod_matrix_mulVec d G p

/-- Only the zero class maps to zero under `phaseSpaceModMulVecEquiv`. -/
@[simp]
lemma phaseSpaceModMulVecEquiv_eq_zero_iff {d : ℕ} [NeZero d] (G : Mat(2, ℤ))
    (hG : IsCoprime G.det (d : ℤ)) {q : PhaseSpaceMod d} :
    phaseSpaceModMulVecEquiv G hG q = 0 ↔ q = 0 := by
  have h0 : phaseSpaceModMulVecEquiv G hG 0 = 0 := by
    rw [phaseSpaceModMulVecEquiv_apply, Matrix.mulVec_zero]
  exact ⟨fun h => (phaseSpaceModMulVecEquiv G hG).injective (h.trans h0.symm),
    fun h => h ▸ h0⟩

/-- **The image of a transversal under an integer matrix.** If `det G` is coprime to `d`, the
points `G·I.repr q` form a complete transversal; its representative of the class `Gq` is
`G·I.repr q` (`PhaseSpaceTransversal.map_repr_apply`). -/
noncomputable def PhaseSpaceTransversal.map {d : ℕ} [NeZero d] (I : PhaseSpaceTransversal d)
    (G : Mat(2, ℤ)) (hG : IsCoprime G.det (d : ℤ)) : PhaseSpaceTransversal d where
  repr q := Matrix.mulVec G (I.repr ((phaseSpaceModMulVecEquiv G hG).symm q))
  residue_repr q := by
    rw [intPhaseSpaceMod_mulVec_eq_mulVecEquiv G hG, I.residue_repr,
      Equiv.apply_symm_apply]

/-- The image transversal represents the class `Gq` by `G` times the representative of `q`. -/
lemma PhaseSpaceTransversal.map_repr_apply {d : ℕ} [NeZero d] (I : PhaseSpaceTransversal d)
    (G : Mat(2, ℤ)) (hG : IsCoprime G.det (d : ℤ)) (q : PhaseSpaceMod d) :
    (I.map G hG).repr (phaseSpaceModMulVecEquiv G hG q) = Matrix.mulVec G (I.repr q) := by
  simp only [PhaseSpaceTransversal.map, Equiv.symm_apply_apply]

/-- A transversal representing the zero class by `0` has an image with the same property. -/
lemma PhaseSpaceTransversal.map_repr_zero {d : ℕ} [NeZero d] (I : PhaseSpaceTransversal d)
    (G : Mat(2, ℤ)) (hG : IsCoprime G.det (d : ℤ)) (hI0 : I.repr 0 = 0) :
    (I.map G hG).repr 0 = 0 := by
  have h := I.map_repr_apply G hG 0
  rw [phaseSpaceModMulVecEquiv_apply G hG 0, Matrix.mulVec_zero, hI0, Matrix.mulVec_zero] at h
  exact h

/-- **Reindexing along the image transversal**: summing `F(G·I.repr q)` over the classes `q`
other than `0` and `p` is summing `F` over the representatives of `I.map G` of the classes other
than `0` and `Gp`. -/
theorem PhaseSpaceTransversal.sum_ite_map_repr {A : Type*} [AddCommMonoid A] {d : ℕ} [NeZero d]
    (I : PhaseSpaceTransversal d) (G : Mat(2, ℤ)) (hG : IsCoprime G.det (d : ℤ))
    (F : IntPhaseSpace → A) (p : PhaseSpaceMod d) :
    (∑ q : PhaseSpaceMod d, if q = 0 ∨ q = p then 0 else F (Matrix.mulVec G (I.repr q))) =
      ∑ q : PhaseSpaceMod d, if q = 0 ∨ q = phaseSpaceModMulVecEquiv G hG p then 0 else
        F ((I.map G hG).repr q) := by
  conv_rhs => rw [← Equiv.sum_comp (phaseSpaceModMulVecEquiv G hG)]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [phaseSpaceModMulVecEquiv_eq_zero_iff,
    (phaseSpaceModMulVecEquiv G hG).injective.eq_iff, PhaseSpaceTransversal.map_repr_apply]

/-- Congruent integer representatives have symplectic pairing divisible by `d`. -/
lemma dvd_intSymplecticForm_of_mod_eq {d : ℕ}
    {p p' : IntPhaseSpace} (h : intPhaseSpaceMod d p' = intPhaseSpaceMod d p) :
    (d : ℤ) ∣ intSymplecticForm p' p := by
  obtain ⟨q, rfl⟩ := exists_eq_add_smul_of_intPhaseSpaceMod_eq d h
  refine ⟨q 1 * p 0 - q 0 * p 1, ?_⟩
  simp only [intSymplecticForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end SIC

end
