/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Admissible.StabilizerExistence
import SICs.Dilogarithm.AdmissibleTuple
import SICs.Dilogarithm.Reciprocity.UnitaryConjugates
import SICs.Ghost.Shifts

/-!
# Unitary conjugates of the tuple cocycle values

An automorphism switching the square root of the field discriminant sends the level-generator
cocycle at every nonzero tuple shift to the unit circle.

This module applies [RW26b, Radchenko, Wheeler (2026b), Definition 1, Proposition 7 and the
paragraph following it] to the level generator and fixed point of [AFK26, Appleby, Flammia,
Kopp (2026), Section 4]. It supplies the unconditional norm-one input for the tuple's ghost
overlaps.

## The argument

Let `τ` be the element of the real quadratic field whose selected real value is `ρ_t`, and let
`x = ⟨⟨p/d,τ⟩⟩`. The attractive fixed point `(A_t,ρ_t)` presents the pseudolattice
`I = ℤτ + ℤ` with period `ε = cτ + d` and period matrix `A_t`. The characteristic of `x` is
`p/d`. Thus `A_t ∈ Γ_{p/d}` gives `(ε - 1)x ∈ I`, while `p ≢ 0 (mod d)` gives `x ∉ I`.
Proposition 7 puts every Galois conjugate of `E_{I,ε}(x) = F_{A_t}(p/d)` on the unit circle
when the automorphism switches the two real embeddings of the field. Off the zero class,
`F_{A_t}(p/d) ש^{p/d}_{A_t}(ρ_t) = μ_{A_t}`. The eta multiplier is a root of unity, so the
cocycle conjugate also has modulus one.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

namespace AdmissibleTuple

/-! ### The level-generator cocycle

The tuple shift is a nonzero class of the pseudolattice dilogarithm, and the eta multiplier
transports its unitary conjugates to the cocycle. -/

/-- Proposition 7 for the tuple value `F_{A_t}(p/d)`, via the pseudolattice of its attractive
fixed point. Used by `norm_map_levelGenerator`. -/
private theorem norm_map_finiteDilogValue (t : AdmissibleTuple) (ha : 0 < t.Q.a)
    (g : ComplexGaloisAutomorphism)
    (hg : SwitchesSqrt g (NumberField.discr t.triple.K)) {p : IntPhaseSpace}
    (hp : intPhaseSpaceMod t.d p ≠ 0) :
    ‖g (finiteDilogValue t.levelGenerator t.Q.rootPlus (shiftRationalPoint t.d p))‖ = 1 := by
  let F := t.triple.tower.toRealQuadraticFieldData
  let τ := F.rootPlusElement t.Q t.formConductor
  have hroot : realEmbeddingAt t.triple.K F.place τ = t.Q.rootPlus :=
    F.realEmbeddingAt_place_rootPlusElement t.formConductor_spec.disc_eq
  have hA : IsAttractiveFixedPoint t.levelGenerator
      (realEmbeddingAt t.triple.K F.place τ) := by
    rw [hroot]
    exact t.isAssociatedStabilizerPair_levelGenerator.isAttractiveFixedPoint ha
  let B := PseudolatticeBasis.ofAttractiveFixedPoint hA
  let hperiod := PseudolatticeBasis.isPeriod_ofAttractiveFixedPoint hA
  have hmatrix : hperiod.matrix = t.levelGenerator :=
    PseudolatticeBasis.matrix_isPeriod_ofAttractiveFixedPoint hA
  let r := shiftRationalPoint t.d p
  let x := fracSymplecticFormRat r τ
  have hchar : B.characteristic x = r := by
    simpa [B, x, PseudolatticeBasis.ofAttractiveFixedPoint] using
      (B.characteristic_scale_fracSymplecticFormRat r)
  have hmem : t.levelGenerator ∈ gammaSubgroup r :=
    t.isAssociatedStabilizerPair_levelGenerator.A_mem_gammaSubgroup
      (exists_intCast_mul_shiftRationalPoint t.d p)
  have hx : ((t.levelGenerator 1 0 : t.triple.K) * τ +
      (t.levelGenerator 1 1 : t.triple.K) - 1) * x ∈ B.submodule := by
    apply (hperiod.mem_gammaSubgroup_characteristic_iff x).mp
    rw [hmatrix, hchar]
    exact hmem
  have hnon : ¬ IsIntegralIndex r :=
    not_isIntegralIndex_shiftRationalPoint t.d (NeZero.pos t.d) hp
  have hx0 : x ∉ B.submodule := by
    intro hx0
    exact hnon (hchar ▸ (B.isIntegralIndex_characteristic_iff x).mpr hx0)
  have h := pseudolatticeDilog_norm_map_eq_one hperiod g
    (F.exists_map_realEmbeddingAt_ne_of_switchesSqrt hg) hx hx0
  change ‖g (finiteDilogValue hperiod.matrix B.beta (B.characteristic x))‖ = 1 at h
  rw [hmatrix, hchar] at h
  change ‖g (finiteDilogValue t.levelGenerator
    (realEmbeddingAt t.triple.K F.place τ) r)‖ = 1 at h
  rwa [hroot] at h

/-- **[RW26b, Radchenko, Wheeler (2026b), Proposition 7 and the paragraph following it] at
the level generator of [AFK26, Appleby, Flammia, Kopp (2026), Section 4]**: for
`p ≢ 0 (mod d)`, an automorphism switching `√disc(K)` sends `ש^{p/d}_{A_t}(ρ_t)` to the unit
circle. This transports `pseudolatticeDilog_norm_map_eq_one` through
`finiteDilogValue_of_not_isIntegralIndex`. -/
theorem norm_map_levelGenerator (t : AdmissibleTuple) (ha : 0 < t.Q.a)
    (g : ComplexGaloisAutomorphism)
    (hg : SwitchesSqrt g (NumberField.discr t.triple.K)) {p : IntPhaseSpace}
    (hp : intPhaseSpaceMod t.d p ≠ 0) :
    ‖g (sfModularCocycleRealTotal (shiftRationalPoint t.d p) t.levelGenerator
      (t.isAssociatedStabilizerPair_levelGenerator.A_mem_gammaSubgroup
        (exists_intCast_mul_shiftRationalPoint t.d p)) t.Q.rootPlus)‖ = 1 := by
  let r := shiftRationalPoint t.d p
  have hmem : t.levelGenerator ∈ gammaSubgroup r :=
    t.isAssociatedStabilizerPair_levelGenerator.A_mem_gammaSubgroup
      (exists_intCast_mul_shiftRationalPoint t.d p)
  have hnon : ¬ IsIntegralIndex r :=
    not_isIntegralIndex_shiftRationalPoint t.d (NeZero.pos t.d) hp
  have hfinite := norm_map_finiteDilogValue t ha g hg hp
  have heta : ‖g (etaMultiplier t.levelGenerator)‖ = 1 := by
    apply norm_eq_one_of_norm_pow_eq_one (by decide : (2 : ℕ) ≠ 0)
    rw [← map_pow, etaMultiplier_sq_of_trace_pos
      (t.isAssociatedStabilizerPair_levelGenerator.isAttractiveFixedPoint ha).trace_pos]
    exact norm_map_etaMultiplierSq g t.levelGenerator
  have hne : sfModularCocycleRealTotal r t.levelGenerator hmem t.Q.rootPlus ≠ 0 :=
    sfModularCocycleRealTotal_ne_zero_of_flt_eq_self hmem
      t.form_admissible.rootPlus_irrational hnon
      t.isAssociatedStabilizerPair_levelGenerator.fltDenominator_A_rootPlus_pos
      t.isAssociatedStabilizerPair_levelGenerator.flt_A_rootPlus
  have hbridge : finiteDilogValue t.levelGenerator t.Q.rootPlus r *
      sfModularCocycleRealTotal r t.levelGenerator hmem t.Q.rootPlus =
        etaMultiplier t.levelGenerator := by
    rw [finiteDilogValue_of_not_isIntegralIndex t.levelGenerator t.Q.rootPlus hnon,
      sfModularCocycleReal'_of_mem hmem]
    exact div_mul_cancel₀ _ hne
  have hnorm := congrArg (fun z : ℂ => ‖g z‖) hbridge
  rw [map_mul, norm_mul, hfinite, one_mul, heta] at hnorm
  exact hnorm

end AdmissibleTuple

end SIC

end
