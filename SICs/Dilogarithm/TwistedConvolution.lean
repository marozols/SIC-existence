/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.Dilogarithm.AdmissibleTuple
import SICs.Dilogarithm.SubgroupPentagon
import SICs.Ghost.Shifts

/-!
# The twisted convolution identity at the explicit shift

`λ₀ = -d_j` is a shift of every admissible tuple whose form has positive leading coefficient.

This module follows [AFK26, Appleby, Flammia, Kopp (2026), Section 5, proof of Theorem 1.2,
`thm:tci`]. It proves the twisted convolution identity of [AFK25, Definition 1.34, `dfn:shift`]
(`AdmissibleTuple.IsShift`) at `λ₀ = -d_j`, from the vanishing torsion sum
`finiteDilogTorsionSum_eq_zero` at `γ = A_t`, `τ = ρ_t`, `R = L_{z,t}^{-1}`, `n = d`. Its consumer
is the live existence theorem of `SICs.Construction`, which builds the ghost datum
from this shift.

## The argument

Write `N = (d_j - 3)d²` (`finiteDilogOrder_eq`) and work in characteristic coordinates: `G` is the
group of `x ∈ (ℤ/N)²` with `(A_t - I)x ≡ 0`, the residue of the characteristic `x/N`, and
`E(x) = F(x/N)`. Since `A_t ≡ I (mod d)` and `d ∣ N`, the `d`-torsion `G[d]` is the image of the
injective map `q ↦ (N/d)q` of `(ℤ/d)²`, the residues of the characteristics `q/d`; so
`E((N/d)q) = F(q/d)`. For a nonzero residue class, and for the literal representative `q = 0`,
`F(q/d) ש^{q/d}_{A_t}(ρ_t) = μ_{A_t}`. The latter uses
`sfModularCocycleRealTotal_zero_of_flt_eq_self`; the transversal chooses literal zero at both
integral summand indices.

The source substitutes row vectors `y = S L^{m+1} p`. In characteristic coordinates an explicit
witness gives the same displacement and phase. By [AFK26, Appleby, Flammia, Kopp (2026), Lemma 4.2]
(`IsAssociatedStabilizerPair.A_sub_one_eq`),
`A_t - I = d L^m (L - I)`. Hence:

- `L^{-1}` fixes `dG` pointwise: `d L^m (L - I)x ≡ 0 (mod N)` and `L^m` is invertible, so
  `(L - I)(dx) ≡ 0`;
- for `p ∈ ℤ²`, take `y = d(I-L)p = d·adj(L-I)Lp` modulo `N`. Then
  `(I-L^{-1})y = -(N/d)p` and `(A_t-I)y = -N L^{m+1}p`. Thus `y ∈ G` and
  `v = y-L^{-1}y` is the residue of `-p/d`, nonzero for `p ≢ 0 (mod d)`;
- the bicharacter `⟨y; (N/d)q⟩` (`thetaBicharacter_div_natCast`) is `ζ_d` to the power
  `ω(p,L^m q)`: its integral displacement is `-L^{m+1}p`, and
  `L^{-(m+1)} ≡ L^m (mod d)` because `L^{2m+1} = A_t ≡ I (mod d)`. By
  [AFK26, Appleby, Flammia, Kopp (2026), Lemma 4.3]
  (`IsAssociatedStabilizerPair.Lz_pow_m_eq`) and
  `r_{j,m-1} ≡ d_j r_{j,m} (mod d)` this is `ζ_d^{r⟨p,(λ₀ I + L)q⟩}` with `λ₀ = -d_j`.

Substituting into `finiteDilogTorsionSum_eq_zero` and reindexing `G[d]` by a transversal gives
`Σ_q ζ_d^{r⟨p,(λ₀ I + L)q⟩} ש^{q/d}_{A_t}(ρ_t) ש^{(q-p)/d}_{A_t^{-1}}(ρ_t) = 0`
(`sfModularCocycleRealTotal_inv_of_lowerLeft_ne_zero` for `ש_{γ^{-1}} = ש_γ^{-1}`). At `p ≡ 0`
the transversal conditions force `p = 0` and each summand is `1`, giving `d²`. Coprimality:
`2λ₀ + d_j - 1 = -(d_j + 1)` and `(d_j + 1) r(d - r) = d² - 1`.

The numerical check at the rank-three tuple `(11, 3, ⟨1,-3,1⟩)` confirms `λ₀ ≡ -d_j`.
-/

noncomputable section

open scoped MatrixGroups

namespace SIC

namespace AdmissibleTuple

/-! ### The explicit shift

[AFK26, Appleby, Flammia, Kopp (2026), Theorem 1.2] at `λ₀ = -d_j`, under the orientation
`γ₂₁ > 0` of [AFK26, Appleby, Flammia, Kopp (2026), Section 4]. -/

/-- The shift `-d_j` satisfies the coprimality clause of `IsShift`, by
`AdmissiblePair.coprime_n_d` and `n = d_j + 1`. -/
private theorem isShiftCoprime_neg_towerDimension (t : AdmissibleTuple) :
    t.IsShiftCoprime (-(t.triple.towerDimension : ℤ)) := by
  have h : IsCoprime (t.pair.n : ℤ) (t.d : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr t.pair.coprime_n_d
  have hneg : IsCoprime (-(t.pair.n : ℤ)) (t.d : ℤ) :=
    (IsCoprime.neg_left_iff _ _).mpr h
  have hn : (t.pair.n : ℤ) = (t.triple.towerDimension : ℤ) + 1 := by
    exact_mod_cast t.pair_n_eq
  rw [hn] at hneg
  have heq : 2 * (-(t.triple.towerDimension : ℤ)) +
      (t.triple.towerDimension : ℤ) - 1 =
      -((t.triple.towerDimension : ℤ) + 1) := by ring
  simpa only [AdmissibleTuple.IsShiftCoprime, heq] using hneg

/-- At the fixed point of an associated level generator, the two cocycle factors with the same
index multiply to one. This is the summand calculation at the zero shift class. -/
private theorem cocycle_mul_inverse {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (hp : t.IsAssociatedStabilizerPair A_t Lz) (q : IntPhaseSpace) :
    sfModularCocycleReal' (shiftRationalPoint t.d q) A_t t.Q.rootPlus *
      sfModularCocycleReal' (shiftRationalPoint t.d q) A_t⁻¹ t.Q.rootPlus = 1 := by
  let r := shiftRationalPoint t.d q
  have hmem : A_t ∈ gammaSubgroup r :=
    hp.A_mem_gammaSubgroup (exists_intCast_mul_shiftRationalPoint t.d q)
  have hne : sfModularCocycleRealTotal r A_t hmem t.Q.rootPlus ≠ 0 := by
    by_cases hint : IsIntegralIndex r
    · exact sfModularCocycleRealTotal_integral_ne_zero
        t.form_admissible.rootPlus_irrational hint hmem
        hp.fltDenominator_A_rootPlus_pos hp.flt_A_rootPlus
    · exact sfModularCocycleRealTotal_ne_zero_of_flt_eq_self hmem
        t.form_admissible.rootPlus_irrational hint
        hp.fltDenominator_A_rootPlus_pos hp.flt_A_rootPlus
  have hinv := sfModularCocycleRealTotal_inv_of_lowerLeft_ne_zero hmem
    hp.lowerLeft_A_ne_zero hp.fltDenominator_A_rootPlus_pos.ne'
    hp.flt_A_rootPlus
  change sfModularCocycleReal' r A_t t.Q.rootPlus *
    sfModularCocycleReal' r A_t⁻¹ t.Q.rootPlus = 1
  rw [sfModularCocycleReal'_of_mem hmem,
    sfModularCocycleReal'_of_mem (inv_mem_gammaSubgroup hmem), hinv,
    mul_inv_cancel₀ hne]

/-- The convolution at `p = 0` has one unit summand per residue class. -/
private theorem shiftConvolutionSum_zero {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (hp : t.IsAssociatedStabilizerPair A_t Lz) (lam : ℤ)
    (I : PhaseSpaceTransversal t.d) :
    t.shiftConvolutionSum A_t Lz lam I 0 = (t.d : ℂ) ^ 2 := by
  simp only [shiftConvolutionSum, shiftRationalPoint_zero, sub_zero]
  simp only [intSymplecticForm, Pi.zero_apply, zero_mul, sub_self, mul_zero, zpow_zero,
    one_mul, cocycle_mul_inverse hp, Finset.sum_const,
    Finset.card_univ]
  simp [PhaseSpaceMod]

/-- The representative conditions force an index in the zero residue class to be zero. -/
private theorem shiftConvolutionSum_of_residue_zero
    {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (hp : t.IsAssociatedStabilizerPair A_t Lz) (lam : ℤ)
    (p : IntPhaseSpace) (I : PhaseSpaceTransversal t.d)
    (hI0 : I.repr 0 = 0) (hIp : I.repr (intPhaseSpaceMod t.d p) = p)
    (hp0 : intPhaseSpaceMod t.d p = 0) :
    t.shiftConvolutionSum A_t Lz lam I p = (t.d : ℂ) ^ 2 := by
  have : p = 0 := by simpa only [hp0, hI0] using hIp.symm
  subst p
  exact shiftConvolutionSum_zero hp lam I

/-! ### Torsion coordinates

The characteristic `q/d` is represented by `(N/d)q` modulo `N`. -/

/-- The residue vector of the characteristic `q/d` in the finite dilogarithm group. -/
private def torsionResidue (t : AdmissibleTuple) (A_t : SL(2, ℤ))
    (q : IntPhaseSpace) : Fin 2 → ZMod (finiteDilogOrder A_t) :=
  fun i => ((((t.triple.towerDimension - 3) * t.d : ℕ) : ℤ) * q i :
    ZMod (finiteDilogOrder A_t))

/-- The residue vector of `q/d` depends injectively on `q` modulo `d`. -/
private theorem torsionResidue_eq_iff {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (hp : t.IsAssociatedStabilizerPair A_t Lz) (p q : IntPhaseSpace) :
    torsionResidue t A_t p = torsionResidue t A_t q ↔
      intPhaseSpaceMod t.d p = intPhaseSpaceMod t.d q := by
  let C : ℤ := ((t.triple.towerDimension - 3) * t.d : ℕ)
  have hC : C ≠ 0 := by
    dsimp [C]
    exact_mod_cast (Nat.mul_pos
      (Nat.sub_pos_of_lt t.triple.three_lt_towerDimension)
      (lt_trans (by decide : 0 < 3) t.pair.three_lt_d)).ne'
  have hN : (finiteDilogOrder A_t : ℤ) = C * (t.d : ℤ) := by
    rw [hp.finiteDilogOrder_eq]
    dsimp [C]
    ring
  have hcoord (a b : ℤ) :
      ((C * a : ℤ) : ZMod (finiteDilogOrder A_t)) =
        ((C * b : ℤ) : ZMod (finiteDilogOrder A_t)) ↔
          (a : ZMod t.d) = (b : ZMod t.d) := by
    rw [ZMod.intCast_eq_intCast_iff, ZMod.intCast_eq_intCast_iff,
      Int.modEq_iff_dvd, Int.modEq_iff_dvd, hN, ← mul_sub]
    exact Int.mul_dvd_mul_iff_left hC
  simp only [torsionResidue, intPhaseSpaceMod, funext_iff]
  constructor <;> intro h i
  · apply (hcoord (p i) (q i)).mp
    simpa only [C, Int.cast_mul, Int.cast_natCast] using h i
  · have hi := (hcoord (p i) (q i)).mpr (h i)
    simpa only [C, Int.cast_mul, Int.cast_natCast] using hi

/-- The lifted torsion residue differs from the rational point `q/d` by an integer vector. -/
private theorem torsionResidue_characteristic {t : AdmissibleTuple}
    {A_t Lz : SL(2, ℤ)} (hp : t.IsAssociatedStabilizerPair A_t Lz)
    (q : IntPhaseSpace) :
    IsIntegralIndex
      (zmodCharacteristic (finiteDilogOrder A_t) (torsionResidue t A_t q) -
        shiftRationalPoint t.d q) := by
  let C : ℤ := ((t.triple.towerDimension - 3) * t.d : ℕ)
  have hC : C ≠ 0 := by
    dsimp [C]
    exact_mod_cast (Nat.mul_pos
      (Nat.sub_pos_of_lt t.triple.three_lt_towerDimension)
      (lt_trans (by decide : 0 < 3) t.pair.three_lt_d)).ne'
  have hd : (t.d : ℚ) ≠ 0 := by
    exact_mod_cast (lt_trans (by decide : 0 < 3) t.pair.three_lt_d).ne'
  have hN : (finiteDilogOrder A_t : ℚ) = (C : ℚ) * t.d := by
    have hNInt : (finiteDilogOrder A_t : ℤ) = C * (t.d : ℤ) := by
      rw [hp.finiteDilogOrder_eq]
      dsimp [C]
      ring
    exact_mod_cast hNInt
  have : NeZero (finiteDilogOrder A_t) := ⟨by
    have hNnonzero : (finiteDilogOrder A_t : ℚ) ≠ 0 := by
      rw [hN]
      exact mul_ne_zero (by exact_mod_cast hC) hd
    exact_mod_cast hNnonzero⟩
  have hq : (fun i : Fin 2 => ((C * q i : ℤ) : ℚ) / finiteDilogOrder A_t) =
      shiftRationalPoint t.d q := by
    funext i
    simp only [shiftRationalPoint, Int.cast_mul]
    rw [hN]
    field_simp
  have ht : torsionResidue t A_t q =
      (fun i => ((C * q i : ℤ) : ZMod (finiteDilogOrder A_t))) := by
    funext i
    simp only [torsionResidue, C, Int.cast_mul, Int.cast_natCast]
  rw [ht, ← hq]
  exact isIntegralIndex_zmodCharacteristic_intCast_sub
    (finiteDilogOrder A_t) (fun i => C * q i)

/-- Every residue of a characteristic `q/d` belongs to the finite dilogarithm group. -/
private theorem torsionResidue_mem {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (hp : t.IsAssociatedStabilizerPair A_t Lz) (q : IntPhaseSpace) :
    torsionResidue t A_t q ∈ finiteDilogGroup A_t := by
  have hN : 0 < finiteDilogOrder A_t := by
    rw [hp.finiteDilogOrder_eq]
    exact Nat.mul_pos
      (Nat.sub_pos_of_lt t.triple.three_lt_towerDimension)
      (pow_pos (lt_trans (by decide : 0 < 3) t.pair.three_lt_d) _)
  have : NeZero (finiteDilogOrder A_t) := ⟨hN.ne'⟩
  apply (mem_fixedCharacteristics_iff A_t (finiteDilogOrder A_t) _).mpr
  exact mem_gammaSubgroup_of_isIntegralIndex_sub
    (torsionResidue_characteristic hp q)
    (hp.A_mem_gammaSubgroup (exists_intCast_mul_shiftRationalPoint t.d q))

/-- The characteristic `q/d` is killed by `d` in the finite group. -/
private theorem torsionResidue_nsmul {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (hp : t.IsAssociatedStabilizerPair A_t Lz) (q : IntPhaseSpace) :
    t.d • torsionResidue t A_t q = 0 := by
  funext i
  simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
  change (t.d : ZMod (finiteDilogOrder A_t)) *
    ((((t.triple.towerDimension - 3) * t.d : ℕ) : ℤ) * q i :
      ZMod (finiteDilogOrder A_t)) = 0
  calc
    _ = (((t.triple.towerDimension - 3) * t.d ^ 2 : ℕ) :
          ZMod (finiteDilogOrder A_t)) * (q i : ZMod (finiteDilogOrder A_t)) := by
      push_cast
      ring
    _ = 0 := by rw [← hp.finiteDilogOrder_eq, ZMod.natCast_self, zero_mul]

/-- Every `d`-torsion element has the characteristic of some integer vector divided by `d`. -/
private theorem torsionResidue_surj {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (hp : t.IsAssociatedStabilizerPair A_t Lz)
    (u : finiteDilogGroup A_t) (hu : t.d • u = 0) :
    ∃ q : IntPhaseSpace, torsionResidue t A_t q = u := by
  let C : ℕ := (t.triple.towerDimension - 3) * t.d
  have hd : 0 < t.d := lt_trans (by decide : 0 < 3) t.pair.three_lt_d
  have hC : 0 < C := Nat.mul_pos
    (Nat.sub_pos_of_lt t.triple.three_lt_towerDimension) hd
  have hN : finiteDilogOrder A_t = t.d * C := by
    rw [hp.finiteDilogOrder_eq]
    dsimp [C]
    ring
  have : NeZero (finiteDilogOrder A_t) := ⟨by rw [hN]; positivity⟩
  have hdiv (i : Fin 2) : C ∣ (u.val i).val := by
    have hi : t.d • (u.val i) = 0 := by
      have huv := congrFun (congrArg (fun x : finiteDilogGroup A_t =>
        (x : Fin 2 → ZMod (finiteDilogOrder A_t))) hu) i
      simpa only [AddSubgroup.coe_nsmul, Pi.smul_apply, Pi.zero_apply,
        AddSubgroup.coe_zero] using huv
    have hcast : ((t.d * (u.val i).val : ℕ) : ZMod (finiteDilogOrder A_t)) = 0 := by
      simpa only [nsmul_eq_mul, Nat.cast_mul, ZMod.natCast_zmod_val] using hi
    have hdivN : finiteDilogOrder A_t ∣ t.d * (u.val i).val :=
      (ZMod.natCast_eq_zero_iff _ _).mp hcast
    apply (Nat.mul_dvd_mul_iff_left hd).mp
    convert hdivN using 1
    exact hN.symm
  refine ⟨fun i => (((u.val i).val / C : ℕ) : ℤ), ?_⟩
  funext i
  have hc := Nat.mul_div_cancel' (hdiv i)
  calc
    torsionResidue t A_t (fun i => (((u.val i).val / C : ℕ) : ℤ)) i =
        ((C * ((u.val i).val / C) : ℕ) : ZMod (finiteDilogOrder A_t)) := by
      simp only [torsionResidue, C, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    _ = u.val i := by rw [hc, ZMod.natCast_zmod_val]

/-- A transversal indexes exactly the `d`-torsion of the finite dilogarithm group. -/
private def torsionEquiv {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (hp : t.IsAssociatedStabilizerPair A_t Lz) (I : PhaseSpaceTransversal t.d) :
    PhaseSpaceMod t.d ≃ {u : finiteDilogGroup A_t // t.d • u = 0} :=
  Equiv.ofBijective
    (fun c => (⟨⟨torsionResidue t A_t (I.repr c), torsionResidue_mem hp _⟩,
      Subtype.ext (torsionResidue_nsmul hp _)⟩ :
        {u : finiteDilogGroup A_t // t.d • u = 0}))
    ⟨by
      intro c c' h
      have heq : torsionResidue t A_t (I.repr c) =
          torsionResidue t A_t (I.repr c') :=
        congrArg (fun x : {u : finiteDilogGroup A_t // t.d • u = 0} =>
          (x.1 : Fin 2 → ZMod (finiteDilogOrder A_t))) h
      have hmod := (torsionResidue_eq_iff hp _ _).mp heq
      simpa only [I.residue_repr] using hmod,
    by
      intro u
      obtain ⟨q, hq⟩ := torsionResidue_surj hp u.1 u.2
      refine ⟨intPhaseSpaceMod t.d q, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact (torsionResidue_eq_iff hp _ _).mpr
        ((I.residue_repr _).trans (by rfl)) |>.trans hq⟩

/-! ### The inverse generator and the displacement

The source's right action by `L` becomes the inverse matrix action on characteristic vectors. -/

/-- Cayley--Hamilton gives `(L-I)^2 = (d_j-3)L`. -/
private theorem Lz_sub_one_sq {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (hp : t.IsAssociatedStabilizerPair A_t Lz) :
    ((Lz : Mat(2, ℤ)) - 1) * ((Lz : Mat(2, ℤ)) - 1) =
      ((t.triple.towerDimension : ℤ) - 3) • (Lz : Mat(2, ℤ)) := by
  have hsq := SL2Z.sq_eq_trace_smul_sub_one Lz
  rw [hp.trace_Lz] at hsq
  calc
    _ = (Lz : Mat(2, ℤ)) ^ 2 - 2 • (Lz : Mat(2, ℤ)) + 1 := by noncomm_ring
    _ = _ := by rw [hsq]; module

/-- The inverse generator gives `(I-L^{-1})(I-L)=-(d_j-3)I`. -/
private theorem Lz_inv_displacement {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (hp : t.IsAssociatedStabilizerPair A_t Lz) :
    (1 - ((Lz⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))) * (1 - (Lz : Mat(2, ℤ))) =
      -(((t.triple.towerDimension : ℤ) - 3) • (1 : Mat(2, ℤ))) := by
  have hmul : ((Lz⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) * (Lz : Mat(2, ℤ)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul]
    simp
  calc
    _ = 1 - (Lz : Mat(2, ℤ)) - ((Lz⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) +
        ((Lz⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) * (Lz : Mat(2, ℤ)) := by
      noncomm_ring
    _ = _ := by rw [hmul, hp.Lz_inv_eq]; module

/-- The integer characteristic witness for displacement `p` in equation `eq:tccproof2`:
`y=d(I-L)p`. -/
private def shiftWitness (t : AdmissibleTuple) (Lz : SL(2, ℤ))
    (p : IntPhaseSpace) : IntPhaseSpace :=
  (t.d : ℤ) • (1 - (Lz : Mat(2, ℤ))).mulVec p

/-- The witness satisfies `(I-L^{-1})y=-(N/d)p` before reduction modulo `N`. -/
private theorem shiftWitness_displacement {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (hp : t.IsAssociatedStabilizerPair A_t Lz) (p : IntPhaseSpace) :
    (1 - ((Lz⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))).mulVec (shiftWitness t Lz p) =
      -(((t.triple.towerDimension - 3) * t.d : ℕ) : ℤ) • p := by
  rw [shiftWitness, ← Matrix.smul_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_smul, Lz_inv_displacement hp]
  ext i
  fin_cases i <;>
    simp [Matrix.ofNat_apply, Matrix.natCast_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Pi.smul_apply, Nat.cast_mul,
      Nat.cast_sub (le_of_lt t.triple.three_lt_towerDimension)] <;> ring

/-- The integral lift of the witness has displacement `-N L^{m+1}p` under `A_t-I`. -/
private theorem shiftWitness_A_sub_one {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (hp : t.IsAssociatedStabilizerPair A_t Lz) (p : IntPhaseSpace) :
    ((A_t : Mat(2, ℤ)) - 1).mulVec (shiftWitness t Lz p) =
      -(finiteDilogOrder A_t : ℤ) •
        (((Lz : Mat(2, ℤ)) ^ ((t.triple.m : ℕ) + 1)).mulVec p) := by
  have hminus : (1 : Mat(2, ℤ)) - (Lz : Mat(2, ℤ)) =
      -((Lz : Mat(2, ℤ)) - 1) := by module
  have hmat : ((A_t : Mat(2, ℤ)) - 1) *
      ((t.d : ℤ) • ((1 : Mat(2, ℤ)) - (Lz : Mat(2, ℤ)))) =
      -(finiteDilogOrder A_t : ℤ) •
        ((Lz : Mat(2, ℤ)) ^ ((t.triple.m : ℕ) + 1)) := by
    rw [hp.A_sub_one_eq, hminus]
    calc
      _ = -((t.d : ℤ) ^ 2) •
          ((Lz : Mat(2, ℤ)) ^ (t.triple.m : ℕ) *
            (((Lz : Mat(2, ℤ)) - 1) * ((Lz : Mat(2, ℤ)) - 1))) := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg,
          Matrix.mul_assoc, smul_neg, smul_smul]
        module
      _ = -((t.d : ℤ) ^ 2 * ((t.triple.towerDimension : ℤ) - 3)) •
          ((Lz : Mat(2, ℤ)) ^ (t.triple.m : ℕ) * (Lz : Mat(2, ℤ))) := by
        rw [Lz_sub_one_sq hp]
        simp only [Matrix.mul_smul, smul_smul]
        module
      _ = _ := by
        rw [← pow_succ]
        rw [hp.finiteDilogOrder_eq]
        simp only [Nat.cast_mul, Nat.cast_pow,
          Nat.cast_sub (le_of_lt t.triple.three_lt_towerDimension)]
        module
  rw [shiftWitness, ← Matrix.smul_mulVec, Matrix.mulVec_mulVec, hmat,
    Matrix.smul_mulVec, neg_smul]

/-- The witness `d(I-L)p` is a fixed characteristic modulo `N`. -/
private theorem shiftWitness_mem {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (hp : t.IsAssociatedStabilizerPair A_t Lz) (p : IntPhaseSpace) :
    (fun i => (shiftWitness t Lz p i : ZMod (finiteDilogOrder A_t))) ∈
      finiteDilogGroup A_t := by
  rw [mem_fixedCharacteristics_iff_mulVec]
  funext i
  change ((((A_t : Mat(2, ℤ)) - 1).map
    (Int.castRingHom (ZMod (finiteDilogOrder A_t)))).mulVec
      (fun j => (shiftWitness t Lz p j : ZMod (finiteDilogOrder A_t)))) i = 0
  calc
    _ = (((((A_t : Mat(2, ℤ)) - 1).mulVec (shiftWitness t Lz p)) i : ℤ) :
          ZMod (finiteDilogOrder A_t)) := by
      simpa only [Function.comp_def, Int.coe_castRingHom] using
        (RingHom.map_mulVec (Int.castRingHom (ZMod (finiteDilogOrder A_t)))
          ((A_t : Mat(2, ℤ)) - 1) (shiftWitness t Lz p) i).symm
    _ = 0 := by rw [shiftWitness_A_sub_one hp]; simp [Pi.smul_apply]

/-- The witness as an element of the finite dilogarithm group. -/
private def shiftWitnessGroup {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (hp : t.IsAssociatedStabilizerPair A_t Lz) (p : IntPhaseSpace) :
    finiteDilogGroup A_t :=
  ⟨_, shiftWitness_mem hp p⟩

/-- In characteristic coordinates, `y-L^{-1}y` is the torsion class of `-p/d`. -/
private theorem shiftWitnessGroup_displacement {t : AdmissibleTuple}
    {A_t Lz : SL(2, ℤ)} (hp : t.IsAssociatedStabilizerPair A_t Lz)
    (p : IntPhaseSpace) :
    (shiftWitnessGroup hp p : Fin 2 → ZMod (finiteDilogOrder A_t)) -
      residueMulVec Lz⁻¹ (finiteDilogOrder A_t) (shiftWitnessGroup hp p) =
        torsionResidue t A_t (-p) := by
  let Y := shiftWitness t Lz p
  let R : Mat(2, ℤ) := ((Lz⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))
  have hint : Y - R.mulVec Y =
      -(((t.triple.towerDimension - 3) * t.d : ℕ) : ℤ) • p := by
    have h := shiftWitness_displacement hp p
    simpa only [Y, R, Matrix.sub_mulVec, Matrix.one_mulVec] using h
  have hR : residueMulVec Lz⁻¹ (finiteDilogOrder A_t)
      (fun i => (Y i : ZMod (finiteDilogOrder A_t))) =
      fun i => ((R.mulVec Y i : ℤ) : ZMod (finiteDilogOrder A_t)) := by
    funext i
    exact (RingHom.map_mulVec (Int.castRingHom (ZMod (finiteDilogOrder A_t))) R Y i).symm
  change (fun i => (Y i : ZMod (finiteDilogOrder A_t))) -
    residueMulVec Lz⁻¹ (finiteDilogOrder A_t)
      (fun i => (Y i : ZMod (finiteDilogOrder A_t))) = _
  rw [hR]
  funext i
  have hi := congrFun hint i
  simpa only [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
    torsionResidue, Int.cast_sub, Int.cast_neg, Int.cast_mul, mul_neg, neg_mul] using
    congrArg (fun z : ℤ => (z : ZMod (finiteDilogOrder A_t))) hi

/-- Lemma 4.2 after reduction modulo the finite dilogarithm order `N`. -/
private theorem A_sub_one_map_eq {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (hp : t.IsAssociatedStabilizerPair A_t Lz) :
    (((A_t : Mat(2, ℤ)) - 1).map (Int.castRingHom (ZMod (finiteDilogOrder A_t)))) =
      (t.d : ZMod (finiteDilogOrder A_t)) •
        (((Lz : Mat(2, ℤ)).map (Int.castRingHom (ZMod (finiteDilogOrder A_t)))) ^
          (t.triple.m : ℕ) *
          (((Lz : Mat(2, ℤ)).map (Int.castRingHom (ZMod (finiteDilogOrder A_t)))) - 1)) := by
  let N := finiteDilogOrder A_t
  let f := Int.castRingHom (ZMod N)
  let M := (Lz : Mat(2, ℤ)).map f
  rw [hp.A_sub_one_eq]
  have hsmul (B : Mat(2, ℤ)) : (((t.d : ℤ) • B).map f) =
      (t.d : ZMod N) • B.map f := by
    calc
      _ = (t.d : ℤ) • B.map f := by
        apply Matrix.map_smul f (t.d : ℤ)
        intro a
        simp [zsmul_eq_mul]
      _ = (t.d : ZMod N) • B.map f := by
        ext i j
        simp [Matrix.smul_apply, zsmul_eq_mul]
  rw [hsmul, Matrix.map_mul, Matrix.map_pow]
  simp [f, Matrix.map_sub]

/-- The generator `L` fixes every multiple `d x` in the finite dilogarithm group. -/
private theorem Lz_fixes_multiples {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (hp : t.IsAssociatedStabilizerPair A_t Lz) (x : finiteDilogGroup A_t) :
    residueMulVec Lz (finiteDilogOrder A_t) (t.d • x) = t.d • x := by
  let N := finiteDilogOrder A_t
  let f := Int.castRingHom (ZMod N)
  let M := (Lz : Mat(2, ℤ)).map f
  have hA : ((((A_t : Mat(2, ℤ)) - 1).map f)).mulVec x = 0 :=
    (mem_fixedCharacteristics_iff_mulVec _ _ _).mp x.property
  rw [A_sub_one_map_eq hp, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec] at hA
  have hzero : (t.d : ZMod N) • (M - 1).mulVec x = 0 := by
    apply (residueMulVec_eq_zero_iff (Lz ^ (t.triple.m : ℕ)) N _).mp
    unfold residueMulVec
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.map_pow,
      Matrix.mulVec_smul]
    exact hA
  have h := hzero
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h
  change M.mulVec (t.d • (x : Fin 2 → ZMod N)) = _
  rw [Matrix.mulVec_smul]
  rw [smul_sub] at h
  funext i
  have hi := congrFun (sub_eq_zero.mp h) i
  simpa only [Pi.smul_apply, nsmul_eq_mul, smul_eq_mul] using hi

/-- The inverse generator fixes every multiple `d x` in the finite group. -/
private theorem Lz_inv_fixes_multiples {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (hp : t.IsAssociatedStabilizerPair A_t Lz) (x : finiteDilogGroup A_t) :
    residueMulVec Lz⁻¹ (finiteDilogOrder A_t) (t.d • x) = t.d • x := by
  let N := finiteDilogOrder A_t
  have hfixed := Lz_fixes_multiples hp x
  have hmul : residueMulVec Lz⁻¹ N (residueMulVec Lz N (t.d • x)) =
      t.d • x := by
    have hcoemul : ((Lz⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) *
        (Lz : Mat(2, ℤ)) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul]
      simp
    unfold residueMulVec
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul]
    rw [hcoemul]
    simp
  rw [hfixed] at hmul
  exact hmul

/-- A nonzero residue class gives a nonzero torsion displacement. -/
private theorem torsionResidue_neg_ne_zero {t : AdmissibleTuple}
    {A_t Lz : SL(2, ℤ)} (hp : t.IsAssociatedStabilizerPair A_t Lz)
    (p : IntPhaseSpace) (hp0 : intPhaseSpaceMod t.d p ≠ 0) :
    (⟨torsionResidue t A_t (-p), torsionResidue_mem hp (-p)⟩ :
      finiteDilogGroup A_t) ≠ 0 := by
  intro h
  have hz0 : torsionResidue t A_t 0 = 0 := by
    funext i
    simp [torsionResidue]
  have hz : torsionResidue t A_t (-p) = torsionResidue t A_t 0 := by
    simpa only [hz0, AddSubgroup.coe_zero] using congrArg
      (fun x : finiteDilogGroup A_t =>
        (x : Fin 2 → ZMod (finiteDilogOrder A_t))) h
  have hmod := (torsionResidue_eq_iff hp (-p) 0).mp hz
  have hmod0 : intPhaseSpaceMod t.d (-p) = 0 := by
    have hz0 : intPhaseSpaceMod t.d (0 : IntPhaseSpace) = 0 := by
      funext i
      simp [intPhaseSpaceMod]
    rwa [hz0] at hmod
  have : intPhaseSpaceMod t.d p = 0 := by
    rw [intPhaseSpaceMod_neg] at hmod0
    exact neg_eq_zero.mp hmod0
  exact hp0 this

/-- The subgroup pentagon relation, indexed by an arbitrary transversal of `q/d`. -/
private theorem torsionSum_eq_zero {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (hp : t.IsAssociatedStabilizerPair A_t Lz) (ha : 0 < t.Q.a)
    (p : IntPhaseSpace) (hp0 : intPhaseSpaceMod t.d p ≠ 0)
    (I : PhaseSpaceTransversal t.d) :
    ∑ c : PhaseSpaceMod t.d,
      fixedBicharacter A_t (finiteDilogOrder A_t) (shiftWitnessGroup hp p)
          (torsionResidue t A_t (I.repr c)) *
        (finiteDilogE A_t t.Q.rootPlus
            (⟨torsionResidue t A_t (I.repr c), torsionResidue_mem hp _⟩ +
              ⟨torsionResidue t A_t (-p), torsionResidue_mem hp _⟩ :
              finiteDilogGroup A_t) /
          finiteDilogE A_t t.Q.rootPlus
            (torsionResidue t A_t (I.repr c))) = 0 := by
  let y := shiftWitnessGroup hp p
  let v : finiteDilogGroup A_t :=
    ⟨torsionResidue t A_t (-p), torsionResidue_mem hp (-p)⟩
  have hfixed : IsAttractiveFixedPoint A_t t.Q.rootPlus :=
    hp.isAttractiveFixedPoint ha
  have : NeZero (finiteDilogOrder A_t) := finiteDilogOrder_neZero hfixed
  have hcomm : Lz⁻¹ * A_t * (Lz⁻¹)⁻¹ = A_t := by
    rw [hp.A_eq_Lz_pow]
    group
  have hR : flt ((Lz⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) t.Q.rootPlus =
      t.Q.rootPlus :=
    flt_inv_of_flt_eq_self hp.fltDenominator_Lz_rootPlus_pos.ne'
      hp.flt_Lz_rootPlus
  have hjR : 0 < fltDenominator ((Lz⁻¹ : SL(2, ℤ)) : Mat(2, ℤ))
      t.Q.rootPlus := by
    have hprod := fltDenominator_inv_mul_self_of_flt_eq_self
      hp.fltDenominator_Lz_rootPlus_pos.ne' hp.flt_Lz_rootPlus
    apply (mul_pos_iff_of_pos_right hp.fltDenominator_Lz_rootPlus_pos).mp
    rw [hprod]
    positivity
  have hfix : ∀ x ∈ finiteDilogGroup A_t,
      residueMulVec Lz⁻¹ (finiteDilogOrder A_t) (t.d • x) = t.d • x := by
    intro x hx
    exact Lz_inv_fixes_multiples hp ⟨x, hx⟩
  have hsum := finiteDilogTorsionSum_eq_zero hfixed
    (hp.finiteDilogFiveTerm ha) hcomm hR hjR t.d hfix
    (shiftWitnessGroup_displacement hp p).symm (torsionResidue_neg_ne_zero hp p hp0)
  let e := torsionEquiv hp I
  rw [Finset.sum_subtype (s := Finset.univ.filter (fun u : finiteDilogGroup A_t =>
      t.d • u = 0)) (p := fun u : finiteDilogGroup A_t =>
      t.d • u = 0) (by simp)] at hsum
  rw [← Equiv.sum_comp e] at hsum
  exact hsum

/-! ### The bicharacter phase

The grid recursion changes the phase of `-L^{m+1}p` into the stated shift phase. -/

/-- Moving `L` from the first to the second argument of the symplectic form uses
`L^{-1}=(d_j-1)I-L`. -/
private theorem intSymplecticForm_Lz_left {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (hp : t.IsAssociatedStabilizerPair A_t Lz) (p q : IntPhaseSpace) :
    intSymplecticForm ((Lz : Mat(2, ℤ)).mulVec p) q =
      ((t.triple.towerDimension : ℤ) - 1) * intSymplecticForm p q -
        intSymplecticForm p ((Lz : Mat(2, ℤ)).mulVec q) := by
  have hmul : (Lz : Mat(2, ℤ)) * ((Lz⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul]
    simp
  have hsymp := intSymplecticForm_matrix_mulVec (Lz : Mat(2, ℤ)) p
    (((Lz⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)).mulVec q)
  rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec,
    Matrix.SpecialLinearGroup.det_coe, one_mul] at hsymp
  calc
    _ = intSymplecticForm p
          (((Lz⁻¹ : SL(2, ℤ)) : Mat(2, ℤ)).mulVec q) := hsymp
    _ = _ := by
      rw [hp.Lz_inv_eq, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      simp only [intSymplecticForm, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring

/-- The witness phase differs from the shift phase by a multiple of `d`. -/
private theorem shiftPhase_difference {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (hp : t.IsAssociatedStabilizerPair A_t Lz) (p q : IntPhaseSpace) :
    intSymplecticForm
        (((Lz : Mat(2, ℤ)) ^ ((t.triple.m : ℕ) + 1)).mulVec p) q =
      (t.r : ℤ) * intSymplecticForm p
        (shiftZaunerAction (-(t.triple.towerDimension : ℤ)) (Lz : Mat(2, ℤ)) q) +
      (t.d : ℤ) * intSymplecticForm ((Lz : Mat(2, ℤ)).mulVec p) q := by
  calc
    _ = ((t.d : ℤ) - (t.r : ℤ)) *
          intSymplecticForm ((Lz : Mat(2, ℤ)).mulVec p) q -
        (t.r : ℤ) * intSymplecticForm p q := by
      rw [hp.Lz_pow_m_succ_eq, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec]
      simp only [intSymplecticForm, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    _ = _ := by
      rw [intSymplecticForm_Lz_left hp p q]
      simp only [shiftZaunerAction, Matrix.add_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, intSymplecticForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring

/-- On the rational witness characteristic, `(A-I)(y/N)=-L^{m+1}p`. -/
private theorem shiftWitness_action_rational {t : AdmissibleTuple}
    {A_t Lz : SL(2, ℤ)} (hp : t.IsAssociatedStabilizerPair A_t Lz)
    (p : IntPhaseSpace) :
    ∀ i, ratVecAction (A_t : Mat(2, ℤ))
          (fun j => (shiftWitness t Lz p j : ℚ) / finiteDilogOrder A_t) i -
        (shiftWitness t Lz p i : ℚ) / finiteDilogOrder A_t =
      (-(((Lz : Mat(2, ℤ)) ^ ((t.triple.m : ℕ) + 1)).mulVec p) i : ℚ) := by
  have hN : (finiteDilogOrder A_t : ℚ) ≠ 0 := by
    have hNpos : 0 < finiteDilogOrder A_t := by
      rw [hp.finiteDilogOrder_eq]
      exact Nat.mul_pos
        (Nat.sub_pos_of_lt t.triple.three_lt_towerDimension)
        (pow_pos (lt_trans (by decide : 0 < 3) t.pair.three_lt_d) _)
    exact_mod_cast hNpos.ne'
  intro i
  have hi := congrFun (shiftWitness_A_sub_one hp p) i
  have hiQ := congrArg (fun z : ℤ => (z : ℚ)) hi
  fin_cases i <;>
    simp [ratVecAction, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.sub_apply, Matrix.map_apply] at hiQ ⊢ <;>
    field_simp [hN] <;>
    linear_combination hiQ

/-- The fixed bicharacter at `q/d` may use the rational witness lift and the literal index
`q/d` in place of their canonical residue lifts. -/
private theorem fixedBicharacter_torsion {t : AdmissibleTuple}
    {A_t Lz : SL(2, ℤ)} (hp : t.IsAssociatedStabilizerPair A_t Lz)
    (p q : IntPhaseSpace) :
    fixedBicharacter A_t (finiteDilogOrder A_t) (shiftWitnessGroup hp p)
        (torsionResidue t A_t q) =
      thetaBicharacter
        (fun i => (shiftWitness t Lz p i : ℚ) / finiteDilogOrder A_t)
        (shiftRationalPoint t.d q) A_t := by
  let N := finiteDilogOrder A_t
  have hNpos : 0 < N := by
    dsimp [N]
    rw [hp.finiteDilogOrder_eq]
    exact Nat.mul_pos
      (Nat.sub_pos_of_lt t.triple.three_lt_towerDimension)
      (pow_pos (lt_trans (by decide : 0 < 3) t.pair.three_lt_d) _)
  have : NeZero N := ⟨hNpos.ne'⟩
  let r := zmodCharacteristic N (shiftWitnessGroup hp p)
  let r₀ := fun i => (shiftWitness t Lz p i : ℚ) / N
  let s := zmodCharacteristic N (torsionResidue t A_t q)
  let s₀ := shiftRationalPoint t.d q
  have hr : A_t ∈ gammaSubgroup r :=
    (mem_fixedCharacteristics_iff A_t N _).mp (shiftWitnessGroup hp p).property
  have hs₀ : A_t ∈ gammaSubgroup s₀ :=
    hp.A_mem_gammaSubgroup (exists_intCast_mul_shiftRationalPoint t.d q)
  have hre : IsIntegralIndex (r - r₀) := by
    change IsIntegralIndex
      (zmodCharacteristic N (fun i => (shiftWitness t Lz p i : ZMod N)) -
        fun i => (shiftWitness t Lz p i : ℚ) / N)
    exact isIntegralIndex_zmodCharacteristic_intCast_sub N _
  have hse : IsIntegralIndex (s - s₀) := torsionResidue_characteristic hp q
  have hr₀ : A_t ∈ gammaSubgroup r₀ :=
    mem_gammaSubgroup_of_isIntegralIndex_sub
      (by simpa only [neg_sub] using (isIntegralIndex_neg_iff _).mpr hre) hr
  calc
    _ = thetaBicharacter r s A_t := rfl
    _ = thetaBicharacter s r A_t := thetaBicharacter_comm _ _ _
    _ = thetaBicharacter s₀ r A_t := by
      have heq : s₀ + (s - s₀) = s := by abel
      rw [← heq]
      exact thetaBicharacter_add_of_isIntegralIndex_left A_t hs₀ hr hse
    _ = thetaBicharacter r s₀ A_t := thetaBicharacter_comm _ _ _
    _ = thetaBicharacter r₀ s₀ A_t := by
      have heq : r₀ + (r - r₀) = r := by abel
      rw [← heq]
      exact thetaBicharacter_add_of_isIntegralIndex_left A_t hr₀ hs₀ hre

/-- The torsion bicharacter is the `d`-th root with exponent
`⟨L^{m+1}p,q⟩`. -/
private theorem fixedBicharacter_torsion_root {t : AdmissibleTuple}
    {A_t Lz : SL(2, ℤ)} (hp : t.IsAssociatedStabilizerPair A_t Lz)
    (p q : IntPhaseSpace) :
    fixedBicharacter A_t (finiteDilogOrder A_t) (shiftWitnessGroup hp p)
        (torsionResidue t A_t q) =
      standardRoot t.d ^
        intSymplecticForm
          (((Lz : Mat(2, ℤ)) ^ ((t.triple.m : ℕ) + 1)).mulVec p) q := by
  have hd : (t.d : ℂ) ≠ 0 := by
    exact_mod_cast (lt_trans (by decide : 0 < 3) t.pair.three_lt_d).ne'
  have : NeZero t.d := ⟨by
    exact (lt_trans (by decide : 0 < 3) t.pair.three_lt_d).ne'⟩
  rw [fixedBicharacter_torsion hp p q]
  change thetaBicharacter
      (fun i => (shiftWitness t Lz p i : ℚ) / finiteDilogOrder A_t)
      (fun i => (q i : ℚ) / t.d) A_t = _
  rw [thetaBicharacter_div_natCast
      (k := fun i => -(((Lz : Mat(2, ℤ)) ^ ((t.triple.m : ℕ) + 1)).mulVec p i))
      A_t t.d (by simpa only [Int.cast_neg] using shiftWitness_action_rational hp p)
      q (hp.A_mem_gammaSubgroup (exists_intCast_mul_shiftRationalPoint t.d q))]
  have hnum : q 1 *
        (-(((Lz : Mat(2, ℤ)) ^ ((t.triple.m : ℕ) + 1)).mulVec p)) 0 -
      q 0 * (-(((Lz : Mat(2, ℤ)) ^ ((t.triple.m : ℕ) + 1)).mulVec p)) 1 =
        intSymplecticForm
          (((Lz : Mat(2, ℤ)) ^ ((t.triple.m : ℕ) + 1)).mulVec p) q := by
    simp only [intSymplecticForm, Pi.neg_apply]
    ring
  simp only [Pi.neg_apply] at hnum
  rw [hnum, standardRoot, ← Complex.exp_int_mul]
  congr 1
  push_cast
  field_simp [hd]

/-- The torsion bicharacter equals the Weyl phase at `λ=-d_j`. -/
private theorem fixedBicharacter_shiftPhase {t : AdmissibleTuple}
    {A_t Lz : SL(2, ℤ)} (hp : t.IsAssociatedStabilizerPair A_t Lz)
    (p q : IntPhaseSpace) :
    fixedBicharacter A_t (finiteDilogOrder A_t) (shiftWitnessGroup hp p)
        (torsionResidue t A_t q) =
      standardRoot t.d ^ ((t.r : ℤ) * intSymplecticForm p
        (shiftZaunerAction (-(t.triple.towerDimension : ℤ)) (Lz : Mat(2, ℤ)) q)) := by
  have : NeZero t.d := ⟨(lt_trans (by decide : 0 < 3) t.pair.three_lt_d).ne'⟩
  rw [fixedBicharacter_torsion_root hp p q]
  apply standardRoot_zpow_eq_of_dvd_sub
  rw [shiftPhase_difference hp p q]
  refine ⟨intSymplecticForm ((Lz : Mat(2, ℤ)).mulVec p) q, ?_⟩
  ring

/-! ### The cocycle quotient

For the two integral positions of the chosen transversal, the representative is literally zero;
all other positions have nonintegral characteristic. -/

/-- The finite dilogarithm at the torsion residue is its value at `q/d`. -/
private theorem finiteDilogE_torsion {t : AdmissibleTuple}
    {A_t Lz : SL(2, ℤ)} (hp : t.IsAssociatedStabilizerPair A_t Lz)
    (ha : 0 < t.Q.a) (q : IntPhaseSpace) :
    finiteDilogE A_t t.Q.rootPlus (torsionResidue t A_t q) =
      finiteDilogValue A_t t.Q.rootPlus (shiftRationalPoint t.d q) := by
  unfold finiteDilogE
  exact finiteDilogValue_congr (hp.isAttractiveFixedPoint ha)
    (hp.A_mem_gammaSubgroup (exists_intCast_mul_shiftRationalPoint t.d q))
    (torsionResidue_characteristic hp q)

/-- At `q=0` or a nonzero residue class, `F(q/d) ש_A^{q/d}(ρ)=μ_A`. -/
private theorem finiteDilogValue_mul_cocycle {t : AdmissibleTuple}
    {A_t Lz : SL(2, ℤ)} (hp : t.IsAssociatedStabilizerPair A_t Lz)
    (q : IntPhaseSpace) (hq : q = 0 ∨ intPhaseSpaceMod t.d q ≠ 0) :
    finiteDilogValue A_t t.Q.rootPlus (shiftRationalPoint t.d q) *
      sfModularCocycleReal' (shiftRationalPoint t.d q) A_t t.Q.rootPlus =
        etaMultiplier A_t := by
  rcases hq with rfl | hq
  · have hM0 : A_t ∈ gammaSubgroup 0 :=
      hp.A_mem_gammaSubgroup fun _ => ⟨0, by simp⟩
    rw [shiftRationalPoint_zero,
      finiteDilogValue_of_isIntegralIndex A_t t.Q.rootPlus
        (by intro i; exact ⟨0, by simp⟩),
      sfModularCocycleReal'_of_mem hM0,
      sfModularCocycleRealTotal_zero_of_flt_eq_self
        t.form_admissible.rootPlus_irrational hM0
        hp.fltDenominator_A_rootPlus_pos hp.flt_A_rootPlus]
    have hs : ((Real.sqrt (fltDenominator (A_t : Mat(2, ℤ)) t.Q.rootPlus) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr hp.fltDenominator_A_rootPlus_pos).ne'
    rw [etaMultiplier]
    exact mul_div_cancel₀ _ hs
  · have hnon : ¬ IsIntegralIndex (shiftRationalPoint t.d q) :=
      not_isIntegralIndex_shiftRationalPoint t.d
        (lt_trans (by decide : 0 < 3) t.pair.three_lt_d) hq
    rw [finiteDilogValue_of_not_isIntegralIndex A_t t.Q.rootPlus hnon]
    have hne : sfModularCocycleReal' (shiftRationalPoint t.d q) A_t t.Q.rootPlus ≠ 0 := by
      rw [hp.sfModularCocycleReal'_A q]
      exact sfModularCocycleRealTotal_ne_zero_of_flt_eq_self
        (hp.A_mem_gammaSubgroup (exists_intCast_mul_shiftRationalPoint t.d q))
        t.form_admissible.rootPlus_irrational hnon
        hp.fltDenominator_A_rootPlus_pos hp.flt_A_rootPlus
    exact div_mul_cancel₀ _ hne

/-- The ratio of finite dilogarithm values is the product of the two cocycle factors at
representatives whose integral characteristics are literally zero. -/
private theorem finiteDilogValue_div_eq_cocycle_product {t : AdmissibleTuple}
    {A_t Lz : SL(2, ℤ)} (hp : t.IsAssociatedStabilizerPair A_t Lz)
    (q p : IntPhaseSpace)
    (hq : q = 0 ∨ intPhaseSpaceMod t.d q ≠ 0)
    (hqp : q - p = 0 ∨ intPhaseSpaceMod t.d (q - p) ≠ 0) :
    finiteDilogValue A_t t.Q.rootPlus (shiftRationalPoint t.d (q - p)) /
        finiteDilogValue A_t t.Q.rootPlus (shiftRationalPoint t.d q) =
      sfModularCocycleReal' (shiftRationalPoint t.d q) A_t t.Q.rootPlus *
        sfModularCocycleReal' (shiftRationalPoint t.d (q - p)) A_t⁻¹ t.Q.rootPlus := by
  let Fq := finiteDilogValue A_t t.Q.rootPlus (shiftRationalPoint t.d q)
  let Fs := finiteDilogValue A_t t.Q.rootPlus (shiftRationalPoint t.d (q - p))
  let Sq := sfModularCocycleReal' (shiftRationalPoint t.d q) A_t t.Q.rootPlus
  let Ss := sfModularCocycleReal' (shiftRationalPoint t.d (q - p)) A_t t.Q.rootPlus
  let Si := sfModularCocycleReal' (shiftRationalPoint t.d (q - p)) A_t⁻¹ t.Q.rootPlus
  have hqprod : Fq * Sq = etaMultiplier A_t :=
    finiteDilogValue_mul_cocycle hp q hq
  have hsprod : Fs * Ss = etaMultiplier A_t :=
    finiteDilogValue_mul_cocycle hp (q - p) hqp
  have hFq : Fq ≠ 0 := by
    intro hFq
    apply etaMultiplier_ne_zero A_t
    rw [← hqprod, hFq, zero_mul]
  have hinv : Ss * Si = 1 := cocycle_mul_inverse hp (q - p)
  have hFs : Fs = Fq * (Sq * Si) := by
    calc
      Fs = Fs * (Ss * Si) := by rw [hinv, mul_one]
      _ = (Fs * Ss) * Si := by ring
      _ = (Fq * Sq) * Si := by rw [hsprod, hqprod]
      _ = Fq * (Sq * Si) := by ring
  change Fs / Fq = Sq * Si
  exact (div_eq_iff hFq).mpr (by rw [hFs]; ring)

/-- In the chosen transversal, an integral summand index is literally zero, both before and
after translation by `p`. -/
private theorem transversal_cocycle_cases {t : AdmissibleTuple}
    (p : IntPhaseSpace) (I : PhaseSpaceTransversal t.d)
    (hI0 : I.repr 0 = 0) (hIp : I.repr (intPhaseSpaceMod t.d p) = p)
    (c : PhaseSpaceMod t.d) :
    (I.repr c = 0 ∨ intPhaseSpaceMod t.d (I.repr c) ≠ 0) ∧
      (I.repr c - p = 0 ∨ intPhaseSpaceMod t.d (I.repr c - p) ≠ 0) := by
  constructor
  · by_cases hc : c = 0
    · left
      simpa only [hc] using hI0
    · right
      rwa [I.residue_repr]
  · by_cases hc : c = intPhaseSpaceMod t.d p
    · left
      rw [hc, hIp, sub_self]
    · right
      intro hzero
      have hsub : intPhaseSpaceMod t.d (I.repr c - p) =
          c - intPhaseSpaceMod t.d p := by
        funext i
        have hi := congrFun (I.residue_repr c) i
        simpa [intPhaseSpaceMod, Pi.sub_apply] using
          congrArg (fun x : ZMod t.d => x - (p i : ZMod t.d)) hi
      exact hc (sub_eq_zero.mp (hsub.symm.trans hzero))

/-- The torsion pentagon summand for witness `p` and torsion coordinate `q`. -/
private def torsionConvolutionSummand {t : AdmissibleTuple}
    {A_t Lz : SL(2, ℤ)} (hp : t.IsAssociatedStabilizerPair A_t Lz)
    (p q : IntPhaseSpace) : ℂ :=
  fixedBicharacter A_t (finiteDilogOrder A_t) (shiftWitnessGroup hp p)
      (torsionResidue t A_t q) *
    (finiteDilogE A_t t.Q.rootPlus
        (⟨torsionResidue t A_t q, torsionResidue_mem hp _⟩ +
          ⟨torsionResidue t A_t (-p), torsionResidue_mem hp _⟩ :
          finiteDilogGroup A_t) /
      finiteDilogE A_t t.Q.rootPlus (torsionResidue t A_t q))

/-- A summand of the torsion pentagon sum is the corresponding twisted convolution summand. -/
private theorem torsionSummand_eq_shiftSummand {t : AdmissibleTuple}
    {A_t Lz : SL(2, ℤ)} (hp : t.IsAssociatedStabilizerPair A_t Lz)
    (ha : 0 < t.Q.a) (p : IntPhaseSpace) (I : PhaseSpaceTransversal t.d)
    (hI0 : I.repr 0 = 0) (hIp : I.repr (intPhaseSpaceMod t.d p) = p)
    (c : PhaseSpaceMod t.d) :
    torsionConvolutionSummand hp p (I.repr c) =
      standardRoot t.d ^ ((t.r : ℤ) * intSymplecticForm p
        (shiftZaunerAction (-(t.triple.towerDimension : ℤ))
          (Lz : Mat(2, ℤ)) (I.repr c))) *
        sfModularCocycleReal' (shiftRationalPoint t.d (I.repr c)) A_t t.Q.rootPlus *
        sfModularCocycleReal'
          (shiftRationalPoint t.d (I.repr c) - shiftRationalPoint t.d p)
          A_t⁻¹ t.Q.rootPlus := by
  unfold torsionConvolutionSummand
  let q := I.repr c
  have hsum :
      ((⟨torsionResidue t A_t q, torsionResidue_mem hp _⟩ +
          ⟨torsionResidue t A_t (-p), torsionResidue_mem hp _⟩ :
            finiteDilogGroup A_t) : Fin 2 → ZMod (finiteDilogOrder A_t)) =
        torsionResidue t A_t (q - p) := by
    funext i
    simp only [torsionResidue, AddSubgroup.coe_add, Pi.add_apply, Pi.sub_apply,
      Pi.neg_apply, Int.cast_sub, Int.cast_neg, Int.cast_natCast]
    ring
  have hEadd : finiteDilogE A_t t.Q.rootPlus
        (⟨torsionResidue t A_t q, torsionResidue_mem hp _⟩ +
          ⟨torsionResidue t A_t (-p), torsionResidue_mem hp _⟩ :
          finiteDilogGroup A_t) =
      finiteDilogValue A_t t.Q.rootPlus (shiftRationalPoint t.d (q - p)) := by
    rw [hsum]
    exact finiteDilogE_torsion hp ha (q - p)
  obtain ⟨hq, hqp⟩ := transversal_cocycle_cases p I hI0 hIp c
  change fixedBicharacter A_t (finiteDilogOrder A_t) (shiftWitnessGroup hp p)
      (torsionResidue t A_t q) *
      (finiteDilogE A_t t.Q.rootPlus
          (⟨torsionResidue t A_t q, torsionResidue_mem hp _⟩ +
            ⟨torsionResidue t A_t (-p), torsionResidue_mem hp _⟩ :
            finiteDilogGroup A_t) /
        finiteDilogE A_t t.Q.rootPlus (torsionResidue t A_t q)) = _
  rw [fixedBicharacter_shiftPhase hp p q, hEadd,
    finiteDilogE_torsion hp ha q,
    finiteDilogValue_div_eq_cocycle_product hp q p hq hqp,
    ← shiftRationalPoint_sub]
  ring

/-- For a nonzero displacement class, the shift convolution is the vanishing torsion sum. -/
private theorem shiftConvolutionSum_nonzero {t : AdmissibleTuple}
    {A_t Lz : SL(2, ℤ)} (hp : t.IsAssociatedStabilizerPair A_t Lz)
    (ha : 0 < t.Q.a) (p : IntPhaseSpace)
    (hp0 : intPhaseSpaceMod t.d p ≠ 0) (I : PhaseSpaceTransversal t.d)
    (hI0 : I.repr 0 = 0) (hIp : I.repr (intPhaseSpaceMod t.d p) = p) :
    t.shiftConvolutionSum A_t Lz (-(t.triple.towerDimension : ℤ)) I p = 0 := by
  unfold shiftConvolutionSum
  convert torsionSum_eq_zero hp ha p hp0 I using 1
  apply Finset.sum_congr rfl
  intro c _
  exact (torsionSummand_eq_shiftSummand hp ha p I hI0 hIp c).symm

/-- **[AFK26, Appleby, Flammia, Kopp (2026), Theorem 1.2, `thm:tci`]**: for an admissible tuple
whose form has positive leading coefficient (the orientation `γ₂₁ > 0` of
[AFK26, Appleby, Flammia, Kopp (2026), Section 4]),
`λ₀ = -d_j` is a shift in the sense of [AFK25, Definition 1.34, `dfn:shift`]: `2λ₀ + Tr L` is
prime to `d`, and the twisted convolution identity holds for every `p` and every transversal. The
source proves it for `λ` with `λ r_{j,m} ≡ -r_{j,m-1} (mod d)`, which is `λ ≡ -d_j`. -/
@[source "AFK26, Theorem 1.2, p. 2, thm:tci (shift -d_j, a > 0)"]
theorem isShift_neg_towerDimension {t : AdmissibleTuple} {A_t Lz : SL(2, ℤ)}
    (hp : t.IsAssociatedStabilizerPair A_t Lz) (ha : 0 < t.Q.a) :
    t.IsShift A_t Lz (-(t.triple.towerDimension : ℤ)) := by
  apply IsShift.intro (isShiftCoprime_neg_towerDimension t)
  intro p I hI0 hIp
  by_cases hp0 : intPhaseSpaceMod t.d p = 0
  · simp only [hp0, ite_true]
    exact shiftConvolutionSum_of_residue_zero hp _ p I hI0 hIp hp0
  · simp only [hp0, ite_false]
    exact shiftConvolutionSum_nonzero hp ha p hp0 I hI0 hIp

end AdmissibleTuple

end SIC

end
