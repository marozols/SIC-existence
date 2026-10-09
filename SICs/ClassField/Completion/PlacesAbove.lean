/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RamificationInertia.Inertia
import SICs.DedekindDomain.Ideals

/-!
# Places above a place in a finite extension

The finite types of finite and infinite places of a finite extension `L/K` above one place of
`K`, their decomposition in a tower `K ⊆ L ⊆ M`, and the finite set of ramified places with its
behavior in towers.

These index the products $\prod_{w \mid v}$ in the decomposition
$K_v \otimes_K L \cong \prod_{w \mid v} L_w$ [83, Neukirch (1999), Chapter II, Proposition 8.3]
and in the idèle norm of Milne, *Class Field Theory*, version 4.03 (2020), Chapter V, §4.

## The argument

At a finite place `v` of `K`, the primes of `𝒪_L` above `v.asIdeal` form a finite set. A prime `u`
of `𝒪_M` above `v` lies above exactly one prime of `𝒪_L`, namely `w = u ∩ 𝒪_L`, and `w` lies
above `v` because contraction is transitive in the tower. Conversely a prime above a prime above
`v` is above `v`. The two maps are inverse, so the primes of `M` above `v` are the disjoint union,
over the primes `w` of `L` above `v`, of the primes of `M` above `w`.

At an infinite place the same holds with restriction of absolute values in place of contraction:
an infinite place `u` of `M` restricts to the unique place `u|_L` of `L` below it, and restriction
is transitive.

The ramified finite places divide the nonzero different ideal, so they form a finite set. Their
restrictions give a finite set of base places outside which the extension is unramified.
The primes above one place are also exactly the fibre of restriction at that place. Since a
nonzero algebraic integer belongs to finitely many primes, only finitely many base places lie
below one of those primes (`finite_below_primes_containing`). A prime of absolute degree one has
the same absolute norm as its restriction (`absNorm_below_eq_of_prime`).
-/

noncomputable section

open IsDedekindDomain NumberField

namespace SIC

/-! ### Primes above a finite place

Primes above one place form a finite type equivalent to the fibre of place restriction. -/

namespace FinitePlace

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L]

/-- The finite set of prime ideals of `L` lying above a finite place of `K`.
The project uses the `mapEquiv` action on this type, which deliberately shadows Mathlib's
`primesOver` actions; Mathlib's lemmas about `σ • w` use those other actions. -/
abbrev PrimeAbove (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :=
  v.asIdeal.primesOver (NumberField.RingOfIntegers L)

/-- The finite place of `L` underlying a prime above `v`. -/
def PrimeAbove.place (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : PrimeAbove (L := L) v) :
    HeightOneSpectrum (NumberField.RingOfIntegers L) where
  asIdeal := w.1
  isPrime := w.2.1
  ne_bot := Ideal.ne_bot_of_mem_primesOver v.ne_bot w.2

/-- A prime-above place lies over its base place. -/
instance PrimeAbove.place_liesOver
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : PrimeAbove (L := L) v) :
    (PrimeAbove.place v w).asIdeal.LiesOver v.asIdeal :=
  w.2.2

omit [NumberField K] [NumberField L] in
/-- Distinct primes above `v` are distinct places. -/
theorem PrimeAbove.place_injective (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Function.Injective (PrimeAbove.place (L := L) v) := by
  intro w₁ w₂ h
  apply Subtype.ext
  exact congrArg HeightOneSpectrum.asIdeal h

/-- The prime above `v` given by a finite place lying over `v`. -/
def PrimeAbove.mk (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : HeightOneSpectrum (NumberField.RingOfIntegers L)) [w.asIdeal.LiesOver v.asIdeal] :
    PrimeAbove (L := L) v :=
  ⟨w.asIdeal, w.isPrime, inferInstance⟩

omit [NumberField K] [NumberField L] in
/-- The place of `PrimeAbove.mk v w` is `w`. -/
@[simp]
theorem PrimeAbove.place_mk (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : HeightOneSpectrum (NumberField.RingOfIntegers L)) [w.asIdeal.LiesOver v.asIdeal] :
    PrimeAbove.place v (PrimeAbove.mk v w) = w :=
  rfl

/-- The finite place below a finite place in an extension. -/
def below (w : HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    HeightOneSpectrum (NumberField.RingOfIntegers K) :=
  w.under (NumberField.RingOfIntegers K)

omit [NumberField K] in
/-- Only finitely many base places lie below a place containing a nonzero algebraic integer. -/
theorem finite_below_primes_containing {c : 𝓞 L} (hc : c ≠ 0) :
    (Set.image (below (K := K)) {w : HeightOneSpectrum (𝓞 L) | c ∈ w.asIdeal}).Finite :=
  (finite_primes_containing hc).image (below (K := K))

omit [NumberField K] in
/-- Restricting a finite place along the identity extension leaves it unchanged. -/
@[simp] theorem below_self (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    below (K := K) v = v := by
  apply HeightOneSpectrum.ext
  change v.asIdeal.comap (algebraMap (𝓞 K) (𝓞 K)) = v.asIdeal
  rw [Algebra.algebraMap_self, Ideal.comap_id]

/-- A finite place lies over the place below it. -/
instance liesOver_below (w : HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    w.asIdeal.LiesOver (below (K := K) w).asIdeal :=
  ⟨rfl⟩

/-- The prime of `K` below a prime `w` of `L` of absolute degree one has the same absolute norm:
`N(w) = N(w ∩ 𝒪_K)^f` and `N(w)` prime force the residue degree `f` to equal one. -/
theorem absNorm_below_eq_of_prime (w : HeightOneSpectrum (𝓞 L))
    (hw : (Ideal.absNorm w.asIdeal).Prime) :
    Ideal.absNorm (below (K := K) w).asIdeal = Ideal.absNorm w.asIdeal := by
  have hnorm := Ideal.absNorm_pow_inertiaDeg (below (K := K) w).asIdeal w.asIdeal
  have hf : w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
    apply Nat.Prime.eq_one_of_pow
    rw [hnorm]
    exact hw
  simpa only [hf, pow_one] using hnorm

omit [NumberField K] [NumberField L] in
/-- A finite place lying over `v` has `v` as the place below it. -/
theorem below_eq_of_liesOver (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : HeightOneSpectrum (NumberField.RingOfIntegers L)) [w.asIdeal.LiesOver v.asIdeal] :
    below (K := K) w = v := by
  apply HeightOneSpectrum.ext
  exact (Ideal.LiesOver.over (P := w.asIdeal) (p := v.asIdeal)).symm

omit [NumberField K] [NumberField L] in
/-- Taking the place below a member of `PrimeAbove v` recovers `v`. -/
@[simp]
theorem PrimeAbove.below_place
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : PrimeAbove (L := L) v) :
    below (K := K) (L := L) (PrimeAbove.place v w) = v := by
  exact below_eq_of_liesOver v (PrimeAbove.place v w)

/-- Primes above `v` are the finite places in the fibre of `below` at `v`. -/
def PrimeAbove.equivFiber (v : HeightOneSpectrum (𝓞 K)) :
    PrimeAbove (L := L) v ≃
      {w : HeightOneSpectrum (𝓞 L) | below (K := K) w = v} where
  toFun w := ⟨PrimeAbove.place v w, PrimeAbove.below_place v w⟩
  invFun w := by
    haveI : w.1.asIdeal.LiesOver v.asIdeal :=
      ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩
    exact PrimeAbove.mk v w.1
  left_inv w := by
    apply Subtype.ext
    rfl
  right_inv w := by
    apply Subtype.ext
    rfl

/-- Only finitely many finite places of `L` lie above each finite place of `K`, so restriction
of places tends to the cofinite filter along the cofinite filter. -/
theorem tendsto_below_cofinite :
    Filter.Tendsto (below (K := K) (L := L)) Filter.cofinite Filter.cofinite := by
  apply Filter.Tendsto.cofinite_of_finite_preimage_singleton
  intro v
  let f : ((below (K := K) (L := L)) ⁻¹' {v}) → PrimeAbove (L := L) v :=
    (PrimeAbove.equivFiber (L := L) v).symm
  exact Finite.of_injective f (PrimeAbove.equivFiber (L := L) v).symm.injective

/-- The finite set of places of `L` lying above a finite set `S` of places of `K`. -/
def placesAbove (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Finset (HeightOneSpectrum (𝓞 L)) := by
  classical
  letI : Filter.TendstoCofinite (below (K := K) (L := L)) :=
    ⟨tendsto_below_cofinite⟩
  exact (Filter.TendstoCofinite.finite_preimage
    (below (K := K) (L := L)) S.finite_toSet).toFinset

/-- A place of `L` belongs to `placesAbove S` exactly when its place below belongs to `S`. -/
@[simp]
theorem mem_placesAbove (S : Finset (HeightOneSpectrum (𝓞 K)))
    (w : HeightOneSpectrum (𝓞 L)) :
    w ∈ placesAbove (L := L) S ↔ below (K := K) w ∈ S := by
  classical
  simp [placesAbove]

/-- The places above `S` in the identity extension are exactly `S`. -/
@[simp] theorem placesAbove_self (S : Finset (HeightOneSpectrum (𝓞 K))) :
    placesAbove (L := K) S = S := by
  ext v
  simp

/-! ### The finite ramification support

A ramified prime divides the nonzero different ideal, whose set of ideal divisors is finite.
Restricting these finitely many places gives a finite set of base places containing all
ramification, as used by Milne, Chapter VII, Proposition 2.5. -/

/-- Only finitely many finite places of `L` ramify over `K`.
This supplies the finite exceptional set used by Milne, *Class Field Theory*, Chapter VII,
Proposition 2.5; it follows from the different-ideal criterion for ramification. -/
theorem finite_ramified :
    {w : HeightOneSpectrum (NumberField.RingOfIntegers L) |
      w.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 1}.Finite := by
  apply (Ideal.finite_factors
    (differentIdeal_ne_bot : differentIdeal (𝓞 K) (𝓞 L) ≠ ⊥)).subset
  intro w hw
  by_contra hd
  have hu : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
    (not_dvd_differentIdeal_iff).mp hd
  exact hw (@Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
    (𝓞 K) (𝓞 L) _ _ _ w.asIdeal w.isPrime hu _)

variable (K L) in
/-- The finite set of places of `K` below a ramified place of `L`: the exceptional set of
Milne, *Class Field Theory*, Chapter VII, Proposition 2.5. -/
noncomputable def ramifiedSet : Finset (HeightOneSpectrum (NumberField.RingOfIntegers K)) := by
  classical
  exact ((finite_ramified (K := K) (L := L)).image (below (K := K) (L := L))).toFinset

/-- A place of `K` lies in `ramifiedSet K L` exactly when a place of `L` above it ramifies. -/
theorem mem_ramifiedSet {v : HeightOneSpectrum (NumberField.RingOfIntegers K)} :
    v ∈ ramifiedSet K L ↔ ∃ w : HeightOneSpectrum (NumberField.RingOfIntegers L),
      below (K := K) w = v ∧ w.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 1 := by
  classical
  simp only [ramifiedSet, Set.Finite.mem_toFinset, Set.mem_image, Set.mem_ofPred_eq]
  exact exists_congr fun _ ↦ and_comm

/-- `L/K` is unramified at every place of `L` above a place outside `ramifiedSet K L`. -/
theorem ramificationIdx_eq_one_of_notMem_ramifiedSet
    (w : HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hw : below (K := K) w ∉ ramifiedSet K L) :
    w.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := by
  by_contra h
  exact hw (mem_ramifiedSet.mpr ⟨w, rfl, h⟩)

/-- `L/K` is unramified outside `S` exactly when its ramified set is contained in `S`. -/
theorem ramifiedSet_subset_iff (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ramifiedSet K L ⊆ S ↔
      ∀ w : HeightOneSpectrum (𝓞 L), below (K := K) w ∉ S →
        w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  constructor
  · intro hS w hw
    exact ramificationIdx_eq_one_of_notMem_ramifiedSet w (fun h ↦ hw (hS h))
  · intro hS v hv
    obtain ⟨w, rfl, hram⟩ := mem_ramifiedSet.mp hv
    by_contra hw
    exact hram (hS w hw)

/-- If `L/K` is unramified outside `S`, every place above a place outside `S` is unramified. -/
theorem ramificationIdx_eq_one_of_ramifiedSet_subset
    {S : Finset (HeightOneSpectrum (𝓞 K))} (hS : ramifiedSet K L ⊆ S)
    (w : HeightOneSpectrum (𝓞 L)) (hw : below (K := K) w ∉ S) :
    w.asIdeal.ramificationIdx (𝓞 K) = 1 :=
  (ramifiedSet_subset_iff S).mp hS w hw

/-! ### Primes above a finite place in a tower -/

section Tower

variable {M : Type*} [Field M] [NumberField M] [Algebra L M] [Algebra K M]
  [IsScalarTower K L M]

omit [NumberField K] [NumberField L] [NumberField M] in
/-- Restriction of finite places is transitive in towers. -/
theorem below_below (u : HeightOneSpectrum (NumberField.RingOfIntegers M)) :
    below (K := K) (below (K := L) u) = below (K := K) u := by
  apply HeightOneSpectrum.ext
  exact Ideal.under_under u.asIdeal

omit [NumberField K] [NumberField L] [NumberField M] in
/-- The place of `L` below a finite place of `M` above `v` also lies over `v`. -/
theorem liesOver_below_of_liesOver
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (u : HeightOneSpectrum (NumberField.RingOfIntegers M))
    [u.asIdeal.LiesOver v.asIdeal] :
    (below (K := L) u).asIdeal.LiesOver v.asIdeal :=
  Ideal.under_liesOver_of_liesOver (𝓞 L) u.asIdeal v.asIdeal

/-- The primes of `M` above a finite place `v` of `K` are the pairs of a prime `w` of `L` above
`v` and a prime of `M` above `w`. The place of the image of `⟨w, u⟩` is the place of `u`
definitionally. -/
def PrimeAbove.sigmaEquiv (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (Σ w : PrimeAbove (L := L) v,
        PrimeAbove (K := L) (L := M) (PrimeAbove.place v w)) ≃
      PrimeAbove (L := M) v where
  toFun p := ⟨p.2.1, p.2.2.1, by
    let _ : p.2.1.LiesOver p.1.1 := p.2.2.2
    let _ : p.1.1.LiesOver v.asIdeal := p.1.2.2
    exact Ideal.LiesOver.trans p.2.1 p.1.1 v.asIdeal⟩
  invFun u := ⟨⟨u.1.under (NumberField.RingOfIntegers L), by
      let _ : u.1.IsPrime := u.2.1
      refine ⟨Ideal.IsPrime.under _ u.1, ?_⟩
      constructor
      rw [Ideal.under_under]
      exact u.2.2.over⟩,
    ⟨u.1, u.2.1, by
      exact ⟨rfl⟩⟩⟩
  left_inv p := by
    apply Sigma.subtype_ext
    · apply Subtype.ext
      exact p.2.2.2.over.symm
    · rfl
  right_inv u := by
    apply Subtype.ext
    rfl

/-- Unramifiedness outside `S` passes from `M/K` to the top `M/L` of the tower, outside the
places of `L` above `S`. -/
theorem ramificationIdx_above_eq_one_of_notMem
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hS : ramifiedSet K M ⊆ S)
    (u : HeightOneSpectrum (NumberField.RingOfIntegers M))
    (hu : below (K := L) u ∉ placesAbove (K := K) (L := L) S) :
    u.asIdeal.ramificationIdx (NumberField.RingOfIntegers L) = 1 := by
  have hout : below (K := K) u ∉ S := by
    simpa only [mem_placesAbove, below_below] using hu
  exact Nat.eq_one_of_dvd_one
    ((ramificationIdx_eq_one_of_ramifiedSet_subset hS u hout) ▸
    Ideal.ramificationIdx_above_dvd (below (K := L) u).asIdeal u.asIdeal)

/-- Unramifiedness outside `S` passes from `M/K` to the bottom `L/K` of the tower. -/
theorem ramificationIdx_below_eq_one_of_notMem
    (S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (hS : ramifiedSet K M ⊆ S)
    (w : HeightOneSpectrum (NumberField.RingOfIntegers L)) (hw : below (K := K) w ∉ S) :
    w.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := by
  let u := PrimeAbove.place (L := M) w (Classical.arbitrary _)
  have hu : below (K := L) u = w := PrimeAbove.below_place w (Classical.arbitrary _)
  have hout : below (K := K) u ∉ S := by
    rwa [← below_below (K := K) (L := L) u, hu]
  exact Nat.eq_one_of_dvd_one
    ((ramificationIdx_eq_one_of_ramifiedSet_subset hS u hout) ▸
      Ideal.ramificationIdx_below_dvd w.asIdeal u.asIdeal)

variable (K L M) in
/-- The places of `K` ramified in a subextension `L` are ramified in `M`. -/
theorem ramifiedSet_subset_ramifiedSet : ramifiedSet K L ⊆ ramifiedSet K M := by
  intro v hv
  obtain ⟨w, hw, hram⟩ := mem_ramifiedSet.mp hv
  by_contra hn
  apply hram
  apply ramificationIdx_below_eq_one_of_notMem (ramifiedSet K M) (subset_rfl) w
  exact hw ▸ hn

/-- If `M/K` is unramified outside `S`, then `M/L` is unramified outside the places above `S`. -/
theorem ramificationIdx_above_eq_one (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ramifiedSet K M ⊆ S) :
    ramifiedSet L M ⊆ placesAbove (K := K) (L := L) S := by
  apply (ramifiedSet_subset_iff _).mpr
  exact ramificationIdx_above_eq_one_of_notMem S hS

/-- If `M/K` is unramified outside `S`, then `L/K` is unramified outside `S`. -/
theorem ramificationIdx_below_eq_one (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ramifiedSet K M ⊆ S) : ramifiedSet K L ⊆ S := by
  exact (ramifiedSet_subset_ramifiedSet K L M).trans hS

end Tower

end FinitePlace

/-! ### Places above an infinite place -/

namespace InfinitePlace

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L]

/-- The finite type of infinite places of `L` above an infinite place of `K`, using Mathlib's
`NumberField.InfinitePlace.placesOver` set. -/
abbrev PlaceAbove (v : NumberField.InfinitePlace K) :=
  ↥(v.placesOver L)

/-- A place above `v` supplies the lying-over instance used by its local norm. -/
instance PlaceAbove.liesOver (v : NumberField.InfinitePlace K)
    (w : PlaceAbove (L := L) v) : w.1.LiesOver v := by
  exact w.2

/-- The places of `L` above one infinite place of `K` form a finite type. -/
noncomputable instance PlaceAbove.fintype (v : NumberField.InfinitePlace K) :
    Fintype (PlaceAbove (L := L) v) := by
  classical
  exact Subtype.fintype _

/-- Every infinite place of `K` has a place of `L` above it. -/
instance PlaceAbove.nonempty (v : NumberField.InfinitePlace K) :
    Nonempty (PlaceAbove (L := L) v) := by
  obtain ⟨w, hw⟩ := NumberField.InfinitePlace.comap_surjective (K := L) v
  exact ⟨⟨w, by
    rw [← hw]
    constructor
    ext x
    rfl⟩⟩

/-- The infinite place below an infinite place in an extension: the restriction to `K`. -/
def below (w : NumberField.InfinitePlace L) : NumberField.InfinitePlace K :=
  w.comap (algebraMap K L)

omit [NumberField K] [NumberField L] in
/-- An infinite place lies over the place below it. -/
instance liesOver_below (w : NumberField.InfinitePlace L) :
    w.LiesOver (below (K := K) w) := by
  constructor
  ext x
  rfl

omit [NumberField K] [NumberField L] in
/-- An infinite place lying over `v` has `v` as the place below it. -/
theorem below_eq_of_liesOver (v : NumberField.InfinitePlace K)
    (w : NumberField.InfinitePlace L) [w.LiesOver v] :
    below (K := K) w = v := by
  exact NumberField.InfinitePlace.LiesOver.comap_eq w v

/-! ### Places above an infinite place in a tower -/

section Tower

variable {M : Type*} [Field M] [NumberField M] [Algebra L M] [Algebra K M]
  [IsScalarTower K L M]

omit [NumberField K] [NumberField L] [NumberField M] in
/-- Restriction of infinite places is transitive in towers. -/
theorem below_below (u : NumberField.InfinitePlace M) :
    below (K := K) (below (K := L) u) = below (K := K) u := by
  change (u.comap (algebraMap L M)).comap (algebraMap K L) =
    u.comap (algebraMap K M)
  rw [← NumberField.InfinitePlace.comap_comp, ← IsScalarTower.algebraMap_eq]

omit [NumberField K] [NumberField L] [NumberField M] in
/-- The place of `L` below an infinite place of `M` above `v` also lies over `v`. -/
theorem liesOver_below_of_liesOver (v : NumberField.InfinitePlace K)
    (u : NumberField.InfinitePlace M) [u.LiesOver v] :
    (below (K := L) u).LiesOver v := by
  rw [← below_eq_of_liesOver v u, ← below_below (K := K) (L := L) u]
  infer_instance

omit [NumberField K] [NumberField L] [NumberField M] in
/-- Lying over is transitive in a tower of infinite places. -/
theorem liesOver_trans (v : NumberField.InfinitePlace K) (w : NumberField.InfinitePlace L)
    (u : NumberField.InfinitePlace M) [w.LiesOver v] [u.LiesOver w] : u.LiesOver v := by
  have h : below (K := K) u = v := by
    calc
      below (K := K) u = below (K := K) (below (K := L) u) :=
        (below_below u).symm
      _ = v := by rw [below_eq_of_liesOver w u, below_eq_of_liesOver v w]
  rw [← h]
  infer_instance

/-- The infinite places of `M` above `v` are the pairs of a place `w` of `L` above `v` and a
place of `M` above `w`. -/
def PlaceAbove.sigmaEquiv (v : NumberField.InfinitePlace K) :
    (Σ w : PlaceAbove (L := L) v, PlaceAbove (K := L) (L := M) w.1) ≃
      PlaceAbove (L := M) v where
  toFun p := ⟨p.2.1, liesOver_trans v p.1.1 p.2.1⟩
  invFun u := ⟨⟨below (K := L) u.1, by
      let _ : u.1.LiesOver v := u.2
      have h : below (K := K) (below (K := L) u.1) = v := by
        calc
          below (K := K) (below (K := L) u.1) = below (K := K) u.1 :=
            below_below u.1
          _ = v := below_eq_of_liesOver v u.1
      exact ⟨congrArg Subtype.val h⟩⟩,
    ⟨u.1, liesOver_below u.1⟩⟩
  left_inv p := by
    apply Sigma.subtype_ext
    · apply Subtype.ext
      exact below_eq_of_liesOver p.1.1 p.2.1
    · rfl
  right_inv u := by
    apply Subtype.ext
    rfl

end Tower

end InfinitePlace

end SIC
