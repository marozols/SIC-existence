/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.ClassField.Ideles.Galois
import SICs.GroupCohomology.Multiplicative

/-!
# S-idèles integral outside a finite set of base places

The Galois-stable subgroup of idèles integral outside the places above a finite set, its
coordinate decomposition, and the exhaustion of the idèle group by these subgroups.

These are the groups $I_{L,S}$ of Milne, *Class Field Theory*, version 4.03 (2020), Chapter VII,
§2, proof of Proposition 2.5(b). All infinite places are included; `S` lists the finite places of
`K`. Finite places of `L` are partitioned by their unique place below them. The restricted
product condition is automatic for arbitrary coordinates in the finite exceptional fibers and
integral units elsewhere. Each idèle has only finitely many nonintegral coordinates, so lies in
one such subgroup. Conjugation preserves integral units and the place below each component.
-/

noncomputable section
open IsDedekindDomain NumberField
open scoped NumberField NumberField.AdeleRing NumberField.LiesOver
namespace SIC.IdeleGroup
variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-! ### The stable subgroup

The exceptional coordinates lie above a finite set of base places. Restrictedness gives
exhaustion by these subgroups, and completion transport preserves their unit conditions. -/

/-- Idèles of `L` integral at every finite place not above `S`; all infinite places are allowed.
Milne, *Class Field Theory*, Chapter VII, §2, proof of Proposition 2.5(b). -/
def sSubgroup (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup (NumberField.IdeleGroup (𝓞 L) L) := by
  refine {
    carrier := {x | ∀ w, FinitePlace.below (K := K) w ∉ S →
      finiteComponent L w x ∈ FinitePlace.unitGroup w}
    one_mem' := by
      intro w _
      simp
    mul_mem' := by
      intro x y hx hy w hw
      rw [map_mul]
      exact (FinitePlace.unitGroup w).mul_mem (hx w hw) (hy w hw)
    inv_mem' := by
      intro x hx w hw
      rw [map_inv]
      exact (FinitePlace.unitGroup w).inv_mem (hx w hw) }
omit [NumberField K] in
/-- Membership in the group of idèles integral outside `S`. -/
theorem mem_sSubgroup (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : NumberField.IdeleGroup (𝓞 L) L) :
    x ∈ sSubgroup (L := L) S ↔ ∀ w, FinitePlace.below (K := K) w ∉ S →
      finiteComponent L w x ∈ FinitePlace.unitGroup w := by
  rfl
omit [NumberField K] in
/-- Enlarging the finite exceptional set enlarges its idèle subgroup. -/
theorem sSubgroup_mono {S T : Finset (HeightOneSpectrum (𝓞 K))} (h : S ⊆ T) :
    sSubgroup (L := L) S ≤ sSubgroup (L := L) T := by
  intro x hx
  rw [mem_sSubgroup] at hx ⊢
  exact fun w hw ↦ hx w (fun hs ↦ hw (h hs))
omit [NumberField K] in
/-- Every idèle is integral outside the places above some finite set of base places.
Milne, *Class Field Theory*, Chapter VII, Proposition 2.5, directed-union argument. -/
theorem exists_mem_sSubgroup (x : NumberField.IdeleGroup (𝓞 L) L) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), x ∈ sSubgroup (L := L) S := by
  classical
  have hfinite :
      {w : HeightOneSpectrum (𝓞 L) |
        finiteComponent L w x ∉ FinitePlace.unitGroup w}.Finite := by
    rw [← Filter.eventually_cofinite]
    filter_upwards [((componentsEquiv L x).2).2] with w hw
    rw [finiteComponent_apply]
    exact hw
  let S := (hfinite.image (FinitePlace.below (K := K))).toFinset
  refine ⟨S, (mem_sSubgroup S x).2 ?_⟩
  intro w hw
  by_contra hunit
  apply hw
  have hmem : FinitePlace.below (K := K) w ∈
      (FinitePlace.below (K := K)) ''
        {w | finiteComponent L w x ∉ FinitePlace.unitGroup w} :=
    ⟨w, hunit, rfl⟩
  simpa only [S, Set.Finite.mem_toFinset] using hmem
omit [NumberField K] in
/-- The Galois action preserves the group of idèles integral outside `S`. -/
theorem smul_mem_sSubgroup (S : Finset (HeightOneSpectrum (𝓞 K)))
    (g : L ≃ₐ[K] L) (x : NumberField.IdeleGroup (𝓞 L) L)
    (hx : x ∈ sSubgroup (L := L) S) : g • x ∈ sSubgroup (L := L) S := by
  rw [mem_sSubgroup] at hx ⊢
  intro w' hw'
  let v := FinitePlace.below (K := K) w'
  let w := (FinitePlace.mapEquiv g.toRingEquiv).symm w'
  let _ : w'.asIdeal.LiesOver v.asIdeal := FinitePlace.liesOver_below w'
  let _ : w.asIdeal.LiesOver v.asIdeal := FinitePlace.liesOver_mapEquiv g.symm v w'
  have hw : FinitePlace.mapEquiv g.toRingEquiv w = w' := by
    change FinitePlace.mapEquiv g.toRingEquiv
      (FinitePlace.mapEquiv g.symm.toRingEquiv w') = w'
    rw [AlgEquiv.symm_toRingEquiv, ← FinitePlace.mapEquiv_symm]
    exact Equiv.apply_symm_apply _ _
  rw [smul_def, finiteComponent_congr g.toRingEquiv w w' hw]
  apply FinitePlace.units_map_completionEquiv_mem g.toRingEquiv w w' hw
  exact hx w (by rw [FinitePlace.below_eq_of_liesOver v w]; exact hw')
/-- The subgroup of idèles integral outside `S`, as a Galois subrepresentation. -/
abbrev sSubrep (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  Representation.subgroupSubrep (sSubgroup (L := L) S) (smul_mem_sSubgroup S)

/-! ### Coordinates grouped by base places

Separate the finite coordinates according to membership in `S`, retaining the integral-unit
subgroups outside `S`. Restriction of places has finite fibers, so the inverse coordinate map
satisfies the restricted-product condition. -/

/-- Coordinates of an idèle integral outside `S`, grouped by places of the base field. -/
abbrev SComponents (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  (∀ v : NumberField.InfinitePlace K, ∀ w : InfinitePlace.PlaceAbove (L := L) v,
    w.1.Completionˣ) ×
  ((∀ v : S, ∀ w : FinitePlace.PrimeAbove (L := L) v.1,
    ((FinitePlace.PrimeAbove.place v.1 w).adicCompletion L)ˣ) ×
  (∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
    ∀ w : FinitePlace.PrimeAbove (L := L) v.1,
    FinitePlace.unitGroup (FinitePlace.PrimeAbove.place v.1 w)))

/-- The full local coordinate selected by a place above `S`; used by `finitePart`. -/
private def insideComponent (S : Finset (HeightOneSpectrum (𝓞 K)))
    (c : SComponents (L := L) S) (w : HeightOneSpectrum (𝓞 L))
    (hw : FinitePlace.below (K := K) w ∈ S) : (w.adicCompletion L)ˣ := by
  exact c.2.1 ⟨FinitePlace.below (K := K) w, hw⟩
    (FinitePlace.PrimeAbove.mk (FinitePlace.below (K := K) w) w)

/-- The integral local coordinate selected outside `S`; used by `finitePart`. -/
private def outsideComponent (S : Finset (HeightOneSpectrum (𝓞 K)))
    (c : SComponents (L := L) S) (w : HeightOneSpectrum (𝓞 L))
    (hw : FinitePlace.below (K := K) w ∉ S) : FinitePlace.unitGroup w := by
  exact c.2.2 ⟨FinitePlace.below (K := K) w, hw⟩
    (FinitePlace.PrimeAbove.mk (FinitePlace.below (K := K) w) w)

/-- The finite idèle determined by full coordinates above `S` and integral unit coordinates
elsewhere; used by `sComponentsEquiv`. -/
private def finitePart (S : Finset (HeightOneSpectrum (𝓞 K)))
    (c : SComponents (L := L) S) : FiniteLocalIdele L := by
  classical
  let f : ∀ w : HeightOneSpectrum (𝓞 L), (w.adicCompletion L)ˣ := fun w ↦
    if h : FinitePlace.below (K := K) w ∈ S then insideComponent S c w h
    else (outsideComponent S c w h).1
  refine ⟨f, ?_⟩
  have hS : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, v ∉ S := by
    rw [Filter.eventually_cofinite]
    convert S.finite_toSet using 1
    ext v
    simp
  filter_upwards [(FinitePlace.tendsto_below_cofinite (K := K) (L := L)).eventually hS]
    with w hw
  change f w ∈ FinitePlace.unitGroup w
  have hf : f w = (outsideComponent S c w hw).1 := by
    exact dite_eq_right hw
  rw [hf]
  exact (outsideComponent S c w hw).property

/-- Outside `S`, `finitePart` evaluates to the chosen integral unit; used by
`fromCoordinates`, `from_to`, and `to_from`. -/
private theorem finitePart_outside (S : Finset (HeightOneSpectrum (𝓞 K)))
    (c : SComponents (L := L) S) (w : HeightOneSpectrum (𝓞 L))
    (hw : FinitePlace.below (K := K) w ∉ S) :
    finitePart S c w = (outsideComponent S c w hw).1 := by
  classical
  exact dite_eq_right hw

/-- Above `S`, `finitePart` evaluates to the chosen full local coordinate; used by `from_to` and
`to_from`. -/
private theorem finitePart_inside (S : Finset (HeightOneSpectrum (𝓞 K)))
    (c : SComponents (L := L) S) (w : HeightOneSpectrum (𝓞 L))
    (hw : FinitePlace.below (K := K) w ∈ S) :
    finitePart S c w = insideComponent S c w hw := by
  classical
  exact dite_eq_left hw

omit [NumberField K] in
/-- The chosen full coordinate agrees with its original `SComponents` entry; used by `to_from`. -/
private theorem insideComponent_place (S : Finset (HeightOneSpectrum (𝓞 K)))
    (c : SComponents (L := L) S) (v : S)
    (w : FinitePlace.PrimeAbove (L := L) v.1)
    (h : FinitePlace.below (K := K) (FinitePlace.PrimeAbove.place v.1 w) ∈ S) :
    insideComponent S c (FinitePlace.PrimeAbove.place v.1 w) h = c.2.1 v w := by
  unfold insideComponent
  rw! [FinitePlace.PrimeAbove.below_place]
  rfl

omit [NumberField K] in
/-- The chosen integral coordinate agrees with its original `SComponents` entry; used by
`to_from`. -/
private theorem outsideComponent_place (S : Finset (HeightOneSpectrum (𝓞 K)))
    (c : SComponents (L := L) S) (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S})
    (w : FinitePlace.PrimeAbove (L := L) v.1)
    (h : FinitePlace.below (K := K) (FinitePlace.PrimeAbove.place v.1 w) ∉ S) :
    outsideComponent S c (FinitePlace.PrimeAbove.place v.1 w) h = c.2.2 v w := by
  unfold outsideComponent
  rw! [FinitePlace.PrimeAbove.below_place]
  rfl

/-- The grouped coordinates of an idèle integral outside `S`, used by `sComponentsEquiv`. -/
private def toCoordinates (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : sSubgroup (L := L) S) : SComponents (L := L) S :=
  (fun _ w ↦ infiniteComponent L w.1 x.1,
    (fun v w ↦ finiteComponent L (FinitePlace.PrimeAbove.place v.1 w) x.1,
      fun v w ↦ ⟨finiteComponent L (FinitePlace.PrimeAbove.place v.1 w) x.1,
        (mem_sSubgroup S x.1).1 x.2 _ (by
          simpa only [FinitePlace.PrimeAbove.below_place] using v.2)⟩))

/-- Assemble an idèle from grouped coordinates; used by `sComponentsEquiv`. -/
private def fromCoordinates (S : Finset (HeightOneSpectrum (𝓞 K)))
    (c : SComponents (L := L) S) : sSubgroup (L := L) S := by
  let y : NumberField.IdeleGroup (𝓞 L) L :=
    (componentsEquiv L).symm
      (fun w ↦ c.1 (InfinitePlace.below (K := K) w) ⟨w,
        show w ∈ (InfinitePlace.below (K := K) w).placesOver L from
          (inferInstance : w.LiesOver (InfinitePlace.below (K := K) w))⟩,
        finitePart S c)
  refine ⟨y, (mem_sSubgroup S y).2 ?_⟩
  intro w hw
  change finitePart S c w ∈ FinitePlace.unitGroup w
  rw [finitePart_outside S c w hw]
  exact (outsideComponent S c w hw).property

/-- Infinite coordinates of the idèle assembled from `SComponents`; used by `from_to` and
`to_from`. -/
private theorem infiniteComponent_fromCoordinates (S : Finset (HeightOneSpectrum (𝓞 K)))
    (c : SComponents (L := L) S) (w : NumberField.InfinitePlace L) :
    infiniteComponent L w (fromCoordinates S c).1 =
      c.1 (InfinitePlace.below (K := K) w) ⟨w,
        show w ∈ (InfinitePlace.below (K := K) w).placesOver L from
          (inferInstance : w.LiesOver (InfinitePlace.below (K := K) w))⟩ := by
  simp only [fromCoordinates, infiniteComponent_apply, MulEquiv.apply_symm_apply]

/-- Finite coordinates of the idèle assembled from `SComponents`; used by `from_to` and
`to_from`. -/
private theorem finiteComponent_fromCoordinates (S : Finset (HeightOneSpectrum (𝓞 K)))
    (c : SComponents (L := L) S) (w : HeightOneSpectrum (𝓞 L)) :
    finiteComponent L w (fromCoordinates S c).1 = finitePart S c w := by
  simp only [fromCoordinates, finiteComponent_apply, MulEquiv.apply_symm_apply]

/-- Reassembling the grouped coordinates of an idèle recovers that idèle; used by
`sComponentsEquiv`. -/
private theorem from_to (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : sSubgroup (L := L) S) : fromCoordinates S (toCoordinates S x) = x := by
  apply Subtype.ext
  apply ext L
  · intro w
    rw [infiniteComponent_fromCoordinates]
    rfl
  · intro w
    rw [finiteComponent_fromCoordinates]
    by_cases hw : FinitePlace.below (K := K) w ∈ S
    · rw [finitePart_inside S _ w hw]
      rfl
    · rw [finitePart_outside S _ w hw]
      rfl

/-- Regrouping the coordinates of an assembled idèle recovers the original family; used by
`sComponentsEquiv`. -/
private theorem to_from (S : Finset (HeightOneSpectrum (𝓞 K)))
    (c : SComponents (L := L) S) : toCoordinates S (fromCoordinates S c) = c := by
  apply Prod.ext
  · funext v w
    change infiniteComponent L w.1 (fromCoordinates S c).1 = c.1 v w
    rw [infiniteComponent_fromCoordinates]
    let _ : w.1.LiesOver v := w.2
    rw! [InfinitePlace.below_eq_of_liesOver v w.1]
    rfl
  · apply Prod.ext
    · funext v w
      change finiteComponent L (FinitePlace.PrimeAbove.place v.1 w)
        (fromCoordinates S c).1 = c.2.1 v w
      rw [finiteComponent_fromCoordinates]
      have hw : FinitePlace.below (K := K) (FinitePlace.PrimeAbove.place v.1 w) ∈ S :=
        by simpa only [FinitePlace.PrimeAbove.below_place] using v.2
      rw [finitePart_inside S c _ hw, insideComponent_place S c v w hw]
    · funext v w
      apply Subtype.ext
      change finiteComponent L (FinitePlace.PrimeAbove.place v.1 w)
        (fromCoordinates S c).1 = (c.2.2 v w).1
      rw [finiteComponent_fromCoordinates]
      have hw : FinitePlace.below (K := K) (FinitePlace.PrimeAbove.place v.1 w) ∉ S :=
        by simpa only [FinitePlace.PrimeAbove.below_place] using v.2
      rw [finitePart_outside S c _ hw, outsideComponent_place S c v w hw]

omit [NumberField K] in
/-- Grouping finite and infinite coordinates respects multiplication; used by
`sComponentsEquiv`. -/
private theorem toCoordinates_mul (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x y : sSubgroup (L := L) S) :
    toCoordinates S (x * y) = toCoordinates S x * toCoordinates S y := by
  ext v w <;> simp [toCoordinates, map_mul]

/-- The coordinate decomposition of $I_{L,S}$ into full local groups at `S` and integral units
elsewhere. Milne, *Class Field Theory*, Chapter VII, Proposition 2.5, proof. -/
def sComponentsEquiv (S : Finset (HeightOneSpectrum (𝓞 K))) :
    sSubgroup (L := L) S ≃* SComponents (L := L) S := by
  exact {
    toFun := toCoordinates S
    invFun := fromCoordinates S
    left_inv := from_to S
    right_inv := to_from S
    map_mul' := toCoordinates_mul S }

/-- The infinite entry of `sComponentsEquiv` is the infinite component of the idèle. -/
@[simp]
theorem sComponentsEquiv_infinite (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : sSubgroup (L := L) S) (v : NumberField.InfinitePlace K)
    (w : InfinitePlace.PlaceAbove (L := L) v) :
    (sComponentsEquiv S x).1 v w = infiniteComponent L w.1 x.1 := rfl

/-- An entry above `S` of `sComponentsEquiv` is the full finite component. -/
@[simp]
theorem sComponentsEquiv_inside (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : sSubgroup (L := L) S) (v : S)
    (w : FinitePlace.PrimeAbove (L := L) v.1) :
    (sComponentsEquiv S x).2.1 v w =
      finiteComponent L (FinitePlace.PrimeAbove.place v.1 w) x.1 := rfl

/-- An entry outside `S` of `sComponentsEquiv` is the integral finite component. -/
@[simp]
theorem sComponentsEquiv_outside (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : sSubgroup (L := L) S)
    (v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S})
    (w : FinitePlace.PrimeAbove (L := L) v.1) :
    ((sComponentsEquiv S x).2.2 v w).1 =
      finiteComponent L (FinitePlace.PrimeAbove.place v.1 w) x.1 := rfl
end SIC.IdeleGroup
