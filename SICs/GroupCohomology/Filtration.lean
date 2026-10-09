/-
Copyright (c) 2026 Maris Ozols. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maris Ozols
-/
import SICs.GroupCohomology.Multiplicative
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Complete filtrations and the vanishing of Tate groups

Serre's approximation lemma: a multiplicative module with a complete separated decreasing
filtration by stable subgroups has trivial Tate groups in degree $0$ (resp. $-1$) as soon as each
step of the filtration does, modulo the next.

This is Serre, *Local class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
*Algebraic Number Theory* (1967), Chapter VI, §1.2, Lemma 3, applied here to the explicit
Tate groups in degrees $0$ and $-1$. The vanishing on the successive quotients
$F_i / F_{i+1}$ is stated as the approximation property it gives inside $F_i$. It is applied to the
units of local fields in `SICs.ClassField.Local.UnitCohomology`.

## The argument

Let $F_0 \supseteq F_1 \supseteq \cdots$ be `G`-stable subgroups with $\bigcap_i F_i = 1$ in which
every product $\prod_i x_i$ with $x_i \in F_i$ converges: there is `y` with
$y / \prod_{i < n} x_i \in F_n$ for all `n`. Since the $F_n$ are subgroups meeting in `1`, such a
limit is unique, and the action of each `g` and the norm $N_G = \prod_g g$ commute with these
limits, because they map each $F_n$ into itself.

*Degree $0$.* Let $x \in F_0$ be fixed by `G`. If $x_i \in F_i$ is fixed, the hypothesis gives
$y_i \in F_i$ with $x_{i+1} = x_i / N_G(y_i) \in F_{i+1}$, again fixed. With $x_0 = x$ this
defines $y_i \in F_i$ for all `i` with $x / N_G(y_0 \cdots y_{n-1}) \in F_n$; for the limit
$y = \prod_i y_i \in F_0$, $x / N_G(y) \in F_n$ for every `n`, so $x = N_G(y)$.

*Degree $-1$.* Let $x \in F_0$ have norm one. If $x_i \in F_i$ has norm one, the hypothesis gives
$y_{i,g} \in F_i$ with $x_{i+1} = x_i / \prod_g g y_{i,g} / y_{i,g} \in F_{i+1}$, again of norm one,
since each $g y / y$ has norm one. For the limits $y_g = \prod_i y_{i,g} \in F_0$,
$x / \prod_g g y_g / y_g \in F_n$ for every `n`, so $x = \prod_g g y_g / y_g$.
-/

noncomputable section

namespace SIC

namespace Representation

variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]

/-! ### Complete filtrations -/

/-- A decreasing filtration $F_0 \supseteq F_1 \supseteq \cdots$ of a commutative group by
subgroups is separated and complete: $\bigcap_i F_i = 1$, and every product $\prod_i x_i$ with
$x_i \in F_i$ converges, to an element `y` with $y / \prod_{i < n} x_i \in F_n$ for every `n`.
Serre, *Local class field theory*, in Cassels–Fröhlich (1967), Chapter VI, §1.2, Lemma 3. -/
structure IsCompleteFiltration (F : ℕ → Subgroup M) : Prop where
  /-- The filtration is decreasing. -/
  antitone : Antitone F
  /-- The filtration is separated: $\bigcap_i F_i = 1$. -/
  iInf_eq_bot : ⨅ i, F i = ⊥
  /-- Every product of elements $x_i \in F_i$ converges. -/
  exists_prod : ∀ x : ℕ → M, (∀ i, x i ∈ F i) →
    ∃ y, ∀ n, y / ∏ i ∈ Finset.range n, x i ∈ F n

/-- A decreasing filtration of a Hausdorff topological group by closed subgroups with compact
first term and trivial intersection is complete: the partial products of $\prod_i x_i$ lie in
the nested compact sets $\{y : y / \prod_{i < n} x_i \in F_n\}$, whose intersection is
nonempty. -/
theorem IsCompleteFiltration.of_isCompact [TopologicalSpace M] [ContinuousMul M]
    {F : ℕ → Subgroup M} (hanti : Antitone F)
    (hclosed : ∀ n, IsClosed (F n : Set M)) (hcompact : IsCompact (F 0 : Set M))
    (hsep : ⨅ n, F n = ⊥) : IsCompleteFiltration F := by
  refine ⟨hanti, hsep, ?_⟩
  intro x hx
  let p : ℕ → M := fun n => ∏ i ∈ Finset.range n, x i
  have hp : ∀ n, p n ∈ F 0 := by
    intro n
    apply Subgroup.prod_mem
    intro i hi
    exact hanti (Nat.zero_le i) (hx i)
  let s : ℕ → Set M := fun n => {y | y / p n ∈ F n}
  have hsclosed : ∀ n, IsClosed (s n) := by
    intro n
    have hset : s n = (fun y : M => y * (p n)⁻¹) ⁻¹' (F n : Set M) := by
      ext y
      simp [s, div_eq_mul_inv]
    rw [hset]
    exact (hclosed n).preimage (continuous_mul_const (p n)⁻¹)
  have hsnonempty : ∀ n, (s n).Nonempty := by
    intro n
    exact ⟨p n, by simp [s]⟩
  have hsnested : ∀ n, s (n + 1) ⊆ s n := by
    intro n y hy
    change y / p n ∈ F n
    have hpnext : p (n + 1) = p n * x n := by simp [p, Finset.prod_range_succ]
    have hy' : y / p (n + 1) ∈ F (n + 1) := hy
    have hyle : y / p (n + 1) ∈ F n := hanti (Nat.le_succ n) hy'
    have hxn : x n ∈ F n := hx n
    convert (F n).mul_mem hyle hxn using 1
    rw [hpnext]
    simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm]
  have hs0 : s 0 = (F 0 : Set M) := by
    ext y
    simp [s, p]
  have hscompact : IsCompact (s 0) := hs0 ▸ hcompact
  obtain ⟨y, hy⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed s
      hsnested hsnonempty hscompact hsclosed
  exact ⟨y, fun n => Set.mem_iInter.mp hy n⟩

/-! ### Serre's lemma in degrees zero and minus one -/

variable [Fintype G]

/-- Two elements with the same residue modulo every group of a separated filtration coincide.
Used in both degrees of Serre's lemma below. -/
private theorem eq_of_div_mem_all {F : ℕ → Subgroup M} (hF : IsCompleteFiltration F)
    {a b : M} (h : ∀ n, a / b ∈ F n) : a = b := by
  have hab : a / b ∈ ⨅ n, F n := Subgroup.mem_iInf.mpr h
  rw [hF.iInf_eq_bot] at hab
  exact div_eq_one.mp (Subgroup.mem_bot.mp hab)

/-- The norm preserves every stable term of the filtration. Used in degree $0$. -/
private theorem mulNorm_mem_filtration {F : ℕ → Subgroup M}
    (hstable : ∀ i (g : G), ∀ x ∈ F i, g • x ∈ F i)
    (i : ℕ) {x : M} (hx : x ∈ F i) : mulNorm G M x ∈ F i := by
  rw [mulNorm_apply]
  exact (F i).prod_mem (fun g _ => hstable i g x hx)

/-- Taking a product of successive corrections commutes with forming the degree $-1$
coboundary product. Used in Serre's degree $-1$ approximation. -/
private theorem prod_smul_div_prod_range (y : ℕ → G → M) (n : ℕ) :
    (∏ g, g • (∏ i ∈ Finset.range n, y i g) / (∏ i ∈ Finset.range n, y i g)) =
      ∏ i ∈ Finset.range n, ∏ g, g • y i g / y i g := by
  simp_rw [Finset.smul_prod', ← Finset.prod_div_distrib]
  exact Finset.prod_comm

/-- The degree $-1$ coboundary product preserves a limit modulo every stable filtration term.
Used in Serre's degree $-1$ approximation. -/
private theorem prod_smul_div_limit_mem {F : ℕ → Subgroup M}
    (hstable : ∀ i (g : G), ∀ x ∈ F i, g • x ∈ F i)
    (y : ℕ → G → M) (Y : G → M)
    (hY : ∀ g n, Y g / ∏ i ∈ Finset.range n, y i g ∈ F n) (n : ℕ) :
    (∏ g, g • Y g / Y g) /
      (∏ g, g • (∏ i ∈ Finset.range n, y i g) /
        (∏ i ∈ Finset.range n, y i g)) ∈ F n := by
  rw [← Finset.prod_div_distrib]
  apply (F n).prod_mem
  intro g _
  have hp := hY g n
  have hgp := hstable n g _ hp
  have hterm : (g • Y g / Y g) /
      (g • (∏ i ∈ Finset.range n, y i g) /
        (∏ i ∈ Finset.range n, y i g)) =
      (g • (Y g / ∏ i ∈ Finset.range n, y i g)) /
        (Y g / ∏ i ∈ Finset.range n, y i g) := by
    rw [smul_div']
    simp [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
  rw [hterm]
  exact (F n).div_mem hgp hp

/-- **Serre's lemma in degree $0$.** If every `G`-fixed element of each $F_i$ is a norm from $F_i$
modulo $F_{i+1}$, then every `G`-fixed element of $F_0$ is a norm from $F_0$. Serre,
*Local class field theory*, in Cassels–Fröhlich (1967), Chapter VI, §1.2, Lemma 3. -/
theorem exists_mulNorm_eq_of_isCompleteFiltration {F : ℕ → Subgroup M}
    (hF : IsCompleteFiltration F) (hstable : ∀ i (g : G), ∀ x ∈ F i, g • x ∈ F i)
    (hstep : ∀ i, ∀ x ∈ F i, (∀ g : G, g • x = x) →
      ∃ y ∈ F i, x / mulNorm G M y ∈ F (i + 1))
    {x : M} (hx : x ∈ F 0) (hfix : ∀ g : G, g • x = x) :
    ∃ y ∈ F 0, mulNorm G M y = x := by
  let S (i : ℕ) := {z : M // z ∈ F i ∧ ∀ g : G, g • z = z}
  let step (i : ℕ) (z : S i) :
      {y : M // y ∈ F i ∧ z.1 / mulNorm G M y ∈ F (i + 1)} :=
    ⟨Classical.choose (hstep i z.1 z.2.1 z.2.2),
      Classical.choose_spec (hstep i z.1 z.2.1 z.2.2)⟩
  let next (i : ℕ) (z : S i) : S (i + 1) :=
    ⟨z.1 / mulNorm G M (step i z).1, (step i z).2.2, by
      intro g
      rw [smul_div', z.2.2 g, smul_mulNorm]⟩
  let z : (i : ℕ) → S i := Nat.rec ⟨x, hx, hfix⟩ (fun i zi => next i zi)
  let y (i : ℕ) : M := (step i (z i)).1
  have hy (i : ℕ) : y i ∈ F i := (step i (z i)).2.1
  have hzsucc (i : ℕ) : (z (i + 1)).1 = (z i).1 / mulNorm G M (y i) := rfl
  have hprefix (n : ℕ) :
      (z n).1 = x / mulNorm G M (∏ i ∈ Finset.range n, y i) := by
    induction n with
    | zero => simp [z]
    | succ n ih =>
      rw [hzsucc, ih, Finset.prod_range_succ, map_mul]
      simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc]
      ac_rfl
  obtain ⟨Y, hY⟩ := hF.exists_prod y hy
  have hY0 : Y ∈ F 0 := by simpa using hY 0
  refine ⟨Y, hY0, ?_⟩
  apply (eq_of_div_mem_all hF ?_).symm
  intro n
  have hres : x / mulNorm G M (∏ i ∈ Finset.range n, y i) ∈ F n := by
    rw [← hprefix n]
    exact (z n).2.1
  have htail : mulNorm G M (Y / ∏ i ∈ Finset.range n, y i) ∈ F n :=
    mulNorm_mem_filtration hstable n (hY n)
  have heq : x / mulNorm G M Y =
      (x / mulNorm G M (∏ i ∈ Finset.range n, y i)) /
        mulNorm G M (Y / ∏ i ∈ Finset.range n, y i) := by
    rw [map_div]
    exact (div_div_div_cancel_right x (mulNorm G M Y)
      (mulNorm G M (∏ i ∈ Finset.range n, y i))).symm
  rw [heq]
  exact (F n).div_mem hres htail

/-- Successive degree $-1$ corrections leave a residue in $F_n$ after $n$ steps.
Used in `exists_prod_smul_div_eq_of_isCompleteFiltration`. -/
private theorem exists_prod_smul_div_corrections {F : ℕ → Subgroup M}
    (hstep : ∀ i, ∀ x ∈ F i, mulNorm G M x = 1 →
      ∃ y : G → M, (∀ g, y g ∈ F i) ∧ x / ∏ g, g • y g / y g ∈ F (i + 1))
    {x : M} (hx : x ∈ F 0) (hnorm : mulNorm G M x = 1) :
    ∃ y : ℕ → G → M, (∀ i g, y i g ∈ F i) ∧
      ∀ n, x / ∏ i ∈ Finset.range n, ∏ g, g • y i g / y i g ∈ F n := by
  let S (i : ℕ) := {z : M // z ∈ F i ∧ mulNorm G M z = 1}
  let step (i : ℕ) (z : S i) :
      {y : G → M // (∀ g, y g ∈ F i) ∧
        z.1 / ∏ g, g • y g / y g ∈ F (i + 1)} :=
    ⟨Classical.choose (hstep i z.1 z.2.1 z.2.2),
      Classical.choose_spec (hstep i z.1 z.2.1 z.2.2)⟩
  let next (i : ℕ) (z : S i) : S (i + 1) :=
    ⟨z.1 / ∏ g, g • (step i z).1 g / (step i z).1 g, (step i z).2.2, by
      rw [map_div, z.2.2, mulNorm_prod_smul_div]
      simp⟩
  let z : (i : ℕ) → S i := Nat.rec ⟨x, hx, hnorm⟩ (fun i zi => next i zi)
  let y (i : ℕ) : G → M := (step i (z i)).1
  let b (i : ℕ) : M := ∏ g, g • y i g / y i g
  have hy (i : ℕ) (g : G) : y i g ∈ F i := (step i (z i)).2.1 g
  have hzsucc (i : ℕ) : (z (i + 1)).1 = (z i).1 / b i := rfl
  have hprefix (n : ℕ) : (z n).1 = x / ∏ i ∈ Finset.range n, b i := by
    induction n with
    | zero => simp [z]
    | succ n ih =>
      rw [hzsucc, ih, Finset.prod_range_succ]
      simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc]
      ac_rfl
  refine ⟨y, hy, ?_⟩
  intro n
  change x / ∏ i ∈ Finset.range n, b i ∈ F n
  rw [← hprefix n]
  exact (z n).2.1

/-- **Serre's lemma in degree $-1$.** If every element of each $F_i$ of norm one is a product
$\prod_g g y_g / y_g$ with $y_g \in F_i$ modulo $F_{i+1}$, then every element of $F_0$ of norm
one is such a product with $y_g \in F_0$. Serre, *Local class field theory*, in Cassels–Fröhlich
(1967), Chapter VI, §1.2, Lemma 3. -/
theorem exists_prod_smul_div_eq_of_isCompleteFiltration {F : ℕ → Subgroup M}
    (hF : IsCompleteFiltration F) (hstable : ∀ i (g : G), ∀ x ∈ F i, g • x ∈ F i)
    (hstep : ∀ i, ∀ x ∈ F i, mulNorm G M x = 1 →
      ∃ y : G → M, (∀ g, y g ∈ F i) ∧ x / ∏ g, g • y g / y g ∈ F (i + 1))
    {x : M} (hx : x ∈ F 0) (hnorm : mulNorm G M x = 1) :
    ∃ y : G → M, (∀ g, y g ∈ F 0) ∧ x = ∏ g, g • y g / y g := by
  obtain ⟨y, hy, hcorrect⟩ := exists_prod_smul_div_corrections hstep hx hnorm
  have hlimit (g : G) :
      ∃ Y : M, ∀ n, Y / ∏ i ∈ Finset.range n, y i g ∈ F n :=
    hF.exists_prod (fun i => y i g) (fun i => hy i g)
  choose Y hY using hlimit
  have hY0 (g : G) : Y g ∈ F 0 := by simpa using hY g 0
  let B : M := ∏ g, g • Y g / Y g
  let P (n : ℕ) : M :=
    ∏ g, g • (∏ i ∈ Finset.range n, y i g) / (∏ i ∈ Finset.range n, y i g)
  refine ⟨Y, hY0, ?_⟩
  apply eq_of_div_mem_all hF
  intro n
  change x / B ∈ F n
  have hres : x / P n ∈ F n := by
    dsimp [P]
    rw [prod_smul_div_prod_range]
    exact hcorrect n
  have htail : B / P n ∈ F n := prod_smul_div_limit_mem hstable y Y hY n
  have heq : x / B = (x / P n) / (B / P n) :=
    (div_div_div_cancel_right x B (P n)).symm
  rw [heq]
  exact (F n).div_mem hres htail

/-- Serre's lemma in degree $0$ for the Tate group: $\widehat H^0(G, F_0) = 0$. Serre,
*Local class field theory*, in Cassels–Fröhlich (1967), Chapter VI, §1.2, Lemma 3. -/
theorem subsingleton_tateZero_of_isCompleteFiltration {F : ℕ → Subgroup M}
    (hF : IsCompleteFiltration F) (hstable : ∀ i (g : G), ∀ x ∈ F i, g • x ∈ F i)
    (hstep : ∀ i, ∀ x ∈ F i, (∀ g : G, g • x = x) →
      ∃ y ∈ F i, x / mulNorm G M y ∈ F (i + 1)) :
    Subsingleton (TateZero (subgroupSubrep (F 0) (hstable 0)).toRepresentation) := by
  exact (subsingleton_tateZero_subgroupSubrep_iff (F 0) (hstable 0)).2
    (fun x hx hfix => exists_mulNorm_eq_of_isCompleteFiltration hF hstable hstep hx hfix)

/-- Serre's lemma in degree $-1$ for the Tate group: $\widehat H^{-1}(G, F_0) = 0$. Serre,
*Local class field theory*, in Cassels–Fröhlich (1967), Chapter VI, §1.2, Lemma 3. -/
theorem subsingleton_tateNegOne_of_isCompleteFiltration {F : ℕ → Subgroup M}
    (hF : IsCompleteFiltration F) (hstable : ∀ i (g : G), ∀ x ∈ F i, g • x ∈ F i)
    (hstep : ∀ i, ∀ x ∈ F i, mulNorm G M x = 1 →
      ∃ y : G → M, (∀ g, y g ∈ F i) ∧ x / ∏ g, g • y g / y g ∈ F (i + 1)) :
    Subsingleton (TateNegOne (subgroupSubrep (F 0) (hstable 0)).toRepresentation) := by
  exact (subsingleton_tateNegOne_subgroupSubrep_iff (F 0) (hstable 0)).2
    (fun x hx hnorm => exists_prod_smul_div_eq_of_isCompleteFiltration hF hstable hstep hx hnorm)

end Representation

end SIC
