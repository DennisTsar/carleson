import Carleson.TwoSidedCarleson.Basic
import Carleson.ToMathlib.HardyLittlewood

open MeasureTheory Set Bornology Function ENNReal Metric Filter Topology
open scoped NNReal

noncomputable section

variable {X : Type*} {a : ℕ} [MetricSpace X] [DoublingMeasure X (defaultA a : ℕ)]
variable {τ C r R : ℝ} {q q' : ℝ≥0}
variable {F G : Set X}
variable {K : X → X → ℂ} {x x' : X} [IsTwoSidedKernel a K]
variable {f : X → ℂ} {α : ℝ≥0∞}

/-! ## Section 10.2 and Lemma 10.0.3

Question: -/

/-- The constant used in `nontangential_from_simple`.
I(F) think the constant needs to be fixed in the blueprint. -/
irreducible_def C10_2_1 (a : ℕ) : ℝ≥0 := 2 ^ (4 * a)

/-- Lemma 10.2.1, formulated differently.
The blueprint version is basically this after unfolding `HasBoundedWeakType`, `wnorm` and `wnorm'`.
-/
theorem maximal_theorem [Nonempty X] :
    HasBoundedWeakType (globalMaximalFunction volume 1 : (X → ℂ) → X → ℝ≥0∞) 1 1 volume volume
      (C10_2_1 a) := by
  apply HasWeakType.hasBoundedWeakType
  have : C10_2_1 a = C_weakType_globalMaximalFunction (defaultA a) 1 1 := by
    unfold C_weakType_globalMaximalFunction C_weakType_maximalFunction
    split_ifs with h; swap; simp at h
    simp_rw [C10_2_1_def, defaultA, coe_pow, coe_ofNat, Nat.cast_pow, Nat.cast_ofNat,
        NNReal.coe_one, div_one, rpow_ofNat, pow_mul', ← npow_add,
        two_add_two_eq_four]; rfl
  rw [this]
  apply hasWeakType_globalMaximalFunction (μ := volume) le_rfl le_rfl

variable [CompatibleFunctions ℝ X (defaultA a)] [IsCancellative X (defaultτ a)]

/-- Lemma 10.2.2.
Should be an easy consequence of `VitaliFamily.ae_tendsto_average`. -/
theorem lebesgue_differentiation
    {f : X → ℂ} (hf : BoundedFiniteSupport f) :
    ∀ᵐ x ∂volume, ∃ (c : ℕ → X) (r : ℕ → ℝ),
    Tendsto (fun i ↦ ⨍ y in ball (c i) (r i), f y ∂volume) atTop (𝓝 (f x)) ∧
    Tendsto r atTop (𝓝[>] 0) ∧
    ∀ i, x ∈ ball (c i) (r i) := by
  sorry


/-! Lemma 10.2.3 is in Mathlib: `Pairwise.countable_of_isOpen_disjoint`. -/

/-- Lemma 10.2.4
This is very similar to `Vitali.exists_disjoint_subfamily_covering_enlargement`.
Can we use that (or adapt it so that we can use it)? -/
theorem ball_covering (ha : 4 ≤ a) {O : Set X} (hO : IsOpen O ∧ O ≠ univ) :
    ∃ (c : ℕ → X) (r : ℕ → ℝ), (univ.PairwiseDisjoint fun i ↦ closedBall (c i) (r i)) ∧
      ⋃ i, ball (c i) (3 * r i) = O ∧ (∀ i, ¬ Disjoint (ball (c i) (7 * r i)) Oᶜ) ∧
      ∀ x ∈ O, Cardinal.mk { i | x ∈ ball (c i) (3 * r i)} ≤ (2 ^ (6 * a) : ℕ) := by
  sorry

/-! ### Lemma 10.2.5

Lemma 10.2.5 has an annoying case distinction between the case `E_α ≠ X` (general case) and
`E_α = X` (finite case). It isn't easy to get rid of this case distinction.

In the formalization we state most properties of Lemma 10.2.5 twice, once for each case
(in some cases the condition is vacuous in the finite case, and then we omit it)

We could have tried harder to uniformize the cases, but in the finite case there is really only set
`B*_j`, and in the general case it is convenient to index `B*_j` by the natural numbers.
-/

/-- The property specifying whether we are in the "general case". -/
def GeneralCase (f : X → ℂ) (α : ℝ≥0∞) : Prop :=
  ∃ x, α < globalMaximalFunction (X := X) volume 1 f x

/-- In the finite case, the volume of `X` is finite. -/
lemma volume_lt_of_not_GeneralCase (h : ¬ GeneralCase f α) : volume (univ : Set X) < ∞ :=
  sorry -- Use Lemma 10.2.1

/- Use `lowerSemiContinuous_globalMaximalFunction` for part 1. -/
lemma isOpen_MB_preimage_Ioi (hf : BoundedFiniteSupport f) (hX : GeneralCase f α) :
    IsOpen (globalMaximalFunction (X := X) volume 1 f ⁻¹' Ioi α) ∧
    globalMaximalFunction (X := X) volume 1 f ⁻¹' Ioi α ≠ univ := by
  sorry

/-- The center of B_j in the proof of Lemma 10.2.5 (general case). -/
def czCenter (ha : 4 ≤ a) (hf : BoundedFiniteSupport f) (hX : GeneralCase f α) (i : ℕ) : X :=
  ball_covering ha (isOpen_MB_preimage_Ioi hf hX) |>.choose i

/-- The radius of B_j in the proof of Lemma 10.2.5 (general case). -/
def czRadius (ha : 4 ≤ a) (hf : BoundedFiniteSupport f) (hX : GeneralCase f α) (i : ℕ) : ℝ :=
  ball_covering ha (isOpen_MB_preimage_Ioi hf hX) |>.choose_spec.choose i

/-- The ball B_j in the proof of Lemma 10.2.5 (general case). -/
abbrev czBall (ha : 4 ≤ a) (hf : BoundedFiniteSupport f) (hX : GeneralCase f α) (i : ℕ) : Set X :=
  ball (czCenter ha hf hX i) (czRadius ha hf hX i)

/-- The ball B_j' introduced below Lemma 10.2.5 (general case). -/
abbrev czBall2 (ha : 4 ≤ a) (hf : BoundedFiniteSupport f) (hX : GeneralCase f α) (i : ℕ) : Set X :=
  ball (czCenter ha hf hX i) (2 * czRadius ha hf hX i)

/-- The ball B_j* in Lemma 10.2.5 (general case). -/
abbrev czBall3 (ha : 4 ≤ a) (hf : BoundedFiniteSupport f) (hX : GeneralCase f α) (i : ℕ) : Set X :=
  ball (czCenter ha hf hX i) (3 * czRadius ha hf hX i)

/-- The ball B_j** in the proof of Lemma 10.2.5 (general case). -/
abbrev czBall7 (ha : 4 ≤ a) (hf : BoundedFiniteSupport f) (hX : GeneralCase f α) (i : ℕ) : Set X :=
  ball (czCenter ha hf hX i) (7 * czRadius ha hf hX i)

lemma czBall_pairwiseDisjoint (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} :
    univ.PairwiseDisjoint fun i ↦ closedBall (czCenter ha hf hX i) (czRadius ha hf hX i) :=
  ball_covering ha (isOpen_MB_preimage_Ioi hf hX) |>.choose_spec.choose_spec.1

lemma iUnion_czBall3 (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} :
    ⋃ i, czBall3 ha hf hX i = globalMaximalFunction volume 1 f ⁻¹' Ioi α :=
  ball_covering ha (isOpen_MB_preimage_Ioi hf hX) |>.choose_spec.choose_spec.2.1

lemma not_disjoint_czBall7 (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} {i : ℕ} :
    ¬ Disjoint (czBall7 ha hf hX i) (globalMaximalFunction volume 1 f ⁻¹' Ioi α)ᶜ :=
  ball_covering ha (isOpen_MB_preimage_Ioi hf hX) |>.choose_spec.choose_spec.2.2.1 i

/-- Part of Lemma 10.2.5 (general case). -/
lemma cardinalMk_czBall3_le (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} {hX : GeneralCase f α}
    {y : X} (hy : α < globalMaximalFunction volume 1 f y) :
    Cardinal.mk { i | y ∈ czBall3 ha hf hX i} ≤ (2 ^ (6 * a) : ℕ) :=
  ball_covering ha (isOpen_MB_preimage_Ioi hf hX) |>.choose_spec.choose_spec.2.2.2 y hy

lemma mem_czBall3_finite (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} {y : X}
    (hy : α < globalMaximalFunction volume 1 f y) :
    { i | y ∈ czBall3 ha hf hX i}.Finite := by
  rw [← Cardinal.lt_aleph0_iff_set_finite]
  exact lt_of_le_of_lt (cardinalMk_czBall3_le ha hy) (Cardinal.nat_lt_aleph0 _)

/-- `Q_i` in the proof of Lemma 10.2.5 (general case). -/
def czPartition (ha : 4 ≤ a) (hf : BoundedFiniteSupport f) (hX : GeneralCase f α) (i : ℕ) : Set X :=
  czBall3 ha hf hX i \ ((⋃ j < i, czPartition ha hf hX j) ∪ ⋃ j > i, czBall ha hf hX j)

lemma czBall_subset_czPartition (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} {i : ℕ} :
    czBall ha hf hX i ⊆ czPartition ha hf hX i := by
  intro r hr
  rw [czPartition]
  refine mem_diff_of_mem ?_ ?_
  · have : dist r (czCenter ha hf hX i) ≥ 0 := dist_nonneg
    simp_all only [mem_ball]
    linarith
  · rw [mem_ball] at hr
    simp only [mem_union, mem_iUnion, mem_ball, not_or, not_exists, not_lt]
    constructor
    · unfold czPartition
      simp only [mem_diff, mem_ball, mem_union, mem_iUnion, not_or, not_and, not_forall, not_not]
      exact fun _ _ _ _ ↦ by use i
    · intro x hx
      have := pairwiseDisjoint_iff.mp <| czBall_pairwiseDisjoint ha (hf := hf) (hX := hX)
      simp only [mem_univ, forall_const] at this
      have := (disjoint_or_nonempty_inter _ _).resolve_right <| (@this i x).mt (by omega)
      exact le_of_not_ge <| mem_closedBall.mpr.mt <| disjoint_left.mp this hr.le

lemma czPartition_subset_czBall3 (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} {i : ℕ} :
    czPartition ha hf hX i ⊆ czBall3 ha hf hX i := by
  rw [czPartition]; exact diff_subset

lemma czPartition_pairwiseDisjoint (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} :
    univ.PairwiseDisjoint fun i ↦ czPartition ha hf hX i := by
  simp only [pairwiseDisjoint_iff, mem_univ, forall_const]
  intro i k hik
  have ⟨x, hxi, hxk⟩ := inter_nonempty.mp hik
  have (t d) (hx : x ∈ czPartition ha hf hX t) (hd : t < d) : x ∉ czPartition ha hf hX d := by
    have : czPartition ha hf hX t ⊆ ⋃ j < d, czPartition ha hf hX j := subset_biUnion_of_mem hd
    rw [czPartition]
    exact notMem_diff_of_mem <| mem_union_left _ (this hx)
  have : _ ∧ _ := ⟨this i k hxi |>.mt (· hxk), this k i hxk |>.mt (· hxi)⟩
  omega

lemma czPartition_pairwiseDisjoint' (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} {hX : GeneralCase f α}
    {x : X} {i j : ℕ} (hi : x ∈ czPartition ha hf hX i) (hj : x ∈ czPartition ha hf hX j) :
    i = j := by
  have := czPartition_pairwiseDisjoint ha (hf := hf) (hX := hX)
  apply pairwiseDisjoint_iff.mp this (mem_univ i) (mem_univ j)
  exact inter_nonempty.mp <| .intro x ⟨hi, hj⟩

lemma iUnion_czPartition (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} :
    ⋃ i, czPartition ha hf hX i = globalMaximalFunction volume 1 f ⁻¹' Ioi α := by
  rw [← iUnion_czBall3 ha (hf := hf) (hX := hX)]
  refine ext fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · have : ⋃ i, czPartition ha hf hX i ⊆ ⋃ i, czBall3 ha hf hX i := fun y hy ↦
      have ⟨r, hr⟩ := mem_iUnion.mp hy
      mem_iUnion_of_mem r (czPartition_subset_czBall3 ha hr)
    exact this hx
  · rw [mem_iUnion] at hx ⊢
    by_contra! hp
    obtain ⟨g, hg⟩ := hx
    have ⟨t, ht⟩ : ∃ i, x ∈ (⋃ j < i, czPartition ha hf hX j) ∪ ⋃ j > i, czBall ha hf hX j := by
      by_contra! hb
      absurd hp g
      rw [czPartition, mem_diff]
      exact ⟨hg, hb g⟩
    have : ⋃ j > t, czBall ha hf hX j ⊆ ⋃ j > t, czPartition ha hf hX j :=
      iUnion₂_mono fun i j ↦ czBall_subset_czPartition ha (i := i)
    have := (mem_or_mem_of_mem_union ht).imp_right (this ·)
    simp_all

open scoped Classical in
/-- The function `g` in Lemma 10.2.5. (both cases) -/
def czApproximation (ha : 4 ≤ a) (hf : BoundedFiniteSupport f) (α : ℝ≥0∞) (x : X) : ℂ :=
  if hX : GeneralCase f α then
    if hx : ∃ j, x ∈ czPartition ha hf hX j then ⨍ y in czPartition ha hf hX hx.choose, f y else f x
  else ⨍ y, f y

lemma czApproximation_def_of_mem (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} {x : X}
    {i : ℕ} (hx : x ∈ czPartition ha hf hX i) :
    czApproximation ha hf α x = ⨍ y in czPartition ha hf hX i, f y := by
  have : ∃ i, x ∈ czPartition ha hf hX i := ⟨i, hx⟩
  simp [czApproximation, hX, this, czPartition_pairwiseDisjoint' ha this.choose_spec hx]

lemma czApproximation_def_of_notMem (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} {x : X} (hX : GeneralCase f α)
    (hx : x ∉ globalMaximalFunction volume 1 f ⁻¹' Ioi α) :
    czApproximation ha hf α x = f x := by
  rw [← iUnion_czPartition ha (hf := hf) (hX := hX), mem_iUnion, not_exists] at hx
  simp only [czApproximation, hX, ↓reduceDIte, hx, exists_const]

lemma czApproximation_def_of_volume_lt (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} {x : X}
    (hX : ¬ GeneralCase f α) : czApproximation ha hf α x = ⨍ y, f y := by
  simp [czApproximation, hX]

/-- The function `b_i` in Lemma 10.2.5 (general case). -/
def czRemainder' (ha : 4 ≤ a)(hf : BoundedFiniteSupport f) (hX : GeneralCase f α) (i : ℕ) (x : X) : ℂ :=
  (czPartition ha hf hX i).indicator (f - czApproximation ha hf α) x

/-- The function `b = ∑ⱼ bⱼ` introduced below Lemma 10.2.5.
In the finite case, we also use this as the function `b = b₁` in Lemma 10.2.5.
We choose a more convenient definition, but prove in `tsum_czRemainder'` that this is the same. -/
def czRemainder (ha : 4 ≤ a) (hf : BoundedFiniteSupport f) (α : ℝ≥0∞) (x : X) : ℂ :=
  f x - czApproximation ha hf α x

/-- Part of Lemma 10.2.5, this is essentially (10.2.16) (both cases). -/
def tsum_czRemainder' (ha : 4 ≤ a) (hf : BoundedFiniteSupport f) (hX : GeneralCase f α) (x : X) :
    ∑ᶠ i, czRemainder' ha hf hX i x = czRemainder ha hf α x := by
  by_cases h : ∃ j, x ∈ czPartition ha hf hX j
  · letI (i) : Decidable (x ∈ czPartition ha hf hX i) := Classical.propDecidable _
    obtain ⟨j, hj⟩ := h
    simp only [czRemainder', indicator_apply, Pi.sub_apply, czRemainder]
    have : f x - czApproximation ha hf α x = if x ∈ czPartition ha hf hX j then _ else 0 :=
      (if_pos hj).symm
    conv_rhs => rw [this]
    refine finsum_eq_single _ j fun g hg ↦ ?_
    apply if_neg <| Disjoint.notMem_of_mem_left ?_ hj
    exact czPartition_pairwiseDisjoint ha (mem_univ _) (mem_univ _) hg.symm
  · simp_all [czRemainder', czRemainder, czApproximation]

/-- Part of Lemma 10.2.5 (both cases). -/
lemma measurable_czApproximation (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} :
    Measurable (czApproximation ha hf α) := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.16) (both cases).
This is true by definition, the work lies in `tsum_czRemainder'` -/
lemma czApproximation_add_czRemainder (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} {x : X} :
    czApproximation ha hf α x + czRemainder ha hf α x = f x := by
  simp [czApproximation, czRemainder]

/-- Part of Lemma 10.2.5, equation (10.2.17) (both cases). -/
lemma norm_czApproximation_le (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} (hα : ⨍⁻ x, ‖f x‖ₑ < α) :
    ∀ᵐ x, ‖czApproximation ha hf α x‖ₑ ≤ 2 ^ (3 * a) * α := by
  sorry

/-- Equation (10.2.17) specialized to the general case. -/
lemma norm_czApproximation_le_infinite (ha : 4 ≤ a) {hf : BoundedFiniteSupport f}
    (hX : GeneralCase f α) (hα : 0 < α) :
    ∀ᵐ x, ‖czApproximation ha hf α x‖ₑ ≤ 2 ^ (3 * a) * α := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.18) (both cases). -/
lemma eLpNorm_czApproximation_le (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} (hα : 0 < α) :
    eLpNorm (czApproximation ha hf α) 1 volume ≤ eLpNorm f 1 volume := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.19) (general case). -/
lemma support_czRemainder'_subset (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} {hX : GeneralCase f α}
    {i : ℕ} :
    support (czRemainder' ha hf hX i) ⊆ czBall3 ha hf hX i := by
  rw [support_subset_iff']
  intro x hx
  exact indicator_of_notMem (fun a ↦ hx (czPartition_subset_czBall3 ha a)) _

/-- Part of Lemma 10.2.5, equation (10.2.20) (general case). -/
lemma integral_czRemainder' (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} {hX : GeneralCase f α} (hα : 0 < α)
    {i : ℕ} :
    ∫ x, czRemainder' ha hf hX i x = 0 := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.20) (finite case). -/
lemma integral_czRemainder (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} (hX : ¬ GeneralCase f α) (hα : 0 < α) :
    ∫ x, czRemainder ha hf α x = 0 := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.21) (general case). -/
lemma eLpNorm_czRemainder'_le (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} {hX : GeneralCase f α}
    (hα : 0 < α) {i : ℕ} :
    eLpNorm (czRemainder' ha hf hX i) 1 volume ≤ 2 ^ (2 * a + 1) * α * volume (czBall3 ha hf hX i) := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.21) (finite case). -/
lemma eLpNorm_czRemainder_le (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} (hX : ¬ GeneralCase f α)
    (hα : 0 < α) :
    eLpNorm (czRemainder ha hf α) 1 volume ≤ 2 ^ (2 * a + 1) * α * volume (univ : Set X) := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.22) (general case). -/
lemma tsum_volume_czBall3_le (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} (hX : GeneralCase f α)
    (hα : 0 < α) :
    ∑' i, volume (czBall3 ha hf hX i) ≤ 2 ^ (4 * a) / α * eLpNorm f 1 volume := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.22) (finite case). -/
lemma volume_univ_le (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} (hX : ¬ GeneralCase f α)
    (hα : 0 < α) :
    volume (univ : Set X) ≤ 2 ^ (4 * a) / α * eLpNorm f 1 volume := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.23) (general case). -/
lemma tsum_eLpNorm_czRemainder'_le (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} (hX : GeneralCase f α)
    (hα : 0 < α) :
    ∑' i, eLpNorm (czRemainder' ha hf hX i) 1 volume ≤ 2 * eLpNorm f 1 volume := by
  sorry

/-- Part of Lemma 10.2.5, equation (10.2.23) (finite case). -/
lemma tsum_eLpNorm_czRemainder_le (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} (hX : ¬ GeneralCase f α)
    (hα : 0 < α) :
    eLpNorm (czRemainder ha hf α) 1 volume ≤ 2 * eLpNorm f 1 volume := by
  sorry

/- ### Lemmas 10.2.6 - 10.2.9 -/

/-- The constant `c` introduced below Lemma 10.2.5. -/
irreducible_def c10_0_3 (a : ℕ) : ℝ≥0 := (2 ^ (a ^ 3 + 12 * a + 4))⁻¹

open scoped Classical in
/-- The set `Ω` introduced below Lemma 10.2.5. -/
def Ω (ha : 4 ≤ a) (hf : BoundedFiniteSupport f) (α : ℝ≥0∞) : Set X :=
  if hX : GeneralCase f α then ⋃ i, czBall2 ha hf hX i else univ

/-- The constant used in `estimate_good`. -/
irreducible_def C10_2_6 (a : ℕ) : ℝ≥0 := 2 ^ (2 * a ^ 3 + 3 * a + 2) * c10_0_3 a

/-- Lemma 10.2.6 -/
lemma estimate_good (ha : 4 ≤ a) {hf : BoundedFiniteSupport f} (hα : ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a < α) :
    distribution (czOperator K r (czApproximation ha hf α)) (α / 2) volume ≤
    C10_2_6 a / α * eLpNorm f 1 volume := by
  sorry

/-- The constant used in `czOperatorBound`. -/
irreducible_def C10_2_7 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 2 * a + 1) * c10_0_3 a

/-- The function `F` defined in Lemma 10.2.7. -/
def czOperatorBound (ha : 4 ≤ a) (hf : BoundedFiniteSupport f) (hX : GeneralCase f α) (x : X) : ℝ≥0∞ :=
  C10_2_7 a * α * ∑' i, ((czRadius ha hf hX i).toNNReal / nndist x (czCenter ha hf hX i)) ^ (a : ℝ)⁻¹ *
    volume (czBall3 ha hf hX i) / volume (ball x (dist x (czCenter ha hf hX i)))

/-- Lemma 10.2.7.
Note that `hx` implies `hX`, but we keep the superfluous hypothesis to shorten the statement. -/
lemma estimate_bad_partial (ha : 4 ≤ a) {hf : BoundedFiniteSupport f}
    (hα : ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a < α)
    (hx : x ∈ (Ω ha hf α)ᶜ) (hX : GeneralCase f α) :
    ‖czOperator K r (czRemainder ha hf α) x‖ₑ ≤ 3 * czOperatorBound ha hf hX x + α / 8 := by
  sorry

/-- The constant used in `distribution_czOperatorBound`. -/
irreducible_def C10_2_8 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 9 * a + 4)

/-- Lemma 10.2.8 -/
lemma distribution_czOperatorBound (ha : 4 ≤ a) {hf : BoundedFiniteSupport f}
    (hα : ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a < α) (hX : GeneralCase f α) :
    volume ((Ω ha hf α)ᶜ ∩ czOperatorBound ha hf hX ⁻¹' Ioi (α / 8)) ≤
    C10_2_8 a / α * eLpNorm f 1 volume := by
  sorry

/-- The constant used in `estimate_bad`. -/
irreducible_def C10_2_9 (a : ℕ) : ℝ≥0 := 2 ^ (5 * a) / c10_0_3 a + 2 ^ (a ^ 3 + 9 * a + 4)

/-- Lemma 10.2.9 -/
-- In the proof, case on `GeneralCase f α`, noting in the finite case that `Ω = univ`
lemma estimate_bad (ha : 4 ≤ a) {hf : BoundedFiniteSupport f}
    (hα : ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a < α) (hX : GeneralCase f α) :
    distribution (czOperator K r (czRemainder ha hf α)) (α / 2) volume ≤
    C10_2_9 a / α * eLpNorm f 1 volume := by
  sorry


/- ### Lemmas 10.0.3 -/

/-- The constant used in `czoperator_weak_1_1`. -/
irreducible_def C10_0_3 (a : ℕ) : ℝ≥0 := 2 ^ (a ^ 3 + 19 * a)

/-- Lemma 10.0.3, formulated differently.
The blueprint version is basically this after unfolding `HasBoundedWeakType`, `wnorm` and `wnorm'`.
-/
-- in proof: do cases on `α ≤ ⨍⁻ x, ‖f x‖ₑ / c10_0_3 a`.
-- If true, use the argument directly below (10.2.37)
theorem czoperator_weak_1_1 (ha : 4 ≤ a) (hr : 0 < r)
    (hT : HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts a)) :
    HasBoundedWeakType (czOperator K r) 1 1 volume volume (C10_0_3 a) := by
  sorry


end
