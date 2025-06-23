import Carleson.Classical.HilbertKernel
import Carleson.Classical.DirichletKernel
import Carleson.Classical.SpectralProjectionBound
import Carleson.ToMathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Data.Real.Pi.Bounds

set_option linter.unusedVariables.analyzeTactics true

/- This file contains the proof that the Hilbert kernel is a bounded operator. -/

noncomputable section

open scoped Real ENNReal
open Complex ComplexConjugate MeasureTheory Bornology Set
-- open MeasureTheory Function Metric Bornology Real ENNReal MeasureTheory.ENNReal MeasureTheory

open MeasureTheory ENNReal Real
open scoped Real

section
@[reducible]
def doublingMeasure_real_two : DoublingMeasure ℝ 2 :=
  InnerProductSpace.DoublingMeasure.mono (by simp)

instance doublingMeasure_real_16 : DoublingMeasure ℝ (2 ^ 4 : ℕ) :=
  doublingMeasure_real_two.mono (by norm_num)
end

/-- The modulation operator `M_n g`, defined in (11.3.1) -/
def modulationOperator (n : ℤ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  g x * Complex.exp (.I * n * x)

/-- The approximate Hilbert transform `L_N g`, defined in (11.3.2).
defined slightly differently. -/
def approxHilbertTransform (n : ℕ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  (n : ℂ)⁻¹ * ∑ k ∈ .Ico n (2 * n),
    modulationOperator (-k) (partialFourierSum k (modulationOperator k g)) x

/-- The kernel `k_r(x)` defined in (11.3.11).
When used, we may assume that `r ∈ Ioo 0 1`.
Todo: find better name? -/
def niceKernel (r : ℝ) (x : ℝ) : ℝ :=
  if Complex.exp (.I * x) = 1 then r⁻¹ else
    min r⁻¹ (1 + r / normSq (1 - Complex.exp (.I * x)))

-- todo: write lemmas for `niceKernel` (periodicity, evenness)

/-- Lemma 11.1.8 -/
lemma mean_zero_oscillation {n : ℤ} (hn : n ≠ 0) :
    ∫ x in (0)..2 * π, Complex.exp (.I * n * x) = 0 := by
  rw [integral_exp_mul_complex (by simp [hn])]
  simp [sub_eq_zero, Complex.exp_eq_one_iff, hn, ← mul_assoc, mul_comm Complex.I,
    mul_right_comm _ Complex.I]


/-- Lemma 11.5.1
Note: might not be used if we can use `spectral_projection_bound_lp` below.
-/
lemma partial_sum_projection {f : ℝ → ℂ} {n : ℕ}
    (hf : MemLp f ∞ volume) (periodic_f : f.Periodic (2 * π)) {x : ℝ} :
    partialFourierSum n (partialFourierSum n f) x = partialFourierSum n f x := by
  sorry

/-- Lemma 11.5.2.
Note: might not be used if we can use `spectral_projection_bound_lp` below.
-/
lemma partial_sum_selfadjoint {f g : ℝ → ℂ} {n : ℕ}
    (hf : MemLp f ∞ volume) (periodic_f : f.Periodic (2 * π))
    (hg : MemLp g ∞ volume) (periodic_g : g.Periodic (2 * π)) :
    ∫ x in (0)..2 * π, conj (partialFourierSum n f x) * g x =
    ∫ x in (0)..2 * π, conj (f x) * partialFourierSum n g x := by
  sorry


--lemma eLpNorm_eq_norm {f : ℝ → ℂ} {p : ENNReal} (hf : MemLp f p) :
--    ‖MemLp.toLp f hf‖ = eLpNorm f p := by
--  sorry

theorem AddCircle.haarAddCircle_eq_smul_volume {T : ℝ} [hT : Fact (0 < T)] :
    (@haarAddCircle T _) = (ENNReal.ofReal T)⁻¹ • (volume : Measure (AddCircle T)) := by
  rw [volume_eq_smul_haarAddCircle, ← smul_assoc, smul_eq_mul,
    ENNReal.inv_mul_cancel (by simp [hT.out]) ENNReal.ofReal_ne_top, one_smul]

open AddCircle in
/-- Lemma 11.1.10.
The blueprint states this on `[-π, π]`, but I think we can consistently change this to `(0, 2π]`.
-/
-- todo: add lemma that relates `eLpNorm ((Ioc a b).indicator f)` to `∫ x in a..b, _`
lemma spectral_projection_bound {f : ℝ → ℂ} {n : ℕ} (hmf : Measurable f) :
    eLpNorm ((Ioc 0 (2 * π)).indicator (partialFourierSum n f)) 2 ≤
    eLpNorm ((Ioc 0 (2 * π)).indicator f) 2 := by
  -- Proof by massaging the statement of `spectral_projection_bound_lp` into this.
  by_cases hf_L2 : eLpNorm ((Ioc 0 (2 * π)).indicator f) 2 = ⊤
  · rw [hf_L2]
    exact OrderTop.le_top _
  push_neg at hf_L2
  rw [← lt_top_iff_ne_top] at hf_L2
  have : Fact (0 < 2 * π) := ⟨by positivity⟩
  have lift_MemLp : MemLp (liftIoc (2 * π) 0 f) 2 haarAddCircle := by
    unfold MemLp
    constructor
    · rw [haarAddCircle_eq_smul_volume]
      apply AEStronglyMeasurable.smul_measure
      exact hmf.aestronglyMeasurable.liftIoc (2 * π) 0
    · rw [haarAddCircle_eq_smul_volume, eLpNorm_smul_measure_of_ne_top (by trivial),
        eLpNorm_liftIoc _ _ hmf.aestronglyMeasurable, smul_eq_mul, zero_add]
      apply ENNReal.mul_lt_top _ hf_L2
      rw [← ENNReal.ofReal_inv_of_pos this.out]
      apply ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  let F : Lp ℂ 2 haarAddCircle :=
    MemLp.toLp (AddCircle.liftIoc (2 * π) 0 f) lift_MemLp

  have lp_version := spectral_projection_bound_lp (N := n) F
  rw [Lp.norm_def, Lp.norm_def,
    ENNReal.toReal_le_toReal (Lp.eLpNorm_ne_top (partialFourierSumLp 2 n F)) (Lp.eLpNorm_ne_top F)]
    at lp_version

  rw [← zero_add (2 * π), ← eLpNorm_liftIoc _ _ hmf.aestronglyMeasurable,
    ← eLpNorm_liftIoc _ _ partialFourierSum_uniformContinuous.continuous.aestronglyMeasurable,
    volume_eq_smul_haarAddCircle,
    eLpNorm_smul_measure_of_ne_top (by trivial), eLpNorm_smul_measure_of_ne_top (by trivial),
    smul_eq_mul, smul_eq_mul, ENNReal.mul_le_mul_left (by simp [Real.pi_pos]) (by simp)]
  have ae_eq_right : F =ᶠ[ae haarAddCircle] liftIoc (2 * π) 0 f := MemLp.coeFn_toLp _
  have ae_eq_left : partialFourierSumLp 2 n F =ᶠ[ae haarAddCircle]
      liftIoc (2 * π) 0 (partialFourierSum n f) :=
    Filter.EventuallyEq.symm (partialFourierSum_aeeq_partialFourierSumLp 2 n f lift_MemLp)
  rw [← eLpNorm_congr_ae ae_eq_right, ← eLpNorm_congr_ae ae_eq_left]
  exact lp_version


/-- Lemma 11.3.1.
The blueprint states this on `[-π, π]`, but I think we can consistently change this to `(0, 2π]`.
-/
lemma modulated_averaged_projection {g : ℝ → ℂ} {n : ℕ}
    (hmg : Measurable g) (hg : MemLp g ∞ volume) (periodic_g : g.Periodic (2 * π)) :
    eLpNorm ((Ioc 0 (2 * π)).indicator (approxHilbertTransform n g)) ≤
    eLpNorm ((Ioc 0 (2 * π)).indicator g) := by
  sorry

/- Lemma 11.3.2 `periodic-domain-shift` is in Mathlib. -/

/-- Lemma 11.3.3.
The blueprint states this on `[-π, π]`, but I think we can consistently change this to `(0, 2π]`.
-/
lemma young_convolution {f g : ℝ → ℂ} (hmf : AEMeasurable f) (periodic_f : f.Periodic (2 * π))
    (hmg : AEMeasurable g) (periodic_g : g.Periodic (2 * π)) :
    eLpNorm ((Ioc 0 (2 * π)).indicator fun x ↦ ∫ y in (0)..2 * π, f y * g (x - y)) 2 ≤
    eLpNorm ((Ioc 0 (2 * π)).indicator f) 2 * eLpNorm ((Ioc 0 (2 * π)).indicator g) 1  := by
  have : Fact (0 < 2 * π) := ⟨mul_pos two_pos Real.pi_pos⟩
  have h2 : (1 : ℝ≥0∞) ≤ 2 := by exact one_le_two
  simpa [zero_add] using ENNReal.eLpNorm_Ioc_convolution_le_of_norm_le_mul
    (ContinuousLinearMap.mul ℝ ℂ) 0 h2 (le_refl 1) h2 (by rw [inv_one])
    periodic_f periodic_g hmf.aestronglyMeasurable hmg.aestronglyMeasurable 1 (by simp)

lemma eLpNorm_indicator_one_ne_top {g : ℝ → ℂ} (hg : MemLp g ∞ volume) :
    eLpNorm ((Set.Ioc 0 (2 * π)).indicator g) 1 volume ≠ ⊤ := by
  grw [← lt_top_iff_ne_top, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioc,
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ (OrderTop.le_top 1) (hg.restrict _).1]
  exact mul_lt_top (hg.restrict _).eLpNorm_lt_top (by norm_num)

#check Set.indicator_add_compl_eq_piecewise
#check Set.indicator

lemma aux1' {r x : ℝ} (hr : r ∈ Ioo 0 π) (hx : x ∈ Ioc 0 r) : r⁻¹ ≤ r / ‖1 - cexp (I * x)‖ ^ 2 := by
  rw [mem_Ioo] at hr
  rw [mem_Ioc] at hx

  rw [norm_sub_rev, norm_exp_I_mul_ofReal_sub_one]
  have : 0 ≤ Real.sin (x / 2) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have : Real.cos x < 1 := by
    rw [← Real.cos_zero]
    apply Real.cos_lt_cos_of_nonneg_of_le_pi (by trivial) (by linarith) (by linarith)
  rw [norm_eq_abs, abs_mul, mul_pow,abs_sin_half,sq_sqrt (by linarith), abs_of_nonneg zero_le_two]
  simp [mul_pow]
  ring_nf
  rw [mul_comm, le_inv_mul_iff₀ (by simp_all),← le_mul_inv_iff₀ (by simp_all)]
  simp only [inv_inv]
  ring_nf
  suffices 1 - r ^ 2 / 2 ≤ Real.cos x by linarith
  have : Real.cos r ≤ Real.cos x := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  apply ge_trans this
  exact Real.one_sub_sq_div_two_le_cos

lemma aux1 {r x : ℝ} (hr : r ∈ Ioo 0 π) (hx : x ∈ Ioc 0 r) : r⁻¹ ≤ r / ‖1 - cexp (I * x)‖ ^ 2 := by
  rw [mem_Ioo] at hr
  rw [mem_Ioc] at hx
  rw [Complex.exp_eq_exp_re_mul_sin_add_cos]
  simp
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp
  rw [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  rw [Real.sq_sqrt (by positivity)]
  rw [sub_sq]
  have : 1 - 2 * Real.cos x + Real.cos x ^ 2 + Real.sin x ^ 2 = 1 - 2 * Real.cos x + (Real.cos x ^ 2 + Real.sin x ^ 2) := by group
  simp [this]
  have : 1 - 2 * Real.cos x + 1 = 2 - 2 * Real.cos x := by group
  simp [this]
  have : Real.cos x < Real.cos 0 := Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  simp at this
  have : (2 - 2 * Real.cos x) ≠ 0 := by linarith
  rw [le_div_iff₀ (by simp_all)]
  rw [mul_comm, ← le_div_iff₀ (by simp_all)]
  simp only [div_inv_eq_mul]
  have : 2 - 2 * Real.cos x = 2 * (1 - Real.cos x) := by ring
  rw [this]
  rw [mul_comm, ← le_div_iff₀ (by simp_all)]
  rw [sub_le_comm]
  rw [← pow_two]
  have : Real.cos r ≤ Real.cos x := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  apply ge_trans this
  exact Real.one_sub_sq_div_two_le_cos

-- TODO: is this worth being a separate lemma?
lemma normSq_one_sub_inv (x : ℝ) :
    normSq (1 - cexp (I * (x : ℂ))) = normSq (1 - (cexp (I * (x : ℂ)))⁻¹) := by
  rw [← normSq_conj, inv_eq_conj (norm_exp_I_mul_ofReal x), map_sub, map_one]

lemma niceKernel_neg {r : ℝ} (x : ℝ) : niceKernel r (-x) = niceKernel r x := by
  simp only [niceKernel, ofReal_neg, mul_neg, Complex.exp_neg, inv_eq_one]
  congr 4
  exact normSq_one_sub_inv _ |>.symm

lemma niceKernel_pos {r x : ℝ} (hr : r > 0) : 0 < niceKernel r x := by
  unfold niceKernel
  split
  · positivity
  · refine lt_min (by positivity) ?_
    apply lt_add_of_lt_of_nonneg (by norm_num)
    apply div_nonneg (by positivity) (normSq_nonneg _)

lemma niceKernel_periodic (r : ℝ) : Function.Periodic (niceKernel r) (2 * π) := by
  simp [niceKernel, mul_add, mul_comm I (2 * π), Complex.exp_add]

lemma intervalIntegrable_niceKernel {a b r : ℝ} (hr : r > 0) :
    IntervalIntegrable (niceKernel r) volume a b := by
  apply intervalIntegrable_const (c := r⁻¹) |>.mono_fun
  · let S : Set ℝ := {x | cexp (I * x) = 1}
    have : AEStronglyMeasurable (S.piecewise (fun _ : ℝ => r⁻¹)
        (fun x : ℝ => min r⁻¹ (1 + r / ‖1 - cexp (I * x)‖ ^ 2)))
        (volume.restrict (uIoc a b)) := by
      have : MeasurableSet S := by
        simpa [S] using (isClosed_eq (by fun_prop) continuous_const).measurableSet
      apply AEStronglyMeasurable.piecewise this
      · fun_prop
      · fun_prop
    convert this using 1
    simp only [← indicator_add_compl_eq_piecewise]
    unfold Set.indicator niceKernel
    simp only [normSq_eq_norm_sq, mem_setOf_eq, mem_compl_iff, ite_not, S]
    funext x
    split_ifs with ff <;> simp [ff]
  · apply Filter.Eventually.of_forall
    intro y
    simp_rw [norm_eq_abs]
    rw [abs_of_pos (niceKernel_pos hr), abs_of_pos (by positivity), niceKernel]
    split <;> simp

lemma integrable_bump_convolution' {f g : ℝ → ℂ}
    (hf : MemLp f ∞ volume) (periodic_f : f.Periodic (2 * π))
    (hg : MemLp g ∞ volume) (periodic_g : g.Periodic (2 * π))
    {r : ℝ} (hr : r ∈ Ioo 0 π) (h : ∀ x, ‖g x‖ ≤ niceKernel r x) :
    eLpNorm ((Ioc 0 (2 * π)).indicator fun x ↦ ∫ y in (0)..2 * π, f y * g (x - y)) 2 ≤
    2 ^ (5 : ℝ) * eLpNorm ((Ioc 0 (2 * π)).indicator f) 2 := by
  grw [young_convolution hf.1.aemeasurable periodic_f hg.1.aemeasurable periodic_g, mul_comm]
  gcongr
  rw [← ENNReal.toReal_le_toReal (eLpNorm_indicator_one_ne_top hg) (by finiteness)]

  have we : r > 0 := hr.1
  have we3 : r < π := mem_Ioo.mp hr |>.2

  have e2 (x) (h : x ∈ Icc r π) : r / ‖1 - cexp (I * x)‖ ^ 2 ≤ 4 * r / x ^ 2 := calc
    _ ≤ r / (x / 2) ^ 2 := by
      have : 0 < x := by linarith [h.1]
      grw [lower_secant_bound ⟨?_, ?_⟩ (le_abs_self x)] <;> linarith [h.2]
    _  = 4 * r / x ^2 := by ring

  have h4 {x} : 0 < niceKernel r x := niceKernel_pos we
  have h3 {a b} : IntervalIntegrable (niceKernel r) volume a b := intervalIntegrable_niceKernel we

  have hg_integrable : Integrable g (volume.restrict (Ioc 0 (2 * π))) := by
    apply IntegrableOn.integrable
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    apply h3.mono_fun hg.1.restrict (Filter.Eventually.of_forall ?_)
    simpa [abs_of_pos h4] using h

  have hbound_integrable : IntervalIntegrable (fun x ↦ 4 * r / x ^ 2) volume r π := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
    have (x) (hx : x ∈ Icc r π) : x ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith [mem_Icc.mp hx])
    fun_prop (disch := assumption)

  calc
    _ ≤ ∫ x in (0)..2 * π, niceKernel r x := by
      simp_rw [eLpNorm_one_eq_lintegral_enorm, enorm_indicator_eq_indicator_enorm,
        lintegral_indicator (measurableSet_Ioc)]
      rw [← ofReal_integral_norm_eq_lintegral_enorm hg_integrable,
        ENNReal.toReal_ofReal (by positivity), intervalIntegral.integral_of_le (by linarith)]
      apply setIntegral_mono_on hg_integrable.norm ?_ measurableSet_Ioc (fun x _ ↦ h x)
      exact intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith) |>.mp h3
    _ = 2 * ∫ x in (0)..π, niceKernel r x := by
      have := (zero_add (2 * π)) ▸ (niceKernel_periodic r).intervalIntegral_add_eq 0 (-π)
      rw [this, show -π + 2 * π = π by group,
        ← intervalIntegral.integral_add_adjacent_intervals (b := 0) h3 h3, two_mul]
      have := intervalIntegral.integral_comp_neg (a := -π) (b := 0) (niceKernel r)
      simpa [neg_zero, neg_neg, niceKernel_neg]
    _ = 2 * (∫ x in (0)..r, niceKernel r x) + 2 * ∫ x in r..π, niceKernel r x := by
      rw [← mul_add, intervalIntegral.integral_add_adjacent_intervals h3 h3]
    _ ≤ 2 * (∫ _ in (0)..r, r⁻¹) + 2 * ∫ x in r..π, 1 + (4 * r) / x ^ 2 := by
      gcongr
      · refine le_of_eq <| intervalIntegral.integral_congr (g := fun _ ↦ r⁻¹) fun x hx ↦ ?_
        rw [niceKernel, ite_eq_iff']
        refine ⟨fun _ ↦ rfl, fun h0 ↦ min_eq_left ?_⟩
        rw [uIcc_of_le (by positivity), mem_Icc] at hx
        have : x ≠ 0 := fun h2 ↦ by simp [h2] at h0
        grw [aux1 hr ⟨lt_of_le_of_ne hx.1 this.symm, hx.2⟩]
        apply le_add_of_nonneg_of_le (by norm_num)
        rw [normSq_eq_norm_sq]
      · apply intervalIntegral.integral_mono_on (by linarith) h3
        · exact intervalIntegrable_const.add hbound_integrable
        · intro x ⟨hx1, hx2⟩
          have : cexp (I * x) ≠ 1 := fun h ↦ by
            have : Real.cos x = 1 := by simpa [mul_comm I x] using congr(($h).re)
            rw [Real.cos_eq_one_iff_of_lt_of_lt] at this <;> linarith
          simp only [niceKernel, this, ↓reduceIte, inf_le_iff, normSq_eq_norm_sq]
          right
          grw [e2 x ⟨hx1, hx2⟩]
    _ ≤ 2 + (2 * π + 8 * r * (r⁻¹ - π⁻¹)) := by
      gcongr
      · simp [we.ne']
      have (x) : 4 * r / x ^ 2 = (4 * r) * (x ^ (-2 : ℤ)) := by group
      simp_rw [intervalIntegral.integral_add intervalIntegrable_const hbound_integrable,
        intervalIntegral.integral_const, this, intervalIntegral.integral_const_mul, ge_iff_le,
        smul_eq_mul, mul_one, mul_add, ← mul_assoc, show 2 * 4 * r = 8 * r by group]
      gcongr
      · exact sub_le_self π (le_of_lt we)
      rw [integral_zpow]
      · apply le_of_eq; group
      · exact .inr ⟨by trivial, by simp [mem_uIcc, we, Real.pi_pos]⟩
    _ ≤ 2 + (2 * π + (8 - 8 * r * π⁻¹)) := by simp [mul_sub, we.ne']
    _ ≤ (2 ^ (5 : ℝ) : ENNReal).toReal := by
      grw [sub_le_self 8 (by positivity), Real.pi_lt_four]
      norm_num

/-- The function `L'`, defined in the Proof of Lemma 11.3.5. -/
def dirichletApprox (n : ℕ) (x : ℝ) : ℂ :=
  (n : ℂ)⁻¹ * ∑ k ∈ .Ico n (2 * n), dirichletKernel k x * Complex.exp (- Complex.I * k * x)

/-- Lemma 11.3.5, part 1. -/
lemma continuous_dirichletApprox {n : ℕ} : Continuous (dirichletApprox n) := by
  sorry

/-- Lemma 11.3.5, part 2. -/
lemma periodic_dirichletApprox (n : ℕ) : (dirichletApprox n).Periodic (2 * π) := by
  sorry

/-- Lemma 11.3.5, part 3.
The blueprint states this on `[-π, π]`, but I think we can consistently change this to `(0, 2π]`.
-/
lemma approxHilbertTransform_eq_dirichletApprox {f : ℝ → ℂ} {n : ℕ}
    (hf : MemLp f ∞ volume) (periodic_f : f.Periodic (2 * π))
    {n : ℕ} {x : ℝ} :
    approxHilbertTransform n f x =
    (2 * π)⁻¹ * ∫ y in (0)..2 * π, f y * dirichletApprox n (x - y) := by
  sorry

/-- Lemma 11.3.5, part 4.
The blueprint states this on `[-π, π]`, but I think we can consistently change this to `(0, 2π]`.
-/
lemma dist_dirichletApprox_le {f : ℝ → ℂ} {n : ℕ}
    (hf : MemLp f ∞ volume) (periodic_f : f.Periodic (2 * π))
    {r : ℝ} (hr : r ∈ Ioo 0 1) {n : ℕ} (hn : n = ⌈r⁻¹⌉₊) {x : ℝ} :
    dist (dirichletApprox n x) ({y : ℂ | ‖y‖ ∈ Ioo r 1}.indicator 1 x) ≤
    2 ^ (5 : ℝ) * niceKernel r x := by
  sorry

/- Lemma 11.1.6.
This verifies the assumption on the operators T_r in two-sided metric space Carleson.
Its proof is done in Section 11.3 (The truncated Hilbert transform) and is yet to be formalized.

Note: we might be able to simplify the proof in the blueprint by using real interpolation
`MeasureTheory.exists_hasStrongType_real_interpolation`.
Note: In the blueprint we have the condition `r < 1`.
Can we get rid of that condition or otherwise fix `two_sided_metric_carleson`?
-/
lemma Hilbert_strong_2_2 ⦃r : ℝ⦄ (hr : 0 < r) :
    HasBoundedStrongType (czOperator K r) 2 2 volume volume (C_Ts 4) :=
  sorry
