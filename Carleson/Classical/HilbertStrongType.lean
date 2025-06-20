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


set_option linter.flexible false

#check intervalIntegral.norm_integral_le_integral_norm_Ioc

lemma eLpNorm_indicator_one_ne_top {g : ℝ → ℂ}
    (hg : MemLp g ∞ volume) :
    eLpNorm ((Set.Ioc 0 (2 * π)).indicator g) 1 volume ≠ ⊤ := by
  -- finiteness of ‖g‖_∞ and of the measure of the interval
  have hinf : eLpNorm g ∞ volume < ⊤ := hg.2
  have hμ   : (volume (Set.Ioc 0 (2 * π)) : ℝ≥0∞) < ⊤ := by simp

  -- integrate the bound over the interval
  have hle : eLpNorm ((Set.Ioc 0 (2 * π)).indicator g) 1 volume ≤
      eLpNorm g ∞ volume * volume (Set.Ioc 0 (2 * π)) := by
    have : (∫⁻ x in Set.Ioc 0 (2 * π), ‖g x‖ₑ) ≤
        eLpNorm g ∞ volume * volume (Set.Ioc 0 (2 * π)) := by
      have hmono : (fun x ↦ ‖g x‖ₑ) ≤ᵐ[volume.restrict (Set.Ioc 0 (2 * π))]
          fun _ : ℝ ↦ eLpNorm g ∞ volume := by
        have h_all : (fun x ↦ ‖g x‖ₑ) ≤ᵐ[volume]
            fun _ : ℝ ↦ eLpNorm g ∞ volume := by
          have h' := ENNReal.ae_le_essSup (μ := volume) (f := fun y ↦ ‖g y‖ₑ)
          simpa [eLpNormEssSup] using h'
        exact ae_restrict_of_ae h_all
      have hle' : (∫⁻ x in Set.Ioc 0 (2 * π), ‖g x‖ₑ) ≤
          ∫⁻ x in Set.Ioc 0 (2 * π), eLpNorm g ∞ volume :=
        lintegral_mono_ae hmono
      have hconst : (∫⁻ x in Set.Ioc 0 (2 * π), eLpNorm g ∞ volume) =
          eLpNorm g ∞ volume * volume (Set.Ioc 0 (2 * π)) := by
        simp [lintegral_const, mul_comm]
      exact (le_trans hle' (le_of_eq hconst))
    simp [eLpNorm_one_eq_lintegral_enorm]
    simp [enorm_indicator_eq_indicator_enorm]
    have : (∫⁻ (x : ℝ), ‖(Ioc 0 (2 * π)).indicator g x‖ₑ) ≤
        eLpNormEssSup g volume * ENNReal.ofReal (2 * π) := by
      have hmono' : (fun x ↦ ‖g x‖ₑ) ≤ᵐ[volume.restrict (Set.Ioc 0 (2 * π))]
          fun _ : ℝ ↦ eLpNormEssSup g volume := by
        have h_all : (fun x ↦ ‖g x‖ₑ) ≤ᵐ[volume]
            fun _ : ℝ ↦ eLpNormEssSup g volume := by
          have h' := ENNReal.ae_le_essSup (μ := volume) (f := fun y ↦ ‖g y‖ₑ)
          simpa using h'
        exact ae_restrict_of_ae h_all
      have hle'' : (∫⁻ x in Set.Ioc 0 (2 * π), ‖g x‖ₑ) ≤
          ∫⁻ x in Set.Ioc 0 (2 * π), eLpNormEssSup g volume :=
        lintegral_mono_ae hmono'
      have hconst'' : (∫⁻ x in Set.Ioc 0 (2 * π), eLpNormEssSup g volume) =
          eLpNormEssSup g volume * volume (Set.Ioc 0 (2 * π)) := by
        simp [lintegral_const, mul_comm]
      have hvol : volume (Set.Ioc 0 (2 * π)) = ENNReal.ofReal (2 * π) := by
        simp [volume_Ioc, Real.pi_pos]
      have : (∫⁻ x in Set.Ioc 0 (2 * π), ‖g x‖ₑ) ≤
          eLpNormEssSup g volume * ENNReal.ofReal (2 * π) := by
        have := le_trans hle'' (le_of_eq hconst'')
        simpa [hvol] using this
      simpa [enorm_indicator_eq_indicator_enorm] using this
    simpa [enorm_indicator_eq_indicator_enorm] using this
  -- RHS is finite, so the LHS can’t be ⊤
  have : eLpNorm ((Set.Ioc 0 (2 * π)).indicator g) 1 volume < ⊤ :=
    lt_of_le_of_lt hle (mul_lt_top (by gcongr) (by gcongr))
  exact this.ne


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


#check Set.indicator_add_compl_eq_piecewise
#check Set.indicator

lemma aux1' {r x : ℝ} (hr : r ∈ Ioo 0 π) (hx : x ∈ Ioc 0 r) : r⁻¹ ≤ r / ‖1 - cexp (I * x)‖ ^ 2 := by
  rw [mem_Ioo] at hr
  rw [mem_Ioc] at hx

  rw [norm_sub_rev, norm_exp_I_mul_ofReal_sub_one]
  have : 0 ≤ Real.sin (x / 2) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have : Real.cos x < 1 := by
    rw [← Real.cos_zero]
    apply Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  rw [norm_eq_abs,]
  rw [abs_mul, mul_pow]
  rw [abs_sin_half]
  rw [sq_sqrt (by linarith)]
  rw [abs_of_nonneg (by linarith)]
  simp [mul_pow]
  ring_nf
  rw [mul_comm, le_inv_mul_iff₀ (by simp_all)]
  rw [← le_mul_inv_iff₀ (by simp_all)]
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

open Complex

lemma normSq_one_sub_inv (x : ℝ) :
    normSq (1 - cexp (I * (x : ℂ))) = normSq (1 - (cexp (I * (x : ℂ)))⁻¹) := by
  set z : ℂ := cexp (I * x) with hz
  have hz_norm : ‖z‖ = 1 := by
    simpa [hz] using norm_exp (I * x)
  have h_inv : z⁻¹ = conj z := by
    simpa using inv_eq_conj hz_norm
  have h_eq : 1 - z⁻¹ = conj (1 - z) := by
    simp [h_inv]
  have h_norm : normSq (1 - z⁻¹) = normSq (1 - z) := by
    rw [h_eq, normSq_conj]
  simpa [hz] using h_norm.symm


-- set_option Elab.async false

-- set_option trace.profiler.output.pp true in
-- set_option trace.profiler.threshold 10 in
-- set_option trace.profiler true in
-- set_option maxHeartbeats 500000 in
lemma integrable_bump_convolution' {f g : ℝ → ℂ}
    (hf : MemLp f ∞ volume) (periodic_f : f.Periodic (2 * π))
    (hg : MemLp g ∞ volume) (periodic_g : g.Periodic (2 * π))
    {r : ℝ} (hr : r ∈ Ioo 0 π) (h : ∀ x, ‖g x‖ ≤ niceKernel r x) :
    eLpNorm ((Ioc 0 (2 * π)).indicator fun x ↦ ∫ y in (0)..2 * π, f y * g (x - y)) 2 ≤
    2 ^ (5 : ℝ) * eLpNorm ((Ioc 0 (2 * π)).indicator f) 2 := by

  have q1 := young_convolution
    hf.aestronglyMeasurable.aemeasurable periodic_f
    hg.aestronglyMeasurable.aemeasurable periodic_g
  have we : r > 0 := hr.1
  have we2 : π > 0 := Real.pi_pos
  have we3 : r < π := mem_Ioo.mp hr |>.2

  have e1 (x) (h : x ∈ Icc r π) := lower_secant_bound (η := x) (x := x)
    (by constructor <;> linarith [mem_Icc.mp h]) (by rw [abs_of_pos (by linarith [mem_Icc.mp h])])

  have e2 (x) (h : x ∈ Icc r π) : 1 + r / ‖1 - cexp (I * ↑x)‖ ^ 2 ≤ 1 + 4 * r / x ^ 2 := calc
    1 + r / ‖1 - cexp (I * ↑x)‖ ^ 2 ≤ 1 + r / (x / 2) ^ 2 := by
      have := e1 x h
      have : x > 0 := by linarith [mem_Icc.mp h]
      have : 2 / π * r > 0 := by positivity
      simp
      refine (div_le_div_iff_of_pos_left we ?_ ?_).mpr ?_
      · refine sq_pos_of_pos ?_
        linarith
      · refine sq_pos_of_pos ?_
        linarith
      · rw [sq_le_sq, abs_of_pos (by linarith), abs_of_pos (by linarith)]
        linarith
    _  = 1 + 4 * r / x ^2 := by ring

  have h4 {x} : 0 < niceKernel r x := by
    unfold niceKernel
    split
    · positivity
    · apply lt_min_iff.mpr
      constructor
      · positivity
      · apply lt_add_of_lt_of_nonneg (by norm_num)
        apply div_nonneg (by positivity) (normSq_nonneg _)

  have h3 {a b} : IntervalIntegrable
      (niceKernel r) volume a b := by
    unfold niceKernel
    apply intervalIntegrable_const (c := r⁻¹) |>.mono_fun
    · let S : Set ℝ := {x | cexp (I * x) = 1}
      classical
      have : AEStronglyMeasurable (S.piecewise (fun _ : ℝ => r⁻¹)
          (fun x : ℝ => min r⁻¹ (1 + r / ‖1 - cexp (I * x)‖ ^ 2)))
          (volume.restrict (uIoc a b)) := by
        have : MeasurableSet S := by
          simpa [S] using (isClosed_eq (by fun_prop) continuous_const).measurableSet
        apply AEStronglyMeasurable.piecewise this
        · fun_prop
        · fun_prop
      convert this using 1
      simp [← indicator_add_compl_eq_piecewise]
      unfold Set.indicator
      simp [S, normSq_eq_norm_sq]
      funext x
      split_ifs with ff <;> simp [ff]
    · apply Filter.Eventually.of_forall
      intro y
      simp_rw [norm_eq_abs]
      rw [abs_of_pos (by exact h4), abs_of_pos (by positivity)]
      split <;> simp

  have bigg : ∫ x in (0)..π, niceKernel r x =
      (∫ x in (0)..r, niceKernel r x) + ∫ x in (r)..π, niceKernel r x := by
    rw [intervalIntegral.integral_add_adjacent_intervals h3 h3]

  have cexp_ne_one (x) (h2 : x ∈ Ioo 0 (2 * π)): cexp (I * x) ≠ 1 := by
    rw [mem_Ioo] at h2
    rw [mul_comm] -- TODO: is our simp normal form backwards?
    by_contra h
    have hcos_eq : Real.cos x = 1 := by simpa using congr(Complex.re $h)
    have : x = 0 := by rw [← Real.cos_eq_one_iff_of_lt_of_lt] <;> linarith
    linarith

  have q2 : (eLpNorm ((Ioc 0 (2 * π)).indicator g) 1 volume).toReal ≤ (2 ^ (5 : ℝ) : ENNReal).toReal := calc
    _ ≤ ∫ x in (0)..2 * π, niceKernel r x := by
      -- sorry -- TODO: this works
      rw [@eLpNorm_one_eq_lintegral_enorm]
      simp [enorm_indicator_eq_indicator_enorm]
      have a2 : ∫⁻ (a : ℝ) in Ioc 0 (2 * π), ‖g a‖ₑ = ENNReal.ofReal (∫ (a : ℝ) in Ioc 0 (2 * π), ‖g a‖) := by
        rw [← ofReal_integral_norm_eq_lintegral_enorm ?_]
        refine IntegrableOn.integrable ?_
        refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp ?_
        apply IntervalIntegrable.mono_fun h3
        · exact AEStronglyMeasurable.restrict hg.1
        · apply Filter.Eventually.of_forall
          simpa [abs_of_pos h4] using h
      rw [a2]
      rw [ENNReal.toReal_ofReal]
      · rw [intervalIntegral.integral_of_le (by linarith)]
        apply setIntegral_mono_on ?_ ?_ measurableSet_Ioc (fun x _ ↦ h x)
        · refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp ?_
          apply IntervalIntegrable.mono_fun h3
          · exact AEStronglyMeasurable.norm (AEStronglyMeasurable.restrict hg.1)
          · apply Filter.Eventually.of_forall
            simpa [abs_of_pos h4] using h
        · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp h3
      · exact setIntegral_nonneg measurableSet_Ioc (fun _ _ ↦ norm_nonneg _)
    _ = 2 * ∫ x in (0)..π, niceKernel r x := by
      -- sorry -- TODO: this works
      have niceKernel_even (x) : niceKernel r (-x) = niceKernel r x := by
        simp [niceKernel, Complex.exp_neg]
        have := Complex.norm_exp
        convert rfl using 5
        apply normSq_one_sub_inv
      have : Function.Periodic (niceKernel r) (2 * π) := by
        intro x
        unfold niceKernel
        simp [mul_add]
        rw [mul_comm I (2 * π)]
        simp [Complex.exp_add]
      have : ∫ (x : ℝ) in (0)..(0 + 2 * π), niceKernel r x =
          ∫ (x : ℝ) in -π..(-π + 2 * π), niceKernel r x :=
        Function.Periodic.intervalIntegral_add_eq this _ _
      simp at this
      rw [this, show -π + 2 * π = π by linarith,
        ← intervalIntegral.integral_add_adjacent_intervals (a := -π) (b := 0) h3 h3]
      conv_rhs => rw [two_mul]
      rw [add_right_cancel_iff]
      have :  ∫ (x : ℝ) in -π..(0), niceKernel r (-x) = ∫ (x : ℝ) in -(0)..-(-π), niceKernel r x :=
        intervalIntegral.integral_comp_neg (f := niceKernel r)
      simpa [niceKernel_even]
    _ ≤ 2 * (∫ x in (0)..r, 1 / r) + 2 * ∫ x in r..π, 1 + (4 * r) / x ^ 2 := by
      -- sorry -- TODO: this works
      have : ∫ (x : ℝ) in (0)..r, niceKernel r x =
          ∫ (x : ℝ) in (0)..r, r⁻¹ := by
        refine intervalIntegral.integral_congr ?_
        intro x hx
        simp only [niceKernel]
        split_ifs with h0 <;> try rfl
        have h1 : x ≠ 0 := by
          contrapose! h0
          simp [h0]
        apply min_eq_left
        rw [add_comm]
        rw [uIcc_of_le (by positivity)] at hx
        apply le_add_of_le_of_nonneg ?_ (by norm_num)
        rw [normSq_eq_norm_sq]
        apply aux1 hr
        rw [mem_Icc] at hx
        rw [mem_Ioc]
        have := lt_of_le_of_ne hx.1 h1.symm
        constructor <;> linarith
      rw [bigg, this, mul_add]
      simp
      have ig3 : ContinuousOn (fun x : ℝ ↦ r / ‖1 - cexp (I * ↑x)‖ ^ 2) (Icc r π) := by
        apply ContinuousOn.div₀ (by fun_prop) (by fun_prop)
        intro x hx
        have := e1 x hx
        apply pow_ne_zero 2
        have : 2 / π * r > 0 := by positivity
        linarith [mem_Icc.mp hx]
      have : ∫ (x : ℝ) in r..π, niceKernel r x ≤ ∫ (x : ℝ) in r..π, (1 + r / ‖1 - cexp (I * ↑x)‖ ^ 2) := by
        apply intervalIntegral.integral_mono_on (by linarith) h3
        · apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
          exact ContinuousOn.add (by fun_prop) ig3
        · unfold niceKernel
          intro x hx
          simp [normSq_eq_norm_sq]
          have : cexp (I * x) ≠ 1 := cexp_ne_one x
            (by rw [mem_Ioo]; constructor <;> linarith [mem_Icc.mp hx])
          simp [this]
      apply le_trans this
      apply intervalIntegral.integral_mono_on (by linarith) ?_ ?_ e2
      · exact ContinuousOn.intervalIntegrable_of_Icc (by linarith) (by fun_prop)
      · have : ∀ x ∈ Icc r π, x ^ 2 ≠ 0 := fun x hx ↦ by
          rw [mem_Icc] at hx
          apply pow_ne_zero 2 (by linarith)
        exact ContinuousOn.intervalIntegrable_of_Icc (by linarith) (by fun_prop (discharger := exact this))
    _ ≤ 2 + 2 * π + 8 * r * (1 / r - 1 / π) := by
      -- sorry -- TODO: this works
      simp only [one_div, intervalIntegral.integral_const, sub_zero, smul_eq_mul, ne_eq,
        show r ≠ 0 by positivity, not_false_eq_true, mul_inv_cancel₀, mul_one,
        intervalIntegrable_const, isUnit_iff_ne_zero]
      -- field_simp
      -- ring_nf
      rw [intervalIntegral.integral_add (intervalIntegrable_const) (by
        -- TODO: duplicated above
        apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
        have : ∀ x ∈ Icc r π, x ^ 2 ≠ 0 := fun x hx ↦ by
          rw [mem_Icc] at hx
          apply pow_ne_zero 2 (by linarith)
        fun_prop (discharger := exact this)
        )]
      have (x) : 4 * r / x ^ 2 = (4 * r) * (1 / x ^ 2) := by group
      simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, this,
        intervalIntegral.integral_const_mul, ge_iff_le]
      rw [mul_add]
      rw [← add_assoc, ← mul_assoc, show 2 * (4 * r) = 8 * r by ring]
      have : 2 + 2 * (π - r) ≤ 2 + 2 * π := by linarith
      refine add_le_add this ?_
      apply mul_le_mul_of_nonneg_left ?_ (by positivity)
      have (x : ℝ) : (1 / x ^ 2) = x ^ (-2 : ℤ) := by group
      simp only [this]
      rw [integral_zpow]
      · apply le_of_eq
        group
      · refine Or.inr ⟨by linarith, ?_⟩
        rw [mem_uIcc]
        simp [we]
        intro hfd
        linarith
    _ ≤ (2 ^ (5 : ℝ) : ENNReal).toReal := by
      rw [mul_sub]
      simp [show r ≠ 0 by positivity]
      have : 8 - 8 * r * π⁻¹ ≤ 8 := by
        apply sub_le_self
        apply mul_nonneg (by positivity) (by positivity)
      refine le_trans (add_le_add_left this _) ?_ -- TODO: use `grw`
      have : π < 4 := Real.pi_lt_four
      rw [add_comm, ← add_assoc]
      refine le_trans (add_le_add_left (mul_le_mul_of_nonneg_left (le_of_lt this) (le_of_lt (by positivity))) _) ?_  -- TODO: use `grw`
      norm_num

  have : MemLp g ⊤ volume := by exact hg
  have : eLpNorm ((Ioc 0 (2 * π)).indicator g) 1 volume ≤ eLpNorm g 1 volume := eLpNorm_indicator_le g

  rw [mul_comm (a := 2 ^ 5)]
  apply le_mul_of_le_mul_left q1
  rwa [ENNReal.toReal_le_toReal ?_ ?_] at q2
  · exact eLpNorm_indicator_one_ne_top hg
  · norm_num

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
