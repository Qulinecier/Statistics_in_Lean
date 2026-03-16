import Mathlib.MeasureTheory.Integral.IntervalAverage
import Mathlib.Probability.StrongLaw
import Mathlib.Analysis.Convex.Integral
import MLE.Measure
import MLE.Defs
import MLE.Basic
import MLE.ENNReal

open scoped NNReal ENNReal Topology
open Filter MeasureTheory ProbabilityTheory

namespace Likelihood

noncomputable abbrev f {Ω : Type*} [MeasurableSpace Ω]
   (X : Ω → ℝ) (P : Measure Ω) (μ : Measure ℝ := by volume_tac)
  := pdf X P μ

theorem likelihood_true_gt_likelihood_tendsto_one
    {Ω : Type*} [MeasurableSpace Ω]
    {ProbFunSet : Set (Measure Ω)}
    [FunLike (↑ProbFunSet) (Set Ω) ℝ≥0∞]
    [OuterMeasureClass (↑ProbFunSet) Ω]
    (μ : Measure ℝ := by volume_tac)
    (P : ℝ → ↑ProbFunSet) (θ₀ : ℝ)
    (X : ℕ → Ω → ℝ) (θ : ℝ)
    [IsProbabilityMeasure (P θ₀).1] [IsProbabilityMeasure (P θ).1]
    [HasPDF (X 0) (↑(P θ)) μ] [HasPDF (X 0) (↑(P θ₀)) μ]
    (hX : ∀ (n : ℕ), ∀ (ω : Ω), ∀ (i : Fin n), (X i ω) ∈ pdf_support (X 0) (P θ₀).1 μ)
    (h0 : ∀ (θ₁ θ₂ : ℝ), pdf_support (X 0) (P θ₁).1 μ
      = pdf_support (X 0) (P θ₂).1 μ)
    {s : NNReal}
    (hfs : ∀ (θ : ℝ), ∀ (a : ℝ), f (X 0) ((P θ)) μ a ≤ s)
    (hfl : ∀ (θ : ℝ), ∀ (a : ℝ), 0 < (f (X 0) ((P θ)) μ a).toReal)
    {S : Set ℝ} {hs1 : S ⊆ (Set.Ioi 0)} {hs2 : Convex ℝ S} {hs3 : IsClosed S}
    (hrv : ∀ (i : ℕ), Measurable (X i))
    (hindep : iIndepFun X ↑(P θ₀))
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) (P θ₀) (P θ₀))
    {hs4 : ∀ᵐ (x : Ω) ∂(P θ₀).1, (f (X 0) (↑(P θ)) μ (X 0 x)).toReal /
      (pdf (X 0) (↑(P θ₀)) μ (X 0 x)).toReal ∈ S}
    (hint1 : Integrable (Real.log ∘ fun ω ↦ (f (X 0) (↑(P θ)) μ (X 0 ω)).toReal /
      (pdf (X 0) (↑(P θ₀)) μ (X 0 ω)).toReal) ↑(P θ₀))
    (hint2 : Integrable (fun ω ↦ (f (X 0) (↑(P θ)) μ (X 0 ω)).toReal /
      (f (X 0) (↑(P θ₀)) μ (X 0 ω)).toReal) ↑(P θ₀))
    (hint0 : Integrable (log_sum_ratio_rv P μ X θ₀ θ 0) (P θ₀).1)
    (hne_const : ¬ ((fun ω ↦ ((f (X 0) ((P θ)) μ (X 0 ω)).toReal /
      (f (X 0) ((P θ₀)) μ (X 0 ω)).toReal)) =ᶠ[ae (P θ₀).1]
  Function.const Ω
    (⨍ (x : Ω),
      (fun ω ↦ ((f (X 0) ((P θ)) μ (X 0 ω)).toReal /
      (f (X 0) ((P θ₀)) μ (X 0 ω)).toReal)) x ∂(P θ₀))))
    :
    Tendsto (fun n : ℕ => ((P θ₀).1) {ω : Ω |
       Likelihood P X θ₀ n μ ω > Likelihood P X θ n μ ω}) atTop (𝓝 1)
 := by
    have htop1 : ∀ᵐ (x : ℝ) ∂μ, pdf (X 0) (↑(P θ)) μ x < ⊤ :=
      Measure.rnDeriv_lt_top (Measure.map (X 0) ↑(P θ)) μ
    have htop2 : ∀ᵐ (x : ℝ) ∂μ, pdf (X 0) (↑(P θ₀)) μ x < ⊤ :=
      Measure.rnDeriv_lt_top (Measure.map (X 0) ↑(P θ₀)) μ

    simp_rw [fun (n: ℕ)=> fun (ω : Ω) =>
      likelihood_iff_log_sum_ratio μ P θ₀ X n ω θ (hX n ω) h0 hfs hfl]
    have hident2 : ∀ (i : ℕ), IdentDistrib (log_sum_ratio_rv P μ X θ₀ θ i)
      (log_sum_ratio_rv P μ X θ₀ θ 0) ↑(P θ₀) ↑(P θ₀) :=by
      exact fun i ↦ IdentDistrib_log_sum_ratio μ P θ₀ θ X hident i
    have hpair :
      Pairwise (Function.onFun (fun x1 x2 ↦ x1 ⟂ᵢ[↑(P θ₀)] x2) (log_sum_ratio_rv P μ X θ₀ θ)) :=by
      classical
      intro i j hij
      simp only [Function.onFun]
      unfold log_sum_ratio_rv
      simpa [Function.onFun] using (iIndepFun_log_sum_ratio μ P θ₀ θ X hindep).indepFun
        hij



    have hlaw := MeasureTheory.tendstoInMeasure_of_tendsto_ae_of_measurable_edist (μ  := (P θ₀).1)
      (Measurable_edist_log_sum_ratio μ P θ₀ θ X hrv)
      (ProbabilityTheory.strong_law_ae_real (log_sum_ratio_rv P μ X θ₀ θ) hint0 hpair hident2)

    have hlog_Ioi : ContinuousOn Real.log (Set.Ioi (0:ℝ)) := by
      intro x hx
      simpa [ContinuousWithinAt] using
        (Real.continuousAt_log (by simp only [Set.mem_Ioi] at hx; nlinarith)).continuousWithinAt
    have hJensen := StrictConcaveOn.ae_eq_const_or_lt_map_average (μ:= (P θ₀).1) (f:=
      fun (ω : Ω) => ((pdf (X 0) (P θ).1 μ (X 0 ω)).toReal/ (pdf (X 0) (P θ₀).1 μ (X 0 ω)).toReal))
      (g:= Real.log)
      (StrictConcaveOn.subset strictConcaveOn_log_Ioi hs1 hs2)
        (hlog_Ioi.mono hs1) hs3 hs4 hint2 hint1


    generalize hε: ∫ (ω : Ω), log_sum_ratio_rv P μ X θ₀ θ 0 ω ∂↑(P θ₀) = ε at *

    unfold TendstoInMeasure at hlaw
    have hε_le_0 : 0 < ((- ε).toEReal).toENNReal := by
      cases hJensen with
      | inl hp => exact False.elim (hne_const hp)
      | inr hJensen =>
          unfold average at hJensen
          simp only [measure_univ, inv_one, one_smul] at hJensen
          rw [← hε]
          rw [integral_sum_ratio_eq_one μ P θ₀ θ X (hrv 0) htop2 htop1] at hJensen
          · simp only [Real.log_one] at hJensen
            have hμ2: 0 < ((- ε).toEReal).toENNReal:= by
              simp only [EReal.coe_neg, ne_eq, EReal.neg_eq_top_iff, EReal.coe_ne_bot,
                not_false_eq_true, EReal.toENNReal_of_ne_top, EReal.toReal_neg, EReal.toReal_coe,
                ENNReal.ofReal_pos, Left.neg_pos_iff]
              exact lt_of_eq_of_lt (id (Eq.symm hε)) hJensen
            exact
              lt_of_lt_of_eq hμ2
                (congrArg EReal.toENNReal
                  (congrArg Real.toEReal (congrArg Neg.neg (id (Eq.symm hε)))))
          · simpa using
              (MeasureTheory.measurable_pdf (X 0) ((↑(P θ) : Measure Ω)) (μ := μ)).aemeasurable
          · intro x
            have hpos : 0 < (pdf (X 0) (↑(P θ₀)) μ x).toReal := by
              simpa using (hfl θ₀ x)
            exact ne_of_gt hpos

    specialize hlaw ((- ε).toEReal).toENNReal hε_le_0
    rw [tendsto_measure_compl_iff] at hlaw
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlaw (univ_tendsto_one (P θ₀).1)
      · intro n
        simp only [EReal.coe_neg, ne_eq, EReal.neg_eq_top_iff, EReal.coe_ne_bot,
                  not_false_eq_true, EReal.toENNReal_of_ne_top, EReal.toReal_neg, EReal.toReal_coe,
                  smul_eq_mul]
        apply ((P θ₀).1).mono
        simp_rw [← Fin.sum_univ_eq_sum_range, log_sum_ratio_rv, div_eq_mul_inv, mul_comm]
        apply edist_compl_ball
      · intro x
        simp only [smul_eq_mul, measure_univ]
        simpa using (prob_le_one (μ := (P θ₀).1) (s := _))
    · intro i
      apply measurableSet_le
      · simp only [EReal.coe_neg, ne_eq, EReal.neg_eq_top_iff, EReal.coe_ne_bot,
        not_false_eq_true, EReal.toENNReal_of_ne_top, EReal.toReal_neg, EReal.toReal_coe,
        measurable_const]
      · apply Measurable.edist
        · apply Measurable.div
          · apply Finset.measurable_fun_sum
            intro x hx
            exact Measurable.comp (Measurable_log_ratio P μ X θ₀ θ) (hrv x)
          · exact measurable_const
        · exact measurable_const
end Likelihood
