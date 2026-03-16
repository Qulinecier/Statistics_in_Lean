import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import MLE.Defs

open MeasureTheory

namespace Likelihood

lemma pos_likelihood_lt
    {Ω : Type*} [MeasurableSpace Ω] {ProbFunSet : Set (Measure Ω)}
    {f : ℝ → ↑ProbFunSet} {θ₀ : ℝ} {μ : Measure ℝ}
    {X : ℕ → Ω → ℝ} (n : ℕ) {θ : ℝ} {ω : Ω}
    (h0 : ∀ (θ₁ θ₂ : ℝ), pdf_support (X 0) (f θ₁).1 μ
      = pdf_support (X 0) (f θ₂).1 μ)
    (hX : ∀ (i : Fin n), (X i ω) ∈ pdf_support (X 0) (f θ₀).1 μ)
    :(0 < Likelihood f X θ n μ ω):= by
  apply pos_of_ne_zero
  by_contra h'
  unfold Likelihood at h'
  rw [Finset.prod_eq_zero_iff] at h'
  obtain ⟨i, hi, h'⟩ := h'
  specialize hX i
  specialize h0 θ₀ θ
  rw [h0] at hX
  exact hX h'

lemma ne_top {Ω : Type*} [MeasurableSpace Ω]
    {ProbFunSet : Set (Measure Ω)}
    (μ : Measure ℝ := by volume_tac)
    (f : ℝ → ↑ProbFunSet)
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (θ : ℝ) {s : NNReal}
    (hfs : ∀ (a : ℝ), pdf (X 0) ((f θ)) μ a ≤ s) :
    Likelihood f X θ n μ ω ≠ ⊤ := by
  unfold Likelihood
  apply ENNReal.prod_ne_top
  intro i hi
  exact LT.lt.ne_top (b := ⊤) (lt_of_le_of_lt (hfs (X i ω)) (ENNReal.coe_lt_top (r:=s)))

lemma toReal_pos_likelihood_lt {Ω : Type*} [MeasurableSpace Ω]
    {ProbFunSet : Set (Measure Ω)} (μ : Measure ℝ := by volume_tac)
    {f : ℝ → ↑ProbFunSet} (θ₀ : ℝ)
    {X : ℕ → Ω → ℝ} (n : ℕ) {ω : Ω} (θ : ℝ)
    (hX : ∀ (i : Fin n), (X i ω) ∈ pdf_support (X 0) (f θ₀).1 μ)
    (h0 : ∀ (θ₁ θ₂ : ℝ), pdf_support (X 0) (f θ₁).1 μ
      = pdf_support (X 0) (f θ₂).1 μ)
    {s : NNReal}
    (hfs : ∀ (θ : ℝ), ∀ (a : ℝ), pdf (X 0) ((f θ)) μ a ≤ s) :
    0 < (Likelihood f X θ n μ ω).toReal:= by
  rw [← ENNReal.toReal_zero, ENNReal.toReal_lt_toReal (ENNReal.zero_ne_top)]
  · exact pos_likelihood_lt n h0 hX
  · exact ne_top μ f X n ω θ (hfs θ)

lemma likelihood_iff_log_sum_ratio
    {Ω : Type*} [MeasurableSpace Ω]
    {ProbFunSet : Set (Measure Ω)} (μ : Measure ℝ := by volume_tac)
    (f : ℝ → ↑ProbFunSet) (θ₀ : ℝ)
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (θ : ℝ)
    (hX : ∀ (i : Fin n), (X i ω) ∈ pdf_support (X 0) (f θ₀).1 μ)
    (h0 : ∀ (θ₁ θ₂ : ℝ), pdf_support (X 0) (f θ₁).1 μ
      = pdf_support (X 0) (f θ₂).1 μ)
    {s : NNReal}
    (hfs : ∀ (θ : ℝ), ∀ (a : ℝ), pdf (X 0) ((f θ)) μ a ≤ s)
    (hfl : ∀ (θ : ℝ), ∀ (a : ℝ), 0 < (pdf (X 0) ((f θ)) μ a).toReal) :
    (Likelihood f X θ₀ n μ ω > Likelihood f X θ n μ ω)
    ↔ (((n: ℝ)⁻¹• (∑ (i: Fin n),
    Real.log ((pdf (X 0) (f θ).1 μ (X i ω)).toReal/
    (pdf (X 0) (f θ₀).1 μ (X i ω)).toReal)) <0)) := by
  by_cases hn: n=0
  · rw [hn]
    unfold Likelihood
    simp only [Finset.univ_eq_empty, Finset.prod_empty, gt_iff_lt, lt_self_iff_false,
      CharP.cast_eq_zero, inv_zero, Finset.sum_empty, smul_eq_mul, mul_zero]
  · constructor
    · intro h
      refine (smul_neg_iff_of_pos_left ?_).mpr ?_
      · simp only [inv_pos, Nat.cast_pos]
        omega
      · rw [gt_iff_lt, ← ENNReal.toReal_lt_toReal (ne_top μ f X n ω θ (hfs θ))
          (ne_top μ f X n ω θ₀ (hfs θ₀)),
          ← div_lt_one] at h
        · rw [← Real.log_neg_iff] at h
          · unfold Likelihood at h
            rw [ENNReal.toReal_prod, ENNReal.toReal_prod, ← Finset.prod_div_distrib,
              Real.log_prod] at h
            · exact h
            · intro i hi
              rw [@div_ne_zero_iff]
              refine ⟨Ne.symm (ne_of_lt (hfl θ (X i ω))), Ne.symm (ne_of_lt (hfl θ₀ (X i ω)))⟩
          · rw [@div_pos_iff]
            left
            refine ⟨toReal_pos_likelihood_lt μ θ₀ n θ hX h0 hfs,
              toReal_pos_likelihood_lt μ θ₀ n θ₀ hX h0 hfs⟩
        · exact toReal_pos_likelihood_lt μ θ₀ n θ₀ hX h0 hfs
    · intro h
      rw [smul_neg_iff_of_pos_left (by simp only [inv_pos, Nat.cast_pos]; omega),
        ← Real.log_prod] at h
      · rw [Finset.prod_div_distrib, ← ENNReal.toReal_prod, ← ENNReal.toReal_prod,
          Real.log_neg_iff, div_lt_one, ENNReal.toReal_lt_toReal] at h
        · rw [gt_iff_lt]
          exact h
        · exact ne_top μ f X n ω θ (hfs θ)
        · exact ne_top μ f X n ω θ₀ (hfs θ₀)
        · exact toReal_pos_likelihood_lt μ θ₀ n θ₀ hX h0 hfs
        · rw [@div_pos_iff]
          left
          exact ⟨toReal_pos_likelihood_lt μ θ₀ n θ hX h0 hfs,
            toReal_pos_likelihood_lt μ θ₀ n θ₀ hX h0 hfs⟩
      · intro i hi
        rw [div_ne_zero_iff]
        refine ⟨Ne.symm (ne_of_lt (hfl θ (X i ω))) , Ne.symm (ne_of_lt (hfl θ₀ (X i ω)))⟩

open ProbabilityTheory

lemma Measurable_log_ratio
    {Ω : Type*} [MeasurableSpace Ω]
    {ProbFunSet : Set (Measure Ω)} (f : ℝ → ↑ProbFunSet) (μ : Measure ℝ := by volume_tac)
    (X : ℕ → Ω → ℝ) (θ₀ θ : ℝ) :
    Measurable
    fun x ↦ Real.log ((pdf (X 0) (↑(f θ)) μ x).toReal / (pdf (X 0) (↑(f θ₀)) μ x).toReal) := by
  apply Measurable.comp (Real.measurable_log)
  apply Measurable.div
  · apply Measurable.comp ENNReal.measurable_toReal
    exact MeasureTheory.measurable_pdf (X := X 0) («ℙ» := (f θ).1) (μ := μ)
  · apply Measurable.comp ENNReal.measurable_toReal
    exact MeasureTheory.measurable_pdf (X := X 0) («ℙ» := (f θ₀).1) (μ := μ)

lemma iIndepFun_log_sum_ratio {Ω : Type*} [MeasurableSpace Ω]
    {ProbFunSet : Set (Measure Ω)}
    (μ : Measure ℝ := by volume_tac)
    (f : ℝ → ↑ProbFunSet) (θ₀ θ : ℝ) (X : ℕ → Ω → ℝ)
    (hindep : iIndepFun X ((f θ₀))) :
    iIndepFun (log_sum_ratio_rv f μ X θ₀ θ) (f θ₀):=by
  unfold log_sum_ratio_rv
  apply iIndepFun.comp hindep (fun (i : ℕ) => fun (x : ℝ) =>
    Real.log ((pdf (X 0) (f θ).1 μ x).toReal/ (pdf (X 0) (f θ₀).1 μ x).toReal))
  intro i
  exact Measurable_log_ratio f μ X θ₀ θ

lemma IdentDistrib_log_sum_ratio
    {Ω : Type*} [MeasurableSpace Ω]
    {ProbFunSet : Set (Measure Ω)}
    (μ : Measure ℝ := by volume_tac)
    (f : ℝ → ↑ProbFunSet) (θ₀ θ : ℝ) (X : ℕ → Ω → ℝ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) (f θ₀) (f θ₀)) :
    ∀ i, IdentDistrib ((log_sum_ratio_rv f μ X θ₀ θ) i) ((log_sum_ratio_rv f μ X θ₀ θ) 0)
    (f θ₀) (f θ₀):=by
  intro i
  specialize hident i
  unfold log_sum_ratio_rv
  apply IdentDistrib.comp hident
    (u:= fun x => Real.log ((pdf (X 0) (f θ).1 μ x).toReal/ (pdf (X 0) (f θ₀).1 μ x).toReal))
  exact Measurable_log_ratio f μ X θ₀ θ

lemma Measurable_edist_log_sum_ratio
    {Ω : Type*} [MeasurableSpace Ω]
    {ProbFunSet : Set (Measure Ω)} (μ : Measure ℝ := by volume_tac)

    (f : ℝ → ↑ProbFunSet) (θ₀ θ : ℝ)
    (X : ℕ → Ω → ℝ)

    (hrv : ∀ (i : ℕ), Measurable (X i)) :
    ∀ (n : ℕ), Measurable fun (ω : Ω) ↦ edist ((∑ i ∈ Finset.range n,
    (log_sum_ratio_rv f μ X θ₀ θ i ω))/n)
      (∫ (ω : Ω), (log_sum_ratio_rv f μ X θ₀ θ) 0 ω ∂(f θ₀).1) := by
  intro n
  unfold log_sum_ratio_rv
  apply Measurable.edist
  · apply Measurable.div
    · apply Finset.measurable_fun_sum
      intro i hi
      refine Measurable.comp (Measurable_log_ratio f μ X θ₀ θ) (hrv i)
    · simp only [measurable_const]
  · simp only [measurable_const]

/-- Under the true parameter `θ₀`, the expectation of the density ratio
`f_θ (X 0) / f_θ₀ (X 0)` equals `1`. -/
lemma integral_sum_ratio_eq_one
    {Ω : Type*} [MeasurableSpace Ω]
    {ProbFunSet : Set (Measure Ω)}
    (μ : Measure ℝ := by volume_tac)
    (f : ℝ → ↑ProbFunSet) (θ₀ θ : ℝ) [IsProbabilityMeasure (f θ₀).1] [IsProbabilityMeasure (f θ).1]
    (X : ℕ → Ω → ℝ)
    (hXm : Measurable (X 0))
    (htop : ∀ᵐ (x : ℝ) ∂μ, pdf (X 0) (↑(f θ₀)) μ x < ⊤)
    (htop2 : ∀ᵐ (x : ℝ) ∂μ, pdf (X 0) (↑(f θ)) μ x < ⊤)
    [HasPDF (X 0) (↑(f θ)) μ] [HasPDF (X 0) (↑(f θ₀)) μ]
    (hAM : AEMeasurable (pdf (X 0) (↑(f θ)) μ) μ)
    (h : ∀ (x : ℝ), (pdf (X 0) (↑(f θ₀)) μ x).toReal ≠ 0) :
    (∫ (x : Ω), (pdf (X 0) (↑(f θ)) μ (X 0 x)).toReal /
      (pdf (X 0) (↑(f θ₀)) μ (X 0 x)).toReal ∂(f θ₀).1) = 1 :=by
  let ν0 : Measure ℝ := Measure.map (X 0) (f θ₀).1
  have hmap :(∫ r : ℝ, (pdf (X 0) (↑(f θ)) μ r).toReal /
      (pdf (X 0) (↑(f θ₀)) μ r).toReal ∂ν0) =
      (∫ x : Ω, (pdf (X 0) (↑(f θ)) μ (X 0 x)).toReal /
      (pdf (X 0) (↑(f θ₀)) μ (X 0 x)).toReal ∂(f θ₀).1) := by
    suffices AEStronglyMeasurable (fun r ↦ (pdf (X 0) (↑(f θ)) μ r).toReal /
        (pdf (X 0) (↑(f θ₀)) μ r).toReal) (Measure.map (X 0) ↑(f θ₀)) by
      simpa [ν0] using (MeasureTheory.integral_map (f := fun r =>
          (pdf (X 0) (↑(f θ)) μ r).toReal /
            (pdf (X 0) (↑(f θ₀)) μ r).toReal) (φ := X 0) (μ := (f θ₀).1 )
            (Measurable.aemeasurable hXm) this)
    exact ((Measurable.comp ENNReal.measurable_toReal (measurable_pdf (X 0) (↑(f θ)) μ)).div
      (Measurable.comp ENNReal.measurable_toReal
      (measurable_pdf (X 0) (↑(f θ₀)) μ))).aestronglyMeasurable

  have hν0 : μ.withDensity (pdf (X 0) (↑(f θ₀)) μ) = ν0 :=
    Eq.symm (map_eq_withDensity_pdf (X 0) (↑(f θ₀)) μ)

  rw [← hmap]

  calc
    _   = (∫ r : ℝ,
              (pdf (X 0) (↑(f θ)) μ r).toReal /
                (pdf (X 0) (↑(f θ₀)) μ r).toReal
            ∂(μ.withDensity (pdf (X 0) (↑(f θ₀)) μ))) := by
      simp only [hν0]
    _   = (∫ r : ℝ, (pdf (X 0) (↑(f θ)) μ r).toReal ∂μ) := by
      rw [integral_withDensity_eq_integral_toReal_smul (measurable_pdf (X 0) (↑(f θ₀)) μ) htop]
      simp_rw [smul_eq_mul, fun x => mul_div_cancel₀ (pdf (X 0) (↑(f θ)) μ x).toReal (h x)]

  have h: ((f θ).1 Set.univ).toReal = 1 := by
    rw [isProbabilityMeasure_iff.mp]
    · rfl
    · (expose_names; exact inst_2)

  rw [← h, ← (pdf.lintegral_eq_measure_univ (X := X 0) (μ := μ) (E:= ℝ) («ℙ» := (f θ).1))]
  exact integral_toReal hAM htop2

end Likelihood

lemma Measurable_log_Likelihood
    {Ω : Type*} [MeasurableSpace Ω]
    {ProbFunSet : Set (Measure Ω)} (f : ℝ → ↑ProbFunSet) (μ : Measure ℝ := by volume_tac)
    {X : ℕ → Ω → ℝ} (θ₀ : ℝ) (k : ℕ) (hrv : ∀ (i : ℕ), Measurable (X i)) :
    Measurable
    (fun ω : Ω => log_Likelihood f X θ₀ k μ ω) := by
  unfold log_Likelihood
  apply Finset.measurable_sum Finset.univ
  intro i hi
  apply Measurable.ennreal_log
  apply Measurable.comp
  · exact MeasureTheory.measurable_pdf (X := X 0) («ℙ» := (f θ₀).1) (μ := μ)
  · exact hrv ↑i
