import Mathlib


universe u v u_1 u_2

namespace MeasureTheory



def pdf_support {Ω : Type u_1} {E : Type u_2} [MeasurableSpace E]
  {h : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac):=
  Function.support (pdf X ℙ μ)

@[simp]
theorem mem_support_iff {Ω : Type u_1} {E : Type u_2} [MeasurableSpace E]
    {h : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac)
    (a : E) : a ∈ pdf_support X ℙ μ ↔ pdf X ℙ μ a ≠ 0 := Iff.rfl






end MeasureTheory

open TopologicalSpace Filter MeasureTheory
open scoped NNReal ENNReal MeasureTheory Topology


namespace MeasureTheory
lemma univ_tendsto_one {ι : Type*}
    {Ω : Type*} [MeasurableSpace Ω] (p : Measure Ω) [IsProbabilityMeasure p] {l : Filter ι} :
    Tendsto (fun (_ : ι) => p (Set.univ)) l (nhds 1) :=by
  simp only [MeasureTheory.measure_univ]
  exact tendsto_const_nhds

-- lemma tendsto_measure_compl_iff {α ι : Type*} [MeasurableSpace α]
--     {p : PMF α} {l : Filter ι} {s : ι → Set α}
--     (hs : ∀ i, MeasurableSet (s i)) :
--   (Tendsto (fun i => p.toMeasure (s i)) l (nhds 0))
--   ↔ (Tendsto (fun i => p.toMeasure ((s i)ᶜ)) l (nhds 1)):=by
--   have hcompl: ∀ (i: ι), p.toMeasure Set.univ - p.toMeasure (s i) = p.toMeasure (s i)ᶜ :=by
--     intro i
--     rw [← MeasureTheory.measure_compl]
--     · exact hs i
--     · exact MeasureTheory.measure_ne_top p.toMeasure (s i)
--   constructor
--   · intro h
--     have hsub := ENNReal.Tendsto.sub (univ_tendsto_one p (l := l)) h
--       (by left; exact ENNReal.one_ne_top)
--     simp_rw [hcompl, tsub_zero] at hsub
--     exact hsub
--   · intro h
--     have hsub := ENNReal.Tendsto.sub (univ_tendsto_one p (l := l)) h
--       (by left; exact ENNReal.one_ne_top)
--     simp_rw [fun (i: ι) => (hcompl i).symm, MeasureTheory.measure_univ, tsub_self] at hsub
--     have hone_sub_p: ∀ (i: ι), 1 - (1 - p.toMeasure (s i)) = p.toMeasure (s i) := by
--       intro i
--       refine ENNReal.sub_sub_cancel ENNReal.one_ne_top MeasureTheory.prob_le_one
--     simp_rw [hone_sub_p] at hsub
--     exact hsub



lemma tendsto_measure_compl_iff {ι Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω}
    [IsProbabilityMeasure p] {l : Filter ι} {s : ι → Set Ω} (hs : ∀ i, MeasurableSet (s i)) :
    (Tendsto (fun i => p (s i)) l (nhds 0))
    ↔ (Tendsto (fun i => p ((s i)ᶜ)) l (nhds 1)):=by
  have hcompl: ∀ (i: ι), p Set.univ - p (s i) = p (s i)ᶜ :=by
    intro i
    rw [← MeasureTheory.measure_compl]
    · exact hs i
    · exact MeasureTheory.measure_ne_top p (s i)
  constructor
  · intro h
    have hsub := ENNReal.Tendsto.sub (univ_tendsto_one p (l := l)) h
      (by left; exact ENNReal.one_ne_top)
    simp_rw [hcompl, tsub_zero] at hsub
    exact hsub
  · intro h
    have hsub := ENNReal.Tendsto.sub (univ_tendsto_one p (l := l)) h
      (by left; exact ENNReal.one_ne_top)
    simp_rw [fun (i: ι) => (hcompl i).symm, MeasureTheory.measure_univ, tsub_self] at hsub
    have hone_sub_p: ∀ (i: ι), 1 - (1 - p (s i)) = p (s i) := by
      intro i
      refine ENNReal.sub_sub_cancel ENNReal.one_ne_top MeasureTheory.prob_le_one
    simp_rw [hone_sub_p] at hsub
    exact hsub

end MeasureTheory

open Filter MeasureTheory ProbabilityTheory

/-- the *likelihood function* of the parameter `θ`
evaluated at the sample point `ω`, based on the first `n` observations of
the statistic `X` -/
noncomputable def Likelihood {Ω : Type*} [MeasurableSpace Ω]
    {ProbFunSet : Set (Measure Ω)} (f : ℝ → ProbFunSet)
    (X : ℕ → Ω → ℝ) (θ : ℝ) (n : ℕ) (μ : Measure ℝ := by volume_tac) : Ω → ENNReal :=
  fun ω => ∏ i : Fin n, pdf (X 0) (f θ) μ (X i ω)


namespace Likelihood


lemma pos_likelihood_lt
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] {ProbFunSet : Set (Measure Ω)}
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

lemma ne_top {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    {ProbFunSet : Set (Measure Ω)}
    (μ : Measure ℝ := by volume_tac)
    (f : ℝ → ↑ProbFunSet)
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (θ : ℝ) {s : NNReal}
    (hfs : ∀ (a : ℝ), pdf (X 0) ((f θ)) μ a ≤ s) :
    Likelihood f X θ n μ ω ≠ ⊤ := by
  unfold Likelihood
  apply ENNReal.prod_ne_top
  intro i hi
  apply LT.lt.ne_top (b := ⊤)
  refine lt_of_le_of_lt ?_ (ENNReal.coe_lt_top (r:=s))
  exact hfs (X i ω)


  -- ENNReal.prod_ne_top (fun x _ => LT.lt.ne_top
  --   (lt_of_le_of_lt (PMF.coe_le_one (f θ).1 (X x.1 ω)) ENNReal.one_lt_top))

lemma toReal_pos_likelihood_lt {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
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
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
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
      rw [smul_neg_iff_of_pos_left (by simp only [inv_pos, Nat.cast_pos]; omega)] at h
      rw [← Real.log_prod] at h
      · rw [Finset.prod_div_distrib, ← ENNReal.toReal_prod, ← ENNReal.toReal_prod,
          Real.log_neg_iff, div_lt_one, ENNReal.toReal_lt_toReal] at h
        · rw [gt_iff_lt]
          unfold Likelihood
          exact h
        · have h1 := by exact ne_top μ f X n ω θ (hfs θ)
          unfold Likelihood at h1
          exact h1
        · have h1:= by exact ne_top μ f X n ω θ₀ (hfs θ₀)
          unfold Likelihood at h1
          exact h1
        · have h1:= toReal_pos_likelihood_lt μ θ₀ n θ₀ hX h0 hfs
          unfold Likelihood at h1
          exact h1
        · rw [@div_pos_iff]
          left
          have h1:= toReal_pos_likelihood_lt μ θ₀ n θ₀ hX h0 hfs
          have h2:= toReal_pos_likelihood_lt μ θ₀ n θ hX h0 hfs
          unfold Likelihood at h1 h2
          exact ⟨h2, h1⟩
      · intro i hi
        rw [div_ne_zero_iff]
        refine ⟨Ne.symm (ne_of_lt (hfl θ (X i ω))) , Ne.symm (ne_of_lt (hfl θ₀ (X i ω)))⟩


example (f : PMF ℝ) (X : ℝ) (hX : X ∉ f.support) : f.toMeasure {X} = 0 :=by
  simp only [PMF.toMeasure]
  simp only [MeasurableSet.singleton, toMeasure_apply]
  rw [@PMF.toOuterMeasure_apply_eq_zero_iff]
  exact Set.disjoint_singleton_right.mpr hX

-- /-- The set of sample points `x`
-- for which the likelihood of parameter `θ₀` exceeds the likelihood of parameter
-- `θ` based on the first `n` observations of the statistic `X` -/
-- def likelihoodStrictSublevelSet
--     {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
--     (X : ℕ → Ω → ℝ) (n : ℕ) (θ₀ θ : ℝ)
--     {ProbFunSet : Set (Measure Ω)} (f : ℝ → ProbFunSet)
--     (μ : Measure ℝ := by volume_tac) : Set ℝ :=
--   {(x : ℝ) | Likelihood f X θ₀ n μ x> Likelihood f X θ n μ x}

noncomputable def logLR {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    (X : ℕ → Ω → ℝ) (θ₀ θ : ℝ)
    {ProbFunSet : Set (Measure Ω)} (f : ℝ → ProbFunSet)
    (μ : Measure ℝ := by volume_tac)
    (i : ℕ) (ω : Ω) : ℝ :=
  Real.log
    ((pdf (X i) (↑(f θ)) μ (X i ω)).toReal /
     (pdf (X i) (↑(f θ₀)) μ (X i ω)).toReal)

open scoped ProbabilityTheory

/-- the sequence of real-valued random variables
representing the *log-likelihood ratio* of parameter `θ` against the reference
parameter `θ₀` evaluated on the observations `X i` -/
noncomputable abbrev log_sum_ratio_rv {Ω : Type*} [MeasurableSpace Ω]
  {ProbFunSet : Set (Measure Ω)} (f : ℝ → ProbFunSet)
  (μ : Measure ℝ := by volume_tac)
  (X : ℕ → Ω → ℝ) (θ₀ θ : ℝ) : ℕ → Ω → ℝ :=
  fun i => fun (ω : Ω) =>
    Real.log ((pdf (X 0) (f θ).1 μ (X i ω)).toReal/ (pdf (X 0) (f θ₀).1 μ (X i ω)).toReal)

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

-- lemma Measurable_log_ratio'
--     {Ω : Type*} [MeasurableSpace Ω]
--     {ProbFunSet : Set (Measure Ω)} (f : ℝ → ↑ProbFunSet) (μ : Measure ℝ := by volume_tac)
--     (X : ℕ → Ω → ℝ) (θ₀ θ : ℝ)
--     (hX : ∀ (i : ℕ), Measurable (X i)) (i : ℕ) :
--     Measurable (log_sum_ratio_rv f μ X θ₀ θ i) :=
--   Measurable.comp (Measurable_log_ratio f μ X θ₀ θ) (hX i)

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
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    {ProbFunSet : Set (Measure Ω)} (μ : Measure ℝ := by volume_tac)
    [IsFiniteMeasure μ]
    (f : ℝ → ↑ProbFunSet) (θ₀ θ : ℝ)
    (X : ℕ → Ω → ℝ)
    [IsFiniteMeasure (f θ₀).1]
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
    (h : ∀ (x : ℝ), (pdf (X 0) (↑(f θ₀)) μ x).toReal ≠ 0):
    (∫ (x : Ω), (pdf (X 0) (↑(f θ)) μ (X 0 x)).toReal /
      (pdf (X 0) (↑(f θ₀)) μ (X 0 x)).toReal ∂(f θ₀).1) = 1 :=by
  let ν0 : Measure ℝ := Measure.map (X 0) (f θ₀).1
  have hmap :
      (∫ r : ℝ,
          (pdf (X 0) (↑(f θ)) μ r).toReal /
            (pdf (X 0) (↑(f θ₀)) μ r).toReal
        ∂ν0)
      =
      (∫ x : Ω,
          (pdf (X 0) (↑(f θ)) μ (X 0 x)).toReal /
            (pdf (X 0) (↑(f θ₀)) μ (X 0 x)).toReal
        ∂(f θ₀).1)
        := by
    -- `integral_map` needs measurability of X0
    have hfm : AEMeasurable (X 0) ↑(f θ₀) :=by exact Measurable.aemeasurable hXm
    have h1 := Measurable_log_ratio f μ X θ₀ θ

    have h2: AEStronglyMeasurable (fun r ↦ (pdf (X 0) (↑(f θ)) μ r).toReal /
      (pdf (X 0) (↑(f θ₀)) μ r).toReal)
      (Measure.map (X 0) ↑(f θ₀)) :=by
      have hmeas_num : Measurable fun r : ℝ => (pdf (X 0) (↑(f θ)) μ r).toReal := by
        apply Measurable.comp ENNReal.measurable_toReal
        exact measurable_pdf (X 0) (↑(f θ)) μ
      have hmeas_den : Measurable fun r : ℝ => (pdf (X 0) (↑(f θ₀)) μ r).toReal := by
        apply Measurable.comp ENNReal.measurable_toReal
        exact measurable_pdf (X 0) (↑(f θ₀)) μ
      have hmeas_ratio :
          Measurable (fun r : ℝ =>
            (pdf (X 0) (↑(f θ)) μ r).toReal /
            (pdf (X 0) (↑(f θ₀)) μ r).toReal) := by
        simpa using hmeas_num.div hmeas_den
      exact hmeas_ratio.aestronglyMeasurable
    simpa [ν0] using (MeasureTheory.integral_map (f := fun r =>
        (pdf (X 0) (↑(f θ)) μ r).toReal /
          (pdf (X 0) (↑(f θ₀)) μ r).toReal) (φ := X 0) (μ := (f θ₀).1 ) hfm h2)



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
      simp only [smul_eq_mul]

      have h2: ∀ (x : ℝ), (pdf (X 0) (↑(f θ₀)) μ x).toReal *
        ((pdf (X 0) (↑(f θ)) μ x).toReal / (pdf (X 0) (↑(f θ₀)) μ x).toReal) =
        (pdf (X 0) (↑(f θ)) μ x).toReal :=by
        intro x
        exact mul_div_cancel₀ (pdf (X 0) (↑(f θ)) μ x).toReal (h x)

      simp_rw [h2]

  have h2: ((f θ).1 Set.univ).toReal = 1 := by
    rw [isProbabilityMeasure_iff.mp]
    · rfl
    · (expose_names; exact inst_2)
  rw [← h2]

  have h3:= pdf.lintegral_eq_measure_univ (X := X 0) (μ := μ) (E:= ℝ) («ℙ» := (f θ).1)
  rw [← h3]
  exact integral_toReal hAM htop2


lemma edist_compl_ball {α : Type*} (μ : ℝ) (S : α → ℝ) :
    {x | ENNReal.ofReal (- μ ) ≤ edist (S x) μ}ᶜ ⊆ {x | (S x) < 0}:= by
  intro x hS
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, edist_lt_ofReal] at hS
  simp only [Set.mem_setOf_eq]
  have h := add_lt_add_of_lt_of_le (lt_of_le_of_lt (Real.sub_le_dist (S x) μ ) hS)
    (le_refl ((μ) ))
  rw [add_comm, ← add_sub_assoc, add_comm, add_sub_assoc] at h
  simp only [neg_add_cancel, sub_self, add_zero] at h
  exact h

-- lemma temp{Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
--     {ProbFunSet : Set (Measure Ω)} (μ : Measure ℝ := by volume_tac)
--     [IsFiniteMeasure μ]
--     (f : ℝ → ↑ProbFunSet) (θ₀ : ℝ)
--     (X : ℕ → Ω → ℝ) (θ : ℝ)
--     [IsFiniteMeasure (f θ₀).1]
--     (hint0 : Integrable (X 0) (f θ₀).1)
--     (hX : ∀ (n: ℕ), ∀ (x: ℝ), ∀ (i : Fin n), x ∈ pdf_support (X i) (f θ₀).1 μ)
--     (h0 : ∀ (n: ℕ), ∀ (i : Fin n), ∀ (θ₁ θ₂ : ℝ), pdf_support (X i) (f θ₁).1 μ
--       = pdf_support (X i) (f θ₂).1 μ)
--     {s : NNReal}
--     (hfs : ∀ (n: ℕ), ∀ (θ : ℝ), ∀ (i : Fin n), ∀ (a : ℝ), pdf (X i) ((f θ)) μ a ≤ s)
--     (hfl : ∀ (n: ℕ), ∀ (θ : ℝ), ∀ (i : Fin n), ∀ (a : ℝ), 0 < (pdf (X i) ((f θ)) μ a).toReal)
--     {S : Set ℝ} {hs1 : S ⊆ (Set.Iio 0)} {hs2 : Convex ℝ S}
--     {hs3 : ContinuousOn Real.log S} {hs4 : IsClosed S}
--     (hrv : ∀ (i : ℕ), Measurable (X i))
--     (hMeasurable : ∀ (θ : ℝ), Measurable (f θ).1.1)
--     (hindep: Pairwise (Function.onFun (fun x1 x2 ↦ x1 ⟂ᵢ[↑(f θ₀)] x2) X))
--     (hident: ∀ (i : ℕ), IdentDistrib (X i) (X 0) ↑(f θ₀) ↑(f θ₀))
--     {hs5 : ∀ (i : ℕ), ∀ (x : ℝ), (pdf (X ↑i) (↑(f θ)) μ x).toReal / (pdf (X ↑i) (↑(f θ₀)) μ x).toReal ∈ S}
--     (hint1 : ∀ (n : ℕ), ∀ (i: Fin n),
--       Integrable (fun x ↦ (pdf (X ↑i) (↑(f θ)) μ x).toReal / (pdf (X ↑i) (↑(f θ₀)) μ x).toReal) μ)
--     (hint2 : ∀ (n : ℕ), ∀ (i: Fin n),
--       Integrable (Real.log ∘ fun x ↦ (pdf (X ↑i) (↑(f θ)) μ x).toReal / (pdf (X ↑i) (↑(f θ₀)) μ x).toReal) μ)
--     (hProb : ∀ (n : ℕ), IsProbabilityMeasure (Measure.map (X n) (f θ₀).1))
--     (a : ℕ): ∀ (n : ℕ), {x | (n: ℝ)⁻¹ • ∑ (i: Fin n ),
--     Real.log ((pdf (X ↑i) (↑(f θ)) μ x).toReal /
--     (pdf (X ↑i) (↑(f θ₀)) μ x).toReal) < 0} = ⊤ := by
--   intro n
--   ext x
--   simp only [Set.mem_setOf_eq, Set.top_eq_univ, Set.mem_univ, iff_true]
--   simp?
--   -- al.log
--   --   (∫ (x : ℝ),
--   --     (fun x ↦ (fun x ↦ (↑↑(f θ) (X 0 x)).toReal / (↑↑(f θ₀) (X 0 x)).toReal) x)
--   --       x ∂((↑(f θ₀)).toMeasure Set.univ)⁻¹ • (↑(f θ₀)).toMeasure)
--   have h: ∫ (x : ℝ), (n: ℝ)⁻¹ •
--     Real.log ((pdf (X ↑i) (↑(f θ)) μ x).toReal /
--     (pdf (X ↑i) (↑(f θ₀)) μ x).toReal) < 0


--   #check (StrictConcaveOn.ae_eq_const_or_lt_map_average (f:=
--       (fun (i : Fin n) => (pdf (X i) (f θ).1 μ x).toReal / (pdf (X i) (f θ₀).1 μ x).toReal)) (g:= Real.log)
--       (StrictConcaveOn.subset strictConcaveOn_log_Iio hs1 hs2) hs3 hs4 ?_ (hint1 n i)
--       (hint2 n i))

--   have hJensen :
--     ∀ (n : ℕ), ∀ (i: Fin n),
--     (fun (i : Fin n) ↦  (pdf (X ↑i) (↑(f θ)) μ x).toReal / (pdf (X ↑i) (↑(f θ₀)) μ x).toReal) =ᶠ[ae μ]
--     Function.const ℝ (⨍ (i : Fin n), (pdf (X ↑i) (↑(f θ)) μ x).toReal / (pdf (X ↑i) (↑(f θ₀)) μ x).toReal ∂μ) ∨
--     ⨍ (x : ℝ), Real.log ((pdf (X ↑i) (↑(f θ)) μ x).toReal / (pdf (X ↑i) (↑(f θ₀)) μ x).toReal) ∂μ <
--     Real.log (⨍ (x : ℝ), (pdf (X ↑i) (↑(f θ)) μ x).toReal / (pdf (X ↑i) (↑(f θ₀)) μ x).toReal ∂μ)
--     :=by
--     intro n i
--     exact
--       (StrictConcaveOn.ae_eq_const_or_lt_map_average (f:=
--       (fun (i : Fin n) ↦  (pdf (X ↑i) (↑(f θ)) μ x).toReal / (pdf (X ↑i) (↑(f θ₀)) μ x).toReal))
--       (g:= Real.log)
--       (StrictConcaveOn.subset strictConcaveOn_log_Iio hs1 hs2) hs3 hs4 ?_ ?_ ?_)







theorem likelihood_consistency_sublevel_measure_tendsto_one
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    {ProbFunSet : Set (Measure Ω)}
    [FunLike (↑ProbFunSet) (Set Ω) ℝ≥0∞]
    [OuterMeasureClass (↑ProbFunSet) Ω]
    (μ : Measure ℝ := by volume_tac)
    [IsFiniteMeasure μ]
    (f : ℝ → ↑ProbFunSet) (θ₀ : ℝ)
    (X : ℕ → Ω → ℝ) (θ : ℝ)
    [IsProbabilityMeasure (f θ₀).1] [IsProbabilityMeasure (f θ).1]
    [HasPDF (X 0) (↑(f θ)) μ] [HasPDF (X 0) (↑(f θ₀)) μ]
    (hX : ∀ (n : ℕ), ∀ (ω : Ω), ∀ (i : Fin n), (X i ω) ∈ pdf_support (X 0) (f θ₀).1 μ)
    (h0 : ∀ (θ₁ θ₂ : ℝ), pdf_support (X 0) (f θ₁).1 μ
      = pdf_support (X 0) (f θ₂).1 μ)
    {s : NNReal}
    (hfs : ∀ (θ : ℝ), ∀ (a : ℝ), pdf (X 0) ((f θ)) μ a ≤ s)
    (hfl : ∀ (θ : ℝ), ∀ (a : ℝ), 0 < (pdf (X 0) ((f θ)) μ a).toReal)
    {S : Set ℝ} {hs1 : S ⊆ (Set.Iio 0)} {hs2 : Convex ℝ S}
    {hs3 : ContinuousOn Real.log S} {hs4 : IsClosed S}
    (hrv : ∀ (i : ℕ), Measurable (X i))
    (hindep : iIndepFun X ↑(f θ₀))
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) (f θ₀) (f θ₀))
    {hs5 : ∀ᵐ (x : Ω) ∂(f θ₀).1, (pdf (X 0) (↑(f θ)) μ (X 0 x)).toReal /
      (pdf (X 0) (↑(f θ₀)) μ (X 0 x)).toReal ∈ S}
    (hint1 : Integrable (Real.log ∘ fun ω ↦ (pdf (X 0) (↑(f θ)) μ (X 0 ω)).toReal /
      (pdf (X 0) (↑(f θ₀)) μ (X 0 ω)).toReal) ↑(f θ₀))
    (hint2 : Integrable (fun ω ↦ (pdf (X 0) (↑(f θ)) μ (X 0 ω)).toReal /
      (pdf (X 0) (↑(f θ₀)) μ (X 0 ω)).toReal) ↑(f θ₀))
    (hint0 : Integrable (log_sum_ratio_rv f μ X θ₀ θ 0) (f θ₀).1)
    (hne_const : ¬ ((fun ω ↦ ((pdf (X 0) (↑(f θ)) μ (X 0 ω)).toReal /
      (pdf (X 0) (↑(f θ₀)) μ (X 0 ω)).toReal)) =ᶠ[ae (f θ₀).1]
  Function.const Ω
    (⨍ (x : Ω),
      (fun ω ↦ ((pdf (X 0) (↑(f θ)) μ (X 0 ω)).toReal /
      (pdf (X 0) (↑(f θ₀)) μ (X 0 ω)).toReal)) x ∂↑(f θ₀))))
    :
    Tendsto (fun n : ℕ => ((f θ₀).1) {ω : Ω |
       Likelihood f X θ₀ n μ ω > Likelihood f X θ n μ ω}) atTop (𝓝 1)
 := by
    have htop1 : ∀ᵐ (x : ℝ) ∂μ, pdf (X 0) (↑(f θ)) μ x < ⊤ :=
      Measure.rnDeriv_lt_top (Measure.map (X 0) ↑(f θ)) μ
    have htop2 : ∀ᵐ (x : ℝ) ∂μ, pdf (X 0) (↑(f θ₀)) μ x < ⊤ :=
      Measure.rnDeriv_lt_top (Measure.map (X 0) ↑(f θ₀)) μ
    simp_rw [fun (n: ℕ)=> fun (ω : Ω) =>
      likelihood_iff_log_sum_ratio μ f θ₀ X n ω θ (hX n ω) h0 hfs hfl]
    have hident2 : ∀ (i : ℕ), IdentDistrib (log_sum_ratio_rv f μ X θ₀ θ i)
      (log_sum_ratio_rv f μ X θ₀ θ 0) ↑(f θ₀) ↑(f θ₀) :=by
      exact fun i ↦ IdentDistrib_log_sum_ratio μ f θ₀ θ X hident i
    have hpair :
      Pairwise (Function.onFun (fun x1 x2 ↦ x1 ⟂ᵢ[↑(f θ₀)] x2) (log_sum_ratio_rv f μ X θ₀ θ)) :=by
      classical
      intro i j hij
      simp only [Function.onFun]
      unfold log_sum_ratio_rv
      simpa [Function.onFun] using (iIndepFun_log_sum_ratio μ f θ₀ θ X hindep).indepFun
        hij



    have hlaw := MeasureTheory.tendstoInMeasure_of_tendsto_ae_of_measurable_edist (μ  := (f θ₀).1)
      (Measurable_edist_log_sum_ratio μ f θ₀ θ X hrv)
      (ProbabilityTheory.strong_law_ae_real (log_sum_ratio_rv f μ X θ₀ θ) hint0 hpair hident2)
    have hJensen := StrictConcaveOn.ae_eq_const_or_lt_map_average (μ:= (f θ₀).1) (f:=
      fun (ω : Ω) => ((pdf (X 0) (f θ).1 μ (X 0 ω)).toReal/ (pdf (X 0) (f θ₀).1 μ (X 0 ω)).toReal))
      (g:= Real.log)
      (StrictConcaveOn.subset strictConcaveOn_log_Iio hs1 hs2) hs3 hs4 hs5 hint2 hint1


    generalize hε: ∫ (ω : Ω), log_sum_ratio_rv f μ X θ₀ θ 0 ω ∂↑(f θ₀) = ε at *

    unfold TendstoInMeasure at hlaw
    have hε_le_0 : 0 < ((- ε).toEReal).toENNReal := by
      cases hJensen with
      | inl hp => exact False.elim (hne_const hp)
      | inr hJensen =>
          unfold average at hJensen
          simp only [measure_univ, inv_one, one_smul] at hJensen
          rw [← hε]
          rw [integral_sum_ratio_eq_one μ f θ₀ θ X (hrv 0) htop2 htop1] at hJensen
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
              (MeasureTheory.measurable_pdf (X 0) ((↑(f θ) : Measure Ω)) (μ := μ)).aemeasurable
          · intro x
            have hpos : 0 < (pdf (X 0) (↑(f θ₀)) μ x).toReal := by
              simpa using (hfl θ₀ x)
            exact ne_of_gt hpos

    specialize hlaw ((- ε).toEReal).toENNReal hε_le_0
    rw [tendsto_measure_compl_iff] at hlaw
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlaw (univ_tendsto_one (f θ₀).1)
      · intro n
        simp only [EReal.coe_neg, ne_eq, EReal.neg_eq_top_iff, EReal.coe_ne_bot,
                  not_false_eq_true, EReal.toENNReal_of_ne_top, EReal.toReal_neg, EReal.toReal_coe,
                  smul_eq_mul]
        apply ((f θ₀).1).mono
        simp_rw [← Fin.sum_univ_eq_sum_range, log_sum_ratio_rv, div_eq_mul_inv, mul_comm]
        apply edist_compl_ball
      · intro x
        simp only [smul_eq_mul, measure_univ]
        simpa using (prob_le_one (μ := (f θ₀).1) (s := _))
    · intro i
      apply measurableSet_le
      · simp only [EReal.coe_neg, ne_eq, EReal.neg_eq_top_iff, EReal.coe_ne_bot,
        not_false_eq_true, EReal.toENNReal_of_ne_top, EReal.toReal_neg, EReal.toReal_coe,
        measurable_const]
      · apply Measurable.edist
        · apply Measurable.div
          · apply Finset.measurable_fun_sum
            intro x hx
            exact Measurable.comp (Measurable_log_ratio f μ X θ₀ θ) (hrv x)
          · exact measurable_const
        · exact measurable_const
