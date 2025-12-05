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

open TopologicalSpace Filter
open scoped NNReal ENNReal MeasureTheory Topology

namespace PMF

lemma univ_tendsto_one {α ι : Type*} [MeasurableSpace α]
    (p : PMF α) {l : Filter ι} :
    Tendsto (fun (_ : ι) => p.toMeasure (Set.univ)) l (nhds 1) :=by
  simp only [MeasureTheory.measure_univ]
  exact tendsto_const_nhds

lemma tendsto_measure_compl_iff {α ι : Type*} [MeasurableSpace α]
    {p : PMF α} {l : Filter ι} {s : ι → Set α}
    (hs : ∀ i, MeasurableSet (s i)) :
  (Tendsto (fun i => p.toMeasure (s i)) l (nhds 0))
  ↔ (Tendsto (fun i => p.toMeasure ((s i)ᶜ)) l (nhds 1)):=by
  have hcompl: ∀ (i: ι), p.toMeasure Set.univ - p.toMeasure (s i) = p.toMeasure (s i)ᶜ :=by
    intro i
    rw [← MeasureTheory.measure_compl]
    · exact hs i
    · exact MeasureTheory.measure_ne_top p.toMeasure (s i)
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
    have hone_sub_p: ∀ (i: ι), 1 - (1 - p.toMeasure (s i)) = p.toMeasure (s i) := by
      intro i
      refine ENNReal.sub_sub_cancel ENNReal.one_ne_top MeasureTheory.prob_le_one
    simp_rw [hone_sub_p] at hsub
    exact hsub

end PMF

open Filter MeasureTheory ProbabilityTheory


/-- the *likelihood function* of the parameter `θ`
evaluated at the sample point `ω`, based on the first `n` observations of
the statistic `X` -/
noncomputable def Likelihood
    {Ω : Type*} [MeasurableSpace Ω] {ProbFunSet : Set (Measure Ω)}
    (f : ℝ → ProbFunSet) (X : ℕ → Ω → ℝ) (θ : ℝ) (n : ℕ) (μ : Measure ℝ := by volume_tac)
    := ∏ (i : Fin (n)), pdf (X i) (f θ).1 μ

namespace Likelihood


lemma pos_likelihood_lt
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] {ProbFunSet : Set (Measure Ω)}
    (f : ℝ → ↑ProbFunSet) {θ₀ : ℝ} {μ : Measure ℝ}
    (X : ℕ → Ω → ℝ) (n : ℕ) (θ : ℝ) (x : ℝ)
    (h0 : ∀ (i : Fin n), ∀ (θ₁ θ₂ : ℝ), pdf_support (X i) (f θ₁).1 μ
      = pdf_support (X i) (f θ₂).1 μ)
    (hX : ∀ (i : Fin n), x ∈ pdf_support (X i) (f θ₀).1 μ)
    :(0 < Likelihood f X θ n μ x):= by
  apply pos_of_ne_zero
  by_contra h'
  unfold Likelihood at h'
  simp only [Finset.prod_apply] at h'
  rw [Finset.prod_eq_zero_iff] at h'
  obtain ⟨i, hi, h'⟩ := h'
  specialize hX i
  specialize h0 i θ₀ θ
  rw [h0] at hX
  exact hX h'

lemma ne_top {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    {ProbFunSet : Set (Measure Ω)}

    (μ : Measure ℝ := by volume_tac)
    (f : ℝ → ↑ProbFunSet)
    {h : ∀ (θ: ℝ), IsFiniteMeasure (f θ).1}
    (θ₀ : ℝ)
    (X : ℕ → Ω → ℝ) (n : ℕ) (x : ℝ) (θ : ℝ)
    (hX : ∀ (i : Fin n), x ∈ pdf_support (X i) (f θ₀).1 μ)
    (h0 : ∀ (i : Fin n), ∀ (θ₁ θ₂ : ℝ), pdf_support (X i) (f θ₁).1
      = pdf_support (X i) (f θ₂).1) :
  ∀ᵐ (x : ℝ) ∂μ, Likelihood f X θ n μ x ≠ ⊤ := by
  unfold Likelihood
  simp only [Finset.prod_apply]
  rw [MeasureTheory.ae_iff]
  have h: {a | ¬ ∀ (c : Fin n), pdf (X ↑c) (↑(f θ)) μ a ≠ ⊤}
    ⊆ {a | ¬ ∏ (c : Fin n), pdf (X ↑c) (↑(f θ)) μ a ≠ ⊤} := by
    simp only [ne_eq, not_forall, Decidable.not_not, Set.setOf_subset_setOf, forall_exists_index]
    intro a i h

    apply ENNReal.prod_eq_top



  intro i hi
  apply LT.lt.ne_top (b := ⊤)



  apply MeasureTheory.pdf.ae_lt_top


  ·
  have h := MeasureTheory.pdf.ae_lt_top (ℙ := (f θ).1) (μ := μ)
  refine lt_of_le_of_lt ?_ ENNReal.one_lt_top



  #check ENNReal.one_lt_top

  -- ENNReal.prod_ne_top (fun x _ => LT.lt.ne_top
  --   (lt_of_le_of_lt (PMF.coe_le_one (f θ).1 (X x.1 ω)) ENNReal.one_lt_top))

-- lemma toReal_pos_likelihood_lt {ProbFunSet : Set (PMF ℝ)} (f : ℝ → ↑ProbFunSet)
--     {θ₀ : ℝ} {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (θ : ℝ)
--     (h0 : ∀ (θ₁ θ₂ : ℝ), (f θ₁).1.support = (f θ₂).1.support)
--     (hX : ∀ (i : Fin n), (X i ω) ∈ (f θ₀).1.support) :
--     0 < (∏ (i: Fin (n)), (f θ).1.1 (X (i) ω)).toReal:= by
--   rw [← ENNReal.toReal_zero, ENNReal.toReal_lt_toReal (ENNReal.zero_ne_top)]
--   · exact (pos_likelihood_lt f X n ω θ h0 hX)
--   · exact ne_top f X n ω θ

lemma likelihood_iff_log_sum_ratio
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    {ProbFunSet : Set (Measure Ω)} (μ : Measure ℝ := by volume_tac)
    (f : ℝ → ↑ProbFunSet) (θ₀ : ℝ)
    (X : ℕ → Ω → ℝ) (n : ℕ) (x : ℝ) (θ : ℝ)
    (hX : ∀ (i : Fin n), x ∈ pdf_support (X i) (f θ₀).1 μ)
    (h0 : ∀ (i : Fin n), ∀ (θ₁ θ₂ : ℝ), pdf_support (X i) (f θ₁).1 μ
      = pdf_support (X i) (f θ₂).1 μ) :
    ∀ᵐ (x : ℝ) ∂μ, (Likelihood f X θ₀ n μ> Likelihood f X θ n μ)
    ↔ (((n: ℝ)⁻¹• (∑ (i: Fin n),
    Real.log ((pdf (X i) (f θ₀).1 μ x).toReal/ (pdf (X i) (f θ).1 μ x).toReal)) <0)) := by
  by_cases hn: n=0
  · rw [hn]


    simp only [gt_iff_lt, CharP.cast_eq_zero, inv_zero, Finset.univ_eq_empty, Finset.sum_empty,
      smul_eq_mul, mul_zero, lt_self_iff_false, Likelihood, Finset.univ_eq_empty, Finset.prod_empty]
  · constructor
    · intro h
      refine (smul_neg_iff_of_pos_left ?_).mpr ?_
      · simp only [inv_pos, Nat.cast_pos]
        omega
      ·
        rw [gt_iff_lt, ← ENNReal.toReal_lt_toReal (ne_top f X n ω θ) (ne_top f X n ω θ₀),
          ← div_lt_one] at h
        · rw [← Real.log_neg_iff] at h
          · unfold Likelihood at h
            rw [ENNReal.toReal_prod, ENNReal.toReal_prod, ← Finset.prod_div_distrib,
              Real.log_prod] at h
            · exact h
            · intro i hi
              rw [@div_ne_zero_iff]
              refine ⟨by rw [ENNReal.toReal_ne_zero]; refine ⟨by
                rw [h0 θ₀ θ] at hX; exact (PMF.mem_support_iff (f θ).1 (X i ω)).mp (hX i),
                ne_of_lt (lt_of_le_of_lt (PMF.coe_le_one (f θ).1 (X i ω)) ENNReal.one_lt_top)⟩, by
                rw [ENNReal.toReal_ne_zero]; refine ⟨
                  (PMF.mem_support_iff (f θ₀).1 (X i ω)).mp (hX i),
                  ne_of_lt (lt_of_le_of_lt (PMF.coe_le_one (f θ₀).1 (X i ω)) ENNReal.one_lt_top)⟩⟩
          · rw [@div_pos_iff]
            left
            refine ⟨by rw [← ENNReal.toReal_zero,
              ENNReal.toReal_lt_toReal (ENNReal.zero_ne_top)
              (ne_top f X n ω θ)]; exact pos_likelihood_lt f X n ω θ h0 hX,
              by rw [← ENNReal.toReal_zero, ENNReal.toReal_lt_toReal
              (ENNReal.zero_ne_top) (ne_top f X n ω θ₀)];exact pos_likelihood_lt f X n ω θ₀ h0 hX⟩
        · rw [← ENNReal.toReal_zero,
            ENNReal.toReal_lt_toReal (ENNReal.zero_ne_top) (ne_top f X n ω θ₀)]
          exact pos_likelihood_lt f X n ω θ₀ h0 hX
    · intro h
      rw [smul_neg_iff_of_pos_left (by simp only [inv_pos, Nat.cast_pos]; omega)] at h
      rw [← Real.log_prod] at h
      · rw [Finset.prod_div_distrib, ← ENNReal.toReal_prod, ← ENNReal.toReal_prod,
          Real.log_neg_iff, div_lt_one, ENNReal.toReal_lt_toReal] at h
        · rw [gt_iff_lt]
          exact h
        · exact ne_top f X n ω θ
        · exact ne_top f X n ω θ₀
        · exact toReal_pos_likelihood_lt f X n ω θ₀ h0 hX
        · rw [@div_pos_iff]
          left
          refine ⟨toReal_pos_likelihood_lt f X n ω θ h0 hX,
            toReal_pos_likelihood_lt f X n ω θ₀ h0 hX⟩
      · intro i hi
        rw [div_ne_zero_iff]
        refine ⟨by rw [h0 θ₀ θ] at hX; rw [ENNReal.toReal_ne_zero]; refine ⟨
          (PMF.mem_support_iff (f θ).1 (X i ω)).mp (hX i),
          ne_of_lt (lt_of_le_of_lt (PMF.coe_le_one (f θ).1 (X i ω)) ENNReal.one_lt_top)⟩, by
          rw [ENNReal.toReal_ne_zero]; refine ⟨(PMF.mem_support_iff (f θ₀ ).1 (X i ω)).mp (hX i),
          ne_of_lt (lt_of_le_of_lt (PMF.coe_le_one (f θ₀).1 (X i ω)) ENNReal.one_lt_top)⟩⟩


example (f : PMF ℝ) (X : ℝ) (hX : X ∉ f.support) : f.toMeasure {X} = 0 :=by
  simp only [PMF.toMeasure]
  simp only [MeasurableSet.singleton, toMeasure_apply]
  rw [@PMF.toOuterMeasure_apply_eq_zero_iff]
  exact Set.disjoint_singleton_right.mpr hX

/-- The set of sample points `x`
for which the likelihood of parameter `θ₀` exceeds the likelihood of parameter
`θ` based on the first `n` observations of the statistic `X` -/
def likelihoodStrictSublevelSet
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    (X : ℕ → Ω → ℝ) (n : ℕ) (θ₀ θ : ℝ)
    {ProbFunSet : Set (Measure Ω)} (f : ℝ → ProbFunSet)
    (μ : Measure ℝ := by volume_tac) : Set ℝ :=
  {(x : ℝ) | Likelihood f X θ₀ n μ x> Likelihood f X θ n μ x}

variable {ProbFunSet : Set (PMF ℝ)} (f : ℝ → ↑ProbFunSet) (θ₀ : ℝ)
    (X : ℕ → ℝ → ℝ) (hindep : iIndepFun X ((f θ₀).1.toMeasure))
    (hident : ∀ i, IdentDistrib (X i) (X 0) ((f θ₀).1.toMeasure) ((f θ₀).1.toMeasure))
    (hX : ∀ (n : ℕ), ∀ᵐ (ω : ℝ), ∀ (i : Fin n), X i ω ∈ (f θ₀).1.support)

open scoped ProbabilityTheory

/-- the sequence of real-valued random variables
representing the *log-likelihood ratio* of parameter `θ` against the reference
parameter `θ₀` evaluated on the observations `X i` -/
noncomputable abbrev log_sum_ratio_rv {Ω : Type u_1}
  {ProbFunSet : Set (PMF ℝ)} (f : ℝ → ↑ProbFunSet)
  (X : ℕ → Ω → ℝ) (θ₀ θ : ℝ) : ℕ → Ω → ℝ :=
  fun i => fun ω => Real.log (((f θ).1.1 (X (i) ω)).toReal/ ((f θ₀).1.1 (X (i) ω)).toReal)

-- lemma Measurable_log_ratio
--     {ProbFunSet : Set (PMF ℝ)} (f : ℝ → ↑ProbFunSet) (θ₀ : ℝ)
--     (hMeasurable : ∀ (θ : ℝ), Measurable (f θ).1.1) :
--   Measurable fun x ↦ Real.log (((f θ).1 x).toReal / ((f θ₀).1 x).toReal) := by
--   apply Measurable.comp (Real.measurable_log)
--   apply Measurable.div
--   · apply Measurable.comp ENNReal.measurable_toReal (hMeasurable θ)
--   · apply Measurable.comp ENNReal.measurable_toReal (hMeasurable θ₀)

-- lemma iIndepFun_log_sum_ratio {ProbFunSet : Set (PMF ℝ)} (f : ℝ → ↑ProbFunSet) (θ₀ : ℝ)
--     (X : ℕ → ℝ → ℝ) (hindep : iIndepFun X ((f θ₀).1.toMeasure))
--     (hMeasurable : ∀ (θ : ℝ), Measurable (f θ).1.1) :
--     iIndepFun (log_sum_ratio_rv f X θ₀ θ) ((f θ₀).1.toMeasure):=by
--   unfold log_sum_ratio_rv
--   apply ProbabilityTheory.iIndepFun.comp hindep (fun (i : ℕ) => fun (x : ℝ) =>
--     Real.log ((((f θ).1.1 x).toReal) / (((f θ₀).1.1 x).toReal)))
--   intro i
--   exact Measurable_log_ratio θ f θ₀ hMeasurable

-- lemma IdentDistrib_log_sum_ratio {ProbFunSet : Set (PMF ℝ)} (f : ℝ → ↑ProbFunSet) (θ₀ : ℝ)
--     (X : ℕ → ℝ → ℝ)
--     (hident : ∀ i, IdentDistrib (X i) (X 0) ((f θ₀).1.toMeasure) ((f θ₀).1.toMeasure))
--     (hMeasurable : ∀ (θ : ℝ), Measurable (f θ).1.1) :
--     ∀ i, IdentDistrib ((log_sum_ratio_rv f X θ₀ θ) i) ((log_sum_ratio_rv f X θ₀ θ) 0)
--     ((f θ₀).1.toMeasure) ((f θ₀).1.toMeasure):=by
--   intro i
--   specialize hident i
--   unfold log_sum_ratio_rv
--   apply IdentDistrib.comp hident
--     (u:=(fun x => Real.log ((((f θ).1.1 x).toReal) / (((f θ₀).1.1 x).toReal))))
--   exact Measurable_log_ratio θ f θ₀ hMeasurable

-- lemma Measurable_edist_log_sum_ratio {ProbFunSet : Set (PMF ℝ)} (f : ℝ → ↑ProbFunSet) (θ₀ : ℝ)
--     (X : ℕ → ℝ → ℝ) (hrv : ∀ (i : ℕ), Measurable (X i))
--     (hMeasurable : ∀ (θ : ℝ), Measurable (f θ).1.1) :
--     ∀ (n : ℕ), Measurable fun a ↦ edist
--     ((∑ i ∈ Finset.range n, log_sum_ratio_rv f X θ₀ θ i a) / n)
--     (∫ (x : ℝ), log_sum_ratio_rv f X θ₀ θ 0 x ∂((f θ₀).1).toMeasure) := by
--   intro n
--   apply Measurable.edist
--   · apply Measurable.div
--     · apply Finset.measurable_fun_sum
--       exact fun i _ => Measurable.comp (Measurable_log_ratio θ f θ₀ hMeasurable) (hrv i)
--     · exact measurable_const
--   · simp only [measurable_const]

-- lemma integral_sum_ratio_eq_one {ProbFunSet : Set (PMF ℝ)} (f : ℝ → ↑ProbFunSet) (θ₀ : ℝ)
--     (X : ℕ → ℝ → ℝ)
--     (hX : ∀ (n : ℕ), ∀ (ω : ℝ), ∀ (i : Fin n), X i ω ∈ (f θ₀).1.support)
--     (hid : ∀ (n : ℕ), ∀ (ω : ℝ), X n ω = ω)
--     (hint2 : Integrable (fun x ↦ ((f θ).1.1 (X 0 x)).toReal /
--     ((f θ₀).1.1 (X 0 x)).toReal) ((f θ₀).1).toMeasure) :
--     ∫ (x : ℝ), ((f θ).1.1 (X 0 x)).toReal / ((f θ₀).1.1 (X 0 x)).toReal ∂((f θ₀).1).toMeasure
--     = 1 :=by
--   have hsubtype₀: ∀ (a : ℝ), (f θ₀).1.1 a = (f θ₀).1 a:= fun a => rfl
--   have hsubtype: ∀ (a : ℝ), (f θ).1.1 a = (f θ).1 a:= fun a => rfl
--   rw [PMF.integral_eq_tsum]
--   · simp_rw [hid 0]
--     simp only [smul_eq_mul]
--     simp_rw [hsubtype₀]
--     have hdiv_cancel: ∀ (a : ℝ), ((f θ₀).1 a).toReal *
--       (((f θ).1.1 a).toReal / ((f θ₀).1 a).toReal) = ((f θ).1.1 a).toReal :=by
--       intro a
--       rw [mul_div_cancel₀]
--       rw [← hsubtype₀, ← hid 0 a]
--       have hX0_coe: X 0 a = X (0: Fin 1) a:= by exact rfl
--       specialize hX 1 a 0
--       rw [hX0_coe, ENNReal.toReal_ne_zero]
--       refine ⟨(PMF.mem_support_iff ((f θ₀).1) (X 0 a)).mp hX,
--         ne_of_lt (lt_of_le_of_lt (PMF.coe_le_one (f θ₀).1 (X 0 a)) ENNReal.one_lt_top)⟩
--     simp_rw [hdiv_cancel]
--     rw [← ENNReal.toReal_one, ← ENNReal.tsum_toReal_eq]
--     · simp_rw [hsubtype]
--       rw [← PMF.tsum_coe (f θ).1]
--     · intro a
--       exact ne_of_lt (lt_of_le_of_lt (PMF.coe_le_one (f θ).1 a) ENNReal.one_lt_top)
--   · exact hint2

lemma edist_compl_ball (μ : ℝ) (S : ℝ → ℝ) :
    {x | ENNReal.ofReal (- μ ) ≤ edist (S x) μ}ᶜ ⊆ {x | (S x) < 0}:= by
  intro x hS
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, edist_lt_ofReal] at hS
  simp only [Set.mem_setOf_eq]
  have h := add_lt_add_of_lt_of_le (lt_of_le_of_lt (Real.sub_le_dist (S x) μ ) hS)
    (le_refl ((μ) ))
  rw [add_comm, ← add_sub_assoc, add_comm, add_sub_assoc] at h
  simp only [neg_add_cancel, sub_self, add_zero] at h
  exact h

theorem likelihood_consistency_sublevel_measure_tendsto_one
    {s : Set ℝ} {hs1 : s ⊆ (Set.Iio 0)} {hs2 : Convex ℝ s}
    {hs3 : ContinuousOn Real.log s} {hs4 : IsClosed s}
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    {ProbFunSet : Set (Measure Ω)}
    {μ : Measure ℝ}
    (f : ℝ → ProbFunSet) (θ₀ θ: ℝ)
    (X : ℕ → Ω → ℝ) (hrv : ∀ (i : ℕ), Measurable (X i))
    (hMeasurable : ∀ (θ : ℝ), Measurable (f θ).1.1)
    {μ : Measure ℝ}
 :
    Tendsto (fun n : ℕ => Measure.map (X n) (f θ₀).1 (likelihoodStrictSublevelSet X n θ₀ θ f))
      atTop (nhds 1) := by
    unfold likelihoodStrictSublevelSet



    simp_rw [fun ω => fun (n: ℕ) => likelihood_iff_log_sum_ratio f θ₀ X n ω θ (hX n ω) h0]
    have hpairindep: Pairwise (Function.onFun
        (fun x1 x2 ↦ x1 ⟂ᵢ[((f θ₀).1).toMeasure] x2) (log_sum_ratio_rv f X θ₀ θ)):= by
      classical
      intro i j hij
      simpa [Function.onFun] using (iIndepFun_log_sum_ratio θ f θ₀ X hindep hMeasurable).indepFun
        hij
    have hlaw := MeasureTheory.tendstoInMeasure_of_tendsto_ae_of_measurable_edist
      (Measurable_edist_log_sum_ratio θ f θ₀ X hrv hMeasurable)
      (ProbabilityTheory.strong_law_ae_real (log_sum_ratio_rv f X θ₀ θ) hint1
      hpairindep (IdentDistrib_log_sum_ratio θ f θ₀ X hident hMeasurable))
    unfold TendstoInMeasure at hlaw
    have hJensen := StrictConcaveOn.ae_eq_const_or_lt_map_average (μ:= ((f θ₀).1).toMeasure) (f:=
      (fun x => (((f θ).1.1 (X 0 x)).toReal / ((f θ₀).1.1 (X 0 x)).toReal))) (g:= Real.log)
      (StrictConcaveOn.subset strictConcaveOn_log_Iio hs1 hs2) hs3 hs4 hs5 hint2 hint1
    cases hJensen with
      | inl hp => exact False.elim (hne_const hp)
      | inr hJensen =>
          unfold average at hJensen
          simp only [measure_univ, inv_one, one_smul] at hJensen
          generalize hμ: ∫ (x : ℝ), Real.log (((f θ).1.1 (X 0 x)).toReal /
            ((f θ₀).1.1 (X 0 x)).toReal) ∂((f θ₀).1).toMeasure = μ at *
          rw [integral_sum_ratio_eq_one θ f θ₀ X hX hid hint2] at hJensen
          simp only [Real.log_one] at hJensen
          have hμ2: 0 < ((- μ).toEReal).toENNReal:= by
            simp only [EReal.coe_neg, ne_eq, EReal.neg_eq_top_iff, EReal.coe_ne_bot,
              not_false_eq_true, EReal.toENNReal_of_ne_top, EReal.toReal_neg, EReal.toReal_coe,
              ENNReal.ofReal_pos, Left.neg_pos_iff]
            exact hJensen
          specialize hlaw ((- μ).toEReal).toENNReal hμ2
          simp only [eventually_const]
          rw [PMF.tendsto_measure_compl_iff] at hlaw
          · apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlaw (PMF.univ_tendsto_one (f θ₀).1)
            · intro n
              simp only [EReal.coe_neg, ne_eq, EReal.neg_eq_top_iff, EReal.coe_ne_bot,
                not_false_eq_true, EReal.toENNReal_of_ne_top, EReal.toReal_neg, EReal.toReal_coe,
                smul_eq_mul]
              apply ((f θ₀).1.toMeasure).mono
              simp_rw [← Fin.sum_univ_eq_sum_range, div_eq_mul_inv, mul_comm]
              apply edist_compl_ball
            · intro x
              simp only [smul_eq_mul, measure_univ]
              exact prob_le_one
          · intro i
            apply measurableSet_le
            · simp only [EReal.coe_neg, ne_eq, EReal.neg_eq_top_iff, EReal.coe_ne_bot,
              not_false_eq_true, EReal.toENNReal_of_ne_top, EReal.toReal_neg, EReal.toReal_coe,
              measurable_const]
            · apply Measurable.edist
              · apply Measurable.div
                · apply Finset.measurable_fun_sum
                  intro x hx
                  exact Measurable.comp (Measurable_log_ratio θ f θ₀ hMeasurable) (hrv x)
                · exact measurable_const
              · exact measurable_const
