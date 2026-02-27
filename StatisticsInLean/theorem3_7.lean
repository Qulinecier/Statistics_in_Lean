import Mathlib

universe u v u_1 u_2


open TopologicalSpace Filter MeasureTheory
open scoped NNReal ENNReal MeasureTheory Topology
namespace MeasureTheory
lemma univ_tendsto_one {ι : Type*}
    {Ω : Type*} [MeasurableSpace Ω] (p : Measure Ω) [IsProbabilityMeasure p] {l : Filter ι} :
    Tendsto (fun (_ : ι) => p (Set.univ)) l (nhds 1) :=by
  simp only [MeasureTheory.measure_univ]
  exact tendsto_const_nhds

lemma tendsto_measure_compl_iff {ι : Type*}
    {Ω : Type*} [MeasurableSpace Ω]
    {p : Measure Ω} [IsProbabilityMeasure p]
    {l : Filter ι} {s : ι → Set Ω}
    (hs : ∀ i, MeasurableSet (s i)) :
  (Tendsto (fun i => p (s i)) l (nhds 0))
  ↔ (Tendsto (fun i => p ((s i)ᶜ)) l (nhds 1)):=by
  have hcompl: ∀ (i: ι), p (Set.univ) - p (s i) = p (s i)ᶜ :=by
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

open scoped NNReal ENNReal MeasureTheory Topology

def TendstoInProbability {Ω : Type u_1} [MeasurableSpace Ω] (θ : ℕ → Ω → ℝ)
    (P : Measure Ω) (θ₀ : ℝ):= TendstoInMeasure P θ atTop (fun _ => θ₀)

noncomputable def Likelihood {Ω : Type*} [MeasurableSpace Ω]
    {ProbFunSet : Set (Measure Ω)} (f : ℝ → ProbFunSet)
    (X : ℕ → Ω → ℝ) (θ : ℝ) (n : ℕ) (μ : Measure ℝ := by volume_tac) : Ω → ENNReal :=
  fun ω => ∏ i : Fin n, pdf (X 0) (f θ) μ (X i ω)

noncomputable def log_Likelihood {Ω : Type*} [MeasurableSpace Ω]
    {ProbFunSet : Set (Measure Ω)} (f : ℝ → ProbFunSet)
    (X : ℕ → Ω → ℝ) (θ : ℝ) (n : ℕ) (μ : Measure ℝ := by volume_tac) : Ω → EReal :=
  fun ω => ∑ (i : Fin n), ENNReal.log (pdf (X 0) (f θ) μ (X i ω))


lemma exists_deriv_eq_zero_of_strict_endpoints
    (g : ℝ → ℝ) (θ₀ : ℝ) (a : ℝ≥0∞)
    (ha : 0 < a) (ha_fin : a < ⊤)
    (hcont : ContinuousOn g (Set.Icc (θ₀ - a.toReal) (θ₀ + a.toReal)))
    (h1 : g θ₀ > g (θ₀ + a.toReal))
    (h2 : g θ₀ > g (θ₀ - a.toReal)) :
    ∃ θ, edist θ θ₀ < a ∧ deriv g θ = 0 := by

  set L : ℝ := θ₀ - a.toReal
  set U : ℝ := θ₀ + a.toReal

  have ha_Real := ENNReal.toReal_pos_iff.mpr ⟨ha, ha_fin⟩

  have hLU : L ≤ U := by
    dsimp [L, U]
    nlinarith

  have hne : (Set.Icc L U).Nonempty := by
    exact Set.nonempty_Icc.2 hLU

  obtain ⟨θ, hθIcc, hθmax'⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc L U)).exists_isMaxOn hne (by
      simpa [L, U] using hcont)

  have hθ_ge_θ0 : g θ ≥ g θ₀ := by
    have : g θ₀ ≤ g θ := by
      have hθ0Icc : θ₀ ∈ Set.Icc L U := by
        have hL : L ≤ θ₀ := by dsimp [L]; nlinarith
        have hU : θ₀ ≤ U := by dsimp [U]; nlinarith
        exact ⟨hL, hU⟩
      exact hθmax' hθ0Icc
    exact this

  have hθ_ne_U : θ ≠ U := by
    intro hEq
    have : g θ₀ ≤ g θ :=by exact hθ_ge_θ0
    have hU_le : g U ≤ g θ := hθmax' ⟨hLU, le_rfl⟩
    have : g θ₀ > g θ := by simpa [hEq, U] using h1
    refine (not_lt_of_ge (le_trans hθ_ge_θ0 (hθmax' hθIcc))).elim (by
      exact this)

  have hθ_ne_L : θ ≠ L := by
    intro hEq
    have hLIcc : L ∈ Set.Icc L U := by exact ⟨le_rfl, hLU⟩
    have hL_le : g L ≤ g θ := by
      exact hθmax' hLIcc
    have : g θ₀ ≤ g θ :=by
      refine le_trans (le_of_lt (lt_imp_lt_of_le_imp_le (fun a ↦ hθ_ge_θ0)
        (by simpa [hEq, L] using h2))) hL_le
    refine (not_lt_of_ge this) (by simpa [hEq, L] using h2)

  have hθIoo : θ ∈ Set.Ioo L U := by
    exact ⟨lt_of_le_of_ne hθIcc.1 (Ne.symm hθ_ne_L), lt_of_le_of_ne hθIcc.2 hθ_ne_U⟩


  have hed : edist θ θ₀ < a := by
    simp only [edist_dist]
    rw [ENNReal.ofReal_lt_iff_lt_toReal dist_nonneg (LT.lt.ne_top ha_fin)]
    have : |θ - θ₀| < a.toReal := by
      have h1' : θ₀ - a.toReal < θ := by simpa [L] using hθIoo.1
      have h2' : θ < θ₀ + a.toReal := by simpa [U] using hθIoo.2
      have : -a.toReal < θ - θ₀ ∧ θ - θ₀ < a.toReal := by
        refine ⟨by linarith, by linarith⟩
      simpa [abs_lt] using this
    simpa [Real.dist_eq, abs_sub_comm] using this

  exact ⟨θ, hed, IsLocalMax.deriv_eq_zero (IsMaxOn.isLocalMax
    (fun y hy => hθmax' ⟨le_of_lt hy.1, le_of_lt hy.2⟩)
    (IsOpen.mem_nhds isOpen_Ioo hθIoo))⟩

open scoped BigOperators
open Finset

lemma EReal.toReal_lt_toReal
    {a : EReal} {b : EReal}
    (ha1 : a ≠ ⊥) (ha2 : a ≠ ⊤) (hb1 : b ≠ ⊤) (hb2 : b ≠ ⊥) :
    a < b → a.toReal < b.toReal :=by
  intro h
  have hne: a.toReal ≠ b.toReal := by
    simp only [ne_eq]
    refine Ne.intro ?_
    intro h_eq_toReal
    rw [EReal.toReal_eq_toReal ha2 ha1 hb1 hb2] at h_eq_toReal
    exact ne_of_lt h h_eq_toReal
  exact lt_of_le_of_ne (EReal.toReal_le_toReal (le_of_lt h) ha1 hb1) hne

open scoped Topology
open Filter

lemma tendsto_measure_inter_of_tendsto_measure
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (s t : ℕ → Set Ω)
    (hs : Tendsto (fun n => P (s n)) atTop (𝓝 (1 : ℝ≥0∞)))
    (ht : Tendsto (fun n => P (t n)) atTop (𝓝 (1 : ℝ≥0∞)))
    (hms : ∀ n, MeasurableSet (s n))
    (hmt : ∀ n, MeasurableSet (t n)) :
    Tendsto (fun n => P (s n ∩ t n)) atTop (𝓝 (1 : ℝ≥0∞)) := by
  refine tendsto_order.2 ?_
  constructor
  · intro a ha
    have hpos : 0 < (1 : ℝ≥0∞) - a := by
      simpa [tsub_pos_iff_lt] using ha
    let ε : ℝ≥0∞ := ((1 : ℝ≥0∞) - a) / 4
    have hεpos : 0 < ε := by
      simp only [ε]
      refine ENNReal.div_pos (Ne.symm (ne_of_lt hpos)) (Ne.symm ENNReal.top_ne_ofNat)
    have hε_lt : a < (1 : ℝ≥0∞) - (ε + ε) := by
      have : ε + ε = ((1 : ℝ≥0∞) - a) / 2 := by
        unfold ε
        rw [ENNReal.div_add_div_same]
        rw [← two_mul]
        rw [div_eq_mul_inv]
        rw [mul_assoc, mul_comm, mul_assoc]
        have h4_2 : (4 : ENNReal)⁻¹ * 2 = 2⁻¹ :=by
          refine ENNReal.eq_inv_of_mul_eq_one_left ?_
          rw [mul_assoc]
          norm_num
          refine ENNReal.inv_mul_cancel (Ne.symm (NeZero.ne' 4)) (Ne.symm ENNReal.top_ne_ofNat)
        rw [h4_2]
        rw [div_eq_mul_inv]
      have ha_fin : a < ⊤ := lt_of_lt_of_le ha (by simp)
      have hε_fin : ε < ⊤ := by
        refine ENNReal.div_lt_top (ENNReal.sub_ne_top ENNReal.one_ne_top) (Ne.symm (NeZero.ne' 4))
      have : a.toReal < ((1 : ℝ≥0∞) - (ε + ε)).toReal := by
        rw [this]
        have ha1: 1 - a ≤ 1 := by
          exact tsub_le_self
        have hεle1 : (ε + ε) ≤ 1 :=by
          rw [this]
          refine (ENNReal.div_le_iff (Ne.symm (NeZero.ne' 2)) (Ne.symm ENNReal.top_ne_ofNat)).mpr ?_
          simp only [one_mul]
          exact Std.IsPreorder.le_trans (1 - a) 1 2 tsub_le_self one_le_two

        have ha_fin' : a < (⊤ : ℝ≥0∞) := lt_of_lt_of_le ha (by simp only [le_top])
        have ha_fin : a ≠ (⊤ : ℝ≥0∞) := by exact LT.lt.ne_top (ha_fin')
        have hR_a : a.toReal < (1 : ℝ) := by
          have := ENNReal.toReal_lt_toReal ha_fin ENNReal.one_ne_top
          simp only [ENNReal.toReal_one] at this
          rw [this]
          exact ha

        have hR_rhs :
            ((1 : ℝ≥0∞) - (ε + ε)).toReal = (1 : ℝ) - (ε + ε).toReal := by
          simpa using (ENNReal.toReal_sub_of_le hεle1)
        have hR_eps :
            (ε + ε).toReal = (((1 : ℝ≥0∞) - a) / 2).toReal := by
          rw [this]
        have hR_div :
            (((1 : ℝ≥0∞) - a) / 2).toReal = ((1 : ℝ) - a.toReal) / 2 := by
          have ha_le1 : a ≤ (1 : ℝ≥0∞) := le_of_lt ha
          simp only [div_eq_mul_inv]
          rw [ENNReal.toReal_mul]
          simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, mul_eq_mul_right_iff, inv_eq_zero,
            OfNat.ofNat_ne_zero, or_false]
          rw [ENNReal.toReal_sub_of_le ha_le1 ENNReal.one_ne_top]
          simp only [ENNReal.toReal_one]
        have hR_sub: (1 - (1 - a) / 2).toReal = (1: ENNReal).toReal - ((1 - a) / 2).toReal:=by
          refine ENNReal.toReal_sub_of_le ?_ ENNReal.one_ne_top
          rw [this] at hεle1
          exact hεle1
        rw [hR_sub]
        simp [hR_div]
        nlinarith [hR_a]
      rw [ENNReal.toReal_lt_toReal (LT.lt.ne_top ha)] at this
      · exact this
      · simp only [ne_eq, ENNReal.sub_eq_top_iff, ENNReal.one_ne_top, ENNReal.add_eq_top, or_self,
        false_and, not_false_eq_true]

    have hs' : ∀ᶠ n in atTop, (1 : ℝ≥0∞) - ε < P (s n) := by
      rw [tendsto_order] at hs
      exact (hs.1 (1 - ε))
        ((ENNReal.sub_lt_self_iff ENNReal.one_ne_top).mpr ⟨zero_lt_one' ℝ≥0∞, hεpos⟩)
    have ht' : ∀ᶠ n in atTop, (1 : ℝ≥0∞) - ε < P (t n) := by
      rw [tendsto_order] at ht
      exact (ht.1 (1 - ε))
        ((ENNReal.sub_lt_self_iff ENNReal.one_ne_top).mpr ⟨zero_lt_one' ℝ≥0∞, hεpos⟩)
    filter_upwards [hs', ht'] with n hs1 ht1
    have hcomplS : P ((s n)ᶜ) < ε := by
      have hcompl : P ((s n)ᶜ) = (1 : ℝ≥0∞) - P (s n) := by
        simpa [measure_univ] using (prob_compl_eq_one_sub (hms n))
      simpa [hcompl] using (ENNReal.sub_lt_of_sub_lt (prob_le_one)
        (by left; exact ENNReal.one_ne_top) hs1)
    have hcomplT : P ((t n)ᶜ) < ε := by
      have hcompl : P ((t n)ᶜ) = (1 : ℝ≥0∞) - P (t n) := by
        simpa [measure_univ] using (prob_compl_eq_one_sub (hmt n))
      simpa [hcompl] using (ENNReal.sub_lt_of_sub_lt (prob_le_one)
        (by left; exact ENNReal.one_ne_top) ht1)

    have hcompl_inter :
        P ((s n ∩ t n)ᶜ) ≤ P ((s n)ᶜ) + P ((t n)ᶜ) := by

      simpa [Set.compl_inter] using (measure_union_le ((s n)ᶜ) ((t n)ᶜ))


    have hinter :
         P (s n ∩ t n) = (1 : ℝ≥0∞) - P ((s n ∩ t n)ᶜ):= by
      have h:= prob_compl_eq_one_sub (μ := P) (s := (s n ∩ t n)ᶜ)
        (MeasurableSet.compl_iff.mpr (MeasurableSet.inter (hms n) (hmt n)))
      simp only [compl_compl] at h
      exact h

    have : (1 : ℝ≥0∞) - (ε + ε) < P (s n ∩ t n) := by

      have hlt : P ((s n ∩ t n)ᶜ) < ε + ε := by
        have hsum : P ((s n)ᶜ) + P ((t n)ᶜ) < ε + ε :=by
          exact ENNReal.add_lt_add hcomplS hcomplT
        exact lt_of_le_of_lt hcompl_inter hsum

      have : (1 : ℝ≥0∞) - (ε + ε) < (1 : ℝ≥0∞) - P ((s n ∩ t n)ᶜ) := by

        have h₂ : (ε + ε) ≤ (1 : ℝ≥0∞) := by
          have : (ε + ε) < (1 : ℝ≥0∞) := by
            have : 0 < (1 : ℝ≥0∞) - (ε + ε) := by
              have ha0 : (0 : ℝ≥0∞) ≤ a := bot_le
              refine lt_of_le_of_lt ha0 hε_lt
            simpa [tsub_pos_iff_lt] using this
          exact le_of_lt this
        have h₃ : (1 : ℝ≥0∞) ≠ ⊤ ∨ (1 - P ((s n ∩ t n)ᶜ)) ≠ ⊤ := by
          left; simp
        have h₁ : (1 : ℝ≥0∞) - (1 - P ((s n ∩ t n)ᶜ)) < ε + ε := by

          have hxle : P ((s n ∩ t n)ᶜ) ≤ (1 : ℝ≥0∞) := by

            exact prob_le_one

          have : (1 : ℝ≥0∞) - (1 - P ((s n ∩ t n)ᶜ)) = P ((s n ∩ t n)ᶜ) := by
            rw [← hinter]
            exact id (Eq.symm (prob_compl_eq_one_sub (μ := P) (s := (s n ∩ t n))
              (MeasurableSet.inter (hms n) (hmt n))))

          simpa [this] using hlt

        exact ENNReal.sub_lt_of_sub_lt h₂ h₃ h₁
      simpa [hinter] using this

    exact lt_trans hε_lt this
  ·
    intro b hb
    rw [@eventually_atTop]
    use 0
    intro n _
    exact lt_of_le_of_lt (prob_le_one (μ := P) (s := s n ∩ t n)) hb


lemma Measurable_log_Likelihood
    {Ω : Type*} [MeasurableSpace Ω]
    {ProbFunSet : Set (Measure Ω)} (f : ℝ → ↑ProbFunSet) (μ : Measure ℝ := by volume_tac)
    (X : ℕ → Ω → ℝ) (θ₀ : ℝ) (k : ℕ) :
    Measurable
    (fun ω : Ω => log_Likelihood f X θ₀ k μ ω) := by sorry


theorem exists_consistent_estimator_of_logLikelihood
  {Ω : Type*} [MeasurableSpace Ω]
  {ProbFunSet : Set (Measure Ω)}
  (f : ℝ → ProbFunSet)
  (X : ℕ → Ω → ℝ) (θ₀ : ℝ) (μ : Measure ℝ := by volume_tac)
  [IsProbabilityMeasure (f θ₀).1]
  (a : ENNReal) (ha : 0 < a) (ha_fin : a < ⊤)
  (hfs : ∀ (n : ℕ), ∀ (θ : ℝ), ∀ (ω : Ω), log_Likelihood f X θ n μ ω ≠ ⊤)
  (hfl : ∀ (n : ℕ), ∀ (θ : ℝ), ∀ (ω : Ω), ⊥ ≠ log_Likelihood f X θ n μ ω)
  (hcont : ∀ (n : ℕ), ∀ (ω : Ω), ContinuousOn (fun θ => log_Likelihood f X θ n μ ω)
    (Set.Icc (θ₀ - a.toReal) (θ₀ + a.toReal)))
  (htendsto : ∀ (θ : ℝ), Tendsto (fun n : ℕ => ((f θ₀).1) {ω : Ω |
    log_Likelihood f X θ₀ n μ ω > log_Likelihood f X θ n μ ω}) atTop (𝓝 1))
  (hfinite :
    ∀ (k : ℕ) (ω : Ω) (θ : ℝ),
      θ ∈ Set.Icc (θ₀ - a.toReal) (θ₀ + a.toReal) →
        log_Likelihood f X θ k μ ω ≠ ⊥ ∧ log_Likelihood f X θ k μ ω ≠ ⊤) :
  ∃ (θ_hat : ℕ → Ω → ℝ),
    Tendsto (fun i =>
      (f θ₀).1 { ω |
        (edist (θ_hat i ω) θ₀ < a) ∧
        (deriv (fun θ => (log_Likelihood f X θ i μ ω).toReal) (θ_hat i ω) = 0) })
      atTop (𝓝 1) := by

  set θU : ℝ := θ₀ + a.toReal
  set θL : ℝ := θ₀ - a.toReal

  let AU : ℕ → Set Ω := fun k => {ω : Ω |
    log_Likelihood f X θ₀ k μ ω > log_Likelihood f X θU k μ ω}
  let AL : ℕ → Set Ω := fun k => {ω : Ω |
    log_Likelihood f X θ₀ k μ ω > log_Likelihood f X θL k μ ω}
  let A : ℕ → Set Ω := fun k => AU k ∩ AL k

  generalize hP : (f θ₀).1 = P at *
  have hAU : Tendsto (fun k => P (AU k)) atTop (𝓝 1) := by
    simpa [hP, θU, AU] using htendsto θU
  have hAL : Tendsto (fun k => P (AL k)) atTop (𝓝 1) := by
    simpa [hP, θL, AL] using htendsto θL

  have hA : Tendsto (fun k => P (A k)) atTop (𝓝 1) := by
    unfold A
    have hmsU : ∀ k, MeasurableSet (AU k) := by
      intro k
      simpa [AU, gt_iff_lt] using
        (measurableSet_lt (Measurable_log_Likelihood f μ X θU k)
          (Measurable_log_Likelihood f μ X θ₀ k))
    have hmsL : ∀ k, MeasurableSet (AL k) := by
      intro k
      simpa [AL, gt_iff_lt] using
        (measurableSet_lt (Measurable_log_Likelihood f μ X θL k)
          (Measurable_log_Likelihood f μ X θ₀ k))
    simpa [A] using
      (tendsto_measure_inter_of_tendsto_measure (P := P) (s := AU) (t := AL)
        hAU hAL hmsU hmsL)

  set I : Set ℝ := Set.Icc (θ₀ - a.toReal) (θ₀ + a.toReal)

  have hcontR :
      ∀ (k : ℕ) (ω : Ω),
        ContinuousOn (fun θ => (log_Likelihood f X θ k μ ω).toReal) I := by
    intro k ω
    have h' : Set.MapsTo (fun θ ↦ log_Likelihood f X θ k μ ω) I {⊥, ⊤}ᶜ := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact hfinite k ω x hx
    exact (ContinuousOn.comp EReal.continuousOn_toReal (hcont k ω)) h'

  let hex := fun k ω (h : (ω ∈ AU k) ∧ (ω ∈ AL k)) =>
      (exists_deriv_eq_zero_of_strict_endpoints
          (g := fun θ => (log_Likelihood f X θ k μ ω).toReal)
          (θ₀ := θ₀) (a := a)
          ha ha_fin
          (by
            have : ContinuousOn (fun θ => (log_Likelihood f X θ k μ ω).toReal) I := hcontR k ω
            simpa [I] using this)
          (by
            exact EReal.toReal_lt_toReal
              (fun a_1 ↦ hfl k (θ₀ + a.toReal) ω (id (Eq.symm a_1)))
              (hfs k (θ₀ + a.toReal) ω) (hfs k θ₀ ω)
              (fun a ↦ hfl k θ₀ ω (id (Eq.symm a)))
              (by simpa [AU, θU] using h.1))
          (by
            exact EReal.toReal_lt_toReal
              (fun a_1 ↦ hfl k (θ₀ - a.toReal) ω (id (Eq.symm a_1)))
              (hfs k (θ₀ - a.toReal) ω) (hfs k θ₀ ω)
              (fun a ↦ hfl k θ₀ ω (id (Eq.symm a)))
              (by simpa [AL, θL] using h.2)))

  let θ_hat := (fun k ω =>
      if h : (ω ∈ AU k) ∧ (ω ∈ AL k) then
        Classical.choose (hex k ω h) else θ₀)

  use θ_hat
  have h : ∀ (k: ℕ), ∀ (ω: Ω), ω ∈ A k → (ω ∈ AU k) ∧ (ω ∈ AL k) := by
    exact fun _ _ hω => ⟨Set.mem_of_mem_inter_left hω, Set.mem_of_mem_inter_right hω⟩

  let T : ℕ → Set Ω := fun k =>
    {ω : Ω |
      (edist (θ_hat k ω) θ₀ < a)
      ∧
      (deriv (fun θ => (log_Likelihood f X θ k μ ω).toReal) (θ_hat k ω) = 0) }

  have hsubset : ∀ k, A k ⊆ T k := by
    intro k ω hω
    have h : (ω ∈ AU k) ∧ (ω ∈ AL k) := by simpa [A] using hω
    simp only [T, θ_hat, Set.mem_setOf_eq, h, and_self, ↓reduceDIte]
    set hs :=
      (Classical.choose_spec (hex k ω h))
    refine ⟨hs.1, hs.2⟩

  have hmono : ∀ k, P (A k) ≤ P (T k) := by
    intro k
    exact measure_mono (hsubset k)

  have : Tendsto (fun k => P (T k)) atTop (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      hA (univ_tendsto_one P) (fun k => hmono k)
      (fun k => by simpa using (prob_le_one (μ := P) (s := T k)))

  simpa [hP, T] using this

theorem eventually_prob_gt_one_sub_half_pow
  {Ω : Type*} [MeasurableSpace Ω]
  {ProbFunSet : Set (Measure Ω)}
  (P : ℝ → ProbFunSet)
  (θ₀ : ℝ)
  [IsProbabilityMeasure (P θ₀).1]
  (A : ℕ → ℕ → Set Ω)
  (hA : ∀ n : ℕ, Tendsto (fun i ↦ (P θ₀).1 (A n i)) atTop (𝓝 (1 : ℝ≥0∞))) :
  ∀ n : ℕ, ∃ N0 : ℕ, ∀ i ≥ N0,
    (1 - ENNReal.ofReal (((2 : ℝ)⁻¹) ^ n)) < (P θ₀).1 (A n i) := by
  have hlt_one :
      ∀ n : ℕ, (1 : ℝ≥0∞) - ENNReal.ofReal (((2 : ℝ)⁻¹) ^ n) < 1 := by
    intro n
    simp only [inv_pow, Nat.ofNat_pos, pow_pos, ENNReal.ofReal_inv_of_pos,
      Nat.ofNat_nonneg, ENNReal.ofReal_pow, ENNReal.ofReal_ofNat]
    apply ENNReal.sub_lt_self ENNReal.one_ne_top (Ne.symm (zero_ne_one' ℝ≥0∞))
    rw [ENNReal.inv_ne_zero, ENNReal.pow_ne_top_iff]
    left
    exact Ne.symm ENNReal.top_ne_ofNat
  intro n
  rcases
      (Filter.eventually_atTop.1
        ((hA n).eventually (Ioi_mem_nhds (hlt_one n))))
    with ⟨N0, hN0⟩
  exact ⟨N0, fun i hi => hN0 i hi⟩

/-- If `u → 0` in `ℝ≥0∞`, then `(1 - u) → 1`. -/
lemma tendsto_one_tsub_of_tendsto_zero
    {α : Type*} {l : Filter α} {u : α → ℝ≥0∞}
    (hu : Tendsto u l (𝓝 (0 : ℝ≥0∞))) :
    Tendsto (fun x => (1 : ℝ≥0∞) - u x) l (𝓝 (1 : ℝ≥0∞)) := by
  refine tendsto_order.2 ⟨?_,
    fun _ hb => Filter.Eventually.of_forall (fun _ => lt_of_le_of_lt (tsub_le_self) hb)⟩
  intro a ha
  let ε : ℝ≥0∞ := (1 : ℝ≥0∞) - a
  have hεpos : 0 < ε := by
    simpa [ε] using (tsub_pos_iff_lt.2 ha)

  have hu_lt : ∀ᶠ x in l, u x < ε :=
    hu.eventually (Iio_mem_nhds hεpos)

  filter_upwards [hu_lt] with x hx

  have htsub : (1 : ℝ≥0∞) - ε < (1 : ℝ≥0∞) - u x := by
      have hε_ne_top : ε ≠ (⊤ : ℝ≥0∞) := by
        have hε_le_one : ε ≤ (1 : ℝ≥0∞) := by
          simp only [ε, tsub_le_iff_right, self_le_add_right]
        exact ne_of_lt (lt_of_le_of_lt hε_le_one (lt_top_iff_ne_top.2 (by simp)))

      have hlt_real : (u x).toReal < ε.toReal := by
        exact (ENNReal.toReal_lt_toReal (LT.lt.ne_top hx) hε_ne_top).2 hx

      have htoReal_left :
          ((1 : ℝ≥0∞) - ε).toReal = (1 : ℝ) - ε.toReal := by
        rw [ENNReal.toReal_sub_of_le (by simp only
          [ε, tsub_le_iff_right, self_le_add_right]) ENNReal.one_ne_top]
        simp only [ENNReal.toReal_one]

      have htoReal_right :
          ((1 : ℝ≥0∞) - u x).toReal = (1 : ℝ) - (u x).toReal := by
        rw [ENNReal.toReal_sub_of_le (Std.le_of_lt (LT.lt.trans_le hx (by
          simp only [ε, tsub_le_iff_right, self_le_add_right])))
          ENNReal.one_ne_top]
        simp only [ENNReal.toReal_one]

      exact (ENNReal.toReal_lt_toReal (ne_of_lt (lt_of_le_of_lt
        (tsub_le_self : (1 : ℝ≥0∞) - ε ≤ 1) (lt_top_iff_ne_top.2 (by
        simp only [ne_eq, ENNReal.one_ne_top, not_false_eq_true]))))
        (ne_of_lt (lt_of_le_of_lt (tsub_le_self : (1 : ℝ≥0∞) - (u x) ≤ 1)
        (lt_top_iff_ne_top.2 (by simp only
        [ne_eq, ENNReal.one_ne_top, not_false_eq_true]))))).1
        (by simpa [htoReal_left, htoReal_right] using (by linarith))

  have ha_le : a ≤ (1 : ℝ≥0∞) := le_of_lt ha
  have hone_sub_eps : (1 : ℝ≥0∞) - ε = a := by
    -- `ε = 1 - a`
    simp [ε, ENNReal.sub_sub_cancel ENNReal.one_ne_top ha_le]

  simpa [hone_sub_eps] using htsub

theorem theorem37
  {Ω : Type*} [MeasurableSpace Ω]
  {ProbFunSet : Set (Measure Ω)}
  (P : ℝ → ProbFunSet)
  (X : ℕ → Ω → ℝ) (θ₀ : ℝ) (μ : Measure ℝ := by volume_tac)
  [IsProbabilityMeasure (P θ₀).1]
  (hfs : ∀ (n : ℕ), ∀ (θ : ℝ), ∀ (ω : Ω), log_Likelihood P X θ n μ ω ≠ ⊤)
  (hfl : ∀ (n : ℕ), ∀ (θ : ℝ), ∀ (ω : Ω), ⊥ ≠ log_Likelihood P X θ n μ ω)
  (hcont : ∀ (a : ℝ≥0∞), ∀ (n : ℕ), ∀ (ω : Ω), ContinuousOn (fun θ => log_Likelihood P X θ n μ ω)
    (Set.Icc (θ₀ - a.toReal) (θ₀ + a.toReal)))
  (htendsto : ∀ (θ : ℝ), Tendsto (fun n : ℕ => ((P θ₀).1) {ω : Ω |
    log_Likelihood P X θ₀ n μ ω > log_Likelihood P X θ n μ ω}) atTop (𝓝 1))
  (hfinite :  ∀ (a : ℝ≥0∞),
    ∀ (k : ℕ) (ω : Ω) (θ : ℝ),
      θ ∈ Set.Icc (θ₀ - a.toReal) (θ₀ + a.toReal) →
        log_Likelihood P X θ k μ ω ≠ ⊥ ∧ log_Likelihood P X θ k μ ω ≠ ⊤):
  ∃ (θ_hat: ℕ → Ω → ℝ), ∀ (a : ℝ≥0∞), (0 < a) ∧ (a < ⊤) →
      Tendsto (fun i ↦ (P θ₀).1 {ω |  edist (θ_hat i ω) θ₀ < a ∧
        (deriv (fun θ => (log_Likelihood P X θ i μ ω).toReal) (θ_hat i ω) = 0)}) atTop (𝓝 1) :=by
  let aN : ℕ → ℝ≥0∞ := fun n => ( (n+1 : ℝ≥0∞) )⁻¹
  have aN_pos : ∀ n, 0 < aN n := by
    intro n; simp [aN]
  have aN_fin : ∀ n, aN n < (⊤ : ℝ≥0∞) := by
    intro n
    simp only [aN, ENNReal.inv_lt_top, add_pos_iff, Nat.cast_pos, zero_lt_one, or_true]
  have hex := fun n =>
    exists_consistent_estimator_of_logLikelihood P X θ₀ μ
      (aN n) (aN_pos n) (aN_fin n) hfs hfl (hcont (aN n)) htendsto (hfinite (aN n))

  choose θseq hθseq using hex
  let δ : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (( (2:ℝ)⁻¹ )^n)

  let Good : ℕ → ℕ → Set Ω := fun n i =>
    {ω | edist (θseq n i ω) θ₀ < aN n ∧
        deriv (fun θ => (log_Likelihood P X θ i μ ω).toReal) (θseq n i ω) = 0 }

  choose N hN using (eventually_prob_gt_one_sub_half_pow P θ₀ (fun n => fun i =>
      {ω | edist (θseq n i ω) θ₀ < ((n+1 : ℝ≥0∞)⁻¹) ∧
      deriv (fun θ ↦ (log_Likelihood P X θ i μ ω).toReal) (θseq n i ω) = 0}) hθseq)

  -- N : ℕ → ℕ
  -- hN : ∀ n, ∀ i ≥ N n, (1 - δ n) < P (Good n i)
  -- pick a_n = 1/(n+1)
  let m : ℕ → ℕ := fun i => Nat.findGreatest (fun n => N n ≤ i) i
  let θ_hat : ℕ → Ω → ℝ := fun i ω => θseq (m i) i ω
  use θ_hat
  intro a ha
  simp_rw [@Set.setOf_and]
  set Pr := (P θ₀).1

  -- abbreviate your target set (it matches the intersection form in the goal)
  let Target : ℕ → Set Ω := fun i =>
    {ω | edist (θ_hat i ω) θ₀ < a ∧
        deriv (fun θ => (log_Likelihood P X θ i μ ω).toReal) (θ_hat i ω) = 0}

  -- First rewrite goal into Target form
  have hTarget :
      (fun i =>
        Pr ({ω | edist (θ_hat i ω) θ₀ < a} ∩
          {ω | deriv (fun θ => (log_Likelihood P X θ i μ ω).toReal) (θ_hat i ω) = 0}))
        =
      (fun i => Pr (Target i)) := by
    funext i
    simp only [Target]
    rw [@Set.setOf_and]

  suffices Tendsto (fun i => Pr (Target i)) atTop (𝓝 (1:ℝ≥0∞)) by
    simpa [hTarget] using this

  -- N (m i) ≤ i
  have hm_spec_of_N0 : ∀ i, N 0 ≤ i → N (m i) ≤ i := by
    intro i hN0i
    have h0le : (0 : ℕ) ≤ i := Nat.zero_le i
    simpa [m] using (Nat.findGreatest_spec (P:= fun n => N n ≤ i) (n := i) h0le hN0i)

  have hN0_eventually : ∀ᶠ i in atTop, N 0 ≤ i := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨N 0, ?_⟩
    intro i hi
    exact hi

  --m i → ∞ i.e. ∀ n, eventually n ≤ m i
  have hm_ge : ∀ n, ∀ᶠ i in atTop, n ≤ m i := by
    intro n
    filter_upwards
      [Filter.eventually_atTop.2 ⟨max n (N n), by intro i hi; exact hi⟩] with i hi
    simpa [m] using (Nat.le_findGreatest (P := fun k => N k ≤ i)
      (le_trans (le_max_left _ _) hi) (le_trans (le_max_right _ _) hi))

  have hn0 : ∃ n0 : ℕ, aN n0 < a := by
    rcases exists_nat_one_div_lt
      (ENNReal.toReal_pos (ha.1).ne' (ha.2).ne) with ⟨n0, hn0⟩
    refine ⟨n0, ?_⟩
    rw [← ENNReal.toReal_lt_toReal (LT.lt.ne_top (aN_fin n0)) (LT.lt.ne_top ha.2)]
    simp only [aN]
    suffices 1 / (↑n0 + 1) = ((↑n0 + 1)⁻¹: ENNReal).toReal by
      rw [← this]
      exact hn0
    simp only [one_div, ENNReal.toReal_inv, inv_inj]
    rw [ENNReal.toReal_add (ENNReal.natCast_ne_top n0) ENNReal.one_ne_top]
    simp only [ENNReal.toReal_natCast, ENNReal.toReal_one]

  rcases hn0 with ⟨n0, hn0_lt⟩

  -- eventually 1 - δ (m i) < P(Target i)
  have hlower_target : ∀ᶠ i in atTop, (1 : ℝ≥0∞) - δ (m i) < Pr (Target i) := by
    have hlower : ∀ᶠ i in atTop, (1 : ℝ≥0∞) - δ (m i) < Pr (Good (m i) i) := by
      filter_upwards [hN0_eventually] with i hN0i
      exact hN (m i) i (hm_spec_of_N0 i hN0i)
    suffices hmonoP : ∀ᶠ i in atTop, Pr (Good (m i) i) ≤ Pr (Target i) by
      filter_upwards [hlower, hmonoP] with i hlt hle
      exact lt_of_lt_of_le hlt hle
    suffices ∀ᶠ i in atTop, Good (m i) i ⊆ Target i by
      filter_upwards [this] with i hsub
      exact measure_mono hsub
    -- eventually aN (m i) ≤ a
    have haN_eventually : ∀ᶠ i in atTop, aN (m i) ≤ a := by
      filter_upwards [hm_ge n0] with i hmi
      exact le_trans (by simpa [aN] using by exact_mod_cast Nat.succ_le_succ hmi)
        (le_of_lt hn0_lt)
    filter_upwards [haN_eventually] with i haN_le
    exact fun ω hω =>
      ⟨lt_of_lt_of_le hω.1 haN_le, by simpa [θ_hat, Good, Target] using hω.2⟩

  have hδ_tendsto0 : Tendsto (fun i => δ (m i)) atTop (𝓝 (0:ℝ≥0∞)) := by
    suffices Tendsto (fun n => δ n) atTop (𝓝 (0:ℝ≥0∞)) by
      refine this.comp (tendsto_atTop.2 (fun n =>by simpa using (hm_ge n)))
    have hδ_rewrite : (fun n => δ n) = fun n => (ENNReal.ofReal ((2:ℝ)⁻¹)) ^ n := by
      funext n
      simp [δ, ENNReal.ofReal_pow]
      rw [@ENNReal.inv_pow]
    simp only [hδ_rewrite, Nat.ofNat_pos, ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_ofNat,
      ENNReal.tendsto_pow_atTop_nhds_zero_iff, ENNReal.inv_lt_one, Nat.one_lt_ofNat]

  have hOneMinus := tendsto_one_tsub_of_tendsto_zero (u := fun i => δ (m i)) hδ_tendsto0

  -- Tendsto (fun i => P (Target i)) atTop (𝓝 (1 : ℝ≥0∞))
  refine (tendsto_order.2 ?_)
  constructor
  · intro r hr
    have hlt1 :
        ∀ᶠ i in atTop, r < (1 : ℝ≥0∞) - δ (m i) :=
      (hOneMinus.eventually (Ioi_mem_nhds hr))
    filter_upwards [hlt1, hlower_target] with i hir hil
    exact lt_trans hir hil
  · intro r hr
    have hle1 : ∀ i, (Pr (Target i) : ℝ≥0∞) ≤ (1 : ℝ≥0∞) := by
      intro i
      have hmono : Pr (Target i) ≤ Pr Set.univ :=
        measure_mono (Set.subset_univ (Target i))
      simp only [measure_univ] at hmono
      exact hmono
    rw [Filter.eventually_atTop]
    use 1
    intro i hi
    exact lt_of_le_of_lt (hle1 i) hr
