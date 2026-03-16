import Mathlib.MeasureTheory.Integral.IntervalAverage
import Mathlib.Probability.StrongLaw
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import MLE.Measure
import MLE.Defs
import MLE.Basic
import MLE.ENNReal
import MLE.EReal

universe u v u_1 u_2


open TopologicalSpace Filter MeasureTheory
open scoped NNReal ENNReal MeasureTheory Topology

open Filter MeasureTheory ProbabilityTheory

open scoped NNReal ENNReal MeasureTheory Topology

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
  (hrv : ∀ (i : ℕ), Measurable (X i))
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
        (measurableSet_lt (Measurable_log_Likelihood f μ θU k hrv)
          (Measurable_log_Likelihood f μ θ₀ k hrv))
    have hmsL : ∀ k, MeasurableSet (AL k) := by
      intro k
      simpa [AL, gt_iff_lt] using
        (measurableSet_lt (Measurable_log_Likelihood f μ θL k hrv)
          (Measurable_log_Likelihood f μ θ₀ k hrv))
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
    simp [ε, ENNReal.sub_sub_cancel ENNReal.one_ne_top ha_le]

  simpa [hone_sub_eps] using htsub


/--
**Existence of a consistent root of the likelihood equation.**

Assume the log-likelihood `log_Likelihood P X θ n μ` is finite and continuous
in `θ` on every compact interval around the true parameter `θ₀`. Suppose also
that the true parameter asymptotically dominates every other parameter in the
sense that

`P θ₀ {ω | log_Likelihood P X θ₀ n μ ω > log_Likelihood P X θ n μ ω} → 1`

for every `θ`.

Then there exists a sequence of estimators `θ_hat n ω` such that, for any
radius `a > 0`, with probability tending to `1` as `n → ∞`.
-/
theorem exists_likelihood_root_tendsto
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
  (hrv : ∀ (i : ℕ), Measurable (X i))
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
      (aN n) (aN_pos n) (aN_fin n) hfs hfl (hcont (aN n)) htendsto hrv (hfinite (aN n))

  choose θseq hθseq using hex
  let δ : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (( (2:ℝ)⁻¹ )^n)

  let Good : ℕ → ℕ → Set Ω := fun n i =>
    {ω | edist (θseq n i ω) θ₀ < aN n ∧
        deriv (fun θ => (log_Likelihood P X θ i μ ω).toReal) (θseq n i ω) = 0 }

  choose N hN using (eventually_prob_gt_one_sub_half_pow P θ₀ (fun n => fun i =>
      {ω | edist (θseq n i ω) θ₀ < ((n+1 : ℝ≥0∞)⁻¹) ∧
      deriv (fun θ ↦ (log_Likelihood P X θ i μ ω).toReal) (θseq n i ω) = 0}) hθseq)

  let m : ℕ → ℕ := fun i => Nat.findGreatest (fun n => N n ≤ i) i
  let θ_hat : ℕ → Ω → ℝ := fun i ω => θseq (m i) i ω
  use θ_hat
  intro a ha
  simp_rw [@Set.setOf_and]
  set Pr := (P θ₀).1

  let Target : ℕ → Set Ω := fun i =>
    {ω | edist (θ_hat i ω) θ₀ < a ∧
        deriv (fun θ => (log_Likelihood P X θ i μ ω).toReal) (θ_hat i ω) = 0}

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

  have hm_spec_of_N0 : ∀ i, N 0 ≤ i → N (m i) ≤ i := by
    intro i hN0i
    have h0le : (0 : ℕ) ≤ i := Nat.zero_le i
    simpa [m] using (Nat.findGreatest_spec (P:= fun n => N n ≤ i) (n := i) h0le hN0i)

  have hN0_eventually : ∀ᶠ i in atTop, N 0 ≤ i := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨N 0, ?_⟩
    intro i hi
    exact hi

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
