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

lemma exists_IsMaxOn_strict_endpoints
    (g : ℝ → ℝ) (θ₀ : ℝ) (a : ℝ≥0∞)
    (ha : 0 < a) (ha_fin : a < ⊤)
    (hcont : ContinuousOn g (Set.Icc (θ₀ - a.toReal) (θ₀ + a.toReal)))
    (h1 : g θ₀ > g (θ₀ + a.toReal))
    (h2 : g θ₀ > g (θ₀ - a.toReal)) :
    ∃ θ, edist θ θ₀ < a ∧ (IsMaxOn g (Set.Icc (θ₀ - a.toReal) (θ₀ + a.toReal)) θ) := by sorry

open scoped BigOperators
open Finset

lemma EReal.toReal_lt_toReal
    {a : EReal} {b : EReal}
    (ha1 : a ≠ ⊥) (ha2 : a ≠ ⊤) (hb1 : b ≠ ⊤) (hb2 : b ≠ ⊥) :
    a < b → a.toReal < b.toReal :=by sorry

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
    Tendsto (fun n => P (s n ∩ t n)) atTop (𝓝 (1 : ℝ≥0∞)) := by sorry


lemma Measurable_log_Likelihood
    {Ω : Type*} [MeasurableSpace Ω]
    {ProbFunSet : Set (Measure Ω)} (f : ℝ → ↑ProbFunSet) (μ : Measure ℝ := by volume_tac)
    (X : ℕ → Ω → ℝ) (θ₀ : ℝ) (k : ℕ) :
    Measurable
    (fun ω : Ω => log_Likelihood f X θ₀ k μ ω) := by sorry


example (α : Type*) (p q : α → Prop): {x | (p x) ∧ q x} = {x | p x} ∩ {x | q x} := by
  rw [@Set.setOf_and]

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
        (IsMaxOn (fun θ => (log_Likelihood f X θ i μ ω).toReal)
        (Set.Icc (θ₀ - a.toReal) (θ₀ + a.toReal)) (θ_hat i ω))})
      atTop (𝓝 1) := by

  set θU : ℝ := θ₀ + a.toReal
  set θL : ℝ := θ₀ - a.toReal

  let AU : ℕ → Set Ω := fun k => {ω : Ω |
    log_Likelihood f X θ₀ k μ ω > log_Likelihood f X θU k μ ω}
  let AL : ℕ → Set Ω := fun k => {ω : Ω |
    log_Likelihood f X θ₀ k μ ω > log_Likelihood f X θL k μ ω}
  let A : ℕ → Set Ω := fun k => AU k ∩ AL k

  set P := (f θ₀).1
  have hAU : Tendsto (fun k => P (AU k)) atTop (𝓝 1) := by
    simpa [P, θU, AU] using htendsto θU
  have hAL : Tendsto (fun k => P (AL k)) atTop (𝓝 1) := by
    simpa [P, θL, AL] using htendsto θL

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

  let θ_hat := (fun k ω =>
      if h : (ω ∈ AU k) ∧ (ω ∈ AL k) then
        Classical.choose
          (exists_IsMaxOn_strict_endpoints
            (g := fun θ => (log_Likelihood f X θ k μ ω).toReal)
            (θ₀ := θ₀) (a := a)
            ha ha_fin
            (by
              have : ContinuousOn (fun θ => (log_Likelihood f X θ k μ ω).toReal) I := hcontR k ω
              simpa [I] using this)
            (by
              have : (log_Likelihood f X (θ₀ + a.toReal) k μ ω).toReal
                  < (log_Likelihood f X θ₀ k μ ω).toReal := by
                exact EReal.toReal_lt_toReal
                  (fun a_1 ↦ hfl k (θ₀ + a.toReal) ω (id (Eq.symm a_1)))
                  (hfs k (θ₀ + a.toReal) ω)
                  (hfs k θ₀ ω)
                  (fun a ↦ hfl k θ₀ ω (id (Eq.symm a)))
                  (by simpa [AU, θU] using h.1)
              simpa [θU] using this)
            (by
              have : (log_Likelihood f X (θ₀ - a.toReal) k μ ω).toReal
                  < (log_Likelihood f X θ₀ k μ ω).toReal := by
                exact EReal.toReal_lt_toReal
                  (fun a_1 ↦ hfl k (θ₀ - a.toReal) ω (id (Eq.symm a_1)))
                  (hfs k (θ₀ - a.toReal) ω)
                  (hfs k θ₀ ω)
                  (fun a ↦ hfl k θ₀ ω (id (Eq.symm a)))
                  (by simpa [AL, θL] using h.2)
              simpa [θL] using this))
      else θ₀)

  use θ_hat

  let T : ℕ → Set Ω := fun i =>
    {ω | edist (θ_hat i ω) θ₀ < a
    ∧ IsMaxOn (fun θ ↦ (log_Likelihood f X θ i μ ω).toReal) I (θ_hat i ω)}

  have hsubset : ∀ k, A k ⊆ T k := by
    intro k ω hω
    have h : ω ∈ AU k ∧ ω ∈ AL k := by simpa [A] using hω
    simp only [T, θ_hat, Set.mem_setOf_eq, h]
    simp only [and_self, ↓reduceDIte]
    set hs :=
      (Classical.choose_spec
        (exists_IsMaxOn_strict_endpoints
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
              (by simpa [AL, θL] using h.2))))
    have h1 := hs.1
    refine ⟨hs.1, hs.2⟩

  have hmono : ∀ k, P (A k) ≤ P (T k) := by
    intro k
    exact measure_mono (hsubset k)

  have : Tendsto (fun k => P (T k)) atTop (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      hA (univ_tendsto_one P) (fun k => hmono k)
      (fun k => by simpa using (prob_le_one (μ := P) (s := T k)))

  simpa [P, T] using this



theorem exists_tendstoInProbability_of_prob_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω]
    {ProbFunSet : Set (Measure Ω)}
    (θ₀ : ℝ)
    (P : ℝ → ProbFunSet)
    (X : ℕ → Ω → ℝ) (θ₀ : ℝ) (μ : Measure ℝ := by volume_tac)
    [IsProbabilityMeasure (P θ₀).1]
    (h : ∀ (a : ENNReal), 0 < a → ∃ (θ_hat : ℕ → Ω → ℝ),
    Tendsto (fun i => (P θ₀).1 { ω |
        (edist (θ_hat i ω) θ₀ < a) ∧
        (IsMaxOn (fun θ => (log_Likelihood P X θ i μ ω).toReal)
        (Set.Icc (θ₀ - a.toReal) (θ₀ + a.toReal)) (θ_hat i ω))}) atTop (𝓝 1)) :
    ∃ (θ_hat: ℕ → Ω → ℝ), ∀ (ε : ℝ≥0∞), 0 < ε →
      Tendsto (fun i ↦ (P θ₀).1 { ω |
        (edist (θ_hat i ω) θ₀ < ε) ∧
        (IsMaxOn (fun θ => (log_Likelihood P X θ i μ ω).toReal)
        (Set.Icc (θ₀ - ε.toReal) (θ₀ + ε.toReal)) (θ_hat i ω))}) atTop (𝓝 1):= by
  -- pick a_n = 1/(n+1)
  let a : ℕ → ENNReal := fun n => ( (n+1 : ENNReal) )⁻¹
  have a_pos : ∀ n, 0 < a n := by
    intro n
    simp [a]  -- (n+1:ENNReal) ≠ 0, so its inverse is > 0
  have hex : ∀ n, ∃ θ : ℕ → Ω → ℝ,
      Tendsto (fun i => P {ω | a n ≤ edist (θ i ω) θ₀}) atTop (𝓝 0) := by
    intro n
    exact h (a n) (a_pos n)

  choose θseq hθseq using hex

  simp_rw [@ENNReal.tendsto_atTop_zero] at hθseq


  have hθseq': ∀ (n : ℕ), ∃ N, P
    {ω | a n ≤ edist (θseq n N ω) θ₀} ≤ ENNReal.ofReal (((2:ℝ)⁻¹)^n):=by
    intro n
    obtain ⟨N, hN⟩ := (fun n => hθseq n (ENNReal.ofReal (((2:ℝ)⁻¹)^n))
      (by simp only [inv_pow, Nat.ofNat_pos,
      pow_pos, ENNReal.ofReal_inv_of_pos, Nat.ofNat_nonneg, ENNReal.ofReal_pow,
      ENNReal.ofReal_ofNat, gt_iff_lt, ENNReal.inv_pos, ne_eq, ENNReal.pow_eq_top_iff,
      ENNReal.ofNat_ne_top, false_and, not_false_eq_true])) n
    specialize hN N (by simp only [ge_iff_le, le_refl])
    use N

  choose f hanθP using hθseq'


  let θ_hat : ℕ → Ω → ℝ := fun n => fun ω => θseq n (f n) ω
  use θ_hat
  intro b hb
  rw [@ENNReal.tendsto_atTop_zero]
  intro ε hε

  obtain ⟨N₁, hN₁, hN₁_pow⟩ : ∃ N₁ > 0, ENNReal.ofReal (((2:ℝ)⁻¹)^N₁) < ε :=by
    by_cases htop : ε = ∞
    · use 1
      rw [htop]
      simp only [gt_iff_lt, zero_lt_one, pow_one, Nat.ofNat_pos, ENNReal.ofReal_inv_of_pos,
        ENNReal.ofReal_ofNat, true_and, ENNReal.inv_lt_top, Nat.ofNat_pos]
    · by_cases h1: ε.toReal < 1
      · have hε_toReal_pos : (0 : ℝ) < ε.toReal := by
          change 0 < ε at hε
          refine (ENNReal.ofReal_lt_iff_lt_toReal (ENNReal.toReal_nonneg (a := 0)) htop).mp ?_
          simp only [ENNReal.toReal_zero, ENNReal.ofReal_zero]
          exact hε
        have hhalf0 : (0 : ℝ) < (2 : ℝ)⁻¹ := by nlinarith
        have hhalf1 : (2 : ℝ)⁻¹ < 1 := by nlinarith
        rcases exists_pow_lt_of_lt_one hε_toReal_pos hhalf1 with ⟨n, hn⟩
        refine ⟨n, ?_⟩
        have hleft_ne_top : ENNReal.ofReal ((2 : ℝ)⁻¹ ^ n) ≠ ∞ := by
          simp only [inv_pow, Nat.ofNat_pos, pow_pos, ENNReal.ofReal_inv_of_pos, Nat.ofNat_nonneg,
            ENNReal.ofReal_pow, ENNReal.ofReal_ofNat, ne_eq, ENNReal.inv_eq_top, pow_eq_zero_iff',
            OfNat.ofNat_ne_zero, false_and, not_false_eq_true]
        have hε_ne_top : ε ≠ ∞ := htop
        have h_toReal :
            (ENNReal.ofReal (((2 : ℝ)⁻¹) ^ n)).toReal < ε.toReal := by
          simpa using hn
        by_cases hn0: n > 0
        · refine ⟨ hn0, (ENNReal.toReal_lt_toReal hleft_ne_top hε_ne_top).1 h_toReal⟩
        · have h0 : n = 0 := by exact Nat.eq_zero_of_not_pos hn0
          exfalso
          rw [h0] at hn
          simp only [pow_zero] at hn
          exact (lt_self_iff_false 1).mp (lt_trans hn h1)

      · use 1
        have h1' := Std.not_lt.mp h1
        rw [← propext (ENNReal.ofReal_le_iff_le_toReal htop)] at h1'
        simp only [ENNReal.ofReal_one] at h1'
        simp only [Nat.ofNat_pos, ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_ofNat, pow_one,
          gt_iff_lt]
        have h: (2: ENNReal)⁻¹ < 1 := by exact ENNReal.one_half_lt_one
        simp only [zero_lt_one, true_and, gt_iff_lt]
        exact Std.lt_of_lt_of_le h h1'
  have ⟨N₂, hN₂, hN₂_lt_b⟩  : ∃ N₂ > 0, a N₂ < b :=by
    unfold a
    simp only [gt_iff_lt]
    by_cases htop : b = ⊤
    · refine ⟨1, by decide, ?_⟩
      rw [htop]
      simp only [Nat.cast_one, ENNReal.inv_lt_top, pos_add_self_iff, zero_lt_one]
    · have hb_toReal : 0 < b.toReal := by
        simpa using ENNReal.toReal_pos hb.ne' htop
      rcases exists_nat_one_div_lt hb_toReal with ⟨n, hn⟩
      refine ⟨n + 1, Nat.succ_pos n, ?_⟩
      have : ((↑(n + 1) + 1 : ℝ≥0∞)⁻¹).toReal < b.toReal := by
        have hpos : (0 : ℝ) < (n + 1 : ℝ) := by
          exact_mod_cast (Nat.succ_pos n)
        have : (1 : ℝ) / (n + 2) < b.toReal := lt_trans (by simpa
          [one_div] using (one_div_lt_one_div_of_lt hpos (by linarith))) hn
        simp only [Nat.cast_add, Nat.cast_one, ENNReal.toReal_inv, gt_iff_lt]
        rw [add_assoc, one_add_one_eq_two]
        simpa using this

      exact (ENNReal.toReal_lt_toReal (by simp) htop).1 this
  let N := max N₁ N₂
  use N
  intro n hn
  have hn_lt_ε : ENNReal.ofReal (((2:ℝ)⁻¹)^n) < ε :=
    lt_of_le_of_lt (ENNReal.ofReal_mono (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (le_trans (le_max_left N₁ N₂) hn))) (by simpa using hN₁_pow)
  have hbset_aset: { ω | b ≤ edist (θ_hat n ω) θ₀} ⊆ { ω | a n ≤ edist (θ_hat n ω) θ₀} :=by
    simp only [Set.setOf_subset_setOf]
    intro ω hω
    have haNb : a n ≤ b := by
      have h_aN_le_aN2 : a n ≤ a N₂ :=by
        unfold a
        simp only [ENNReal.inv_le_inv]
        refine (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).mpr ?_
        exact Nat.cast_le.mpr (le_trans (le_max_right N₁ N₂) hn)
      exact le_trans h_aN_le_aN2 (le_of_lt hN₂_lt_b)
    exact le_trans haNb (by simpa using hω)
  have hP_le: P {ω | b ≤ edist (θ_hat n ω) θ₀} ≤ P { ω | a n ≤ edist (θ_hat n ω) θ₀} := by
    exact OuterMeasureClass.measure_mono P hbset_aset
  exact le_of_lt (Std.lt_of_le_of_lt hP_le (lt_of_le_of_lt (hanθP n) hn_lt_ε))


theorem exists_tendstoInProbability_of_prob_tendsto_zero'
  {Ω : Type*} [MeasurableSpace Ω]
  {ProbFunSet : Set (Measure Ω)}
  (f : ℝ → ProbFunSet)
  (X : ℕ → Ω → ℝ) (θ₀ : ℝ) (μ : Measure ℝ := by volume_tac)
  [IsProbabilityMeasure (f θ₀).1]
  (hfs : ∀ (n : ℕ), ∀ (θ : ℝ), ∀ (ω : Ω), log_Likelihood f X θ n μ ω ≠ ⊤)
  (hfl : ∀ (n : ℕ), ∀ (θ : ℝ), ∀ (ω : Ω), ⊥ ≠ log_Likelihood f X θ n μ ω)
  (hcont : ∀ (a : ℝ≥0∞), ∀ (n : ℕ), ∀ (ω : Ω), ContinuousOn (fun θ => log_Likelihood f X θ n μ ω)
    (Set.Icc (θ₀ - a.toReal) (θ₀ + a.toReal)))
  (htendsto : ∀ (θ : ℝ), Tendsto (fun n : ℕ => ((f θ₀).1) {ω : Ω |
    log_Likelihood f X θ₀ n μ ω > log_Likelihood f X θ n μ ω}) atTop (𝓝 1))
  (hfinite :  ∀ (a : ℝ≥0∞),
    ∀ (k : ℕ) (ω : Ω) (θ : ℝ),
      θ ∈ Set.Icc (θ₀ - a.toReal) (θ₀ + a.toReal) →
        log_Likelihood f X θ k μ ω ≠ ⊥ ∧ log_Likelihood f X θ k μ ω ≠ ⊤):
  ∃ (θ_hat: ℕ → Ω → ℝ), ∀ (a : ℝ≥0∞), (0 < a) ∧ (a < ⊤) →
      Tendsto (fun i ↦ (f θ₀).1 {ω |  edist (θ_hat i ω) θ₀ < a ∧
        (deriv (fun θ => (log_Likelihood f X θ i μ ω).toReal) (θ_hat i ω) = 0)}) atTop (𝓝 1) :=by
  sorry


def pdf_support {Ω : Type u_1} {E : Type u_2} [MeasurableSpace E]
  {h : MeasurableSpace Ω} (X : Ω → E) (P : Measure Ω) (μ : Measure E := by volume_tac):=
  Function.support (pdf X P μ)

noncomputable abbrev log_sum_ratio_rv {Ω : Type*} [MeasurableSpace Ω]
  {ProbFunSet : Set (Measure Ω)} (f : ℝ → ProbFunSet)
  (μ : Measure ℝ := by volume_tac)
  (X : ℕ → Ω → ℝ) (θ₀ θ : ℝ) : ℕ → Ω → ℝ :=
  fun i => fun (ω : Ω) =>
    Real.log ((pdf (X 0) (f θ).1 μ (X i ω)).toReal/ (pdf (X 0) (f θ₀).1 μ (X i ω)).toReal)

theorem log_likelihood_consistency_sublevel_measure_tendsto_one
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
      log_Likelihood f X θ₀ n μ ω > log_Likelihood f X θ n μ ω}) atTop (𝓝 1)
 := by sorry


theorem theorem37
    {Ω : Type*} [MeasurableSpace Ω]
    {ProbFunSet : Set (Measure Ω)}
    (f : ℝ → ProbFunSet)
    (X : ℕ → Ω → ℝ) (θ₀ : ℝ) (μ : Measure ℝ := by volume_tac)
    [IsFiniteMeasure μ]
    (hcont : ∀ (a : ℝ≥0∞), ∀ (n : ℕ), ∀ (ω : Ω), ContinuousOn (fun θ => log_Likelihood f X θ n μ ω)
      (Set.Icc (θ₀ - a.toReal) (θ₀ + a.toReal)))
    (hIsProbabilityMeasure: ∀ (θ: ℝ), IsProbabilityMeasure (f θ).1)
    (hHasPDF: ∀ (θ : ℝ), HasPDF (X 0) (↑(f θ)) μ)
    (hX : ∀ (n : ℕ), ∀ (ω : Ω), ∀ (i : Fin n), (X i ω) ∈ pdf_support (X 0) (f θ₀).1 μ)
    (h0 : ∀ (θ₁ θ₂ : ℝ), pdf_support (X 0) (f θ₁).1 μ = pdf_support (X 0) (f θ₂).1 μ)
    {s : NNReal}
    (hfs : ∀ (θ : ℝ), ∀ (a : ℝ), pdf (X 0) ((f θ)) μ a ≤ s)
    (hfl : ∀ (θ : ℝ), ∀ (a : ℝ), 0 < (pdf (X 0) ((f θ)) μ a).toReal)
    {S : Set ℝ} {hs1 : S ⊆ (Set.Iio 0)} {hs2 : Convex ℝ S}
    {hs3 : ContinuousOn Real.log S} {hs4 : IsClosed S}
    (hrv : ∀ (i : ℕ), Measurable (X i))
    (hindep : iIndepFun X (f θ₀))
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) (f θ₀) (f θ₀))
    {hs5 : ∀ (θ: ℝ), ∀ᵐ (x : Ω) ∂(f θ₀).1, (pdf (X 0) (↑(f θ)) μ (X 0 x)).toReal /
      (pdf (X 0) (↑(f θ₀)) μ (X 0 x)).toReal ∈ S}
    (hint : ∀ (θ: ℝ), Integrable (fun ω ↦ (pdf (X 0) (↑(f θ)) μ (X 0 ω)).toReal /
      (pdf (X 0) (↑(f θ₀)) μ (X 0 ω)).toReal) ↑(f θ₀))
    (hne_const : ∀ (θ: ℝ), ¬ ((fun ω ↦ ((pdf (X 0) (↑(f θ)) μ (X 0 ω)).toReal /
      (pdf (X 0) (↑(f θ₀)) μ (X 0 ω)).toReal)) =ᶠ[ae (f θ₀).1]
  Function.const Ω
    (⨍ (x : Ω),
      (fun ω ↦ ((pdf (X 0) (↑(f θ)) μ (X 0 ω)).toReal /
      (pdf (X 0) (↑(f θ₀)) μ (X 0 ω)).toReal)) x ∂↑(f θ₀))))
    :
    ∃ (θ_hat: ℕ → Ω → ℝ), ∀ (a : ℝ≥0∞), (0 < a) ∧ (a < ⊤) →
      Tendsto (fun i ↦ (f θ₀).1 {ω |  edist (θ_hat i ω) θ₀ < a ∧
        (deriv (fun θ => (log_Likelihood f X θ i μ ω).toReal) (θ_hat i ω) = 0)}) atTop (𝓝 1)
 := by sorry

#check ConvexOn.map_integral_le
theorem theorem37'
    {α : Type u} {ProbFunSet : Set (PMF α)} {Ω : Type u_1} [MeasurableSpace Ω]
    (f : ℝ → ProbFunSet) (θ θ₀ : ℝ) (ω : Set ℝ) (hω : IsOpen ω) (h3 : θ₀ ∈ ω) (x_set : Finset α)
    (x_set_fun : ℕ → α) (P : ProbabilityMeasure Ω) :  ∃ (θ: ℕ → Ω → ℝ),
    ∀ (n : ℕ), deriv g (θ n)  = 0
    ∧ TendstoInProbability θ P θ₀:= by
  rw [Metric.isOpen_iff] at hω
  obtain ⟨a, ha, hω⟩ := hω θ₀ h3
  sorry
