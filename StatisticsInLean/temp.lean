import Mathlib
import StatisticsInLean.theorem3_2

universe u v u_1 u_3

open TopologicalSpace Filter
open scoped NNReal ENNReal MeasureTheory Topology

namespace MeasureTheory

theorem measure_inter_le
    {α : Type u_1} {F : Type u_3} [FunLike F (Set α) ENNReal] [OuterMeasureClass F α]
    {μ : F} (s t : Set α) : μ (s ∩ t) ≤ μ s + μ t :=
  Std.IsPreorder.le_trans (μ (s ∩ t)) (μ (s ∪ t)) (μ s + μ t)
  (OuterMeasureClass.measure_mono μ
  (fun _ a_1 ↦ Set.subset_union_left (Set.inter_subset_left a_1)))
  (measure_union_le s t)

end MeasureTheory

namespace PMF

lemma measure_tendsto_zero_of_le_add {α ι : Type*} [Preorder ι] [MeasurableSpace α]
    {p : PMF α} {l : Filter ι} {A B C : ι → Set α}
    (hl : Tendsto (fun i => p.toMeasure (A i)) l (nhds 0))
    (hr : Tendsto (fun i => p.toMeasure (B i)) l (nhds 0))
    (h : ∀ (i : ι), p.toMeasure (C i) ≤ p.toMeasure (A i) + p.toMeasure (B i)) :
    Tendsto (fun i => p.toMeasure (C i)) l (nhds 0):= by
  apply Filter.Tendsto.squeeze (g := fun i => p.toMeasure {})
    (h := fun i => p.toMeasure (A i) + p.toMeasure (B i))
  · simp only [MeasureTheory.measure_empty]
    exact tendsto_const_nhds
  · rw [← add_zero 0]
    apply Filter.Tendsto.add hl hr
  · intro i
    simp only [MeasureTheory.measure_empty, zero_le]
  · intro i
    exact h i

lemma measure_tendsto_one_of_le_add {α ι : Type*} [Preorder ι] [MeasurableSpace α]
    {p : PMF α} {l : Filter ι} {A B C : ι → Set α}
    (hA : ∀ i, MeasurableSet (A i))
    (hB : ∀ i, MeasurableSet (B i))
    (hC : ∀ i, MeasurableSet (C i))
    (hl : Tendsto (fun i => p.toMeasure (A i)) l (nhds 1))
    (hr : Tendsto (fun i => p.toMeasure (B i)) l (nhds 1))
    (h : ∀ (i : ι), p.toMeasure (C i)ᶜ ≤ p.toMeasure (A i)ᶜ + p.toMeasure (B i)ᶜ) :
    Tendsto (fun i => p.toMeasure (C i)) l (nhds 1):= by
  have hcompl_compl: ∀ (S : ι → Set α),
    ∀ (i : ι), p.toMeasure (S i) = p.toMeasure (S i)ᶜᶜ := by
    intro S i
    rw [compl_compl]
  simp_rw [hcompl_compl] at hl hr ⊢
  rw [← tendsto_measure_compl_iff (p:= p) (l := l)
    (fun (i : ι) => MeasurableSet.compl_iff.mpr (hC i))]
  rw [← tendsto_measure_compl_iff (p:= p) (l := l)
    (fun (i : ι) => MeasurableSet.compl_iff.mpr (hA i))] at hl
  rw [← tendsto_measure_compl_iff (p:= p) (l := l)
    (fun (i : ι) => MeasurableSet.compl_iff.mpr (hB i))] at hr
  apply Filter.Tendsto.squeeze (g := fun i => p.toMeasure {})
    (h := fun i => p.toMeasure (A i)ᶜ + p.toMeasure (B i)ᶜ)
  · simp only [MeasureTheory.measure_empty]
    exact tendsto_const_nhds
  · rw [← add_zero 0]
    apply Filter.Tendsto.add hl hr
  · intro i
    simp only [MeasureTheory.measure_empty, zero_le]
  · intro i
    exact h i

end PMF

namespace RandomVariable

def C {α : Type*} {β : Type*} (Ω : Type u_1) (X : α → β) : α → Ω → β := fun n _ => X n

end RandomVariable

namespace ProbabilityMeasure

open MeasureTheory

def TendstoInProbability {Ω : Type u_1} [MeasurableSpace Ω] (X : ℕ → (Ω → ℝ))
    (P : ProbabilityMeasure Ω) (c : ℝ):= TendstoInMeasure (P.toMeasure) X atTop (fun _ => c)
end ProbabilityMeasure

open Filter MeasureTheory ProbabilityTheory Likelihood ProbabilityMeasure PMF

abbrev root_of_deriv (f : ℝ → ENNReal):= {(θ: ℝ) | deriv (fun x => (f x).toReal) θ = 0}

theorem theorem3_7
    {s : Set ℝ} {hs1 : s ⊆ (Set.Iio 0)} {hs2 : Convex ℝ s}
    {hs3 : ContinuousOn Real.log s} {hs4 : IsClosed s}
    {ProbFunSet : Set (PMF ℝ)} (f : ℝ → ↑ProbFunSet) (θ₀ θ : ℝ)
    (X : ℕ → ℝ → ℝ) (hrv : ∀ (i : ℕ), Measurable (X i))
    {hs5 : ∀ (θ : ℝ), ∀ᵐ (x : ℝ) ∂((f θ₀).1).toMeasure,
    ((f θ).1.1 (X 0 x)).toReal / ((f θ₀).1.1 (X 0 x)).toReal ∈ s}
    (hindep : iIndepFun X ((f θ₀).1.toMeasure))
    (hident : ∀ i, IdentDistrib (X i) (X 0) ((f θ₀).1.toMeasure) ((f θ₀).1.toMeasure))
    (hX : ∀ (n : ℕ), ∀ (ω : ℝ), ∀ (i : Fin n), X i ω ∈ (f θ₀).1.support)
    (hid : ∀ (n : ℕ), ∀ (ω : ℝ), X n ω = ω)
    (h0 : ∀ (θ₁ θ₂ : ℝ), (f θ₁).1.support = (f θ₂).1.support)
    (hint1 : ∀ (θ : ℝ), Integrable (log_sum_ratio_rv f X θ₀ θ 0) (f θ₀).1.toMeasure)
    (hint2 : ∀ (θ : ℝ), Integrable (fun x ↦ ((f θ).1.1 (X 0 x)).toReal /
    ((f θ₀).1.1 (X 0 x)).toReal) ((f θ₀).1).toMeasure)
    (hMeasurable : ∀ (θ : ℝ), Measurable (f θ).1.1)
    (hne_const : ∀ (θ : ℝ), ¬ ((fun x ↦ ((f θ).1.1 (X 0 x)).toReal / ((f θ₀).1.1 (X 0 x)).toReal)
    =ᶠ[ae ((f θ₀).1).toMeasure] Function.const ℝ (⨍ (x : ℝ), ((f θ).1.1 (X 0 x)).toReal /
    ((f θ₀).1.1 (X 0 x)).toReal ∂((f θ₀).1).toMeasure)))
    (P : ProbabilityMeasure ℝ)
    (ω : Set ℝ) (hω : IsOpen ω) (h3 : θ₀ ∈ ω)
    :
    ∃ (θ: ℕ → ℝ), ∀ (i : ℝ),
    (∀ (n : ℕ), (θ n) ∈ root_of_deriv (fun
    θ => Likelihood f X θ n i))
    ∧ (TendstoInProbability (RandomVariable.C ℝ θ) P θ₀)
  := by
  rw [Metric.isOpen_iff] at hω
  obtain ⟨a, ha, hω⟩ := hω θ₀ h3
  let A := fun (n: ℕ) => likelihoodStrictSublevelSet X n θ₀ (θ₀ - a) f
  let B := fun (n: ℕ) => likelihoodStrictSublevelSet X n θ₀ (θ₀ + a) f
  let S := fun (n: ℕ) => (likelihoodStrictSublevelSet X n θ₀ (θ₀ - a) f) ∩
    (likelihoodStrictSublevelSet X n θ₀ (θ₀ + a) f)
  have h : ∀ (n : ℕ), ((f θ₀).1).toMeasure (S n)ᶜ ≤ ((f θ₀).1).toMeasure (A n)ᶜ
    + ((f θ₀).1).toMeasure (B n)ᶜ :=by
    intro n
    unfold S A B
    nth_rw 1 [← compl_compl (likelihoodStrictSublevelSet X n θ₀ (θ₀ - a) f)]
    nth_rw 1 [← compl_compl (likelihoodStrictSublevelSet X n θ₀ (θ₀ + a) f)]
    rw [← Set.union_eq_compl_compl_inter_compl]
    apply measure_union_le
  have hl: ∀ᵐ _ ∂((f θ₀).1.toMeasure),
    Tendsto (fun i => ((f θ₀).1).toMeasure (A i)) atTop (nhds 1):=by
    exact likelihood_consistency_sublevel_measure_tendsto_one (θ₀ - a)
      (s := s) f θ₀ X hrv hindep hident hX hid h0 (hint1 (θ₀ - a)) (hint2 (θ₀ - a))
      hMeasurable (hne_const (θ₀ - a)) (hs5 := hs5 (θ₀ - a)) (hs4 := hs4) (hs3 := hs3)
      (hs2 := hs2) (hs1 := hs1)
  have hr: ∀ᵐ _ ∂((f θ₀).1.toMeasure),
    Tendsto (fun i => ((f θ₀).1).toMeasure (B i)) atTop (nhds 1):=by
    exact likelihood_consistency_sublevel_measure_tendsto_one (θ₀ + a)
      (s := s) f θ₀ X hrv hindep hident hX hid h0 (hint1 (θ₀ + a)) (hint2 (θ₀ + a))
      hMeasurable (hne_const (θ₀ + a)) (hs5 := hs5 (θ₀ + a)) (hs4 := hs4) (hs3 := hs3)
      (hs2 := hs2) (hs1 := hs1)
  simp only [eventually_const] at hl hr
  have hA : ∀ (n: ℕ), MeasurableSet (A n) := by sorry
  have hB : ∀ (n: ℕ), MeasurableSet (B n) := by sorry
  have hS : ∀ (n: ℕ), MeasurableSet (S n) := by sorry
  have hSn:= measure_tendsto_one_of_le_add hA hB hS hl hr h










  sorry
