import Mathlib

noncomputable def Likelihood.{u, v} {α : Type u} {ProbFunSet : Set (PMF α)} {β : Type v}
    (P : β → ↑ProbFunSet) (θ : β) (Xset : Finset α):= ∏ (x : Xset), (P θ).1.1 x

def MaximumLikelihoodEstimator.{u, v} {α : Type u} {ProbFunSet : Set (PMF α)} {β : Type v}
    (P : β → ↑ProbFunSet) (Xset : Finset α):=
  {θ_max : β // Likelihood P θ_max Xset = sSup (Set.range (fun θ => Likelihood P θ Xset))}

def TendstoInProbability.{u_1} {Ω : Type u_1} [MeasurableSpace Ω] {ι : Type*}
    {X : ι → (Ω → ℝ)} {P : MeasureTheory.ProbabilityMeasure Ω} (l : Filter ι)
    (X_lim : Ω → ℝ):=
  MeasureTheory.TendstoInMeasure (MeasureTheory.ProbabilityMeasure.toMeasure P) X l X_lim

/-
variable {α : Type u} {ProbFunSet: Set (PMF α)} {β : Type v} (P: β → ProbFunSet) (x : α)

noncomputable def Likelihood (θ : β) (Xset : Finset α):= ∏ (x : Xset), (P θ).1.1 x

variable (θ : β) (Xset : Finset α)
#check Set.range (fun θ => Likelihood P θ Xset)

def MaximumLikelihoodEstimator (Xset : Finset α) : Set β := {θ_max | Likelihood P θ_max Xset = sSup (Set.range (fun θ => Likelihood P θ Xset))}

#check Seq
#check Stream'.Seq

abbrev Xset_with_n_variables (Xset_fun: ℕ → α):= fun (n: ℕ) => {Xset_fun i| i ∈ Finset.range (n+1)}

instance (n : ℕ) (Xset_fun: ℕ → α) : Fintype (Xset_with_n_variables Xset_fun n) := by sorry

variable {Ω : Type u_1} [MeasurableSpace Ω] (Pr: MeasureTheory.ProbabilityMeasure Ω)
#check MeasureTheory.TendstoInMeasure (MeasureTheory.ProbabilityMeasure.toMeasure Pr)
#check MeasureTheory.ProbabilityMeasure.toMeasure Pr


def converge_in_probability

theorem temp (Xset_fun: ℕ → α): ∃ (S: ℕ → β), (∀ (n : ℕ), S n ∈ MaximumLikelihoodEstimator P (Xset_with_n_variables Xset_fun n).toFinset) ∧ MeasureTheory.TendstoInMeasure
-/
