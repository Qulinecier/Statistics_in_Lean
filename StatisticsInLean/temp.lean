import Mathlib
import Clt

universe u v u_1

-- theorem central_limit (hX : ∀ n, Measurable (X n))
--     {P : ProbabilityMeasure Ω} (h0 : P[X 0] = 0) (h1 : P[X 0 ^ 2] = 1)
--     (hindep : iIndepFun X P) (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) :
--     Tendsto (fun n : ℕ => P.map (aemeasurable_invSqrtMulSum n hX)) atTop (𝓝 stdGaussian)



namespace RandomVariable

def C {α : Type*} {β : Type*} (Ω : Type u_1) (X : α → β) : α → Ω → β := fun n _ => X n

end RandomVariable

open Filter MeasureTheory

def TendstoInProbability {Ω : Type u_1} [MeasurableSpace Ω] (X : ℕ → (Ω → ℝ))
    (P : ProbabilityMeasure Ω) (c : ℝ):= TendstoInMeasure (P.toMeasure) X atTop (fun _ => c)

variable {α : Type u} {ProbFunSet : Set (PMF α)}
    (f : ℝ → ProbFunSet) (Xset : Finset α) (θ : ℝ)

noncomputable def Likelihood {α : Type u} {ProbFunSet : Set (PMF α)}
    (f : ℝ → ProbFunSet) (Xset : Finset α) (θ : ℝ):= ∏ (x : Xset), (f θ).1.1 x



namespace Likelihood

noncomputable def log_likelihood {α : Type u} {ProbFunSet : Set (PMF α)} {β : Type v}
    (f : β → ProbFunSet) (θ : β) (Xset : Finset α):= ∑ (x : Xset), ENNReal.log ((f θ).1.1 x)

abbrev root_of_deriv (f : ℝ → ENNReal):= {(θ: ℝ) | deriv (fun x => (f x).toReal) θ = 0}

theorem theorem37
    {α : Type u} {ProbFunSet : Set (PMF α)} {Ω : Type u_1} [MeasurableSpace Ω]
    (f : ℝ → ↑ProbFunSet) (θ θ₀ : ℝ) (Xset : Finset α) {ι : Type u_1} {X : ι → ℝ}
    (Xset_fun : ℕ → α) (P : ProbabilityMeasure Ω) : ∃ (θ₀ : ℝ), ∃ (S: ℕ → ℝ),
    (∀ (n : ℕ), (S n) ∈ root_of_deriv (Likelihood f Xset))
    ∧ (TendstoInProbability (RandomVariable.C Ω S) P θ₀):= sorry


-- variable {Ω : Type u_1} [MeasurableSpace Ω]

-- def MaximumLikelihoodEstimator {α : Type u} {ProbFunSet : Set (PMF α)}
--     (P : (Ω → ℝ) → ↑ProbFunSet) (Xset : Finset α): Set (Ω → ℝ) :=
--     {θ_max | Likelihood P θ_max Xset = sSup (Set.range (fun θ => Likelihood P θ Xset))}

-- abbrev Xset_with_n_variables{α : Type u} (Xset_fun : ℕ → α):=
--   fun (n: ℕ) => {Xset_fun i| i ∈ Finset.range (n+1)}

-- instance finX_set_fun {α : Type u} (n : ℕ) (Xset_fun: ℕ → α) :
--   Fintype (Xset_with_n_variables Xset_fun n) := by sorry


-- theorem temp {α : Type u} {ProbFunSet : Set (PMF α)} [MeasurableSpace Ω]
-- (P : (Ω → ℝ) → ↑ProbFunSet)
-- (θ θ₀: Ω → ℝ) (Xset : Finset α) {ι : Type u_1} {X : ι → (Ω → ℝ)}
-- (Xset_fun: ℕ → α) (Pr: MeasureTheory.ProbabilityMeasure Ω) : ∃ (S: ℕ → (Ω → ℝ)), (∀ (n : ℕ),
-- (S n) ∈ MaximumLikelihoodEstimator P (Xset_with_n_variables Xset_fun n).toFinset)
-- ∧ (TendstoInProbability (ι:=ℕ) S Pr (⊤) θ₀):= sorry
