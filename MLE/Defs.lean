import Mathlib.Probability.Density
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog


universe u_1 u_2
namespace MeasureTheory

/-- `pdf_support X ℙ μ` is the support of the probability density function of the
random variable `X` with respect to the base measure `μ`. -/
def pdf_support {Ω : Type u_1} {E : Type u_2} [MeasurableSpace E]
  {h : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac):=
  Function.support (pdf X ℙ μ)

end MeasureTheory

open MeasureTheory

/-- the *likelihood function* of the parameter `θ`
evaluated at the sample point `ω`, based on the first `n` observations of
the statistic `X` -/
noncomputable def Likelihood {Ω : Type*} [MeasurableSpace Ω]
    {ProbFunSet : Set (Measure Ω)} (f : ℝ → ProbFunSet)
    (X : ℕ → Ω → ℝ) (θ : ℝ) (n : ℕ) (μ : Measure ℝ := by volume_tac) : Ω → ENNReal :=
  fun ω => ∏ i : Fin n, pdf (X 0) (f θ) μ (X i ω)

/-- `log_Likelihood f X θ n μ` is the **log-likelihood function** for the first `n`
observations of the sample sequence `X`. -/
noncomputable def log_Likelihood {Ω : Type*} [MeasurableSpace Ω]
    {ProbFunSet : Set (Measure Ω)} (f : ℝ → ProbFunSet)
    (X : ℕ → Ω → ℝ) (θ : ℝ) (n : ℕ) (μ : Measure ℝ := by volume_tac) : Ω → EReal :=
  fun ω => ∑ (i : Fin n), ENNReal.log (pdf (X 0) (f θ) μ (X i ω))

namespace Likelihood
/-- the sequence of real-valued random variables
representing the *log-likelihood ratio* of parameter `θ` against the reference
parameter `θ₀` evaluated on the observations `X i` -/
noncomputable abbrev log_sum_ratio_rv {Ω : Type*} [MeasurableSpace Ω]
  {ProbFunSet : Set (Measure Ω)} (f : ℝ → ProbFunSet)
  (μ : Measure ℝ := by volume_tac)
  (X : ℕ → Ω → ℝ) (θ₀ θ : ℝ) : ℕ → Ω → ℝ :=
  fun i => fun (ω : Ω) =>
    Real.log ((pdf (X 0) (f θ).1 μ (X i ω)).toReal/ (pdf (X 0) (f θ₀).1 μ (X i ω)).toReal)

end Likelihood
