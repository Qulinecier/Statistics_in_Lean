import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open Filter MeasureTheory

namespace MeasureTheory
lemma univ_tendsto_one {ι : Type*}
    {Ω : Type*} [MeasurableSpace Ω] (p : Measure Ω) [IsProbabilityMeasure p] {l : Filter ι} :
    Tendsto (fun (_ : ι) => p (Set.univ)) l (nhds 1) :=by
  simp only [MeasureTheory.measure_univ]
  exact tendsto_const_nhds

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
