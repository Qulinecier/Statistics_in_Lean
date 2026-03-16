import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Data.ENNReal.Basic

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

open scoped ENNReal Topology

/-- If two sequences of measurable events `s n` and `t n` both have probability
tending to `1`, then the probability of their intersection also tends to `1`. -/
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
        rw [ENNReal.div_add_div_same, ← two_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_assoc]
        have h4_2 : (4 : ENNReal)⁻¹ * 2 = 2⁻¹ :=by
          refine ENNReal.eq_inv_of_mul_eq_one_left ?_
          rw [mul_assoc]
          norm_num
          refine ENNReal.inv_mul_cancel (Ne.symm (NeZero.ne' 4)) (Ne.symm ENNReal.top_ne_ofNat)
        rw [h4_2, div_eq_mul_inv]
      have : a.toReal < ((1 : ℝ≥0∞) - (ε + ε)).toReal := by
        rw [this]
        have hεle1 : (ε + ε) ≤ 1 :=by
          rw [this]
          refine (ENNReal.div_le_iff (Ne.symm (NeZero.ne' 2)) (Ne.symm ENNReal.top_ne_ofNat)).mpr ?_
          simp only [one_mul]
          exact Std.IsPreorder.le_trans (1 - a) 1 2 tsub_le_self one_le_two

        have ha_fin : a < (⊤ : ℝ≥0∞) := lt_of_lt_of_le ha (by simp only [le_top])
        have hR_a : a.toReal < (1 : ℝ) := by
          have := ENNReal.toReal_lt_toReal (LT.lt.ne_top (ha_fin)) ENNReal.one_ne_top
          simp only [ENNReal.toReal_one] at this
          rw [this]
          exact ha
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

    have hinter :
         P (s n ∩ t n) = (1 : ℝ≥0∞) - P ((s n ∩ t n)ᶜ):= by
      have h:= prob_compl_eq_one_sub (μ := P) (s := (s n ∩ t n)ᶜ)
        (MeasurableSet.compl_iff.mpr (MeasurableSet.inter (hms n) (hmt n)))
      simp only [compl_compl] at h
      exact h

    have : (1 : ℝ≥0∞) - (ε + ε) < P (s n ∩ t n) := by
      have : (1 : ℝ≥0∞) - (ε + ε) < (1 : ℝ≥0∞) - P ((s n ∩ t n)ᶜ) := by
        have h₁ : (1 : ℝ≥0∞) - (1 - P ((s n ∩ t n)ᶜ)) < ε + ε := by
          have : (1 : ℝ≥0∞) - (1 - P ((s n ∩ t n)ᶜ)) = P ((s n ∩ t n)ᶜ) := by
            rw [← hinter]
            exact id (Eq.symm (prob_compl_eq_one_sub (μ := P) (s := (s n ∩ t n))
              (MeasurableSet.inter (hms n) (hmt n))))
          simpa [this] using (lt_of_le_of_lt (by simpa [Set.compl_inter] using
          (measure_union_le ((s n)ᶜ) ((t n)ᶜ))) (ENNReal.add_lt_add hcomplS hcomplT))
        exact ENNReal.sub_lt_of_sub_lt (le_of_lt (by simpa [tsub_pos_iff_lt]
          using (lt_of_le_of_lt (bot_le) hε_lt))) (by left; simp) h₁
      simpa [hinter] using this
    exact lt_trans hε_lt this
  · intro b hb
    rw [@eventually_atTop]
    use 0
    intro n _
    exact lt_of_le_of_lt (prob_le_one (μ := P) (s := s n ∩ t n)) hb
