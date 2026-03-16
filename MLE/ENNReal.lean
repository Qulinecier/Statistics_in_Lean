import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

lemma edist_compl_ball {α : Type*} (μ : ℝ) (S : α → ℝ) :
    {x | ENNReal.ofReal (- μ ) ≤ edist (S x) μ}ᶜ ⊆ {x | (S x) < 0}:= by
  intro x hS
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, edist_lt_ofReal] at hS
  simp only [Set.mem_setOf_eq]
  have h := add_lt_add_of_lt_of_le (lt_of_le_of_lt (Real.sub_le_dist (S x) μ ) hS)
    (le_refl ((μ) ))
  rw [add_comm, ← add_sub_assoc, add_comm, add_sub_assoc] at h
  simp only [neg_add_cancel, sub_self, add_zero] at h
  exact h
