import Mathlib.Data.EReal.Basic

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
