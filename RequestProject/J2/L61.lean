module

public import Mathlib
public import J2Fast.Check

/-!
# The eight-element lattice `#61`

The lattice `#61` of Figure 2 of the note: elements `0, a, b, c, d, e, f, 1` with covering
relations `0 ≺ a, b, c`, `a ≺ e, f`, `b ≺ d, e`, `c ≺ d` and `d, e, f ≺ 1`
(so `a < e, f`; `b < d, e`; `c < d`). The type `L61` and its order `L61.leB` are defined in
`J2Fast.Check`; here we equip it with its lattice structure.
-/

@[expose] public section

namespace J2Cert

namespace L61

instance : Fintype L61 := ⟨⟨all, by decide⟩, mem_all⟩

instance : LE L61 := ⟨fun x y => leB x y = true⟩

instance : DecidableRel (α := L61) (· ≤ ·) := fun x y =>
  inferInstanceAs (Decidable (leB x y = true))

instance : Lattice L61 where
  le := (· ≤ ·)
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  sup := supL
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide
  inf := infL
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide

instance : OrderBot L61 where
  bot := bot
  bot_le := by decide

instance : OrderTop L61 where
  top := top
  le_top := by decide

theorem le_iff_leB {x y : L61} : x ≤ y ↔ leB x y = true := Iff.rfl

theorem sup_eq_supL (x y : L61) : x ⊔ y = supL x y := rfl

end L61

end J2Cert

end
