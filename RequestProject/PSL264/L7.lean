module

public import Mathlib

/-!
# DeMeo's seven-element lattice `𝐋₇`

Elements `0, K, J₁, J₂, M₁, M₂, 1` with covering relations
`0 ≺ K ≺ 1`, `0 ≺ J₁ ≺ M₁ ≺ 1`, `0 ≺ J₂ ≺ M₁`, `J₂ ≺ M₂ ≺ 1`.
-/

@[expose] public section

namespace PSL264

/-- The seven elements of DeMeo's lattice `𝐋₇`. -/
inductive L7 where
  | bot | K | J1 | J2 | M1 | M2 | top
deriving DecidableEq, Fintype, Repr

namespace L7

/-- The order of `𝐋₇`: `0` is least, `1` is greatest, and in addition
`J₁ < M₁`, `J₂ < M₁`, `J₂ < M₂`. -/
def leB : L7 → L7 → Bool
  | bot, _ => true
  | _, top => true
  | K, K => true
  | J1, J1 => true
  | J1, M1 => true
  | J2, J2 => true
  | J2, M1 => true
  | J2, M2 => true
  | M1, M1 => true
  | M2, M2 => true
  | _, _ => false

/-- Join in `𝐋₇`. -/
def supL (x y : L7) : L7 :=
  if leB x y then y else if leB y x then x else
  match x, y with
  | J1, J2 => M1
  | J2, J1 => M1
  | _, _ => top

/-- Meet in `𝐋₇`. -/
def infL (x y : L7) : L7 :=
  if leB x y then x else if leB y x then y else
  match x, y with
  | M1, M2 => J2
  | M2, M1 => J2
  | _, _ => bot

instance : LE L7 := ⟨fun x y => leB x y = true⟩

instance : DecidableRel (α := L7) (· ≤ ·) := fun x y => inferInstanceAs (Decidable (leB x y = true))

instance : Lattice L7 where
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

instance : OrderBot L7 where
  bot := bot
  bot_le := by decide

instance : OrderTop L7 where
  top := top
  le_top := by decide

end L7

end PSL264

end
