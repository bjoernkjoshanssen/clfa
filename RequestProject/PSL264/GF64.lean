module

public import Mathlib

/-!
# A computable model of the field with 64 elements

Elements are bit vectors `b₀ + b₁ x + ⋯ + b₅ x⁵` over `𝔽₂`, stored as `Fin 64`,
with multiplication modulo the primitive polynomial `x⁶ + x + 1`.
All field axioms are checked by exhaustive computation.
-/

@[expose] public section

namespace PSL264

/-- The field with `64` elements, as polynomials over `𝔽₂` modulo `x⁶ + x + 1`. -/
structure GF64 where
  val : Fin 64
deriving DecidableEq, Fintype

namespace GF64

/-- Carry-less multiplication followed by reduction modulo `x⁶ + x + 1` (`0x43`). -/
def mulNat (a b : Nat) : Nat :=
  let r := (List.range 6).foldl (fun acc i => if b.testBit i then acc ^^^ (a <<< i) else acc) 0
  (List.range 6).reverse.foldl
    (fun acc i => if acc.testBit (i + 6) then acc ^^^ (0x43 <<< i) else acc) r

/-- Multiplication table. -/
def mulTable : Array (Fin 64) :=
  Array.ofFn (n := 4096) fun i => ⟨mulNat (i.val / 64) (i.val % 64) % 64, Nat.mod_lt _ (by decide)⟩

/-- Inverse table (`a⁻¹ = a ^ 62`, and `0⁻¹ = 0`). -/
def invTable : Array (Fin 64) :=
  Array.ofFn (n := 64) fun i =>
    (List.range 61).foldl (fun acc _ => mulTable[acc.val * 64 + i.val]!) i

instance : Zero GF64 := ⟨⟨0⟩⟩
instance : One GF64 := ⟨⟨1⟩⟩
instance : Add GF64 := ⟨fun a b => ⟨⟨(a.val.val ^^^ b.val.val) % 64, Nat.mod_lt _ (by decide)⟩⟩⟩
instance : Neg GF64 := ⟨fun a => a⟩
instance : Sub GF64 := ⟨fun a b => a + b⟩
instance : Mul GF64 := ⟨fun a b => ⟨mulTable[a.val.val * 64 + b.val.val]!⟩⟩
instance : Inv GF64 := ⟨fun a => ⟨invTable[a.val.val]!⟩⟩
instance : Div GF64 := ⟨fun a b => a * b⁻¹⟩
instance : Inhabited GF64 := ⟨0⟩

theorem add_assoc' : ∀ a b c : GF64, a + b + c = a + (b + c) := by native_decide
theorem zero_add' : ∀ a : GF64, 0 + a = a := by native_decide
theorem add_zero' : ∀ a : GF64, a + 0 = a := by native_decide
theorem add_comm' : ∀ a b : GF64, a + b = b + a := by native_decide
theorem neg_add_cancel' : ∀ a : GF64, -a + a = 0 := by native_decide
theorem sub_eq_add_neg' : ∀ a b : GF64, a - b = a + -b := by native_decide
theorem mul_assoc' : ∀ a b c : GF64, a * b * c = a * (b * c) := by native_decide
theorem one_mul' : ∀ a : GF64, 1 * a = a := by native_decide
theorem mul_one' : ∀ a : GF64, a * 1 = a := by native_decide
theorem zero_mul' : ∀ a : GF64, 0 * a = 0 := by native_decide
theorem mul_zero' : ∀ a : GF64, a * 0 = 0 := by native_decide
theorem mul_comm' : ∀ a b : GF64, a * b = b * a := by native_decide
theorem left_distrib' : ∀ a b c : GF64, a * (b + c) = a * b + a * c := by native_decide
theorem right_distrib' : ∀ a b c : GF64, (a + b) * c = a * c + b * c := by native_decide
theorem mul_inv_cancel' : ∀ a : GF64, a ≠ 0 → a * a⁻¹ = 1 := by native_decide
theorem inv_zero' : (0 : GF64)⁻¹ = 0 := by native_decide
theorem zero_ne_one' : (0 : GF64) ≠ 1 := by native_decide

instance : CommRing GF64 where
  add_assoc := add_assoc'
  zero_add := zero_add'
  add_zero := add_zero'
  add_comm := add_comm'
  neg_add_cancel := neg_add_cancel'
  sub_eq_add_neg := sub_eq_add_neg'
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  zero_mul := zero_mul'
  mul_zero := mul_zero'
  mul_comm := mul_comm'
  left_distrib := left_distrib'
  right_distrib := right_distrib'
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Field GF64 where
  mul_inv_cancel := mul_inv_cancel'
  inv_zero := inv_zero'
  exists_pair_ne := ⟨0, 1, zero_ne_one'⟩
  nnqsmul := _
  qsmul := _

theorem card_eq : Fintype.card GF64 = 2 ^ 6 := by native_decide

theorem one_add_one : (1 : GF64) + 1 = 0 := by native_decide

instance : CharP GF64 2 := by
  rw [CharP.charP_iff_prime_eq_zero Nat.prime_two]
  rw [show ((2 : ℕ) : GF64) = 1 + 1 by norm_num]
  exact one_add_one

end GF64

end PSL264

end
