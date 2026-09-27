module

public import Mathlib
public import J2Fast.Perm

/-!
# The group structure on `P100`

`P100` (defined in `J2Fast.Perm`) is a group, isomorphic to `Equiv.Perm (Fin 100)` via
`P100.toPermEquiv`.
-/

@[expose] public section

namespace J2Cert

namespace P100

instance : Group P100 where
  mul_assoc x y z := ext_get fun i => by simp only [mul_f_get]
  one_mul x := ext_get fun i => by simp only [mul_f_get, one_f_get]
  mul_one x := ext_get fun i => by simp only [mul_f_get, one_f_get]
  inv_mul_cancel x := ext_get fun i => by
    simp only [mul_f_get, one_f_get]
    exact x.bf i

/-- The permutation of `Fin 100` represented by `x`. -/
def toPerm (x : P100) : Equiv.Perm (Fin 100) where
  toFun i := x.f.get i
  invFun i := x.b.get i
  left_inv i := x.bf i
  right_inv i := x.fb i

/-- `P100` is isomorphic to the symmetric group on `Fin 100`. -/
def toPermEquiv : P100 ≃* Equiv.Perm (Fin 100) where
  toFun := toPerm
  invFun σ :=
    { f := Vector.ofFn σ
      b := Vector.ofFn σ.symm
      fb := by intro i; simp
      bf := by intro i; simp }
  left_inv x := ext_get fun i => by simp [toPerm]
  right_inv σ := by ext i; simp [toPerm]
  map_mul' x y := by ext i; simp [toPerm, mul_f_get]

@[simp] theorem toPermEquiv_apply (x : P100) (i : Fin 100) :
    toPermEquiv x i = x.f.get i := rfl

end P100

end J2Cert

end
