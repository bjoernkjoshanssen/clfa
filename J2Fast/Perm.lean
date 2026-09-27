module

/-!
# Fast permutations of `Fin 100` (no Mathlib)

`P100` stores a permutation of `Fin 100` together with its inverse as two lookup tables.
This module only uses the Lean core library, so that it can be compiled to native code and
used by `native_decide` at full speed. The group structure and the isomorphism with
`Equiv.Perm (Fin 100)` are in `RequestProject.J2.Perm100`.
-/

@[expose] public section

namespace J2Cert

/-- Permutations of `Fin 100` as a pair of mutually inverse lookup tables. -/
structure P100 where
  f : Vector (Fin 100) 100
  b : Vector (Fin 100) 100
  fb : ∀ i : Fin 100, f.get (b.get i) = i
  bf : ∀ i : Fin 100, b.get (f.get i) = i

namespace P100

@[simp] theorem get_ofFn' {n : Nat} {α : Type} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  simp [Vector.get]

theorem vec_ext {v w : Vector (Fin 100) 100} (h : ∀ i : Fin 100, v.get i = w.get i) : v = w := by
  apply Vector.ext
  intro i hi
  exact h ⟨i, hi⟩

theorem ext_f {x y : P100} (h : x.f = y.f) : x = y := by
  obtain ⟨xf, xb, xfb, xbf⟩ := x
  obtain ⟨yf, yb, yfb, ybf⟩ := y
  simp only at h
  subst h
  have : xb = yb := by
    apply vec_ext
    intro i
    have h1 := xbf (yb.get i)
    rw [yfb] at h1
    exact h1
  subst this
  rfl

instance : DecidableEq P100 := fun x y =>
  decidable_of_iff (x.f = y.f) ⟨ext_f, fun h => h ▸ rfl⟩

instance : Hashable P100 := ⟨fun x => hash x.f.toArray⟩

instance : Mul P100 := ⟨fun x y =>
  { f := Vector.ofFn fun i => x.f.get (y.f.get i)
    b := Vector.ofFn fun i => y.b.get (x.b.get i)
    fb := by intro i; simp [y.fb, x.fb]
    bf := by intro i; simp [y.bf, x.bf] }⟩

instance : One P100 := ⟨
  { f := Vector.ofFn id
    b := Vector.ofFn id
    fb := by intro i; simp
    bf := by intro i; simp }⟩

instance : Inv P100 := ⟨fun x => { f := x.b, b := x.f, fb := x.bf, bf := x.fb }⟩

instance : Inhabited P100 := ⟨1⟩

theorem mul_f_get (x y : P100) (i : Fin 100) : (x * y).f.get i = x.f.get (y.f.get i) :=
  get_ofFn' _ _

theorem one_f_get (i : Fin 100) : (1 : P100).f.get i = i := get_ofFn' _ _

theorem ext_get {x y : P100} (h : ∀ i : Fin 100, x.f.get i = y.f.get i) : x = y :=
  ext_f (vec_ext h)

/-- Inverse table of a table (garbage-in, garbage-out if `v` is not a permutation). -/
def invTable (v : Vector (Fin 100) 100) : Vector (Fin 100) 100 :=
  Vector.ofFn fun i => ((List.finRange 100).find? fun j => v.get j = i).getD 0

/-- Build a permutation from a table; returns `1` if the table is not a permutation. -/
def ofVec (v : Vector (Fin 100) 100) : P100 :=
  if h : (∀ i : Fin 100, v.get ((invTable v).get i) = i) ∧
      (∀ i : Fin 100, (invTable v).get (v.get i) = i) then
    { f := v, b := invTable v, fb := h.1, bf := h.2 }
  else 1

/-- Build a permutation from a list of images `[σ 0, σ 1, …, σ 99]` (with `Nat` entries). -/
def ofList (l : List Nat) : P100 :=
  ofVec (Vector.ofFn fun i => ⟨l.getD i 0 % 100, Nat.mod_lt _ (by decide)⟩)

end P100

end J2Cert

end
