module

public import RequestProject.PSL264.GF64
meta import RequestProject.PSL264.GF64

/-!
# A computable model of `SL(2, 64)`

`G2` is the group of `2 × 2` matrices of determinant one over `GF64`, with a fast
multiplication. We also provide an exhaustive-loop combinator `forallG2` over all its
elements, and prove that `SL(2,2)` together with a single diagonal element generates the
whole group.
-/

@[expose] public section

namespace PSL264

open GF64

/-- `2 × 2` matrices `[[a, b], [c, d]]` over `GF64`. -/
structure M2 where
  a : GF64
  b : GF64
  c : GF64
  d : GF64
deriving DecidableEq

namespace M2

instance : Mul M2 := ⟨fun x y => ⟨x.a * y.a + x.b * y.c, x.a * y.b + x.b * y.d,
  x.c * y.a + x.d * y.c, x.c * y.b + x.d * y.d⟩⟩

@[simp] theorem mul_a' (x y : M2) : (x * y).a = x.a * y.a + x.b * y.c := rfl
@[simp] theorem mul_b' (x y : M2) : (x * y).b = x.a * y.b + x.b * y.d := rfl
@[simp] theorem mul_c' (x y : M2) : (x * y).c = x.c * y.a + x.d * y.c := rfl
@[simp] theorem mul_d' (x y : M2) : (x * y).d = x.c * y.b + x.d * y.d := rfl

/-- Determinant. -/
def det (x : M2) : GF64 := x.a * x.d - x.b * x.c

theorem det_mul (x y : M2) : (x * y).det = x.det * y.det := by
  simp only [det, mul_a', mul_b', mul_c', mul_d']
  ring

/-- Numeric code of a matrix (used as a hash key). -/
def code (x : M2) : ℕ :=
  x.a.val.val * 262144 + x.b.val.val * 4096 + x.c.val.val * 64 + x.d.val.val

end M2

/-- The group `SL(2, 64)`, concretely. -/
def G2 : Type := {m : M2 // m.det = 1}

namespace G2

instance : DecidableEq G2 := inferInstanceAs (DecidableEq {m : M2 // m.det = 1})

instance : Mul G2 := ⟨fun x y => ⟨x.1 * y.1, by rw [M2.det_mul, x.2, y.2, one_mul]⟩⟩
instance : One G2 := ⟨⟨⟨1, 0, 0, 1⟩, by simp [M2.det]⟩⟩
instance : Inv G2 := ⟨fun x => ⟨⟨x.1.d, -x.1.b, -x.1.c, x.1.a⟩, by
  have := x.2; simp only [M2.det] at *; linear_combination this⟩⟩

@[ext] theorem ext {x y : G2} (h : x.1 = y.1) : x = y := Subtype.ext h

theorem ext_iff' {x y : G2} : x = y ↔ x.1.a = y.1.a ∧ x.1.b = y.1.b ∧ x.1.c = y.1.c ∧
    x.1.d = y.1.d := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h1, h2, h3, h4⟩
    apply ext
    cases hx : x.1; cases hy : y.1
    simp_all

@[simp] theorem mul_a (x y : G2) : (x * y).1.a = x.1.a * y.1.a + x.1.b * y.1.c := rfl
@[simp] theorem mul_b (x y : G2) : (x * y).1.b = x.1.a * y.1.b + x.1.b * y.1.d := rfl
@[simp] theorem mul_c (x y : G2) : (x * y).1.c = x.1.c * y.1.a + x.1.d * y.1.c := rfl
@[simp] theorem mul_d (x y : G2) : (x * y).1.d = x.1.c * y.1.b + x.1.d * y.1.d := rfl
@[simp] theorem one_a : (1 : G2).1.a = 1 := rfl
@[simp] theorem one_b : (1 : G2).1.b = 0 := rfl
@[simp] theorem one_c : (1 : G2).1.c = 0 := rfl
@[simp] theorem one_d : (1 : G2).1.d = 1 := rfl
@[simp] theorem inv_a (x : G2) : (x⁻¹).1.a = x.1.d := rfl
@[simp] theorem inv_b (x : G2) : (x⁻¹).1.b = -x.1.b := rfl
@[simp] theorem inv_c (x : G2) : (x⁻¹).1.c = -x.1.c := rfl
@[simp] theorem inv_d (x : G2) : (x⁻¹).1.d = x.1.a := rfl

theorem det_eq (x : G2) : x.1.a * x.1.d - x.1.b * x.1.c = 1 := x.2

instance : Group G2 := Group.ofLeftAxioms
  (fun x y z => by rw [ext_iff']; simp only [mul_a, mul_b, mul_c, mul_d]; refine ⟨?_, ?_, ?_, ?_⟩ <;> ring)
  (fun x => by rw [ext_iff']; simp)
  (fun x => by
    have := det_eq x
    rw [ext_iff']; simp only [mul_a, mul_b, mul_c, mul_d, inv_a, inv_b, inv_c, inv_d, one_a,
      one_b, one_c, one_d]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | linear_combination this | ring)

/-- All elements of `GF64`, as a list. -/
def all64 : List GF64 := (List.finRange 64).map GF64.mk

theorem mem_all64 (z : GF64) : z ∈ all64 := by
  cases z; simp [all64]

/-- Exhaustive check of a boolean predicate on all elements of `G2`. -/
def forallG2 (p : G2 → Bool) : Bool :=
  all64.all fun a => all64.all fun b => all64.all fun c =>
    (if a = 0 then all64 else [(1 + b * c) / a]).all fun d =>
      if h : (M2.mk a b c d).det = 1 then p ⟨_, h⟩ else true

theorem forallG2_spec {p : G2 → Bool} (h : forallG2 p = true) (x : G2) : p x = true := by
  obtain ⟨⟨a, b, c, d⟩, hx⟩ := x
  simp only [forallG2, List.all_eq_true] at h
  have hd : d ∈ (if a = 0 then all64 else [(1 + b * c) / a]) := by
    split_ifs with ha
    · exact mem_all64 d
    · simp only [List.mem_singleton]
      simp only [M2.det] at hx
      field_simp
      linear_combination hx
  have := h a (mem_all64 _) b (mem_all64 _) c (mem_all64 _) d hd
  rw [dif_pos hx] at this
  exact this

/-! ### Special elements -/

/-- The element `[[0,1],[1,1]]` of order `3`. -/
def a0 : G2 := ⟨⟨0, 1, 1, 1⟩, by native_decide⟩
/-- The involution `[[0,1],[1,0]]`. -/
def t0 : G2 := ⟨⟨0, 1, 1, 0⟩, by native_decide⟩
/-- Upper unitriangular matrices. -/
def U (s : GF64) : G2 := ⟨⟨1, s, 0, 1⟩, by simp [M2.det]⟩
/-- Lower unitriangular matrices. -/
def L (s : GF64) : G2 := ⟨⟨1, 0, s, 1⟩, by simp [M2.det]⟩
/-- The diagonal element `diag(x, x⁻¹)` for the generator `x` of `GF64ˣ`. -/
def Dα : G2 := ⟨⟨⟨2⟩, 0, 0, (⟨2⟩ : GF64)⁻¹⟩, by native_decide⟩

theorem U_conj_check : (all64.all fun s => s == 0 ||
    (List.range 63).any fun k => U s == Dα ^ k * U 1 * (Dα ^ k)⁻¹) = true := by native_decide

theorem U_one_eq : U 1 = t0 * a0 := by native_decide

theorem L_eq_check : (all64.all fun s => L s == t0 * U s * t0) = true := by native_decide

/-- An explicit factorisation of an element into unitriangular matrices (and `t0`). -/
def factor (x : G2) : G2 :=
  if x.1.c ≠ 0 then U ((x.1.a - 1) / x.1.c) * L x.1.c * U ((x.1.d - 1) / x.1.c)
  else
    let y := t0 * x
    t0 * (U ((y.1.a - 1) / y.1.c) * L y.1.c * U ((y.1.d - 1) / y.1.c))

theorem factor_check : forallG2 (fun x => x == factor x) = true := by native_decide

theorem closure_top : Subgroup.closure {a0, t0, Dα} = ⊤ := by
  set S := Subgroup.closure ({a0, t0, Dα} : Set G2)
  have ha0 : a0 ∈ S := Subgroup.subset_closure (by simp)
  have ht0 : t0 ∈ S := Subgroup.subset_closure (by simp)
  have hD : Dα ∈ S := Subgroup.subset_closure (by simp)
  have hU : ∀ s, U s ∈ S := by
    intro s
    have h := U_conj_check
    simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
    rcases h s (mem_all64 s) with h0 | ⟨k, -, hk⟩
    · subst h0
      have : U 0 = 1 := by native_decide
      rw [this]; exact S.one_mem
    · rw [hk]
      refine S.mul_mem (S.mul_mem (S.pow_mem hD k) ?_) (S.inv_mem (S.pow_mem hD k))
      rw [U_one_eq]; exact S.mul_mem ht0 ha0
  have hL : ∀ s, L s ∈ S := by
    intro s
    have h := L_eq_check
    simp only [List.all_eq_true, beq_iff_eq] at h
    rw [h s (mem_all64 s)]
    exact S.mul_mem (S.mul_mem ht0 (hU s)) ht0
  rw [eq_top_iff]
  intro x _
  have h := forallG2_spec factor_check x
  simp only [beq_iff_eq] at h
  rw [h, factor]
  split_ifs
  · exact S.mul_mem (S.mul_mem (hU _) (hL _)) (hU _)
  · exact S.mul_mem ht0 (S.mul_mem (S.mul_mem (hU _) (hL _)) (hU _))

end G2

end PSL264

end
