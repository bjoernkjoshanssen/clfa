module

public import RequestProject.PSL264.SL2
public import RequestProject.PSL264.L7
public import RequestProject.PSL264.Table
meta import RequestProject.PSL264.SL2
meta import RequestProject.PSL264.L7
meta import RequestProject.PSL264.Table

/-!
# The overgroups of `SL(2,2)` in `SL(2,64)`

We exhibit seven explicit subgroups `T i` (`i : L7`) of `G2 ≅ SL(2,64)` containing
`H₀ = T ⊥ ≅ SL(2,2) ≅ S₃`, and prove that they are exactly the subgroups containing `H₀`,
with `T i ≤ T j ↔ i ≤ j`. The proof is a certificate check: for every `g`, the subgroup
`⟨H₀, g⟩` is identified with one of the `T i` using the data in `Table.lean`.
-/

@[expose] public section

namespace PSL264

open G2

/-! ### Closures computed as lists -/

/-- One step of a breadth-first closure computation. -/
def genStep (S : List G2) (l : List G2) : List G2 := (l ++ l.flatMap fun x => S.map (x * ·)).dedup

/-- Iterated closure computation (stops once the list no longer grows). -/
def genList (S : List G2) : ℕ → List G2 → List G2
  | 0, l => l
  | n + 1, l => let l' := genStep S l; if l'.length = l.length then l else genList S n l'

theorem mem_genList (S : List G2) (n : ℕ) (l : List G2)
    (hl : ∀ x ∈ l, x ∈ Subgroup.closure {y | y ∈ S}) :
    ∀ x ∈ genList S n l, x ∈ Subgroup.closure {y | y ∈ S} := by
  induction n generalizing l with
  | zero => simpa [genList] using hl
  | succ n ih =>
    simp only [genList]
    split
    · exact hl
    · apply ih
      intro x hx
      simp only [genStep, List.mem_dedup, List.mem_append, List.mem_flatMap, List.mem_map] at hx
      rcases hx with h | ⟨y, hy, s, hs, rfl⟩
      · exact hl x h
      · exact Subgroup.mul_mem _ (hl y hy) (Subgroup.subset_closure hs)

/-- Boolean check that a list is (the carrier of) a subgroup. -/
def checkSub (L : List G2) : Bool :=
  L.contains 1 && L.all (fun x => L.all fun y => L.contains (x * y)) && L.all fun x => L.contains x⁻¹

/-- The subgroup with carrier a list that passes `checkSub`. -/
def mkSub (L : List G2) (h : checkSub L = true) : Subgroup G2 where
  carrier := {x | x ∈ L}
  one_mem' := by
    simp only [checkSub, Bool.and_eq_true, List.contains_iff_mem] at h
    exact h.1.1
  mul_mem' := by
    intro x y hx hy
    simp only [checkSub, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
    exact h.1.2 x hx y hy
  inv_mem' := by
    intro x hx
    simp only [checkSub, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
    exact h.2 x hx

theorem mem_mkSub {L : List G2} {h : checkSub L = true} {x : G2} : x ∈ mkSub L h ↔ x ∈ L :=
  Iff.rfl

/-! ### The seven subgroups -/

/-- Generator (with `H₀`) of the subgroup `D₁₈` (the element `J₂`). -/
def wJ2 : G2 := ⟨⟨⟨14⟩, ⟨23⟩, ⟨23⟩, ⟨25⟩⟩, by native_decide⟩
/-- Generator (with `H₀`) of the subgroup `D₄₂` (the element `J₁`). -/
def wJ1 : G2 := ⟨⟨⟨15⟩, ⟨33⟩, ⟨33⟩, ⟨46⟩⟩, by native_decide⟩
/-- Generator (with `H₀`) of the subgroup `A₅ ≅ SL(2,4)` (the element `K`). -/
def wK : G2 := ⟨⟨⟨0⟩, ⟨1⟩, ⟨1⟩, ⟨58⟩⟩, by native_decide⟩
/-- Generator (with `H₀`) of the subgroup `D₁₂₆` (the element `M₁`). -/
def wM1 : G2 := ⟨⟨⟨6⟩, ⟨51⟩, ⟨51⟩, ⟨53⟩⟩, by native_decide⟩
/-- Generator (with `H₀`) of the subgroup `SL(2,8)` (the element `M₂`). -/
def wM2 : G2 := ⟨⟨⟨0⟩, ⟨1⟩, ⟨1⟩, ⟨14⟩⟩, by native_decide⟩

/-- The chosen generator of each subgroup (together with `a0`, `t0`). -/
def wOf : L7 → G2
  | .bot => 1
  | .K => wK
  | .J1 => wJ1
  | .J2 => wJ2
  | .M1 => wM1
  | .M2 => wM2
  | .top => Dα

def lstBot : List G2 := genList [a0, t0, 1] 60 [1]
def lstK : List G2 := genList [a0, t0, wK] 60 [1]
def lstJ1 : List G2 := genList [a0, t0, wJ1] 60 [1]
def lstJ2 : List G2 := genList [a0, t0, wJ2] 60 [1]
def lstM1 : List G2 := genList [a0, t0, wM1] 60 [1]
def lstM2 : List G2 := genList [a0, t0, wM2] 60 [1]

/-- The elements of the finite subgroups. -/
def lst : L7 → List G2
  | .bot => lstBot
  | .K => lstK
  | .J1 => lstJ1
  | .J2 => lstJ2
  | .M1 => lstM1
  | .M2 => lstM2
  | .top => []

theorem lst_eq (i : L7) (h : i ≠ .top) : lst i = genList [a0, t0, wOf i] 60 [1] := by
  cases i
  all_goals first | rfl | exact absurd rfl h

theorem checkSub_lst : ∀ i : L7, i ≠ .top → checkSub (lst i) = true := by native_decide

/-- The seven overgroups of `H₀`, indexed by `𝐋₇`. -/
def T (i : L7) : Subgroup G2 := if h : i = .top then ⊤ else mkSub (lst i) (checkSub_lst i h)

/-- Membership test for `T i`. -/
def memB (i : L7) (x : G2) : Bool := if i = .top then true else (lst i).contains x

theorem mem_T_iff {i : L7} {x : G2} : x ∈ T i ↔ memB i x = true := by
  unfold T memB
  split_ifs with h
  · simp
  · rw [mem_mkSub, List.contains_iff_mem]

theorem mem_T_of_mem_lst {i : L7} {x : G2} (hi : i ≠ .top) (hx : x ∈ lst i) : x ∈ T i := by
  rw [mem_T_iff, memB, if_neg hi, List.contains_iff_mem]; exact hx

theorem T_top : T .top = ⊤ := by simp [T]

theorem T_le_closure (i : L7) : T i ≤ Subgroup.closure {a0, t0, wOf i} := by
  by_cases h : i = .top
  · subst h; rw [T_top, wOf, closure_top]
  · intro x hx
    rw [mem_T_iff, memB, if_neg h, List.contains_iff_mem, lst_eq i h] at hx
    have := mem_genList [a0, t0, wOf i] 60 [1] (by simp) x hx
    convert this using 2
    ext y; simp

theorem gens_check : ∀ i : L7, (memB i a0 && memB i t0) = true := by native_decide

theorem a0_mem_T (i : L7) : a0 ∈ T i := by
  have := gens_check i; simp only [Bool.and_eq_true] at this; exact mem_T_iff.2 this.1

theorem t0_mem_T (i : L7) : t0 ∈ T i := by
  have := gens_check i; simp only [Bool.and_eq_true] at this; exact mem_T_iff.2 this.2

/-! ### Words and the certificate table -/

/-- Letters: the five non-identity elements of `H₀`, then `r` and `r⁻¹`. -/
def letter (r : G2) : ℕ → G2
  | 0 => a0
  | 1 => a0 * a0
  | 2 => t0
  | 3 => t0 * a0
  | 4 => t0 * (a0 * a0)
  | 5 => r
  | _ => r⁻¹

/-- Evaluate a word. -/
def evalWord (r : G2) (w : List ℕ) : G2 := w.foldl (fun acc l => acc * letter r l) 1

theorem evalWord_mem (S : Subgroup G2) (r : G2) (ha : a0 ∈ S) (ht : t0 ∈ S) (hr : r ∈ S)
    (w : List ℕ) : evalWord r w ∈ S := by
  have hl : ∀ l, letter r l ∈ S := by
    intro l
    match l with
    | 0 => exact ha
    | 1 => exact S.mul_mem ha ha
    | 2 => exact ht
    | 3 => exact S.mul_mem ht ha
    | 4 => exact S.mul_mem ht (S.mul_mem ha ha)
    | 5 => exact hr
    | _ + 6 => exact S.inv_mem hr
  have key : ∀ (w : List ℕ) (acc : G2), acc ∈ S →
      w.foldl (fun acc l => acc * letter r l) acc ∈ S := by
    intro w
    induction w with
    | nil => intro acc h; exact h
    | cons l w ih => intro acc h; exact ih _ (S.mul_mem h (hl l))
  exact key w 1 S.one_mem

/-- Parse one table entry `code,idx,word`. -/
def parseEntry (s : String) : Option (ℕ × ℕ × List ℕ) :=
  match s.splitOn "," with
  | [c, i, w] => some (c.toNat!, i.toNat!, w.toList.map fun ch => ch.toNat - 48)
  | _ => none

/-- The certificate table, keyed by the code of a double coset representative. -/
def table : Std.HashMap ℕ (ℕ × List ℕ) :=
  (tableData.flatMap (·.splitOn ";")).foldl
    (fun m s => match parseEntry s with
      | some (c, i, w) => m.insert c (i, w)
      | none => m) {}

/-- The elements of `H₀ = SL(2,2)`. -/
def H0list : List G2 := [1, a0, a0 * a0, t0, t0 * a0, t0 * (a0 * a0)]

theorem H0list_mem (S : Subgroup G2) (ha : a0 ∈ S) (ht : t0 ∈ S) : ∀ h ∈ H0list, h ∈ S := by
  intro h hh
  simp only [H0list, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl
  · exact S.one_mem
  · exact ha
  · exact S.mul_mem ha ha
  · exact ht
  · exact S.mul_mem ht ha
  · exact S.mul_mem ht (S.mul_mem ha ha)

/-- Find a double coset representative `r = h₁ g h₂` present in the table. -/
def lookup (g : G2) : Option (G2 × ℕ × List ℕ) :=
  H0list.findSome? fun h1 => H0list.findSome? fun h2 =>
    let r := h1 * g * h2
    (table.get? r.1.code).map fun e => (r, e)

theorem lookup_spec {g r : G2} {i : ℕ} {w : List ℕ} (h : lookup g = some (r, i, w)) :
    ∃ h1 ∈ H0list, ∃ h2 ∈ H0list, r = h1 * g * h2 := by
  obtain ⟨h1, hh1, e1⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨h2, hh2, e2⟩ := List.exists_of_findSome?_eq_some e1
  refine ⟨h1, hh1, h2, hh2, ?_⟩
  simp only [Option.map_eq_some_iff] at e2
  obtain ⟨_, -, he⟩ := e2
  exact (congrArg Prod.fst he).symm

/-- Decoding of the table's subgroup indices. -/
def ofIdx : ℕ → L7
  | 0 => .bot
  | 1 => .J2
  | 2 => .J1
  | 3 => .K
  | 4 => .M1
  | 5 => .M2
  | _ => .top

/-- The certificate check for a single element. -/
def checkA (g : G2) : Bool :=
  match lookup g with
  | none => false
  | some (r, i, w) => evalWord r w == wOf (ofIdx i) && memB (ofIdx i) g

/-- The index of the subgroup `⟨H₀, g⟩`. -/
def idxOf (g : G2) : L7 :=
  match lookup g with
  | some (_, i, _) => ofIdx i
  | none => .top

theorem checkA_all : forallG2 checkA = true := by native_decide

/-- For every `g`, the subgroup generated by `H₀` and `g` is one of the seven `T i`. -/
theorem closure_eq (g : G2) : Subgroup.closure {a0, t0, g} = T (idxOf g) := by
  have hc := forallG2_spec checkA_all g
  unfold checkA at hc
  unfold idxOf
  rcases hl : lookup g with _ | ⟨r, i, w⟩
  · rw [hl] at hc; exact absurd hc (by simp)
  · rw [hl] at hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨hw, hm⟩ := hc
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact a0_mem_T _
      · exact t0_mem_T _
      · exact mem_T_iff.2 hm
    · refine le_trans (T_le_closure _) ?_
      set S := Subgroup.closure ({a0, t0, g} : Set G2)
      have ha : a0 ∈ S := Subgroup.subset_closure (by simp)
      have ht : t0 ∈ S := Subgroup.subset_closure (by simp)
      have hg : g ∈ S := Subgroup.subset_closure (by simp)
      obtain ⟨h1, hh1, h2, hh2, rfl⟩ := lookup_spec hl
      have hr : h1 * g * h2 ∈ S :=
        S.mul_mem (S.mul_mem (H0list_mem S ha ht h1 hh1) hg) (H0list_mem S ha ht h2 hh2)
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ha
      · exact ht
      · rw [← hw]; exact evalWord_mem S _ ha ht hr w

/-! ### Order relations among the seven subgroups -/

theorem le_check : ∀ i j : L7, i ≤ j → i ≠ .top → j ≠ .top →
    (lst i).all (fun x => (lst j).contains x) = true := by native_decide

theorem nle_check : ∀ i j : L7, ¬ i ≤ j →
    ((if i = .top then [Dα] else lst i).any fun x => !(lst j).contains x) = true := by native_decide

theorem T_mono {i j : L7} (h : i ≤ j) : T i ≤ T j := by
  by_cases hj : j = .top
  · subst hj; rw [T_top]; exact le_top
  by_cases hi : i = .top
  · subst hi; exact absurd (top_le_iff.1 h) (Ne.symm (Ne.symm hj))
  intro x hx
  have := le_check i j h hi hj
  rw [List.all_eq_true] at this
  rw [mem_T_iff, memB, if_neg hi, List.contains_iff_mem] at hx
  exact mem_T_of_mem_lst hj (by simpa using this x hx)

theorem T_le_iff {i j : L7} : T i ≤ T j ↔ i ≤ j := by
  refine ⟨fun h => ?_, T_mono⟩
  by_contra hij
  have hj : j ≠ .top := fun hj => hij (hj ▸ le_top)
  have := nle_check i j hij
  rw [List.any_eq_true] at this
  obtain ⟨x, hx, hnx⟩ := this
  have hxi : x ∈ T i := by
    split_ifs at hx with hi
    · subst hi; rw [T_top]; exact Subgroup.mem_top x
    · exact mem_T_of_mem_lst hi hx
  have := h hxi
  rw [mem_T_iff, memB, if_neg hj] at this
  rw [this] at hnx
  exact absurd hnx (by decide)

theorem join_check : ∀ i j : L7, (i ≤ j ∨ j ≤ i) ∨
    ((lst i).any fun x => (lst j).any fun y => idxOf (x * y) == i ⊔ j) = true := by native_decide

theorem T_sup (i j : L7) : T (i ⊔ j) = T i ⊔ T j := by
  apply le_antisymm
  · rcases join_check i j with (h | h) | h
    · rw [sup_eq_right.2 h]; exact le_sup_right
    · rw [sup_eq_left.2 h]; exact le_sup_left
    · simp only [List.any_eq_true, beq_iff_eq] at h
      obtain ⟨x, hx, y, hy, hxy⟩ := h
      have hi : i ≠ .top := by rintro rfl; simp [lst] at hx
      have hj : j ≠ .top := by rintro rfl; simp [lst] at hy
      rw [← hxy, ← closure_eq, Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact Subgroup.mem_sup_left (a0_mem_T i)
      · exact Subgroup.mem_sup_left (t0_mem_T i)
      · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_T_of_mem_lst hi hx))
          (Subgroup.mem_sup_right (mem_T_of_mem_lst hj hy))
  · exact sup_le (T_mono le_sup_left) (T_mono le_sup_right)

/-! ### Classification of the overgroups -/

/-- The subgroup `H₀ = SL(2,2) ≅ S₃`. -/
def H0 : Subgroup G2 := T .bot

theorem classify (K : Subgroup G2) (hK : H0 ≤ K) : ∃ i, K = T i := by
  classical
  let I : Finset L7 := Finset.univ.filter fun i => T i ≤ K
  refine ⟨I.sup id, le_antisymm ?_ ?_⟩
  · intro g hg
    have hmem : g ∈ T (idxOf g) := by
      rw [← closure_eq]; exact Subgroup.subset_closure (by simp)
    have hle : T (idxOf g) ≤ K := by
      rw [← closure_eq, Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hK (a0_mem_T _)
      · exact hK (t0_mem_T _)
      · exact hg
    have hI : idxOf g ∈ I := by simp [I, hle]
    exact T_mono (Finset.le_sup (f := id) hI) hmem
  · refine Finset.sup_induction (p := fun j => T j ≤ K) hK ?_ ?_
    · intro a ha b hb
      rw [T_sup]; exact sup_le ha hb
    · intro i hi
      simpa [I] using hi

/-- The interval `[H₀, G]` in the subgroup lattice of `SL(2,64)` is order-isomorphic to `𝐋₇`. -/
noncomputable def intervalIso : Set.Icc H0 ⊤ ≃o L7 :=
  let f : L7 → Set.Icc H0 ⊤ := fun i => ⟨T i, T_mono bot_le, le_top⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j h => ?_, fun K => ?_⟩
    · have h' : T i = T j := congrArg Subtype.val h
      exact le_antisymm (T_le_iff.1 h'.le) (T_le_iff.1 h'.ge)
    · obtain ⟨i, hi⟩ := classify K.1 K.2.1
      exact ⟨i, Subtype.ext hi.symm⟩
  ({ toEquiv := Equiv.ofBijective f hf
     map_rel_iff' := fun {i j} => by
      change T i ≤ T j ↔ i ≤ j
      exact T_le_iff } : L7 ≃o Set.Icc H0 ⊤).symm

end PSL264

end
