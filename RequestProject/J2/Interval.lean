module

public import RequestProject.J2.Perm100
public import RequestProject.J2.L61
public import J2Fast
meta import J2Fast

/-!
# The interval `[D₂₀, J₂]` in the subgroup lattice of `J₂`

We work in the computable model `P100` of `Equiv.Perm (Fin 100)`. `G` is the group generated
by the ATLAS standard generators of `J₂` on 100 points, `H` is a dihedral subgroup of order 20,
and `T i` (`i : L61`) are eight explicit subgroups. We prove that the subgroups `K` with
`H ≤ K ≤ G` are exactly the `T i`, with `T i ≤ T j ↔ i ≤ j`.

The proof is a certificate check. Every element of `G` lies in a double coset `H r H` for one
of the representatives `r` listed in `Data.lean` (checked by showing that the union of these
double cosets is closed under multiplication by the generators of `G`), and for each `r` the
subgroup `⟨H, r⟩` is identified with one of the `T i` by explicit words.
-/

@[expose] public section

namespace J2Cert

open P100

/-! ### The group `J₂` -/

/-- The group `J₂ = ⟨a, b⟩` inside `P100`. -/
def G : Subgroup P100 := Subgroup.closure {pA, pB}

/-! ### Words -/

theorem evalW_mem (K : Subgroup P100) (gens : List P100) (h : ∀ g ∈ gens, g ∈ K)
    (w : List ℤ) : evalW gens w ∈ K := by
  have hget : ∀ n, gens.getD n 1 ∈ K := by
    intro n
    rw [List.getD_eq_getElem?_getD]
    cases hn : gens[n]? with
    | none => exact K.one_mem
    | some x => exact h x (List.mem_of_getElem? hn)
  have hl : ∀ k, letterOf gens k ∈ K := by
    intro k
    unfold letterOf
    split_ifs
    · exact hget _
    · exact K.inv_mem (hget _)
  have key : ∀ (w : List ℤ) (acc : P100), acc ∈ K →
      w.foldl (fun acc k => letterOf gens k * acc) acc ∈ K := by
    intro w
    induction w with
    | nil => intro acc h; exact h
    | cons l w ih => intro acc h; exact ih _ (K.mul_mem (hl l) h)
  exact key w 1 K.one_mem

/-! ### The eight subgroups -/

/-- The eight subgroups of the interval. -/
def T (i : L61) : Subgroup P100 := Subgroup.closure {x | x ∈ allGens i}

/-- The dihedral subgroup `D₂₀ = ⟨h1, h2⟩`. -/
def H : Subgroup P100 := T .bot

theorem allGens_mem_T (i : L61) {x : P100} (hx : x ∈ allGens i) : x ∈ T i :=
  Subgroup.subset_closure hx

theorem h1_mem_T (i : L61) : h1 ∈ T i := allGens_mem_T i (by simp [allGens])
theorem h2_mem_T (i : L61) : h2 ∈ T i := allGens_mem_T i (by simp [allGens])

/-! ### Membership in `G` -/

theorem words_check :
    (List.zip wordsInAB wordTargets).all (fun p => evalW [pA, pB] p.1 == p.2) = true ∧
    wordsInAB.length = 6 := by native_decide

theorem wordTargets_mem_G : ∀ x ∈ wordTargets, x ∈ G := by
  have hA : ∀ g ∈ [pA, pB], g ∈ G := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> exact Subgroup.subset_closure (by simp)
  obtain ⟨h, hlen⟩ := words_check
  rw [List.all_eq_true] at h
  intro x hx
  obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.1 hx
  have hn' : n < wordsInAB.length := by rw [hlen]; simpa [wordTargets] using hn
  have hmem : (wordsInAB[n], wordTargets[n]) ∈ List.zip wordsInAB wordTargets := by
    rw [List.mem_iff_getElem]
    exact ⟨n, by simp [hn', hn], by simp⟩
  have := h _ hmem
  simp only [beq_iff_eq] at this
  rw [← this]
  exact evalW_mem G _ hA _

theorem allGens_mem_G (i : L61) : ∀ x ∈ allGens i, x ∈ G := by
  intro x hx
  have hw := wordTargets_mem_G
  simp only [wordTargets, List.mem_cons, List.not_mem_nil, or_false] at hw
  have hA : pA ∈ G := Subgroup.subset_closure (by simp)
  have hB : pB ∈ G := Subgroup.subset_closure (by simp)
  have key : x = h1 ∨ x = h2 ∨ x = qa ∨ x = qb ∨ x = qc ∨ x = qf ∨ x = pA ∨ x = pB := by
    cases i <;> simp only [allGens, gensOf, List.mem_cons, List.not_mem_nil, or_false] at hx <;>
      tauto
  rcases key with h | h | h | h | h | h | h | h
  all_goals first
    | exact h ▸ hA
    | exact h ▸ hB
    | exact hw x (by tauto)

theorem T_le_G (i : L61) : T i ≤ G := by
  rw [T, Subgroup.closure_le]
  exact allGens_mem_G i

theorem T_top : T .top = G := by
  apply le_antisymm (T_le_G _)
  rw [G, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl <;> exact allGens_mem_T _ (by simp [allGens, gensOf])

theorem H_le_G : H ≤ G := T_le_G _

/-! ### The finite subgroups as lists -/

theorem mem_dedupH {l : List P100} {x : P100} (hx : x ∈ dedupH l) : x ∈ l := by
  have key : ∀ (l : List P100) (p : List P100 × Std.HashSet P100),
      ∀ y ∈ (l.foldl (fun (p : List P100 × Std.HashSet P100) x =>
        if p.2.contains x then p else (x :: p.1, p.2.insert x)) p).1, y ∈ p.1 ∨ y ∈ l := by
    intro l
    induction l with
    | nil => intro p y hy; exact Or.inl hy
    | cons a l ih =>
      intro p y hy
      rw [List.foldl_cons] at hy
      rcases ih _ y hy with h | h
      · split_ifs at h with hc
        · exact Or.inl h
        · simp only [List.mem_cons] at h
          rcases h with rfl | h
          · exact Or.inr (List.mem_cons_self)
          · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
  rcases key l ([], {}) x hx with h | h
  · simp at h
  · exact h

theorem mem_genList (S : List P100) (n : ℕ) (l : List P100)
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
      have hx := mem_dedupH hx
      simp only [List.mem_append, List.mem_flatMap, List.mem_map] at hx
      rcases hx with h | ⟨y, hy, s, hs, rfl⟩
      · exact hl x h
      · exact Subgroup.mul_mem _ (hl y hy) (Subgroup.subset_closure hs)

theorem lst_eq {i : L61} (h : i ≠ .top) : lst i = genList (allGens i) 40 [1] := by
  cases i <;> first | rfl | exact absurd rfl h

theorem memB_iff (i : L61) (x : P100) : memB i x = true ↔ x ∈ lst i := by
  cases i <;>
    simp [memB, setBot, setA, setB, setC, setD, setE, setF, Std.HashSet.contains_ofList, lst]

theorem lst_sound {i : L61} {x : P100} (hx : x ∈ lst i) : x ∈ T i := by
  by_cases h : i = .top
  · subst h; simp [lst] at hx
  · rw [lst_eq h] at hx
    exact mem_genList _ _ _ (by simp) x hx

theorem closed_check : ∀ i : L61, i ≠ .top → closedB i = true := by native_decide

theorem lst_complete {i : L61} (hi : i ≠ .top) {x : P100} (hx : x ∈ T i) : x ∈ lst i := by
  have hc := closed_check i hi
  simp only [closedB, Bool.and_eq_true, List.all_eq_true, memB_iff] at hc
  obtain ⟨h1m, hc⟩ := hc
  have key : ∀ y ∈ lst i, y * x ∈ lst i := by
    refine Subgroup.closure_induction'' (p := fun x _ => ∀ y ∈ lst i, y * x ∈ lst i)
      ?_ ?_ ?_ ?_ hx
    · intro g hg y hy; exact (hc y hy g hg).1
    · intro g hg y hy; exact (hc y hy g hg).2
    · intro y hy; simpa using hy
    · intro a b _ _ ha hb y hy
      rw [← mul_assoc]; exact hb _ (ha y hy)
  simpa using key 1 h1m

theorem mem_T_iff {i : L61} (hi : i ≠ .top) {x : P100} : x ∈ T i ↔ memB i x = true := by
  rw [memB_iff]; exact ⟨lst_complete hi, lst_sound⟩

/-! ### Double coset representatives -/

theorem reps_check : reps.all repOK = true := by native_decide

theorem closure_rep_eq {rp : Rep} (hrp : repOK rp = true) (hr : rp.r ∈ G) :
    Subgroup.closure {h1, h2, rp.r} = T rp.idx := by
  simp only [repOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true,
    List.any_eq_true] at hrp
  obtain ⟨hmem, hw⟩ := hrp
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact h1_mem_T _
    · exact h2_mem_T _
    · rcases hmem with htop | hm
      · rw [htop, T_top]; exact hr
      · by_cases htop : rp.idx = .top
        · rw [htop, T_top]; exact hr
        · exact (mem_T_iff htop).2 hm
  · set K := Subgroup.closure ({h1, h2, rp.r} : Set P100)
    have hK : ∀ g ∈ [h1, h2, rp.r], g ∈ K := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;> exact Subgroup.subset_closure (by simp)
    rw [T, Subgroup.closure_le]
    intro x hx
    simp only [allGens, Set.mem_setOf_eq, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hK _ (by simp)
    · exact hK _ (by simp)
    · obtain ⟨w, -, hwx⟩ := hw x hx
      rw [← hwx]; exact evalW_mem K _ hK w

/-! ### The union of the double cosets contains `G` -/

theorem Hl_mem {i : ℕ} (h : i < Hl.size) : Hl[i] ∈ H := by
  have : Hl[i] ∈ lst .bot := by
    have hmem : Hl[i] ∈ lstBot.toArray := Array.getElem_mem h
    exact List.mem_toArray.1 hmem
  exact lst_sound this

theorem locate_spec {g : P100} {i k j : ℕ} (h : locate g = some (i, k, j)) :
    ∃ hi : i < Hl.size, ∃ hk : k < reps.size, ∃ hj : j < Hl.size,
      g = Hl[i] * reps[k].r * Hl[j] := by
  unfold locate at h
  split at h
  · split_ifs at h with h1 h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨h1.1, h1.2.1, h1.2.2, h2⟩
  · exact absurd h (by simp)

/-- The union of the double cosets `H r H`. -/
def S : Set P100 := {g | ∃ x ∈ H, ∃ rp ∈ reps, ∃ y ∈ H, g = x * rp.r * y}

theorem mem_S_of_checkS {g : P100} (h : checkS g = true) : g ∈ S := by
  unfold checkS at h
  obtain ⟨⟨i, k, j⟩, hl⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨hi, hk, hj, rfl⟩ := locate_spec hl
  exact ⟨_, Hl_mem hi, _, Array.getElem_mem hk, _, Hl_mem hj, rfl⟩

theorem sClosed_check : sClosedB = true := by native_decide

theorem G_subset_S {g : P100} (hg : g ∈ G) : g ∈ S := by
  have hc := sClosed_check
  simp only [sClosedB, Bool.and_eq_true, Array.all_eq_true, List.all_eq_true] at hc
  obtain ⟨h1S, hc⟩ := hc
  have hgen : ∀ t ∈ genChecks, ∀ s ∈ S, s * t ∈ S := by
    rintro t ht s ⟨x, hx, rp, hrp, y, hy, rfl⟩
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hrp
    have hy' : y ∈ lstBot := lst_complete (i := .bot) (by decide) hy
    obtain ⟨x', hx', rp', hrp', y', hy'', he⟩ := mem_S_of_checkS (hc k hk y hy' t ht)
    refine ⟨x * x', H.mul_mem hx hx', rp', hrp', y', hy'', ?_⟩
    rw [mul_assoc, mul_assoc, mul_assoc, ← mul_assoc reps[k].r, he]
    group
  have key : ∀ s ∈ S, s * g ∈ S := by
    refine Subgroup.closure_induction'' (p := fun g _ => ∀ s ∈ S, s * g ∈ S) ?_ ?_ ?_ ?_ hg
    · intro t ht s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl
      · exact hgen _ (by simp [genChecks]) s hs
      · exact hgen _ (by simp [genChecks]) s hs
    · intro t ht s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl
      · exact hgen _ (by simp [genChecks]) s hs
      · exact hgen _ (by simp [genChecks]) s hs
    · intro s hs; simpa using hs
    · intro a b _ _ ha hb s hs
      rw [← mul_assoc]; exact hb _ (ha s hs)
  simpa using key 1 (mem_S_of_checkS h1S)

/-! ### The subgroup generated by `H` and one element -/

theorem closure_eq_of_dcoset {g x y r : P100} (hx : x ∈ H) (hy : y ∈ H) (hg : g = x * r * y) :
    Subgroup.closure {h1, h2, g} = Subgroup.closure {h1, h2, r} := by
  have hH : ∀ K : Subgroup P100, h1 ∈ K → h2 ∈ K → H ≤ K := by
    intro K ha hb
    rw [H, T, Subgroup.closure_le]
    intro z hz
    simp only [allGens, gensOf, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil,
      or_false] at hz
    rcases hz with rfl | rfl
    · exact ha
    · exact hb
  apply le_antisymm
  · set K := Subgroup.closure ({h1, h2, r} : Set P100)
    have hHK := hH K (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · rw [hg]
      exact K.mul_mem (K.mul_mem (hHK hx) (Subgroup.subset_closure (by simp))) (hHK hy)
  · set K := Subgroup.closure ({h1, h2, g} : Set P100)
    have hHK := hH K (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · have : z = x⁻¹ * g * y⁻¹ := by rw [hg]; group
      rw [this]
      exact K.mul_mem (K.mul_mem (K.inv_mem (hHK hx)) (Subgroup.subset_closure (by simp)))
        (K.inv_mem (hHK hy))

theorem repOK_of_mem {rp : Rep} (hrp : rp ∈ reps) : repOK rp = true := by
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hrp
  exact (Array.all_eq_true.1 reps_check) k hk

/-- For every `g ∈ G`, the subgroup generated by `H` and `g` is one of the `T i`. -/
theorem closure_eq_T {g : P100} (hg : g ∈ G) : ∃ i, Subgroup.closure {h1, h2, g} = T i := by
  obtain ⟨x, hx, rp, hrp, y, hy, he⟩ := G_subset_S hg
  refine ⟨rp.idx, ?_⟩
  rw [closure_eq_of_dcoset hx hy he]
  apply closure_rep_eq (repOK_of_mem hrp)
  have : rp.r = x⁻¹ * g * y⁻¹ := by rw [he]; group
  rw [this]
  exact G.mul_mem (G.mul_mem (G.inv_mem (H_le_G hx)) hg) (G.inv_mem (H_le_G hy))

/-- Computable version, via the table. -/
theorem closure_eq_idxOf {g : P100} (hg : g ∈ G) (hc : checkS g = true) :
    Subgroup.closure {h1, h2, g} = T (idxOf g) := by
  unfold checkS at hc
  obtain ⟨⟨i, k, j⟩, hl⟩ := Option.isSome_iff_exists.1 hc
  obtain ⟨hi, hk, hj, he⟩ := locate_spec hl
  have hidx : idxOf g = reps[k].idx := by
    simp [idxOf, hl, Array.getD, hk]
  rw [hidx, closure_eq_of_dcoset (Hl_mem hi) (Hl_mem hj) he]
  apply closure_rep_eq (repOK_of_mem (Array.getElem_mem hk))
  have : reps[k].r = (Hl[i])⁻¹ * g * (Hl[j])⁻¹ := by rw [he]; group
  rw [this]
  exact G.mul_mem (G.mul_mem (G.inv_mem (H_le_G (Hl_mem hi))) hg)
    (G.inv_mem (H_le_G (Hl_mem hj)))

/-! ### Order relations among the eight subgroups -/

theorem mem_T_of_memT {j : L61} {x : P100} (hx : x ∈ G) (h : memT j x = true) : x ∈ T j := by
  by_cases hj : j = .top
  · rw [hj, T_top]; exact hx
  · simp only [memT, Bool.or_eq_true, beq_iff_eq, hj, false_or] at h
    exact (mem_T_iff hj).2 h

theorem le_check : ∀ i j : L61, i ≤ j → (allGens i).all (memT j) = true := by native_decide

theorem nle_check : ∀ i j : L61, ¬ i ≤ j →
    ((if i = .top then [pA, pB] else lst i).any fun x => !memB j x) = true := by native_decide

theorem T_mono {i j : L61} (h : i ≤ j) : T i ≤ T j := by
  rw [T, Subgroup.closure_le]
  intro x hx
  have := le_check i j h
  rw [List.all_eq_true] at this
  exact mem_T_of_memT (allGens_mem_G i x hx) (this x hx)

theorem T_le_iff {i j : L61} : T i ≤ T j ↔ i ≤ j := by
  refine ⟨fun h => ?_, T_mono⟩
  by_contra hij
  have hj : j ≠ .top := fun hj => hij (hj ▸ le_top)
  have := nle_check i j hij
  rw [List.any_eq_true] at this
  obtain ⟨x, hx, hnx⟩ := this
  have hxi : x ∈ T i := by
    split_ifs at hx with hi
    · subst hi
      rw [T_top]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> exact Subgroup.subset_closure (by simp)
    · exact lst_sound hx
  have := (mem_T_iff hj).1 (h hxi)
  rw [this] at hnx
  exact absurd hnx (by decide)

theorem join_check : ∀ i j : L61, (i ≤ j ∨ j ≤ i) ∨
    ((lst i).any fun x => (lst j).any fun y => checkS (x * y) && idxOf (x * y) == i ⊔ j) = true :=
  by native_decide

theorem T_sup (i j : L61) : T (i ⊔ j) = T i ⊔ T j := by
  apply le_antisymm
  · rcases join_check i j with (h | h) | h
    · rw [sup_eq_right.2 h]; exact le_sup_right
    · rw [sup_eq_left.2 h]; exact le_sup_left
    · simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨x, hx, y, hy, hc, hxy⟩ := h
      have hxT := lst_sound hx
      have hyT := lst_sound hy
      have hxyG : x * y ∈ G := G.mul_mem (T_le_G i hxT) (T_le_G j hyT)
      rw [← hxy, ← closure_eq_idxOf hxyG hc, Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact Subgroup.mem_sup_left (h1_mem_T i)
      · exact Subgroup.mem_sup_left (h2_mem_T i)
      · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hxT) (Subgroup.mem_sup_right hyT)
  · exact sup_le (T_mono le_sup_left) (T_mono le_sup_right)

/-! ### Classification of the intermediate subgroups -/

theorem classify (K : Subgroup P100) (hHK : H ≤ K) (hKG : K ≤ G) : ∃ i, K = T i := by
  classical
  let I : Finset L61 := Finset.univ.filter fun i => T i ≤ K
  refine ⟨I.sup id, le_antisymm ?_ ?_⟩
  · intro g hg
    obtain ⟨i, hi⟩ := closure_eq_T (hKG hg)
    have hmem : g ∈ T i := by
      rw [← hi]; exact Subgroup.subset_closure (by simp)
    have hle : T i ≤ K := by
      rw [← hi, Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hHK (h1_mem_T _)
      · exact hHK (h2_mem_T _)
      · exact hg
    have hI : i ∈ I := by simp [I, hle]
    exact T_mono (Finset.le_sup (f := id) hI) hmem
  · refine Finset.sup_induction (p := fun j => T j ≤ K) hHK ?_ ?_
    · intro u hu v hv
      rw [T_sup]; exact sup_le hu hv
    · intro i hi
      simpa [I] using hi

/-- The interval `[H, G]` in the subgroup lattice of `P100` is order-isomorphic to `#61`. -/
noncomputable def intervalIso : Set.Icc H G ≃o L61 :=
  let f : L61 → Set.Icc H G := fun i => ⟨T i, T_mono bot_le, T_le_G i⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j h => ?_, fun K => ?_⟩
    · have h' : T i = T j := congrArg Subtype.val h
      exact le_antisymm (T_le_iff.1 h'.le) (T_le_iff.1 h'.ge)
    · obtain ⟨i, hi⟩ := classify K.1 K.2.1 K.2.2
      exact ⟨i, Subtype.ext hi.symm⟩
  ({ toEquiv := Equiv.ofBijective f hf
     map_rel_iff' := fun {i j} => by
      change T i ≤ T j ↔ i ≤ j
      exact T_le_iff } : L61 ≃o Set.Icc H G).symm

end J2Cert

end
