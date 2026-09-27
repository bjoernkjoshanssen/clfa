module

public import Mathlib

/-!
# Congruence lattices of coset algebras

For a unary algebra `⟨X; (F i)_{i : ι}⟩` (a set with a family of unary operations), a
congruence is an equivalence relation on `X` compatible with every operation; `UnaryCon F` is
the set of congruences, ordered by inclusion.

For a group `Γ` and a subgroup `K`, the coset algebra is `Γ ⧸ K` with the unary operations
`x ↦ g • x` (`g : Γ`). Its congruences are the block systems of the action, and
`conIso K : UnaryCon (cosetOps K) ≃o Set.Icc K ⊤` identifies them with the interval `[K, Γ]`
in the subgroup lattice of `Γ`.
-/

@[expose] public section

namespace J2Cert

/-- The congruence lattice of the unary algebra `⟨X; (F i)_{i : ι}⟩`: the equivalence relations
on `X` that are compatible with every operation `F i`, ordered by inclusion. -/
def UnaryCon {ι X : Type*} (F : ι → X → X) : Type _ :=
  {r : Setoid X // ∀ i x y, r x y → r (F i x) (F i y)}

instance {ι X : Type*} (F : ι → X → X) : PartialOrder (UnaryCon F) :=
  inferInstanceAs (PartialOrder {r : Setoid X // ∀ i x y, r x y → r (F i x) (F i y)})

section

variable {Γ : Type*} [Group Γ] (K : Subgroup Γ)

/-- The operations of the coset algebra `Γ ⧸ K`: left multiplication by the elements of `Γ`. -/
def cosetOps : Γ → Γ ⧸ K → Γ ⧸ K := fun g x => g • x

theorem cosetOps_mk (g a : Γ) : cosetOps K g (a : Γ ⧸ K) = ((g * a : Γ) : Γ ⧸ K) := rfl

/-- The congruence attached to a subgroup `L ≥ K`: `aK ~ bK` iff `aL = bL`. -/
def conOfSub (L : Subgroup Γ) (hL : K ≤ L) : UnaryCon (cosetOps K) :=
  ⟨Setoid.ker (Subgroup.quotientMapOfLE hL), by
    intro g x y hxy
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    rw [Setoid.ker_def, Subgroup.quotientMapOfLE_apply_mk, Subgroup.quotientMapOfLE_apply_mk,
      QuotientGroup.eq] at hxy
    rw [cosetOps_mk, cosetOps_mk, Setoid.ker_def, Subgroup.quotientMapOfLE_apply_mk,
      Subgroup.quotientMapOfLE_apply_mk, QuotientGroup.eq]
    simpa [mul_inv_rev, mul_assoc] using hxy⟩

theorem conOfSub_mk (L : Subgroup Γ) (hL : K ≤ L) (a b : Γ) :
    (conOfSub K L hL).1 (a : Γ ⧸ K) (b : Γ ⧸ K) ↔ a⁻¹ * b ∈ L := by
  change Setoid.ker _ _ _ ↔ _
  rw [Setoid.ker_def, Subgroup.quotientMapOfLE_apply_mk, Subgroup.quotientMapOfLE_apply_mk,
    QuotientGroup.eq]

variable {K}

/-- The subgroup attached to a congruence: the elements `g` with `K ~ gK`. -/
def subOfCon (r : UnaryCon (cosetOps K)) : Subgroup Γ where
  carrier := {g | r.1 ((1 : Γ) : Γ ⧸ K) (g : Γ ⧸ K)}
  one_mem' := r.1.refl _
  mul_mem' := by
    intro a b ha hb
    have := r.2 a _ _ hb
    rw [cosetOps_mk, cosetOps_mk, mul_one] at this
    exact r.1.trans ha this
  inv_mem' := by
    intro a ha
    have := r.2 a⁻¹ _ _ ha
    rw [cosetOps_mk, cosetOps_mk, mul_one, inv_mul_cancel] at this
    exact r.1.symm this

theorem mem_subOfCon (r : UnaryCon (cosetOps K)) (g : Γ) :
    g ∈ subOfCon r ↔ r.1 ((1 : Γ) : Γ ⧸ K) (g : Γ ⧸ K) := Iff.rfl

theorem le_subOfCon (r : UnaryCon (cosetOps K)) : K ≤ subOfCon r := by
  intro k hk
  rw [mem_subOfCon]
  have : ((1 : Γ) : Γ ⧸ K) = (k : Γ ⧸ K) := QuotientGroup.eq.2 (by simpa using hk)
  rw [this]

theorem rel_iff_mem (r : UnaryCon (cosetOps K)) (a b : Γ) :
    r.1 (a : Γ ⧸ K) (b : Γ ⧸ K) ↔ a⁻¹ * b ∈ subOfCon r := by
  rw [mem_subOfCon]
  constructor
  · intro h
    have := r.2 a⁻¹ _ _ h
    rwa [cosetOps_mk, cosetOps_mk, inv_mul_cancel] at this
  · intro h
    have := r.2 a _ _ h
    rwa [cosetOps_mk, cosetOps_mk, mul_one, ← mul_assoc, mul_inv_cancel, one_mul] at this

variable (K)

/-- The congruence lattice of the coset algebra `Γ ⧸ K` is isomorphic to the interval `[K, Γ]`
of the subgroup lattice of `Γ`. -/
def conIso : UnaryCon (cosetOps K) ≃o Set.Icc K ⊤ where
  toFun r := ⟨subOfCon r, le_subOfCon r, le_top⟩
  invFun L := conOfSub K L.1 L.2.1
  left_inv r := by
    apply Subtype.ext
    ext x y
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    change (conOfSub K _ _).1 _ _ ↔ _
    rw [conOfSub_mk, rel_iff_mem]
  right_inv L := by
    apply Subtype.ext
    ext g
    change g ∈ subOfCon (conOfSub K L.1 L.2.1) ↔ g ∈ L.1
    rw [mem_subOfCon, conOfSub_mk, inv_one, one_mul]
  map_rel_iff' := by
    intro r s
    change subOfCon r ≤ subOfCon s ↔ r ≤ s
    constructor
    · intro h
      change r.1 ≤ s.1
      rw [Setoid.le_def]
      intro x y hxy
      induction x using QuotientGroup.induction_on with | H a => ?_
      induction y using QuotientGroup.induction_on with | H b => ?_
      rw [rel_iff_mem] at hxy ⊢
      exact h hxy
    · intro h g hg
      exact Setoid.le_def.1 h hg

end

/-- For subgroups `H ≤ G` of `P`, the interval `[H, G]` in the subgroup lattice of `P` is
isomorphic to the interval `[H ∩ G, G]` in the subgroup lattice of `G` itself. -/
def iccSubgroupOfIso {P : Type*} [Group P] (H G : Subgroup P) (h : H ≤ G) :
    Set.Icc (H.subgroupOf G) ⊤ ≃o Set.Icc H G where
  toFun K := ⟨K.1.map G.subtype,
      (Subgroup.map_subgroupOf_eq_of_le h).symm.le.trans (Subgroup.map_mono K.2.1),
      Subgroup.map_subtype_le _⟩
  invFun L := ⟨L.1.subgroupOf G, Subgroup.comap_mono L.2.1, le_top⟩
  left_inv K := by
    apply Subtype.ext
    exact Subgroup.comap_map_eq_self_of_injective G.subtype_injective _
  right_inv L := by
    apply Subtype.ext
    change (L.1.subgroupOf G).map G.subtype = L.1
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 L.2.2]
  map_rel_iff' := by
    intro K L
    change K.1.map G.subtype ≤ L.1.map G.subtype ↔ K.1 ≤ L.1
    exact Subgroup.map_le_map_iff_of_injective G.subtype_injective

end J2Cert

end
