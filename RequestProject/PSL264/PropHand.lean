module

public import RequestProject.PSL264.Overgroups
meta import RequestProject.PSL264.Overgroups

/-!
# Proposition `prop:hand`

Let `G = PSL(2,64)` and `H ≅ S₃` a subgroup. Then the interval `[H, G]` of the subgroup
lattice of `G` is isomorphic to DeMeo's lattice `𝐋₇`.
-/

@[expose] public section

namespace PSL264

open G2

/-! ### All subgroups `S₃` are conjugate -/

/-- A candidate conjugator sending an element of order `3` to `a0`. -/
def conjCand (a : G2) : Option G2 :=
  [((1 : GF64), (0 : GF64)), (0, 1), (1, 1)].findSome? fun v =>
    let w1 := a.1.a * v.1 + a.1.b * v.2
    let w2 := a.1.c * v.1 + a.1.d * v.2
    let lam := ((v.1 * w2 - w1 * v.2)⁻¹) ^ 32
    let P : M2 := ⟨lam * v.1, lam * w1, lam * v.2, lam * w2⟩
    if h : P.det = 1 then some (⟨P, h⟩ : G2)⁻¹ else none

def conj3Check (a : G2) : Bool :=
  !(a ^ 3 == 1) || a == 1 ||
    match conjCand a with
    | some g => g * a * g⁻¹ == a0
    | none => false

theorem conj3_all : forallG2 conj3Check = true := by native_decide

theorem conj_order3 (a : G2) (h3 : a ^ 3 = 1) (h1 : a ≠ 1) : ∃ g : G2, g * a * g⁻¹ = a0 := by
  have h := forallG2_spec conj3_all a
  have e1 : (a ^ 3 == 1) = true := by simp [h3]
  have e2 : (a == 1) = false := by simp [h1]
  unfold conj3Check at h
  rw [e1, e2] at h
  revert h
  rcases conjCand a with _ | g
  · simp
  · intro h; exact ⟨g, by simpa using h⟩

def invCheck (t : G2) : Bool :=
  !(t ^ 2 == 1) || t == 1 || !(t * a0 * t⁻¹ == a0⁻¹) ||
    (let g := (t0 * t) ^ 32
     g * a0 * g⁻¹ == a0 && g * t * g⁻¹ == t0)

theorem inv_all : forallG2 invCheck = true := by native_decide

theorem conj_pair (a t : G2) (h3 : a ^ 3 = 1) (ha : a ≠ 1) (h2 : t ^ 2 = 1) (ht : t ≠ 1)
    (hinv : t * a * t⁻¹ = a⁻¹) : ∃ g : G2, g * a * g⁻¹ = a0 ∧ g * t * g⁻¹ = t0 := by
  obtain ⟨g1, hg1⟩ := conj_order3 a h3 ha
  set t' := g1 * t * g1⁻¹ with ht'
  have h2' : t' ^ 2 = 1 := by rw [ht', conj_pow, h2]; group
  have ht1 : t' ≠ 1 := by
    intro h; apply ht
    have : t = g1⁻¹ * t' * g1 := by rw [ht']; group
    rw [this, h]; group
  have hinv' : t' * a0 * t'⁻¹ = a0⁻¹ := by
    have e1 : t' * a0 * t'⁻¹ = g1 * (t * a * t⁻¹) * g1⁻¹ := by rw [ht', ← hg1]; group
    rw [e1, hinv, ← hg1]; group
  have h := forallG2_spec inv_all t'
  have e1 : (t' ^ 2 == 1) = true := by simp [h2']
  have e2 : (t' == 1) = false := by simp [ht1]
  have e3 : (t' * a0 * t'⁻¹ == a0⁻¹) = true := by simp [hinv']
  unfold invCheck at h
  rw [e1, e2, e3] at h
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hA, hB⟩ := h
  refine ⟨(t0 * t') ^ 32 * g1, ?_, ?_⟩
  · have e : (t0 * t') ^ 32 * g1 * a * ((t0 * t') ^ 32 * g1)⁻¹ =
        (t0 * t') ^ 32 * (g1 * a * g1⁻¹) * ((t0 * t') ^ 32)⁻¹ := by group
    rw [e, hg1, hA]
  · have e : (t0 * t') ^ 32 * g1 * t * ((t0 * t') ^ 32 * g1)⁻¹ =
        (t0 * t') ^ 32 * t' * ((t0 * t') ^ 32)⁻¹ := by rw [ht']; group
    rw [e, hB]

/-- A `3`-cycle in `S₃`. -/
def c3 : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
/-- A transposition in `S₃`. -/
def s3 : Equiv.Perm (Fin 3) := Equiv.swap 0 1

theorem c3_pow : c3 ^ 3 = 1 := by decide
theorem c3_ne : c3 ≠ 1 := by decide
theorem s3_pow : s3 ^ 2 = 1 := by decide
theorem s3_ne : s3 ≠ 1 := by decide
theorem s3_c3 : s3 * c3 * s3⁻¹ = c3⁻¹ := by decide
theorem S3_elems : ∀ σ : Equiv.Perm (Fin 3), ∃ i < 3, ∃ j < 2, σ = c3 ^ i * s3 ^ j := by decide

/-- Every subgroup of `SL(2,64)` isomorphic to `S₃` is conjugate to `H₀ = SL(2,2)`. -/
theorem conj_S3 (H : Subgroup G2) (e : H ≃* Equiv.Perm (Fin 3)) :
    ∃ g : G2, H.map (MulAut.conj g).toMonoidHom = H0 := by
  set a : G2 := (e.symm c3).1
  set t : G2 := (e.symm s3).1
  have hcoe : ∀ σ τ : Equiv.Perm (Fin 3), σ = τ → ((e.symm σ : H) : G2) = (e.symm τ : H) := by
    rintro _ _ rfl; rfl
  have ha3 : a ^ 3 = 1 := by
    simp only [a, ← Subgroup.coe_pow, ← map_pow, c3_pow, map_one, Subgroup.coe_one]
  have ht2 : t ^ 2 = 1 := by
    simp only [t, ← Subgroup.coe_pow, ← map_pow, s3_pow, map_one, Subgroup.coe_one]
  have ha1 : a ≠ 1 := by
    intro h
    apply c3_ne
    apply e.symm.injective
    rw [map_one]; exact Subtype.ext h
  have ht1 : t ≠ 1 := by
    intro h
    apply s3_ne
    apply e.symm.injective
    rw [map_one]; exact Subtype.ext h
  have hinv : t * a * t⁻¹ = a⁻¹ := by
    have := hcoe _ _ s3_c3
    simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using this
  obtain ⟨g, hga, hgt⟩ := conj_pair a t ha3 ha1 ht2 ht1 hinv
  refine ⟨g, le_antisymm ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, -, j, -, hij⟩ := S3_elems (e ⟨x, hx⟩)
    have hx' : x = a ^ i * t ^ j := by
      have := congrArg (fun σ => ((e.symm σ : H) : G2)) hij
      simpa only [MulEquiv.symm_apply_apply, map_mul, map_pow, Subgroup.coe_mul,
        Subgroup.coe_pow] using this
    rw [hx']
    change g * (a ^ i * t ^ j) * g⁻¹ ∈ H0
    have : g * (a ^ i * t ^ j) * g⁻¹ = (g * a * g⁻¹) ^ i * (g * t * g⁻¹) ^ j := by
      rw [conj_pow, conj_pow]; group
    rw [this, hga, hgt]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (a0_mem_T _) _)
      (Subgroup.pow_mem _ (t0_mem_T _) _)
  · refine le_trans (T_le_closure _) ?_
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact ⟨a, (e.symm c3).2, by simp [hga]⟩
    · exact ⟨t, (e.symm s3).2, by simp [hgt]⟩
    · exact Subgroup.one_mem _

/-! ### Transfer to `PSL(2, 64)` -/

/-- `G2` is `SL(2, GF64)`. -/
def toSL : G2 →* Matrix.SpecialLinearGroup (Fin 2) GF64 where
  toFun x := ⟨!![x.1.a, x.1.b; x.1.c, x.1.d], by rw [Matrix.det_fin_two_of]; exact x.2⟩
  map_one' := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_mul' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_mul]

theorem toSL_bijective : Function.Bijective toSL := by
  refine ⟨fun x y h => ?_, fun A => ?_⟩
  · have h' := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) GF64 => (A : Matrix (Fin 2) (Fin 2) GF64)) h
    have e00 := congrFun (congrFun h' 0) 0
    have e01 := congrFun (congrFun h' 0) 1
    have e10 := congrFun (congrFun h' 1) 0
    have e11 := congrFun (congrFun h' 1) 1
    simp [toSL] at e00 e01 e10 e11
    exact G2.ext_iff'.2 ⟨e00, e01, e10, e11⟩
  · refine ⟨⟨⟨A 0 0, A 0 1, A 1 0, A 1 1⟩, ?_⟩, ?_⟩
    · have := A.2
      rw [Matrix.det_fin_two] at this
      exact this
    · ext i j
      fin_cases i <;> fin_cases j <;> rfl

/-- `G2 ≃* SL(2, GF64)`. -/
noncomputable def toSLEquiv : G2 ≃* Matrix.SpecialLinearGroup (Fin 2) GF64 :=
  MulEquiv.ofBijective toSL toSL_bijective

/-- A ring isomorphism `GF64 ≃+* GaloisField 2 6`. -/
noncomputable def gfEquiv : GF64 ≃+* GaloisField 2 6 :=
  letI : Algebra (ZMod 2) GF64 := ZMod.algebra GF64 2
  (GaloisField.algEquivGaloisFieldOfFintype 2 6 GF64.card_eq).toRingEquiv

/-- `SL(2, R) ≃* SL(2, S)` induced by a ring isomorphism. -/
noncomputable def slCongr {R S : Type*} [CommRing R] [CommRing S] (f : R ≃+* S) :
    Matrix.SpecialLinearGroup (Fin 2) R ≃* Matrix.SpecialLinearGroup (Fin 2) S :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map f.toRingHom)
    (Matrix.SpecialLinearGroup.map f.symm.toRingHom)
    (by ext A i j; simp [Matrix.SpecialLinearGroup.map])
    (by ext A i j; simp [Matrix.SpecialLinearGroup.map])

theorem center_SL_eq_bot :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 6)) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hA'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    have h2 : (2 : GaloisField 2 6) = 0 := CharTwo.two_eq_zero
    have : (r - 1) * (r - 1) = 0 := by
      have e : (r - 1) * (r - 1) = r ^ 2 - 1 - 2 * (r - 1) := by ring
      rw [e, hr, h2]; ring
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hA', hr1]
  simp

/-- `PSL(2, GaloisField 2 6) ≃* SL(2, GaloisField 2 6)` (the center is trivial). -/
noncomputable def pslEquiv :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 6) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 6) :=
  (QuotientGroup.quotientMulEquivOfEq center_SL_eq_bot).trans QuotientGroup.quotientBot

/-- `PSL(2, 64) ≃* G2`. -/
noncomputable def pslToG2 : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 6) ≃* G2 :=
  (pslEquiv.trans (slCongr gfEquiv.symm)).trans toSLEquiv.symm

/-- **Proposition (`prop:hand`).** Let `G = PSL(2,64)` and let `H ≤ G` be a subgroup
isomorphic to `S₃`. Then the interval `[H, G]` in the subgroup lattice of `G` is
order-isomorphic to DeMeo's seven-element lattice `𝐋₇`. -/
theorem prop_hand (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 6)))
    (hH : Nonempty (H ≃* Equiv.Perm (Fin 3))) : Nonempty (Set.Icc H ⊤ ≃o L7) := by
  obtain ⟨e⟩ := hH
  set φ := pslToG2
  have e' : H.map φ.toMonoidHom ≃* Equiv.Perm (Fin 3) := (φ.subgroupMap H).symm.trans e
  obtain ⟨g, hg⟩ := conj_S3 _ e'
  let Ψ := φ.mapSubgroup.trans (MulAut.conj g).mapSubgroup
  have hΨH : Ψ H = H0 := by
    simp only [Ψ, OrderIso.trans_apply, MulEquiv.coe_mapSubgroup]
    exact hg
  have hΨtop : Ψ ⊤ = ⊤ := OrderIso.map_top Ψ
  exact ⟨((OrderIso.Icc Ψ H ⊤).trans
    (OrderIso.setCongr _ _ (by rw [hΨH, hΨtop]))).trans intervalIso⟩

end PSL264

end
