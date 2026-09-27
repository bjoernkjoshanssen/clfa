module

public import J2Fast.Perm
public import J2Fast.Data
public import Std.Data.HashMap
public import Std.Data.HashSet

/-!
# The certificate checks for the interval `[D₂₀, J₂]` (no Mathlib)

All the computations used by `native_decide` in `RequestProject.J2.Interval`, written against
the Lean core library only, so that this module can be compiled to native code. The proofs
that these checks imply the lattice isomorphism are in `RequestProject.J2.Interval`.
-/

@[expose] public section

namespace J2Cert

/-! ### The lattice `#61` (data only) -/

/-- The eight elements of the lattice `#61`. -/
inductive L61 where
  | bot | a | b | c | d | e | f | top
deriving DecidableEq, Repr, Inhabited

namespace L61

/-- The order of `#61`: `0` is least, `1` is greatest, and in addition
`a < e`, `a < f`, `b < d`, `b < e`, `c < d`. -/
def leB : L61 → L61 → Bool
  | bot, _ => true
  | _, top => true
  | a, a => true
  | a, e => true
  | a, f => true
  | b, b => true
  | b, d => true
  | b, e => true
  | c, c => true
  | c, d => true
  | d, d => true
  | e, e => true
  | f, f => true
  | _, _ => false

/-- All elements, listed. -/
def all : List L61 := [bot, a, b, c, d, e, f, top]

theorem mem_all (x : L61) : x ∈ all := by
  cases x <;> simp [all]

/-- Join in `#61` (the least common upper bound, found by search). -/
def supL (x y : L61) : L61 :=
  ((all.filter fun z => leB x z && leB y z).find? fun z =>
    all.all fun w => !(leB x w && leB y w) || leB z w).getD top

/-- Meet in `#61` (the greatest common lower bound, found by search). -/
def infL (x y : L61) : L61 :=
  ((all.filter fun z => leB z x && leB z y).find? fun z =>
    all.all fun w => !(leB w x && leB w y) || leB w z).getD bot

end L61

/-! ### Explicit elements -/

/-- ATLAS generator `a` of `J₂`. -/
def pA : P100 := P100.ofList genAData
/-- ATLAS generator `b` of `J₂`. -/
def pB : P100 := P100.ofList genBData
/-- First generator of `D₂₀`. -/
def h1 : P100 := P100.ofList hgen1Data
/-- Second generator of `D₂₀`. -/
def h2 : P100 := P100.ofList hgen2Data
/-- Generator (with `D₂₀`) of the overgroup `a`. -/
def qa : P100 := P100.ofList xaData
/-- Generator (with `D₂₀`) of the overgroup `b`. -/
def qb : P100 := P100.ofList xbData
/-- Generator (with `D₂₀`) of the overgroup `c`. -/
def qc : P100 := P100.ofList xcData
/-- Generator (with `D₂₀`) of the overgroup `f`. -/
def qf : P100 := P100.ofList xfData

/-! ### Words -/

/-- The letter `k` (`k = ±1, ±2, …`) over a list of generators. -/
def letterOf (gens : List P100) (k : Int) : P100 :=
  if 0 < k then gens.getD (k.toNat - 1) 1 else (gens.getD ((-k).toNat - 1) 1)⁻¹

/-- Evaluate a word, read left to right with the convention (used by GAP) that the leftmost
letter acts first; so `[k₁, …, kₙ]` evaluates to `letter kₙ * ⋯ * letter k₁`. -/
def evalW (gens : List P100) (w : List Int) : P100 :=
  w.foldl (fun acc k => letterOf gens k * acc) 1

/-- The elements whose membership in `J₂` is certified by words in `a, b`. -/
def wordTargets : List P100 := [h1, h2, qa, qb, qc, qf]

/-- Check of the words in `a, b`. -/
def wordsB : Bool :=
  (List.zip wordsInAB wordTargets).all (fun p => evalW [pA, pB] p.1 == p.2) &&
    wordsInAB.length == 6

/-! ### The eight subgroups -/

/-- Extra generators (besides those of `D₂₀`) of the subgroup indexed by `i`. -/
def gensOf : L61 → List P100
  | .bot => []
  | .a => [qa]
  | .b => [qb]
  | .c => [qc]
  | .d => [qb, qc]
  | .e => [qa, qb]
  | .f => [qf]
  | .top => [pA, pB]

/-- All generators of the subgroup indexed by `i`. -/
def allGens (i : L61) : List P100 := h1 :: h2 :: gensOf i

/-- Remove duplicates using a hash set. -/
def dedupH (l : List P100) : List P100 :=
  (l.foldl (fun (p : List P100 × Std.HashSet P100) x =>
    if p.2.contains x then p else (x :: p.1, p.2.insert x)) ([], {})).1

/-- One step of a breadth-first closure computation. -/
def genStep (S : List P100) (l : List P100) : List P100 :=
  dedupH (l ++ l.flatMap fun x => S.map (x * ·))

/-- Iterated closure computation (stops once the list no longer grows). -/
def genList (S : List P100) : Nat → List P100 → List P100
  | 0, l => l
  | n + 1, l => let l' := genStep S l; if l'.length = l.length then l else genList S n l'

/-- The elements of the finite subgroups (computed once each). -/
def lstBot : List P100 := genList (allGens .bot) 40 [1]
/-- Elements of the subgroup `a`. -/
def lstA : List P100 := genList (allGens .a) 40 [1]
/-- Elements of the subgroup `b`. -/
def lstB : List P100 := genList (allGens .b) 40 [1]
/-- Elements of the subgroup `c`. -/
def lstC : List P100 := genList (allGens .c) 40 [1]
/-- Elements of the subgroup `d`. -/
def lstD : List P100 := genList (allGens .d) 40 [1]
/-- Elements of the subgroup `e`. -/
def lstE : List P100 := genList (allGens .e) 40 [1]
/-- Elements of the subgroup `f`. -/
def lstF : List P100 := genList (allGens .f) 40 [1]

/-- The elements of the finite subgroups (empty for `top`). -/
def lst (i : L61) : List P100 :=
  match i with
  | .bot => lstBot
  | .a => lstA
  | .b => lstB
  | .c => lstC
  | .d => lstD
  | .e => lstE
  | .f => lstF
  | .top => []

/-- Hash sets of the finite subgroups (computed once). -/
def setBot : Std.HashSet P100 := Std.HashSet.ofList lstBot
/-- Hash set of `a`. -/
def setA : Std.HashSet P100 := Std.HashSet.ofList lstA
/-- Hash set of `b`. -/
def setB : Std.HashSet P100 := Std.HashSet.ofList lstB
/-- Hash set of `c`. -/
def setC : Std.HashSet P100 := Std.HashSet.ofList lstC
/-- Hash set of `d`. -/
def setD : Std.HashSet P100 := Std.HashSet.ofList lstD
/-- Hash set of `e`. -/
def setE : Std.HashSet P100 := Std.HashSet.ofList lstE
/-- Hash set of `f`. -/
def setF : Std.HashSet P100 := Std.HashSet.ofList lstF

/-- Fast membership test for the lists `lst i`. -/
def memB (i : L61) (x : P100) : Bool :=
  match i with
  | .bot => setBot.contains x
  | .a => setA.contains x
  | .b => setB.contains x
  | .c => setC.contains x
  | .d => setD.contains x
  | .e => setE.contains x
  | .f => setF.contains x
  | .top => false

/-- Completeness check: `lst i` contains `1` and is closed under right multiplication by the
generators and their inverses. -/
def closedB (i : L61) : Bool :=
  memB i 1 && (lst i).all fun x => (allGens i).all fun g => memB i (x * g) && memB i (x * g⁻¹)

/-- `closedB` for all finite subgroups. -/
def closedAllB : Bool := L61.all.all fun i => i == .top || closedB i

/-! ### Double coset representatives -/

/-- A double coset representative with its certificate. -/
structure Rep where
  idx : L61
  r : P100
  words : List (List Int)

instance : Inhabited Rep := ⟨⟨.bot, 1, []⟩⟩

/-- Decoding of subgroup indices. -/
def ofIdx : Nat → L61
  | 0 => .bot
  | 1 => .a
  | 2 => .b
  | 3 => .c
  | 4 => .d
  | 5 => .e
  | 6 => .f
  | _ => .top

/-- Parse one entry `idx;img;w₁|w₂|…`. -/
def parseRep (s : String) : Rep :=
  match s.splitOn ";" with
  | [c, img, ws] =>
    { idx := ofIdx c.toNat!
      r := P100.ofList ((img.splitOn ",").map String.toNat!)
      words := ((ws.splitOn "|").filter (· ≠ "")).map fun w =>
        ((w.splitOn ",").filter (· ≠ "")).map String.toInt! }
  | _ => default

/-- The double coset representatives. -/
def reps : Array Rep := ((repData.flatMap (·.splitOn "/")).map parseRep).toArray

/-- Check the certificate of one representative: `r` lies in `T idx`, and every generator of
`T idx` is given by a word in `h1, h2, r`. -/
def repOK (rp : Rep) : Bool :=
  (rp.idx == .top || memB rp.idx rp.r) &&
    (gensOf rp.idx).all fun t => rp.words.any fun w => evalW [h1, h2, rp.r] w == t

/-- All representatives pass `repOK`. -/
def repsB : Bool := reps.all repOK

/-! ### Locating elements in double cosets -/

/-- The elements of `H`, as an array. -/
def Hl : Array P100 := lstBot.toArray

/-- Hash of an element, used as a key. -/
def key (x : P100) : UInt64 := hash x

/-- Table from (hashes of) elements `h * r * h'` to the indices of `h`, `r`, `h'`. -/
def dmap : Std.HashMap UInt64 (Nat × Nat × Nat) := Id.run do
  let mut m : Std.HashMap UInt64 (Nat × Nat × Nat) := {}
  for k in [0:reps.size] do
    let r := reps[k]!.r
    for j in [0:Hl.size] do
      let rj := r * Hl[j]!
      for i in [0:Hl.size] do
        m := m.insert (key (Hl[i]! * rj)) (i, k, j)
  return m

/-- Locate `g` in a double coset: returns indices `(i, k, j)` with `g = Hl[i] * r_k * Hl[j]`,
all indices checked to be in range and the equation checked. -/
def locate (g : P100) : Option (Nat × Nat × Nat) :=
  match dmap.get? (key g) with
  | some (i, k, j) =>
    if h : i < Hl.size ∧ k < reps.size ∧ j < Hl.size then
      if g = Hl[i] * reps[k].r * Hl[j] then some (i, k, j) else none
    else none
  | none => none

/-- Boolean: `g` has been located. -/
def checkS (g : P100) : Bool := (locate g).isSome

/-- The subgroup index attached to `g` by the table. -/
def idxOf (g : P100) : L61 :=
  match locate g with
  | some (_, k, _) => (reps.getD k default).idx
  | none => .top

/-- The generators of `J₂` and their inverses. -/
def genChecks : List P100 := [pA, pA⁻¹, pB, pB⁻¹]

/-- Closure of the union of double cosets under right multiplication by the generators. -/
def sClosedB : Bool :=
  checkS 1 && reps.all fun rp => lstBot.all fun h => genChecks.all fun t => checkS (rp.r * h * t)

/-! ### Order relations and joins -/

/-- Membership test for `T j`, valid for elements of `J₂`. -/
def memT (j : L61) (x : P100) : Bool := j == .top || memB j x

/-- `T i ≤ T j` whenever `i ≤ j`. -/
def leAllB : Bool :=
  L61.all.all fun i => L61.all.all fun j => !L61.leB i j || (allGens i).all (memT j)

/-- `T i ≰ T j` whenever `i ≰ j`. -/
def nleAllB : Bool :=
  L61.all.all fun i => L61.all.all fun j => L61.leB i j ||
    (if i = .top then [pA, pB] else lst i).any fun x => !memB j x

/-- Joins of incomparable elements. -/
def joinAllB : Bool :=
  L61.all.all fun i => L61.all.all fun j => L61.leB i j || L61.leB j i ||
    (lst i).any fun x => (lst j).any fun y => checkS (x * y) && idxOf (x * y) == L61.supL i j

end J2Cert

end
