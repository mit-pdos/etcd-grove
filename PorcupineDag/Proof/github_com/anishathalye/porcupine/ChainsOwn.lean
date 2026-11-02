/-
Lean-first (no Rocq counterpart).

# The chains in the heap (2026-11-02)

`checkSingle`'s `chains` value (`dag.go`): its clients slice (client `c`: `id = c`, `cltOps`, its
`head`, its `nDeps`), the number of operations, and the frontier slice (client indices). Its
state is one record of pure values (`ChSt`): the heads, the `nDeps`, the frontier, each
operation's `visited` flag and `firstUnk` slice. `chainsOwn ch h cs st` is the memory;
`ChainsInv h cs B st` the invariant of the search at the operations linearized `B`: the heads are
`B`'s, every visited operation's `firstUnk` holds `FUe` (`Chains.lean`), the operations at or
below a head are visited, an unfinished client's `nDeps` is `deps`, and the frontier, mapped to
the head operations (`frOf`), is the sorted candidate list of `B` (`DagTheory.CandList` for
`Before`): what makes the cursor `liftFrom` meaningful after a pop.
-/
module

public import PorcupineDag.Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.anishathalye.porcupine

open Theory

/-- The chains' state. -/
structure ChSt where
  heads : List Nat
  nDeps : List w64
  frontier : List Nat
  vis : List (List Bool)
  fu : List (List (List w64))

namespace ChSt

/-- Client `c`'s head. -/
def head (st : ChSt) (c : Nat) : Nat := st.heads.getD c 0
/-- Whether client `c`'s `k`-th operation is visited. -/
def visAt (st : ChSt) (c k : Nat) : Bool := (st.vis.getD c []).getD k false
/-- Client `c`'s `k`-th operation's `firstUnk` slice's contents. -/
def fuAt (st : ChSt) (c k : Nat) : List w64 := (st.fu.getD c []).getD k []

end ChSt

/-- Client `c`'s head operation. -/
def hdOp (cs : List (List Nat)) (st : ChSt) (c : Nat) : Nat := opAt cs c (st.head c)

/-- The frontier, as operations. -/
def frOf (cs : List (List Nat)) (st : ChSt) : List Nat := st.frontier.map (hdOp cs st)

section pure
variable [GooseExts]

/-- A client's slice of `clientOperation`s: each holds its operation of the chain `ch` (its id,
input, output, times), and is visited as `vs` says. -/
def CoOk (h : List (Op OpV)) (ch : List Nat) (vs : List Bool) (cos : List clientOperation) : Prop :=
  cos.length = ch.length ∧ ∀ (k : Nat) (co : clientOperation), cos[k]? = some co →
    ∃ (y : Nat) (o : Op OpV), ch[k]? = some y ∧ h[y]? = some o ∧ sint.Z co.id' = y ∧
      co.Op'.Input' = o.val.1 ∧ co.Op'.Output' = o.val.2 ∧ sint.Z co.Op'.Call' = o.call ∧
      sint.Z co.Op'.Return' = o.ret ∧ co.visited' = vs.getD k false

end pure

/-- The shapes of the state: one entry per client, per operation, per client again. -/
def ShapeOk (cs : List (List Nat)) (st : ChSt) : Prop :=
  st.heads.length = cs.length ∧ st.nDeps.length = cs.length ∧ st.vis.length = cs.length ∧
  st.fu.length = cs.length ∧
  ∀ c k, k < (chain cs c).length → (st.vis.getD c []).length = (chain cs c).length ∧
    (st.fu.getD c []).length = (chain cs c).length ∧ (st.fuAt c k).length = cs.length

/-- Every visited operation's `firstUnk` holds `FUe` (but at its own client, never written). -/
def FuOk (h : List (Op α)) (cs : List (List Nat)) (st : ChSt) : Prop :=
  ∀ c k, st.visAt c k = true → ∀ d, d < cs.length → d ≠ c →
    sint.Z ((st.fuAt c k).getD d 0) = FUe h cs c d k

/-- The chains' invariant at the operations linearized `B` (see the file header). -/
def ChainsInv (h : List (Op α)) (cs : List (List Nat)) (B : List Nat) (st : ChSt) : Prop :=
  ShapeOk cs st ∧ st.heads = headsOf cs B ∧ PosOk cs B st.heads ∧ HeadsOk cs st.heads ∧
  (∀ z w, w ∈ B → Before h cs z w → z ∈ B) ∧ (∀ y ∈ B, y < h.length) ∧
  FuOk h cs st ∧
  (∀ c k, k < (chain cs c).length → k ≤ st.head c → st.visAt c k = true) ∧
  (∀ c, c < cs.length → st.head c < (chain cs c).length →
    sint.Z (st.nDeps.getD c 0) = deps h cs st.heads c) ∧
  (∀ c ∈ st.frontier, c < cs.length ∧ st.head c < (chain cs c).length) ∧
  CandList h cs (Before h cs) B (frOf cs st)

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- Client `c`'s struct: its id, head and `nDeps`, its operations (`CoOk`) and their `firstUnk`
slices. -/
def clientOwn (h : List (Op OpV)) (cs : List (List Nat)) (st : ChSt) (c : Nat) (cv : client) :
    IProp GF :=
  iprop(⌜sint.Z cv.id' = c ∧ sint.Z cv.head' = st.head c ∧ cv.nDeps' = st.nDeps.getD c 0⌝ ∗
    ∃ cos : List clientOperation, cv.cltOps' ↦* cos ∗ ⌜CoOk h (chain cs c) (st.vis.getD c []) cos⌝ ∗
      [∗list] k ↦ co ∈ cos, co.firstUnk' ↦* st.fuAt c k)

/-- A `chains` value: its clients, its operation count, its frontier (with its capacity, for
`append`). -/
def chainsRepr (chV : chains) (h : List (Op OpV)) (cs : List (List Nat)) (st : ChSt) : IProp GF :=
  iprop(∃ cvs : List client, chV.clients' ↦* cvs ∗
    ⌜cvs.length = cs.length ∧ sint.Z chV.numOps' = h.length⌝ ∗
    chV.frontier' ↦* (st.frontier.map (fun (c : Nat) => (W64 (c : Int) : w64))) ∗
    ownSliceCap w64 chV.frontier' (DFrac.own 1) ∗
    [∗list] c ↦ cv ∈ cvs, clientOwn h cs st c cv)

/-- The chains at `ch`. -/
def chainsOwn (ch : Loc) (h : List (Op OpV)) (cs : List (List Nat)) (st : ChSt) : IProp GF :=
  iprop(∃ chV : chains, ch ↦ chV ∗ chainsRepr chV h cs st)

end heap

end github_com.anishathalye.porcupine

end Perennial
