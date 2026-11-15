/-
A writer's cursor moves (U6z, `notes/bbolt-proof-plan.md`, "Writer reads at a fraction"): the
vocabulary of the internal writer cursor specs (`Cursor.next_w`, `first_w`, `last_w`,
`goToFirstElementOnTheStack_w`, `keyValue_ws`), over `boltCurDef`'s writer relation (`wCurAt`,
`Model/Cursor`): what a move returns (`wEntKV`), where `next` goes (`wNextTo`, `wNextPost`), and the
registry fact the moves read node references by (`nlocCur`).
-/
module

public import Proof.go_etcd_io.bbolt.Read.WCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section wcurPure
variable [GooseExts]

/-- **The writer's facts a cursor move of the top-level bucket `n` (handle `bl`) reads under**:
`X` well-formed, `bl` its opened bucket, its registry current (`nlocCur`), its root position
`rt` (U6y's F5), and not the root bucket (U6aa: a leaf node's entries are plain, `leafShape`). -/
def wCurCtx (X : WX) (n : GoString) (bl : Loc) (rt : Nat) : Prop :=
  wOK X ∧ bktLoc X n = some bl ∧ nlocCur X ∧ (X.rootPid bl).toNat = rt ∧ bl ≠ X.rl

/-- The entries of the top-level bucket `n` of the writer, in order (`boltCur`'s `es`). -/
def wEs (X : WX) (n : GoString) : List BoltEnt := bktEnts (((wtxData X) !! n).getD ∅)

/-- **Where `next` goes from a stack**: one past its position on an entry of its leaf, its position
(the next leaf's first entry) past its leaf's end. -/
def wNextTo (v : View) (es : List BoltEnt) (pids : List Nat) (els : List elemRef) : Nat :=
  if leafIdx els < leafCnt v es pids els then stackPos v es pids els + 1 else stackPos v es pids els

/-- **`next`'s new stack** (from a `wStk` stack at `pids`, going to `t`): a path from `rt` whose leaf
page holds its bounds' entries, on an entry at `t` if there is one; else unchanged on its entry (at
the last), or at the end (`wEndAt`: over trailing empty leaves, or past the last entry). -/
def wNextPost (nl : Loc → Option (Loc × Nat)) (v : View) (es : List BoltEnt) (b : Loc) (rt : Nat)
    (ipg : List w8) (els : List elemRef) (pids : List Nat) (t : Nat) (els' : List elemRef) : Prop :=
  ∃ pids', sPathR nl v b rt els' pids' ∧ sLeafOK v ipg es pids' els' ∧
    ((t < es.length ∧ leafIdx els' < leafCnt v es pids' els' ∧ stackPos v es pids' els' = t) ∨
     (es.length ≤ t ∧ ((els' = els ∧ pids' = pids ∧ leafIdx els < leafCnt v es pids els) ∨
       wEndAt v es pids' els')))

/-- **A stack prefix** (`goToFirstElementOnTheStack`'s and `last`'s pre): `sPathR` but that its top
element may be a branch reference (a branch page at its position, its index on an entry) not yet
descended from. -/
def sPrefix (nl : Loc → Option (Loc × Nat)) (v : View) (b : Loc) (rt : Nat)
    (els : List elemRef) (pids : List Nat) : Prop :=
  els ≠ [] ∧ pids.length = els.length ∧ pids.head? = some rt ∧
  ∀ j e pid, els[j]? = some e → pids[j]? = some pid →
    (e.node' ≠ null → nl e.node' = some (b, pid)) ∧
    (e.node' = null → e.page' ≠ null ∧ (pid ≠ 0 → e.page' = pageLoc v pid)) ∧
    (j + 1 < els.length → ∃ pg, v.pages !! pid = some pg ∧ pageFlags pg = branchPageFlag ∧
      e.index'.toNat < pageCount pg ∧ pids[j + 1]? = some (branchPgid pg e.index'.toNat)) ∧
    (j + 1 = els.length → pid = 0 ∨ ∃ pg, v.pages !! pid = some pg ∧
      (pageFlags pg = leafPageFlag ∨
        (pageFlags pg = branchPageFlag ∧ e.index'.toNat < pageCount pg)))

/-- Every index of the stack is the first. -/
def sAllFirst (els : List elemRef) : Prop := ∀ x ∈ els, x.index' = W64 0

/-- **The stack's top is at its last index** (`Last`'s and `last`'s): a branch page's last entry,
or the leaf's last (`-1` in an empty leaf). -/
def sTopLast (v : View) (es : List BoltEnt) (pids : List Nat) (els : List elemRef) : Prop :=
  ∀ e pid, els.getLast? = some e → pids.getLast? = some pid →
    (∃ pg, v.pages !! pid = some pg ∧ pageFlags pg = branchPageFlag ∧
      e.index'.toNat + 1 = pageCount pg) ∨
    ((pid = 0 ∨ ∃ pg, v.pages !! pid = some pg ∧ pageFlags pg = leafPageFlag) ∧
      e.index' = W64 ((leafCnt v es pids els : Int) - 1))

/-- **Every entry after the stack's leaf is in it** (`Last`'s loop, U6y's F4: the leaves after the
stack's are empty): the entries below the leaf's lower bound and the leaf's are all of `es`. -/
def sTailEmpty (v : View) (es : List BoltEnt) (pids : List Nat) (els : List elemRef) : Prop :=
  open Classical in
  (es.filter fun e => decide (¬ keyGe (pathBnd v pids els).1 e.1)).length +
    leafCnt v es pids els = es.length

/-- **`Last`'s loop invariant** (U6y's F4): a path whose leaf page holds its bounds' entries, every
entry after its leaf in it, its leaf empty (at `0` or `-1`) or at its last entry. -/
def wLastInv (nl : Loc → Option (Loc × Nat)) (v : View) (es : List BoltEnt) (b : Loc) (rt : Nat)
    (ipg : List w8) (els : List elemRef) (pids : List Nat) : Prop :=
  sPathR nl v b rt els pids ∧ sLeafOK v ipg es pids els ∧ sTailEmpty v es pids els ∧
  ∃ e, els.getLast? = some e ∧
    ((leafCnt v es pids els = 0 ∧ (e.index' = W64 0 ∨ e.index' = W64 (-1))) ∨
     (0 < leafCnt v es pids els ∧ e.index'.toNat + 1 = leafCnt v es pids els))

open Classical in
private theorem filter_disj_le (es : List BoltEnt) (f g : BoltEnt → Bool)
    (h : ∀ e ∈ es, ¬ (f e = true ∧ g e = true)) :
    (es.filter f).length + (es.filter g).length ≤ es.length := by
  induction es with
  | nil => simp
  | cons a t ih =>
    have ht := ih (fun e he => h e (List.mem_cons_of_mem _ he))
    have ha := h a (List.mem_cons_self ..)
    simp only [List.filter_cons, List.length_cons]
    split <;> split <;> simp_all <;> omega

open Classical in
/-- **A stack on an entry of its leaf is before the end**: its position is below `es.length` (the
entries below its leaf's lower bound and its leaf's are disjoint). -/
theorem stackPos_lt (v : View) (es : List BoltEnt) (pids : List Nat) (els : List elemRef)
    (h : leafIdx els < leafCnt v es pids els) : stackPos v es pids els < es.length := by
  unfold stackPos
  unfold leafCnt entsIn at h
  have := filter_disj_le es (fun e => decide (¬ keyGe (pathBnd v pids els).1 e.1))
    (fun e => decide (keyIn (pathBnd v pids els).1 (pathBnd v pids els).2 e.1))
    (by intro e _ ⟨h1, h2⟩; simp only [decide_eq_true_eq] at h1 h2; exact h1 h2.1)
  omega

end wcurPure

section wcurIProp
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A writer cursor move's result at entry `i` of `es`**: the entry's key (a non-nil slice) and
value, persistent bytes or bytes of the view `v` (what `txBytes` holds), its flags plain; nil, nil,
`0` past the end. -/
def wEntKV (v : View) (es : List BoltEnt) (i : Nat) (k vl : GoSlice) (fl : w32) : IProp GF :=
  match es[i]? with
  | some e => iprop(⌜k ≠ slice.nil ∧ ¬ isBktFlag fl⌝ ∗ (k ↦*□ e.1 ∨ ⌜inViewAt v k e.1⌝) ∗
      (vl ↦*□ e.2 ∨ ⌜inViewAt v vl e.2⌝))
  | none => iprop(⌜k = slice.nil ∧ vl = slice.nil ∧ fl = W32 0⌝)

instance wEntKV_persistent (v : View) (es : List BoltEnt) (i : Nat) (k vl : GoSlice) (fl : w32) :
    Persistent (wEntKV (GF := GF) v es i k vl fl) := by
  unfold wEntKV; split <;> infer_instance

/-- A writer cursor's stack's persistent part: its node references' registry fragments and its
inline root page's bytes. -/
def wStkOwn (r : TxReg) (nl : Loc → Option (Loc × Nat)) (v : View) (rt : Nat) (ipg : List w8)
    (els : List elemRef) : IProp GF :=
  iprop(([∗list] e ∈ els, nodeLoc r nl e) ∗ wInlOwn v rt ipg els)

instance wStkOwn_persistent (r : TxReg) (nl : Loc → Option (Loc × Nat)) (v : View) (rt : Nat)
    (ipg : List w8) (els : List elemRef) : Persistent (wStkOwn (GF := GF) r nl v rt ipg els) := by
  unfold wStkOwn
  have : ∀ e, Persistent (nodeLoc (GF := GF) r nl e) := fun e => by
    unfold nodeLoc; split <;> infer_instance
  infer_instance

end wcurIProp

end bbolt
end EtcdGrove
end Perennial
