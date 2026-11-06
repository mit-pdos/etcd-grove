/-
**The watchable write transaction's steps, at the writer slot's compaction revision** (M4, track B,
2026-11-06; `notes/mvcc-api-invariants.md` §3). Lean-first (no Rocq counterpart).

The watchable `End`'s caller's step (`wsEndCbY`) is `TxnSteps`' `wsEndCb` with the writer's slot at
the transaction's compaction revision (`slotYc γ L c`: `slotY` with its compaction revision named,
the transaction's, `muHeld_wcr`), so that the API's step can tell the state it fires at is the one
the transaction began at (its compaction revision is the slot's). And the watchable transaction
with its trace part a parameter (`isWatchTxnWriteT`, as `isTxnWriteT`: the API's transaction holds
none), at a watchable store's names with the inner store's physical names replaced
(`WsNames.withPhys`: a store's write transaction is at its current physical names).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.TxnSteps
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.WriteCtx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-- A watchable store's names with its inner store's physical names `p`. -/
def WsNames.withPhys (γ : WsNames) (p : PhysNames) : WsNames := { γ with st := γ.st.withPhys p }

@[simp] theorem WsNames.withPhys_st (γ : WsNames) (p : PhysNames) :
    (γ.withPhys p).st = γ.st.withPhys p := rfl

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The writer's slot at the compaction revision `c`** (`slotY` with it named). -/
def slotYc (γ : StoreNames) (L : Log) (c : Int) : IProp GF :=
  iprop(api.absPart γ.api (1 : Qp).half.half L c ∗ api.pndPart γ.api (pndW γ) none ∗
    rcvW γ (1 : Qp).half c ∗ api.wcrPart γ.api (1 : Qp).half c)

theorem slotYc_slotY (γ : StoreNames) (L : Log) (c : Int) : slotYc (GF := GF) γ L c ⊢ slotY γ L := by
  iintro H
  iunfold slotYc at H
  icases H with ⟨Ha, Hp, Hr, Hw⟩
  iunfold slotY
  iexists c
  iframe Ha Hp Hr Hw

/-- **The writer's slot out of a transaction's core, at the transaction's compaction revision**
(the slot's half of `wcr` agrees with `s.mu`'s, the transaction's `muHeld`); any slot back. -/
theorem storeTxnWriteCore_takeYc (tw s : Loc) (γ : StoreNames) (trace : Loc) (ilog : Log)
    (pend : List Change) (chs : GoSlice) (ps : List Loc) (sealed : Bool) (crev : Int)
    (Z : IProp GF) (ld : Bool) :
    storeTxnWriteCore (GF := GF) tw s γ trace ilog pend chs ps sealed crev Z ld ⊢
      slotYc γ ilog crev ∗ ∀ Y : IProp GF, Y -∗
        storeTxnWriteCoreY tw s γ trace ilog pend chs ps sealed crev Z ld Y := by
  rw [storeTxnWriteCore_Y]
  iintro H
  iunfold storeTxnWriteCoreY at H
  iNamed H
  iunfold slotY at HY
  icases HY with ⟨%cy, HYa, HYp, HYr, HYw⟩
  icases muHeld_wcr s γ crev ti _ cy $$ [$Hmu $HYw] with ⟨Hmu, HYw, %Hcy⟩
  subst Hcy
  isplitl [HYa HYp HYr HYw]
  · iunfold slotYc; iframe HYa HYp HYr HYw
  iintro %Y' HY'
  iunfold storeTxnWriteCoreY
  iexists ti, bt, Locked, ntok, Pw, fw, Dep
  simp only [named]
  iframe Htoks Htok Htw Hcap Hlocked Hw Hclog Hcur Hbv Hwv HY' Htko Hmu HrevMu Hti Hrt Hcres Hlrd
  iframe #
  ipureintro; exact ⟨Hbudget, Hps, Hne, Htrnn, Hcrev⟩

/-- A write transaction leaves room for its revision (its token is counted by the budget). -/
theorem storeTxnWriteCore_room (tw s : Loc) (γ : StoreNames) (trace : Loc) (ilog : Log)
    (pend : List Change) (chs : GoSlice) (ps : List Loc) (b : Bool) (crev : Int) (Z : IProp GF)
    (ld : Bool) :
    storeTxnWriteCore (GF := GF) tw s γ trace ilog pend chs ps b crev Z ld ⊢
      storeTxnWriteCore tw s γ trace ilog pend chs ps b crev Z ld ∗ ⌜ilog.length + 4 ≤ 2 ^ 63⌝ := by
  rw [storeTxnWriteCore_Y]
  iintro H
  iunfold storeTxnWriteCoreY at H
  iNamed H
  unfold revToken
  icombine Htoks Htok gives %Hle
  isplitl
  · iunfold storeTxnWriteCoreY
    iexists ti, bt, Locked, ntok, Pw, fw, Dep
    simp only [named]
    unfold revToken
    iframe Htoks Htok Htw Hcap Hlocked Hw Hclog Hcur Hbv Hwv HY Htko Hmu HrevMu Hti Hrt Hcres Hlrd
    iframe #
    ipureintro; exact ⟨Hbudget, Hps, Hne, Htrnn, Hcrev⟩
  ipureintro; omega

end defs

section wdefs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The watchable `End`'s ghost step, at the writer slot's compaction revision** (`wsEndCb` with
`slotYc γ.st ilog crev` for `slotY γ.st ilog`): with a change, at its notification under its `s.mu`
(given the sealed log), the writer's slot and the lock's to the API's `nlLb (ilog ++ [pend])` and
some `Y` with the commit's step from it; with none, the commit's step. -/
def wsEndCbY (γ : WsNames) (ilog : Log) (pend : List Change) (crev : Int) (R : IProp GF) :
    IProp GF :=
  if pend = [] then endCb γ.st ilog [] crev (slotYc γ.st ilog crev) R
  else iprop(idxSealed γ.st.idx (ilog ++ [pend]) -∗ slotYc γ.st ilog crev ∗ wsSlot γ 1 ilog ={⊤}=∗
    api.nlLb γ.st.api (ilog ++ [pend]) ∗
    ∃ Y : IProp GF, Y ∗ endCb γ.st ilog pend crev Y iprop(wsSlot γ 1 (ilog ++ [pend]) ∗ R))

theorem wsEndCbY_nil_iff (γ : WsNames) (ilog : Log) (crev : Int) (R : IProp GF) :
    wsEndCbY (GF := GF) γ ilog [] crev R ⊣⊢ endCb γ.st ilog [] crev (slotYc γ.st ilog crev) R := by
  unfold wsEndCbY; simp only [↓reduceIte]; exact .rfl

theorem wsEndCbY_cons_iff (γ : WsNames) (ilog : Log) (pend : List Change) (h : pend ≠ [])
    (crev : Int) (R : IProp GF) :
    wsEndCbY (GF := GF) γ ilog pend crev R ⊣⊢
      iprop(idxSealed γ.st.idx (ilog ++ [pend]) -∗ slotYc γ.st ilog crev ∗ wsSlot γ 1 ilog ={⊤}=∗
        api.nlLb γ.st.api (ilog ++ [pend]) ∗
        ∃ Y : IProp GF, Y ∗ endCb γ.st ilog pend crev Y iprop(wsSlot γ 1 (ilog ++ [pend]) ∗ R)) := by
  unfold wsEndCbY; simp only [h, ↓reduceIte]; exact .rfl

/-- **`isWatchTxnWrite` with its trace part `Tr`** (as `isTxnWriteT`; the API's transaction holds
none, `Tr := True`). -/
def isWatchTxnWriteT (tw s st : Loc) (γ : WsNames) (trace : Loc) (ilog : Log) (pend : List Change)
    (puts deletes putSize : w64) (crev : Int) (ld : Bool) (Tr : IProp GF) : IProp GF :=
  iprop(∃ mw : Loc,
    "#Htw" ∷ tw ↦□ ({ TxnWrite' := interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw,
                      s' := s } : watchableStoreTxnWrite) ∗
    "#Hws" ∷ isWatchableStore s st γ ∗
    "Htx" ∷ isTxnWriteT mw st γ.st trace ilog pend puts deletes putSize crev iprop(True) ld Tr ∗
    "#Hcert" ∷ idxCert γ.st.idx ilog)

theorem isWatchTxnWrite_T (tw s st : Loc) (γ : WsNames) (trace : Loc) (ilog : Log)
    (pend : List Change) (puts deletes putSize : w64) (crev : Int) (ld : Bool) :
    isWatchTxnWrite (GF := GF) tw s st γ trace ilog pend puts deletes putSize crev ld =
      isWatchTxnWriteT tw s st γ trace ilog pend puts deletes putSize crev ld
        iprop(∃ te : Bool, traceutil.ownTrace trace te) := rfl

/-- The trace part, out; any back. -/
theorem isWatchTxnWriteT_tr (tw s st : Loc) (γ : WsNames) (trace : Loc) (ilog : Log)
    (pend : List Change) (puts deletes putSize : w64) (crev : Int) (ld : Bool) (Tr : IProp GF) :
    isWatchTxnWriteT (GF := GF) tw s st γ trace ilog pend puts deletes putSize crev ld Tr ⊢
      Tr ∗ ∀ Tr' : IProp GF, Tr' -∗
        isWatchTxnWriteT tw s st γ trace ilog pend puts deletes putSize crev ld Tr' := by
  iintro H
  iunfold isWatchTxnWriteT at H
  iNamed H
  icases isTxnWriteT_tr _ _ _ _ _ _ _ _ _ _ _ _ _ $$ Htx with ⟨Htr, Htx⟩
  iframe Htr
  iintro %Tr' Htr'
  iunfold isWatchTxnWriteT
  iexists mw
  simp only [named]
  ihave Htx := Htx $$ %Tr' Htr'
  iframe Htx
  iframe #

/-- A watchable store reads only its inner store's logical names. -/
theorem isWatchableStore_withPhys (s st : Loc) (γ : WsNames) (p : PhysNames) :
    isWatchableStore (GF := GF) s st (γ.withPhys p) = isWatchableStore s st γ := rfl

end wdefs

end mvcc
end EtcdGrove
end Perennial
