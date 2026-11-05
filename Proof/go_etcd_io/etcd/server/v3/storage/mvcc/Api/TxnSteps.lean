/-
**The write transaction's commit steps, as its callers' ghost steps** (M4, track B, 2026-11-06;
`notes/mvcc-api-invariants.md` §3, "the slot steps' shapes"). Lean-first (no Rocq counterpart).

`End` moves the API's ghost state held by the store's locks and by the writer (`slotX`, `slotY`,
`wsSlot`), which only the API's client may move (its halves are the client's `mvccState`). So the
internal `End`s take the move as their caller's ghost step, fired where the update fires (§3),
instead of moving the slots themselves (strict M1's placeholders `slotX_step_M1`, `slotY_step_M1`,
`wsSlot_step_M1`); and the writer's check-in excludes the frozen state by the caller's resource
`G` (the API's backend share: `slotF_share_excl`), not by the placeholder `slotF_excl_M1`.

* `storeTxnWriteCoreY`, `isTxnWriteCoreY`, `isTxnEndY`: `storeTxnWriteCore`, `isTxnWriteCore`,
  `isTxnEnd` with the writer's slot any `Y` (`slotY` at the committed log, or, in the watchable
  `End` between its notification and the commit, the slot as its notify step left it:
  `storeTxnWriteCore_Y`, `isTxnWriteCore_Y`, `isTxnEnd_Y` at `Y := slotY γ ilog`).
* `endCb γ ilog pend crev Y R`: the commit's ghost step, `storeTxnWrite.End`'s. With no change, at
  the check-in, `Y` back to the writer's slot at `ilog`, giving `R`; with a change, at the bump
  (`currentRev++` under `s.revMu`, held), given the committed log's certificate: `s.revMu`'s slot
  (the whole lock's, at the transaction's compaction revision `crev`, which the lock's agrees with)
  and `Y` to both slots at `ilog ++ [pend]`, giving `R`.
* `txnEndX`, `txnEndXPost`: what `metricsTxnWrite.End` takes and gives beside `txnEndPre`/`Post`
  (nothing for a read transaction; for a write one the excluder `G` and the step).
* `wsEndCb γ ilog pend crev R`: the watchable `End`'s step: with a change, at its notification
  (under the watchable store's `s.mu`, before the watchers are sent the revision's events), given
  the sealed log: the writer's slot and the lock's (`wsSlot` at the committed log) to a lower bound
  of the API's notified log at `ilog ++ [pend]` and some `Y` with the commit's step from it (the
  lock's slot at the notified log back with `R`); with none, the commit's step.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `storeTxnWriteCore` with the writer's slot `Y`. -/
def storeTxnWriteCoreY (tw s : Loc) (γ : StoreNames) (trace : Loc) (ilog : Log) (pend : List Change)
    (chs : GoSlice) (ps : List Loc) (sealed : Bool) (crev : Int) (Z : IProp GF) (ld : Bool)
    (Y : IProp GF) : IProp GF :=
  iprop(∃ (ti : Loc) (bt : GoInterfaceOk) (Locked : Puts → IProp GF) (ntok : Nat)
    (Pw : IProp GF) (fw : val) (Dep : IProp GF),
    "Htoks" ∷ ownTokAuthDfrac γ.revs (DFrac.own (1 : Qp).half) ntok ∗
    "%Hbudget" ∷ ⌜ilog.length + ntok + 3 ≤ 2 ^ 63⌝ ∗
    "Htok" ∷ revToken γ ∗
    "Htw" ∷ tw ↦ ({
        storeTxnCommon' := {
          s' := s, tx' := GoInterface.ok bt, firstRev' := W64 0, rev' := W64 0, trace' := trace },
        tx' := GoInterface.ok bt, beginRev' := W64 ((ilog.length : Int) - 1),
        changes' := chs } : storeTxnWrite) ∗
    "Hcap" ∷ ownSliceCap Loc chs (DFrac.own 1) ∗
    "%Hps" ∷ ⌜ps.length = pend.length ∧ ps.length = sint.nat chs.len ∧ 0 ≤ sint.Z chs.len⌝ ∗
    "#Hs" ∷ isStore s γ ∗
    "#Hhook" ∷ hookOk γ Pw fw ∗
    "#Hbt" ∷ batchTxSpecG bt (bucketView γ) (storeRT γ) (storeWT γ) (storePutOk γ) (delKey γ)
      (storeW s γ) Dep (storeCmp γ) Locked Pw (hookFn γ) (storeRb γ) (kbMWv γ.kb γ.bucket) ∗
    "#HbtB" ∷ storeBt γ bt ∗
    "#Hreg" ∷ storeRegd s γ ∗
    "Hrt" ∷ storeRT γ ∗
    "Hlocked" ∷ lockedIs ld bt (bucketView γ) (storeW s γ) Pw Locked (pendPuts ilog pend) ∗
    "Hw" ∷ idxWriterB γ.idx ilog pend sealed ∗
    "Hclog" ∷ ghostVar γ.clog (1 : Qp).half ilog ∗
    "Hcur" ∷ (s.[store, go!"currentRev"] ↦{DFrac.own (1 : Qp).half}
      (W64 ((ilog.length : Int) - 1) : w64) : IProp GF) ∗
    "Hbv" ∷ bucketViewL γ txQ ilog ∗
    "Hwv" ∷ ghostVar γ.wv 1 ilog ∗
    "HY" ∷ Y ∗
    "Htko" ∷ ownToks γ.tko 1 ∗
    "#Hcert" ∷ idxCert γ.idx ilog ∗
    "%Hne" ∷ ⌜ilog ≠ []⌝ ∗
    "Hmu" ∷ muHeld s γ crev ti ∗
    "HrevMu" ∷ sync.ownRWMutex (revMuAddr s) (revMuInv s γ) ∗
    "Hti" ∷ idxReader ti γ.idx ∗
    "%Htrnn" ∷ ⌜trace ≠ null⌝ ∗
    "Hcres" ∷ (compactRes γ ilog ∗ writerLoan γ) ∗
    "Hlrd" ∷ lease.lessorRdOf γ.leases ∗
    "%Hcrev" ∷ ⌜-1 ≤ crev ∧ crev < ilog.length⌝ ∗
    "#HZ" ∷ □ Z)

/-- The core is the one at the writer's slot. -/
theorem storeTxnWriteCore_Y (tw s : Loc) (γ : StoreNames) (trace : Loc) (ilog : Log)
    (pend : List Change) (chs : GoSlice) (ps : List Loc) (sealed : Bool) (crev : Int)
    (Z : IProp GF) (ld : Bool) :
    storeTxnWriteCore (GF := GF) tw s γ trace ilog pend chs ps sealed crev Z ld =
      storeTxnWriteCoreY tw s γ trace ilog pend chs ps sealed crev Z ld (slotY γ ilog) := rfl

/-- `isTxnWriteCore` with the writer's slot `Y`. -/
def isTxnWriteCoreY (mw s : Loc) (γ : StoreNames) (trace : Loc) (ilog : Log) (pend : List Change)
    (puts deletes putSize : w64) (chs : GoSlice) (ps : List Loc) (sealed : Bool)
    (crev : Int) (Z : IProp GF) (ld : Bool) (Y : IProp GF) : IProp GF :=
  iprop(∃ (tw : Loc) (ranges : w64),
    "Hmw" ∷ mw ↦ ({
        TxnWrite' := interface.mkOk (go.GoType.PointerType storeTxnWrite.ty) #tw,
        ranges' := ranges, puts' := puts, deletes' := deletes, putSize' := putSize } : metricsTxnWrite) ∗
    "Htw" ∷ storeTxnWriteCoreY tw s γ trace ilog pend chs ps sealed crev Z ld Y ∗
    "Htrc" ∷ (∃ te : Bool, traceutil.ownTrace trace te))

theorem isTxnWriteCore_Y (mw s : Loc) (γ : StoreNames) (trace : Loc) (ilog : Log)
    (pend : List Change) (puts deletes putSize : w64) (chs : GoSlice) (ps : List Loc)
    (sealed : Bool) (crev : Int) (Z : IProp GF) (ld : Bool) :
    isTxnWriteCore (GF := GF) mw s γ trace ilog pend puts deletes putSize chs ps sealed crev Z ld =
      isTxnWriteCoreY mw s γ trace ilog pend puts deletes putSize chs ps sealed crev Z ld
        (slotY γ ilog) := rfl

/-- The writer's slot out of a transaction's core, any slot back. -/
theorem isTxnWriteCore_takeY (mw s : Loc) (γ : StoreNames) (trace : Loc) (ilog : Log)
    (pend : List Change) (puts deletes putSize : w64) (chs : GoSlice) (ps : List Loc)
    (sealed : Bool) (crev : Int) (Z : IProp GF) (ld : Bool) :
    isTxnWriteCore (GF := GF) mw s γ trace ilog pend puts deletes putSize chs ps sealed crev Z ld ⊢
      slotY γ ilog ∗ ∀ Y : IProp GF, Y -∗
        isTxnWriteCoreY mw s γ trace ilog pend puts deletes putSize chs ps sealed crev Z ld Y := by
  rw [isTxnWriteCore_Y]
  iintro H
  iunfold isTxnWriteCoreY at H
  iNamed H
  iunfold storeTxnWriteCoreY at Htw
  iNamed Htw
  iframe HY
  iintro %Y' HY'
  iunfold isTxnWriteCoreY
  iexists tw, ranges
  iframe Hmw Htrc
  iunfold storeTxnWriteCoreY
  iexists ti, bt, Locked, ntok, Pw, fw, Dep
  simp only [named]
  iframe Htoks Htok Htw Hcap Hlocked Hw Hclog Hcur Hbv Hwv HY' Htko Hmu HrevMu Hti Hrt Hcres Hlrd
  iframe #
  ipureintro; exact ⟨Hbudget, Hps, Hne, Htrnn, Hcrev⟩

/-- `isTxnEnd` with a write transaction's slot `Y`. -/
def isTxnEndY (mw s : Loc) (γ : StoreNames) (trace : Loc) (kind : TxnKind) (crev : Int)
    (Z : IProp GF) (Y : IProp GF) : IProp GF :=
  match kind with
  | .read log rev => isTxnRead mw s γ trace log rev crev Z
  | .write ilog pend puts deletes putSize =>
    iprop(∃ (chs : GoSlice) (ps : List Loc) (sealed ld : Bool),
      isTxnWriteCoreY mw s γ trace ilog pend puts deletes putSize chs ps sealed crev Z ld Y)

/-- A transaction ready to end, at the writer's slot. -/
theorem isTxnEnd_Y (mw s : Loc) (γ : StoreNames) (trace : Loc) (kind : TxnKind) (crev : Int)
    (Z : IProp GF) :
    isTxnEnd (GF := GF) mw s γ trace kind crev Z ⊢
      isTxnEndY mw s γ trace kind crev Z (match kind with
        | .read _ _ => iprop(True)
        | .write ilog _ _ _ _ => slotY γ ilog) := by
  cases kind <;> exact .rfl

/-- A write transaction ready to end, at the writer's slot. -/
theorem isTxnEnd_Y_write (mw s : Loc) (γ : StoreNames) (trace : Loc) (ilog : Log)
    (pend : List Change) (puts deletes putSize : w64) (crev : Int) (Z : IProp GF) :
    isTxnEnd (GF := GF) mw s γ trace (.write ilog pend puts deletes putSize) crev Z ⊢
      isTxnEndY mw s γ trace (.write ilog pend puts deletes putSize) crev Z (slotY γ ilog) := .rfl

/-- A read transaction ready to end, at any slot. -/
theorem isTxnEnd_Y_read (mw s : Loc) (γ : StoreNames) (trace : Loc) (log : Log) (rev : w64)
    (crev : Int) (Z Y : IProp GF) :
    isTxnEnd (GF := GF) mw s γ trace (.read log rev) crev Z ⊢
      isTxnEndY mw s γ trace (.read log rev) crev Z Y := .rfl

/-- **The commit's ghost step** (`storeTxnWrite.End`'s; see the file header). -/
def endCb (γ : StoreNames) (ilog : Log) (pend : List Change) (crev : Int) (Y R : IProp GF) :
    IProp GF :=
  if pend = [] then iprop(idxCert γ.idx ilog -∗ Y ={⊤}=∗ slotY γ ilog ∗ R)
  else iprop(idxCert γ.idx (ilog ++ [pend]) -∗ slotX γ 1 ilog crev ∗ Y ={⊤}=∗
    slotX γ 1 (ilog ++ [pend]) crev ∗ slotY γ (ilog ++ [pend]) ∗ R)

/-- The step that does nothing, with no change, at the writer's slot. -/
theorem endCb_nil (γ : StoreNames) (ilog : Log) (crev : Int) :
    ⊢ endCb (GF := GF) γ ilog [] crev (slotY γ ilog) iprop(True) := by
  unfold endCb
  simp only [↓reduceIte]
  iintro #_ HY
  imodintro; iframe HY

theorem endCb_nil_iff (γ : StoreNames) (ilog : Log) (crev : Int) (Y R : IProp GF) :
    endCb (GF := GF) γ ilog [] crev Y R ⊣⊢ iprop(idxCert γ.idx ilog -∗ Y ={⊤}=∗ slotY γ ilog ∗ R) := by
  unfold endCb; simp only [↓reduceIte]; exact .rfl

theorem endCb_cons_iff (γ : StoreNames) (ilog : Log) (pend : List Change) (h : pend ≠ [])
    (crev : Int) (Y R : IProp GF) :
    endCb (GF := GF) γ ilog pend crev Y R ⊣⊢
      iprop(idxCert γ.idx (ilog ++ [pend]) -∗ slotX γ 1 ilog crev ∗ Y ={⊤}=∗
        slotX γ 1 (ilog ++ [pend]) crev ∗ slotY γ (ilog ++ [pend]) ∗ R) := by
  unfold endCb; simp only [h, ↓reduceIte]; exact .rfl

/-- The caller's excluder, with its proof, as a resource the writer's check-in takes. -/
theorem slotF_excl_of (γ : StoreNames) (G : IProp GF) :
    slotF γ ∗ iprop(G ∗ □ (slotF γ ∗ G -∗ False)) ⊢ False := by
  iintro ⟨HF, HG, #Hx⟩
  iapply Hx; iframe HF HG

/-- A transaction's compaction revision is the one `s.revMu`'s resource holds (the two quarters of
the index's compaction revision's authority agree). -/
theorem muHeld_crevUB (s : Loc) (γ : StoreNames) (c : Int) (ti : Loc) (q : Qp) (c' : Int)
    (h : -1 ≤ c') :
    muHeld (GF := GF) s γ c ti ∗ crevUB γ.idx q c' ⊢
      muHeld s γ c ti ∗ crevUB γ.idx q c' ∗ ⌜c = c'⌝ := by
  iintro ⟨Hm, Hc⟩
  iunfold muHeld at Hm
  icases Hm with ⟨Hl, Ha, Hrest⟩
  iunfold muInvAt at Ha
  iNamed Ha
  ihave %Hcc := crevUB_agree γ.idx _ _ c c' HcM h $$ HcrevM Hc
  iframe Hc
  isplitl
  · iunfold muHeld; iframe Hl Hrest
    iunfold muInvAt; iframe HcmpM HcrevM; iframe #; ipureintro; exact HcM
  ipureintro; exact Hcc

/-- **What `metricsTxnWrite.End` takes beside `txnEndPre`**: for a write transaction, the
excluder `G` of the frozen state (given back) and the commit's step. -/
def txnEndX (γ : StoreNames) (kind : TxnKind) (crev : Int) (Y G R : IProp GF) : IProp GF :=
  match kind with
  | .read _ _ => iprop(True)
  | .write ilog pend _ _ _ =>
    iprop(G ∗ □ (slotF γ ∗ G -∗ False) ∗ endCb γ ilog pend crev Y R)

/-- What it gives back beside `txnEndPost`. -/
def txnEndXPost (kind : TxnKind) (G R : IProp GF) : IProp GF :=
  match kind with
  | .read _ _ => iprop(True)
  | .write _ _ _ _ _ => iprop(G ∗ R)

theorem txnEndX_read (γ : StoreNames) (log : Log) (rev : w64) (crev : Int) (Y G R : IProp GF) :
    ⊢ txnEndX (GF := GF) γ (.read log rev) crev Y G R := by
  unfold txnEndX; iintro; itrivial

end defs

section wdefs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The watchable `End`'s ghost step** (see the file header). -/
def wsEndCb (γ : WsNames) (ilog : Log) (pend : List Change) (crev : Int) (R : IProp GF) :
    IProp GF :=
  if pend = [] then endCb γ.st ilog [] crev (slotY γ.st ilog) R
  else iprop(idxSealed γ.st.idx (ilog ++ [pend]) -∗ slotY γ.st ilog ∗ wsSlot γ 1 ilog ={⊤}=∗
    api.nlLb γ.st.api (ilog ++ [pend]) ∗
    ∃ Y : IProp GF, Y ∗ endCb γ.st ilog pend crev Y iprop(wsSlot γ 1 (ilog ++ [pend]) ∗ R))

theorem wsEndCb_nil_iff (γ : WsNames) (ilog : Log) (crev : Int) (R : IProp GF) :
    wsEndCb (GF := GF) γ ilog [] crev R ⊣⊢ endCb γ.st ilog [] crev (slotY γ.st ilog) R := by
  unfold wsEndCb; simp only [↓reduceIte]; exact .rfl

theorem wsEndCb_cons_iff (γ : WsNames) (ilog : Log) (pend : List Change) (h : pend ≠ [])
    (crev : Int) (R : IProp GF) :
    wsEndCb (GF := GF) γ ilog pend crev R ⊣⊢
      iprop(idxSealed γ.st.idx (ilog ++ [pend]) -∗ slotY γ.st ilog ∗ wsSlot γ 1 ilog ={⊤}=∗
        api.nlLb γ.st.api (ilog ++ [pend]) ∗
        ∃ Y : IProp GF, Y ∗ endCb γ.st ilog pend crev Y iprop(wsSlot γ 1 (ilog ++ [pend]) ∗ R)) := by
  unfold wsEndCb; simp only [h, ↓reduceIte]; exact .rfl

end wdefs

end mvcc
end EtcdGrove
end Perennial
