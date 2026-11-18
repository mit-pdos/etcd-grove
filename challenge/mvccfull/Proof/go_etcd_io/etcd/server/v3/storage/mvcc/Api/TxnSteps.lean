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
    "#Hhook" ∷ hookP γ Pw ∗
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
    "Hcres" ∷ (compactRes γ ilog ∗ writerLoan γ ∗ wrToks γ (2 ^ 63 - 4 - ilog.length) ilog) ∗
    "Hlrd" ∷ lease.lessorRdOf γ.leases ∗
    "%Hcrev" ∷ ⌜-1 ≤ crev ∧ crev < ilog.length⌝ ∗
    "#HZ" ∷ □ Z)

/-- **`isTxnRead` with its trace part `Tr`** (M4, track B, 2026-11-06: the API's transaction holds
none, `Tr := True`; the methods that use no trace, `End`, `Rev`, `FirstRev`, are stated at any
`Tr`). -/
def isTxnReadT (mw s : Loc) (γ : StoreNames) (trace : Loc) (log : Log) (rev : w64) (crev : Int)
    (Z : IProp GF) (Tr : IProp GF) : IProp GF :=
  iprop(∃ (p : PhysNames) (trw tr ti : Loc) (rt : GoInterfaceOk) (ranges : w64),
    "Hmw" ∷ mw ↦ ({
        TxnWrite' := interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #trw,
        ranges' := ranges, puts' := W64 0, deletes' := W64 0, putSize' := W64 0 } : metricsTxnWrite) ∗
    "Htrw" ∷ trw.[txnReadWrite, go!"TxnRead"] ↦
      (interface.mkOk (go.GoType.PointerType storeTxnRead.ty) #tr : GoInterface) ∗
    "#Hs" ∷ isStore s γ ∗
    "#Htr" ∷ storeTxnReadIs tr s rt trace (γ.withPhys p) log rev crev Z ∗
    "Hrd" ∷ txReader (γ.withPhys p) rt log ∗
    "Hmu" ∷ muHeld s (γ.withPhys p) crev ti ∗
    "HrevMu" ∷ sync.ownRWMutex (revMuAddr s) (revMuInv s γ) ∗
    "Hti" ∷ idxReader ti (γ.withPhys p).idx ∗
    "Htrc" ∷ Tr)

/-- **`isTxnWrite` with its trace part `Tr`** (as `isTxnReadT`). -/
def isTxnWriteT (mw s : Loc) (γ : StoreNames) (trace : Loc) (ilog : Log) (pend : List Change)
    (puts deletes putSize : w64) (crev : Int) (Z : IProp GF) (ld : Bool) (Tr : IProp GF) :
    IProp GF :=
  iprop(∃ (tw : Loc) (ranges : w64),
    "Hmw" ∷ mw ↦ ({
        TxnWrite' := interface.mkOk (go.GoType.PointerType storeTxnWrite.ty) #tw,
        ranges' := ranges, puts' := puts, deletes' := deletes, putSize' := putSize } : metricsTxnWrite) ∗
    "Htw" ∷ storeTxnWriteIs tw s γ trace ilog pend crev Z ld ∗
    "Htrc" ∷ Tr)

end defs

section wdefs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

end wdefs

end mvcc
end EtcdGrove
end Perennial
