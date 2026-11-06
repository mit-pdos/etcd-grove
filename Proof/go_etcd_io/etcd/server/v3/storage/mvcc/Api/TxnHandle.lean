/-
**The API's transaction, over the internal one** (M4, track B, 2026-11-06; `notes/mvcc-api-invariants.md`
§2, `mvccTxn`). Lean-first (no Rocq counterpart). `Api.lean` imports it non-publicly and defines its
sealed `mvccTxn` as `mvccTxnI`.

A transaction of the API is the internal transaction (`isTxnReadT`, `isTxnWriteT`) **without its
trace** (`Tr := True`: `KV.Read`/`Write` give the trace back to the caller, which lends it to `Range`
and `Put`), at the state it began at (`σ.log`, `σ.crev`; nothing pending, reachable), with the
thread token's way back (`storeReaderC s γ ={⊤}=∗ threadTok`: the readers' pool's loan, whatever the
pool is; `End` gives the reader back through it), as an interface value of one of three types:
* a read transaction is `*metricsTxnWrite` (`store.Read`'s), or `NewReadOnlyTxnWrite`'s
  `*txnReadWrite` around a read transaction, to any depth (`roWrap n t mw`: the wrappers' chain down
  to the internal transaction `mw`; `NewReadOnlyTxnWrite` takes any read transaction);
* a write transaction is at the store's current physical names `p`, with the certificate map's free
  entry (`certFree`, `End`'s `certOkNext`): a store without watchers' `*metricsTxnWrite`, or a
  watchable store's `*watchableStoreTxnWrite` around it (`wsWrap`: the wrapper and the sole writer's
  certificate, tokens and notified-log half, `isWatchTxnWriteT`'s rest, at the watchable store's
  names with the current physical names, `WsNames.withPhys`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.WsTxnSteps
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiState

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The thread token's way back, from the reader the transaction holds. -/
def tokBack (s : Loc) (γ : StoreNames) : IProp GF := iprop(storeReaderC s γ ={⊤}=∗ threadTok)

/-- **The read-only wrappers' chain**, `n` deep, from `t` down to the read transaction `mw`. -/
def roWrap : Nat → GoInterface → Loc → IProp GF
  | 0, t, mw => iprop(⌜t = interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw⌝)
  | n + 1, t, mw => iprop(∃ (trw : Loc) (ty : go.GoType) (v : val),
      ⌜t = interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #trw⌝ ∗
      trw.[txnReadWrite, go!"TxnRead"] ↦ (interface.mkOk ty v : GoInterface) ∗
      roWrap n (interface.mkOk ty v) mw)

/-- **A watchable store's wrapper of the write transaction `mw`** (`isWatchTxnWriteT`'s rest). -/
def wsWrap (tw sw s : Loc) (γw : WsNames) (mw : Loc) (ilog : Log) : IProp GF :=
  iprop(tw ↦□ ({ TxnWrite' := interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw,
                 s' := sw } : watchableStoreTxnWrite) ∗
    isWatchableStore sw s γw ∗ idxCert γw.st.idx ilog ∗ ownToks γw.st.revs (wBudget ilog - 1) ∗
    monoListAuthOwn γw.wlog (1 : Qp).half ilog)

/-- **The write transaction's interface value**: `*metricsTxnWrite` of a store without watchers, or a
watchable store's wrapper (at the names `γ`, the current ones). -/
def wrWrap (t : GoInterface) (γ : StoreNames) (s mw : Loc) (ilog : Log) : IProp GF :=
  iprop(⌜t = interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw ∧ γ.watchQ = false⌝ ∨
    ∃ (tw sw : Loc) (γw : WsNames),
      ⌜t = interface.mkOk (go.GoType.PointerType watchableStoreTxnWrite.ty) #tw ∧ γw.st = γ⌝ ∗
      wsWrap tw sw s γw mw ilog)

/-- **The API's transaction** (see the header). -/
def mvccTxnI (t : GoInterface) (γ : StoreNames) (trace : Loc) (k : MTxn) : IProp GF :=
  match k with
  | .read σ => iprop(∃ (mw s : Loc) (n : Nat), ⌜MvccReachable σ⌝ ∗
      isTxnReadT mw s γ trace σ.log (W64 ((σ.log.length : Int) - 1)) σ.crev iprop(True) iprop(True) ∗
      tokBack s γ ∗ roWrap n t mw)
  | .write σ pend => iprop(∃ (mw s : Loc) (p : PhysNames) (puts deletes putSize : w64),
      ⌜σ.pending = none ∧ MvccReachable σ⌝ ∗
      isTxnWriteT mw s (γ.withPhys p) trace σ.log pend puts deletes putSize σ.crev iprop(True) false
        iprop(True) ∗
      tokBack s (γ.withPhys p) ∗ certFree (γ.withPhys p) ∗ wrWrap t (γ.withPhys p) s mw σ.log)

/-- The watchable transaction, from its wrapper and the inner one. -/
theorem wsWrap_join (tw sw s : Loc) (γw : WsNames) (mw : Loc) (trace : Loc) (ilog : Log)
    (pend : List Change) (puts deletes putSize : w64) (crev : Int) (ld : Bool) (Tr : IProp GF) :
    wsWrap (GF := GF) tw sw s γw mw ilog ∗
      isTxnWriteT mw s γw.st trace ilog pend puts deletes putSize crev iprop(True) ld Tr ⊢
      isWatchTxnWriteT tw sw s γw trace ilog pend puts deletes putSize crev ld Tr := by
  iintro ⟨H, Htx⟩
  iunfold wsWrap at H
  icases H with ⟨#Htw, #Hws, #Hcert, Htoks, Hwlog⟩
  iunfold isWatchTxnWriteT
  iexists mw
  simp only [named]
  iframe Htw Hws Htx Hcert Htoks Hwlog

/-- The watchable transaction, split into its wrapper and the inner one. -/
theorem wsWrap_split (tw sw s : Loc) (γw : WsNames) (trace : Loc) (ilog : Log)
    (pend : List Change) (puts deletes putSize : w64) (crev : Int) (ld : Bool) (Tr : IProp GF) :
    isWatchTxnWriteT (GF := GF) tw sw s γw trace ilog pend puts deletes putSize crev ld Tr ⊢
      ∃ mw : Loc, wsWrap tw sw s γw mw ilog ∗
        isTxnWriteT mw s γw.st trace ilog pend puts deletes putSize crev iprop(True) ld Tr := by
  iintro H
  iunfold isWatchTxnWriteT at H
  iNamed H
  iexists mw
  iframe Htx
  iunfold wsWrap
  iframe Htw Hws Hcert Htoks Hwlog

/-! ### The interface values' types -/

theorem ty_PM_ne_PR : go.GoType.PointerType metricsTxnWrite.ty ≠ go.GoType.PointerType txnReadWrite.ty := by
  simp [metricsTxnWrite.ty, txnReadWrite.ty]

theorem ty_PM_ne_PT :
    go.GoType.PointerType metricsTxnWrite.ty ≠ go.GoType.PointerType watchableStoreTxnWrite.ty := by
  simp [metricsTxnWrite.ty, watchableStoreTxnWrite.ty]

theorem ty_PR_ne_PT :
    go.GoType.PointerType txnReadWrite.ty ≠ go.GoType.PointerType watchableStoreTxnWrite.ty := by
  simp [txnReadWrite.ty, watchableStoreTxnWrite.ty]

/-- A chain at `*metricsTxnWrite` is the transaction itself. -/
theorem roWrap_pm (n : Nat) (t mw : Loc) :
    roWrap (GF := GF) n (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #t) mw ⊢
      ⌜t = mw ∧ n = 0⌝ := by
  cases n with
  | zero =>
    simp only [roWrap]
    iintro %h
    ipureintro; exact ⟨mkOk_loc_inj _ h, by simp⟩
  | succ n =>
    simp only [roWrap]
    iintro ⟨%trw, %ty, %v, %h, -⟩
    exfalso
    rw [interface_mkOk_inj] at h
    exact ty_PM_ne_PR h.1

theorem roWrap_zero (mw : Loc) :
    ⊢ roWrap (GF := GF) 0 (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw) mw := by
  simp only [roWrap]
  iintro; ipureintro; first | rfl | trivial

/-- No chain is at `*watchableStoreTxnWrite`. -/
theorem roWrap_pt (n : Nat) (t mw : Loc) :
    roWrap (GF := GF) n (interface.mkOk (go.GoType.PointerType watchableStoreTxnWrite.ty) #t) mw ⊢
      False := by
  cases n with
  | zero =>
    simp only [roWrap]
    iintro %h
    exfalso
    rw [interface_mkOk_inj] at h
    exact ty_PM_ne_PT h.1.symm
  | succ n =>
    simp only [roWrap]
    iintro ⟨%trw, %ty, %v, %h, -⟩
    exfalso
    rw [interface_mkOk_inj] at h
    exact ty_PR_ne_PT h.1.symm

/-- A chain at `*txnReadWrite` is one wrapper deeper. -/
theorem roWrap_pr (n : Nat) (t mw : Loc) :
    roWrap (GF := GF) n (interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #t) mw ⊢
      ∃ (m : Nat) (ty : go.GoType) (v : val), ⌜n = m + 1⌝ ∗
        t.[txnReadWrite, go!"TxnRead"] ↦ (interface.mkOk ty v : GoInterface) ∗
        roWrap m (interface.mkOk ty v) mw := by
  cases n with
  | zero =>
    simp only [roWrap]
    iintro %h
    exfalso
    rw [interface_mkOk_inj] at h
    exact ty_PM_ne_PR h.1.symm
  | succ n =>
    simp only [roWrap]
    iintro ⟨%trw, %ty, %v, %h, Hf, Hw⟩
    have ht : t = trw := mkOk_loc_inj _ h
    subst ht
    iexists n, ty, v
    iframe Hf Hw
    ipureintro; first | rfl | trivial

/-- A write transaction at `*metricsTxnWrite` is the plain one. -/
theorem wrWrap_pm (t : Loc) (γ : StoreNames) (s mw : Loc) (ilog : Log) :
    wrWrap (GF := GF) (interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #t) γ s mw ilog ⊢
      ⌜t = mw ∧ γ.watchQ = false⌝ := by
  iintro H
  iunfold wrWrap at H
  icases H with (%h | ⟨%tw, %sw, %γw, %h, -⟩)
  · ipureintro; exact ⟨mkOk_loc_inj _ h.1, h.2⟩
  · exfalso
    obtain ⟨h, -⟩ := h
    rw [interface_mkOk_inj] at h
    exact ty_PM_ne_PT h.1

/-- A write transaction at `*watchableStoreTxnWrite` is a watchable store's. -/
theorem wrWrap_pt (t : Loc) (γ : StoreNames) (s mw : Loc) (ilog : Log) :
    wrWrap (GF := GF) (interface.mkOk (go.GoType.PointerType watchableStoreTxnWrite.ty) #t) γ s mw
        ilog ⊢
      ∃ (sw : Loc) (γw : WsNames), ⌜γw.st = γ⌝ ∗ wsWrap t sw s γw mw ilog := by
  iintro H
  iunfold wrWrap at H
  icases H with (%h | ⟨%tw, %sw, %γw, %h, Hw⟩)
  · exfalso
    obtain ⟨h, -⟩ := h
    rw [interface_mkOk_inj] at h
    exact ty_PM_ne_PT h.1.symm
  · obtain ⟨h, hγ⟩ := h
    have ht : t = tw := mkOk_loc_inj _ h
    subst ht
    iexists sw, γw
    iframe Hw
    ipureintro; exact hγ

/-- No write transaction is at `*txnReadWrite`. -/
theorem wrWrap_pr (t : Loc) (γ : StoreNames) (s mw : Loc) (ilog : Log) :
    wrWrap (GF := GF) (interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #t) γ s mw ilog ⊢
      False := by
  iintro H
  iunfold wrWrap at H
  icases H with (%h | ⟨%tw, %sw, %γw, %h, -⟩)
  · exfalso
    obtain ⟨h, -⟩ := h
    rw [interface_mkOk_inj] at h
    exact ty_PM_ne_PR h.1.symm
  · exfalso
    obtain ⟨h, -⟩ := h
    rw [interface_mkOk_inj] at h
    exact ty_PR_ne_PT h.1

end defs

end api
end mvcc
end EtcdGrove
end Perennial
