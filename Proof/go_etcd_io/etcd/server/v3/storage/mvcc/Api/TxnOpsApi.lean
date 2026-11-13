/-
**`Txn.Rev.contract` at `*metricsTxnWrite`** (M4, track B, 2026-11-06). Lean-first (no Rocq
counterpart). Over the sealed definitions of `Api.lean` (imported with `import all`).

`metricsTxnWrite.Rev` over the transaction without its trace (`isTxnT` at `True`): the revision it
began at, its log's last (a reachable state's log is not empty, `reach_ne`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.TxnHandle
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Rev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__FirstRev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Changes
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.txnReadWrite__Changes

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-- A reachable state's log is not empty. -/
theorem reach_ne {σ : MvccState} (h : MvccReachable σ) : σ.log ≠ [] := by
  induction h with
  | start => simp [mvccStart]
  | notify σ pend _ _ _ ih => exact ih
  | commit σ _ ih =>
    simp only [MvccState.commitPending, commitLog]
    split <;> simp_all
  | compact σ r _ _ _ _ _ ih => exact ih

/-- A reachable state's revision, as the transaction's. -/
theorem reach_rev {σ : MvccState} (h : MvccReachable σ) :
    (W64 ((σ.log.length : Int) - 1) : w64) = W64 (σ.rev : Int) := by
  have hne := List.length_pos_iff.2 (reach_ne h)
  unfold MvccState.rev
  congr 1
  omega

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`Txn.Rev.contract` at `*metricsTxnWrite`.** -/
theorem metricsTxnWrite.Rev.wp_api (hRev : mvcc.metricsTxnWrite.Rev.spec (GF := GF) (hG := hG)) :
    ∀ t : Loc, Txn.Rev.contract (GF := GF) (go.GoType.PointerType metricsTxnWrite.ty) #t := by
  intro t0 (γ : mvcc.StoreNames) trace k
  iintro %Φ ⟨#Hpkg, Htx⟩ HΦ
  iunfold mvccTxn at Htx
  cases k with
  | read σ =>
    simp only [mvccTxnI, MTxn.state]
    icases Htx with ⟨%mw, %s, %n, %hre, Htx, Hback, Hwrap⟩
    ihave %Hmw := roWrap_pm n t0 mw $$ Hwrap
    obtain ⟨hm, -⟩ := Hmw
    subst hm
    ihave Htx : isTxnT t0 s γ trace (.read σ.log (W64 ((σ.log.length : Int) - 1))) σ.crev
        iprop(True) iprop(True) $$ [Htx]
    · simp only [isTxnT]; iexact Htx
    iapply (hRev trace t0 s γ (.read σ.log (W64 ((σ.log.length : Int) - 1))) σ.crev iprop(True)
        iprop(True)) $$ [Htx] [HΦ Hback]
    · iframe Hpkg Htx
    inext
    iintro Htx
    simp only [TxnKind.beginRev]
    rw [← reach_rev hre]
    iapply HΦ
    iunfold mvccTxn
    simp only [mvccTxnI]
    iexists t0, s, 0
    simp only [isTxnT]
    iframe Htx Hback
    isplitr
    · ipureintro; exact hre
    iapply roWrap_zero
  | write σ pend =>
    simp only [mvccTxnI, MTxn.state]
    icases Htx with ⟨%mw, %s, %p, %puts, %deletes, %putSize, %Hk0, Htx, Hback, #Hfree, Hwrap⟩
    obtain ⟨Hpn, hre⟩ := Hk0
    ihave %Hw := wrWrap_pm t0 _ s mw σ.log $$ Hwrap
    obtain ⟨hm, Hwq⟩ := Hw
    subst hm
    ihave Htx : isTxnT t0 s (γ.withPhys p) trace (.write σ.log pend puts deletes putSize) σ.crev
        iprop(True) iprop(True) $$ [Htx]
    · simp only [isTxnT]; iexact Htx
    iapply (hRev trace t0 s (γ.withPhys p) (.write σ.log pend puts deletes putSize) σ.crev
        iprop(True) iprop(True)) $$ [Htx] [HΦ Hback]
    · iframe Hpkg Htx
    inext
    iintro Htx
    simp only [TxnKind.beginRev]
    rw [← reach_rev hre]
    iapply HΦ
    iunfold mvccTxn
    simp only [mvccTxnI]
    iexists t0, s, p, puts, deletes, putSize
    simp only [isTxnT]
    iframe Htx Hback Hfree
    isplitr
    · ipureintro; exact ⟨Hpn, hre⟩
    iunfold wrWrap; ileft; ipureintro; exact ⟨rfl, Hwq⟩

/-- A write transaction's key-values back into it, after `Changes` (`storeTxnWriteIs_join`). -/
theorem isTxnWriteT_join (mw s : Loc) (γ : StoreNames) (trace : Loc) (ilog : Log)
    (pend : List Change) (puts deletes putSize : w64) (chs : GoSlice) (ps : List Loc) (crev : Int)
    (Z : IProp GF) (ld : Bool) (Tr : IProp GF) :
    isTxnWriteCoreY (GF := GF) mw s γ trace ilog pend puts deletes putSize chs ps false crev Z ld
        (slotY γ ilog) Tr ∗ chs ↦* ps ∗ changesAre ps ilog pend ⊢
      isTxnWriteT mw s γ trace ilog pend puts deletes putSize crev Z ld Tr := by
  iintro ⟨H, Hchs, Hkvs⟩
  iunfold isTxnWriteCoreY at H
  icases H with ⟨%tw, %ranges, Hmw, Hc, Htrc⟩
  iunfold isTxnWriteT
  iexists tw, ranges
  iframe Hmw Htrc
  iapply storeTxnWriteIs_join tw s γ ilog pend chs ps crev Z ld
  iframe Hchs Hkvs
  rw [storeTxnWriteCore_Y]
  iexact Hc

/-- A write transaction's `FirstRev`: its `firstRev` field, `0` (`storeTxnCommon`'s, read through the
embedded write transaction). -/
theorem metricsTxnWrite_FirstRevW (mw s : Loc) (γ : StoreNames) (trace : Loc) (ilog : Log)
    (pend : List Change) (puts deletes putSize : w64) (crev : Int) (Z : IProp GF) (ld : Bool)
    (Tr : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        isTxnWriteT mw s γ trace ilog pend puts deletes putSize crev Z ld Tr }}
      (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"FirstRev")) (Val #()))
    {{ RET #(W64 0 : w64); isTxnWriteT mw s γ trace ilog pend puts deletes putSize crev Z ld Tr }} := by
  wp_start as Htx
  iunfold isTxnWriteT at Htx
  iNamed Htx
  iunfold storeTxnWriteIs at Htw
  iNamed Htw
  (try wp_auto)
  rw [method_unfold (t := go.GoType.PointerType storeTxnWrite.ty) (m := go!"FirstRev")]; wp_call
  (try wp_auto)
  rw [method_unfold (t := go.GoType.PointerType storeTxnCommon.ty) (m := go!"FirstRev")]; wp_call
  (try wp_auto)
  iapply HΦ
  iunfold isTxnWriteT
  iexists tw, ranges
  iframe Hmw Htrc
  iunfold storeTxnWriteIs
  iexists ti, bt, Locked, chs, ps, ntok, Pw, fw, Dep
  simp only [named]
  iframe Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hbv Hwv HY Htko Hmu HrevMu Hti Hrt
    Hcres Hlrd
  iframe #
  ipureintro; exact ⟨Hbudget, Hps, Hne, Htrnn, Hcrev⟩

/-- **`Txn.FirstRev.contract` at `*metricsTxnWrite`**: a read transaction's compaction revision
(`metricsTxnWrite.FirstRev.spec`); a write transaction's `firstRev` field, `0` (`storeTxnCommon`'s,
read through the embedded write transaction). -/
theorem metricsTxnWrite.FirstRev.wp_api
    (hFR : mvcc.metricsTxnWrite.FirstRev.spec (GF := GF) (hG := hG)) :
    ∀ t : Loc, Txn.FirstRev.contract (GF := GF) (go.GoType.PointerType metricsTxnWrite.ty) #t := by
  intro t0 (γ : mvcc.StoreNames) trace k
  iintro %Φ ⟨#Hpkg, Htx⟩ HΦ
  iunfold mvccTxn at Htx
  cases k with
  | read σ =>
    simp only [mvccTxnI]
    icases Htx with ⟨%mw, %s, %n, %hre, Htx, Hback, Hwrap⟩
    ihave %Hmw := roWrap_pm n t0 mw $$ Hwrap
    obtain ⟨hm, -⟩ := Hmw
    subst hm
    iapply (hFR trace t0 s γ σ.log (W64 ((σ.log.length : Int) - 1)) σ.crev iprop(True) iprop(True))
      $$ [Htx] [HΦ Hback]
    · iframe Hpkg Htx
    inext
    iintro Htx
    iapply HΦ
    iunfold mvccTxn
    simp only [mvccTxnI]
    iexists t0, s, 0
    iframe Htx Hback
    isplitr
    · ipureintro; exact hre
    iapply roWrap_zero
  | write σ pend =>
    simp only [mvccTxnI]
    icases Htx with ⟨%mw, %s, %p, %puts, %deletes, %putSize, %Hk0, Htx, Hback, #Hfree, Hwrap⟩
    ihave %Hw := wrWrap_pm t0 _ s mw σ.log $$ Hwrap
    obtain ⟨hm, Hwq⟩ := Hw
    subst hm
    iapply (metricsTxnWrite_FirstRevW t0 s (γ.withPhys p) trace σ.log pend puts deletes putSize σ.crev
        iprop(True) false iprop(True)) $$ [Htx] [HΦ Hback]
    · iframe Hpkg Htx
    inext
    iintro Htx
    iapply HΦ
    iunfold mvccTxn
    simp only [mvccTxnI]
    iexists t0, s, p, puts, deletes, putSize
    iframe Htx Hback Hfree
    isplitr
    · ipureintro; exact Hk0
    iunfold wrWrap; ileft; ipureintro; exact ⟨rfl, Hwq⟩

/-- **`Txn.Changes.contract` at `*metricsTxnWrite`**: a read transaction's (its inner
`*txnReadWrite`'s) `nil`; a write transaction's slice of its pending changes
(`metricsTxnWrite.Changes.spec`), its key-values back into the transaction. -/
theorem metricsTxnWrite.Changes.wp_api
    (hCh : mvcc.metricsTxnWrite.Changes.spec (GF := GF) (hG := hG))
    (hChR : mvcc.txnReadWrite.Changes.spec (GF := GF) (hG := hG)) :
    ∀ t : Loc, Txn.Changes.contract (GF := GF) (go.GoType.PointerType metricsTxnWrite.ty) #t := by
  intro t0 (γ : mvcc.StoreNames) trace k
  iintro %Φ ⟨#Hpkg, Htx⟩ HΦ
  iunfold mvccTxn at Htx
  cases k with
  | read σ =>
    simp only [mvccTxnI]
    icases Htx with ⟨%mw, %s, %n, %hre, Htx, Hback, Hwrap⟩
    ihave %Hmw := roWrap_pm n t0 mw $$ Hwrap
    obtain ⟨hm, -⟩ := Hmw
    subst hm
    iunfold isTxnReadT at Htx
    iNamed Htx
    rw [method_unfold (t := go.GoType.PointerType metricsTxnWrite.ty) (m := go!"Changes")]; wp_call
    (try wp_auto)
    wp_apply (hChR trw)
    iapply HΦ
    isplitl
    · iunfold mvccTxn
      simp only [mvccTxnI]
      iexists t0, s, 0
      iframe Hback
      isplitr
      · ipureintro; exact hre
      isplitl
      · iunfold isTxnReadT
        iexists p, trw, tr, ti, rt, ranges
        iframe
        iframe #
      iapply roWrap_zero
    ipureintro
    simp only [MTxn.pend, List.length_nil]
    exact ⟨rfl, by simp [slice.nil]⟩
  | write σ pend =>
    simp only [mvccTxnI]
    icases Htx with ⟨%mw, %s, %p, %puts, %deletes, %putSize, %Hk0, Htx, Hback, #Hfree, Hwrap⟩
    ihave %Hw := wrWrap_pm t0 _ s mw σ.log $$ Hwrap
    obtain ⟨hm, Hwq⟩ := Hw
    subst hm
    iapply (hCh trace t0 s (γ.withPhys p) σ.log pend puts deletes putSize σ.crev iprop(True) false
        iprop(True)) $$ [Htx] [HΦ Hback]
    · iframe Hpkg Htx
    inext
    iintro %chs %ps ⟨Hchs, Hkvs, %Hps, Hcore⟩
    ihave %Hlen := ownSlice_len _ _ _ $$ Hchs
    ihave Htx := isTxnWriteT_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ $$ [$Hcore $Hchs $Hkvs]
    iapply HΦ
    isplitl
    · iunfold mvccTxn
      simp only [mvccTxnI]
      iexists t0, s, p, puts, deletes, putSize
      iframe Htx Hback Hfree
      isplitr
      · ipureintro; exact Hk0
      iunfold wrWrap; ileft; ipureintro; exact ⟨rfl, Hwq⟩
    ipureintro
    simp only [MTxn.pend]
    refine ⟨?_, Hlen.2⟩
    rw [← Hps, Hlen.1]
    word

end proof

end api
end mvcc
end EtcdGrove
end Perennial
