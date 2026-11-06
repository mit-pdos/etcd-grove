/-
**The `Txn` contracts at `*watchableStoreTxnWrite` but `End`** (M4, track B, 2026-11-06). Lean-first
(no Rocq counterpart). Over the sealed definitions of `Api.lean` (imported with `import all`).

The watchable wrapper's `Rev`, `FirstRev`, `Changes`, `Range`, `Put` and `DeleteRange` are its
embedded `TxnWrite`'s, the inner `*metricsTxnWrite` (Go's promotion: the wrapper's field, read-only,
`wsWrap`'s `↦□`), so each is the plain store's write transaction's step (`TxnOpsApi`, `RangeApi`,
`WriteOpsApi`), with the wrapper kept (`pt_open`, `pt_close`). No read transaction is a watchable
wrapper (`roWrap_pt`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.WriteOpsApi
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Rev

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- A watchable wrapper's write transaction, opened. -/
theorem pt_open (t0 : Loc) (γ : StoreNames) (trace : Loc) (σ : MvccState) (pend : List Change) :
    mvccTxnI (GF := GF) (interface.mkOk (go.GoType.PointerType watchableStoreTxnWrite.ty) #t0) γ trace
        (.write σ pend) ⊢
      ∃ (mw s : Loc) (p : PhysNames) (puts deletes putSize : w64) (sw : Loc),
        ⌜σ.pending = none ∧ MvccReachable σ⌝ ∗
        isTxnWriteT mw s (γ.withPhys p) trace σ.log pend puts deletes putSize σ.crev iprop(True) false
          iprop(True) ∗
        tokBack s (γ.withPhys p) ∗ certFree (γ.withPhys p) ∗
        t0 ↦□ ({ TxnWrite' := interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw,
                 s' := sw } : watchableStoreTxnWrite) ∗
        (∀ (pend' : List Change) (puts' deletes' putSize' : w64),
          isTxnWriteT mw s (γ.withPhys p) trace σ.log pend' puts' deletes' putSize' σ.crev iprop(True)
            false iprop(True) -∗ tokBack s (γ.withPhys p) -∗
          mvccTxnI (interface.mkOk (go.GoType.PointerType watchableStoreTxnWrite.ty) #t0) γ trace
            (.write σ pend')) := by
  simp only [mvccTxnI]
  iintro ⟨%mw, %s, %p, %puts, %deletes, %putSize, %Hk0, Htx, Hback, #Hfree, Hwrap⟩
  icases wrWrap_pt t0 _ s mw σ.log $$ Hwrap with ⟨%sw, %γw, %hγw, Hwrap⟩
  iunfold wsWrap at Hwrap
  icases Hwrap with ⟨#Htw, #Hws, #Hcert⟩
  iexists mw, s, p, puts, deletes, putSize, sw
  iframe Htx Hback Hfree Htw
  isplitr
  · ipureintro; exact Hk0
  iintro %pend' %puts' %deletes' %putSize' Htx Hback
  iexists mw, s, p, puts', deletes', putSize'
  iframe Htx Hback Hfree
  isplitr
  · ipureintro; exact Hk0
  iunfold wrWrap
  iright
  iexists t0, sw, γw
  isplitr
  · ipureintro; exact ⟨rfl, hγw⟩
  iunfold wsWrap
  iframe Htw Hws Hcert

/-- **`Txn.Rev.contract` at `*watchableStoreTxnWrite`.** -/
theorem watchableStoreTxnWrite.Rev.wp_api
    (hRev : mvcc.metricsTxnWrite.Rev.spec (GF := GF) (hG := hG)) :
    ∀ t : Loc, Txn.Rev.contract (GF := GF) (go.GoType.PointerType watchableStoreTxnWrite.ty) #t := by
  intro t0 (γ : mvcc.StoreNames) trace k
  iintro %Φ ⟨#Hpkg, Htx⟩ HΦ
  iunfold mvccTxn at Htx
  cases k with
  | read σ =>
    simp only [mvccTxnI]
    icases Htx with ⟨%mw, %s, %n, -, -, -, Hwrap⟩
    iexfalso
    iapply roWrap_pt n t0 mw $$ Hwrap
  | write σ pend =>
    icases pt_open t0 γ trace σ pend $$ Htx
      with ⟨%mw, %s, %p, %puts, %deletes, %putSize, %sw, %Hk0, Htx, Hback, #Hfree, #Htw, Hclose⟩
    iStructNamed Htw
    rw [method_unfold (t := go.GoType.PointerType watchableStoreTxnWrite.ty) (m := go!"Rev")]; wp_call
    (try wp_auto)
    ihave Htx : isTxnT mw s (γ.withPhys p) trace (.write σ.log pend puts deletes putSize) σ.crev
        iprop(True) iprop(True) $$ [Htx]
    · simp only [isTxnT]; iexact Htx
    iapply (hRev trace mw s (γ.withPhys p) (.write σ.log pend puts deletes putSize) σ.crev iprop(True)
        iprop(True)) $$ [Htx] [HΦ Hback Hclose]
    · iframe Hpkg Htx
    inext
    iintro Htx
    simp only [TxnKind.beginRev, MTxn.state]
    rw [← reach_rev Hk0.2]
    iapply HΦ
    iunfold mvccTxn
    iapply Hclose $$ [Htx] Hback
    simp only [isTxnT]; iexact Htx

/-- **`Txn.FirstRev.contract` at `*watchableStoreTxnWrite`** (`0`). -/
theorem watchableStoreTxnWrite.FirstRev.wp_api :
    ∀ t : Loc, Txn.FirstRev.contract (GF := GF) (go.GoType.PointerType watchableStoreTxnWrite.ty) #t := by
  intro t0 (γ : mvcc.StoreNames) trace k
  iintro %Φ ⟨#Hpkg, Htx⟩ HΦ
  iunfold mvccTxn at Htx
  cases k with
  | read σ =>
    simp only [mvccTxnI]
    icases Htx with ⟨%mw, %s, %n, -, -, -, Hwrap⟩
    iexfalso
    iapply roWrap_pt n t0 mw $$ Hwrap
  | write σ pend =>
    icases pt_open t0 γ trace σ pend $$ Htx
      with ⟨%mw, %s, %p, %puts, %deletes, %putSize, %sw, %Hk0, Htx, Hback, #Hfree, #Htw, Hclose⟩
    iStructNamed Htw
    rw [method_unfold (t := go.GoType.PointerType watchableStoreTxnWrite.ty) (m := go!"FirstRev")]
    wp_call
    (try wp_auto)
    iapply (metricsTxnWrite_FirstRevW mw s (γ.withPhys p) trace σ.log pend puts deletes putSize σ.crev
        iprop(True) false iprop(True)) $$ [Htx] [HΦ Hback Hclose]
    · iframe Hpkg Htx
    inext
    iintro Htx
    iapply HΦ
    iunfold mvccTxn
    iapply Hclose $$ [Htx] Hback
    iexact Htx

/-- **`Txn.Changes.contract` at `*watchableStoreTxnWrite`.** -/
theorem watchableStoreTxnWrite.Changes.wp_api
    (hCh : mvcc.metricsTxnWrite.Changes.spec (GF := GF) (hG := hG)) :
    ∀ t : Loc, Txn.Changes.contract (GF := GF) (go.GoType.PointerType watchableStoreTxnWrite.ty) #t := by
  intro t0 (γ : mvcc.StoreNames) trace k
  iintro %Φ ⟨#Hpkg, Htx⟩ HΦ
  iunfold mvccTxn at Htx
  cases k with
  | read σ =>
    simp only [mvccTxnI]
    icases Htx with ⟨%mw, %s, %n, -, -, -, Hwrap⟩
    iexfalso
    iapply roWrap_pt n t0 mw $$ Hwrap
  | write σ pend =>
    icases pt_open t0 γ trace σ pend $$ Htx
      with ⟨%mw, %s, %p, %puts, %deletes, %putSize, %sw, %Hk0, Htx, Hback, #Hfree, #Htw, Hclose⟩
    iStructNamed Htw
    rw [method_unfold (t := go.GoType.PointerType watchableStoreTxnWrite.ty) (m := go!"Changes")]
    wp_call
    (try wp_auto)
    iapply (hCh trace mw s (γ.withPhys p) σ.log pend puts deletes putSize σ.crev iprop(True) false
        iprop(True)) $$ [Htx] [HΦ Hback Hclose]
    · iframe Hpkg Htx
    inext
    iintro %chs %ps ⟨Hchs, Hkvs, %Hps, Hcore⟩
    ihave %Hlen := ownSlice_len _ _ _ $$ Hchs
    ihave Htx := isTxnWriteT_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ $$ [$Hcore $Hchs $Hkvs]
    iapply HΦ
    isplitl
    · iunfold mvccTxn
      iapply Hclose $$ [Htx] Hback
      iexact Htx
    ipureintro
    simp only [MTxn.pend]
    refine ⟨?_, Hlen.2⟩
    rw [← Hps, Hlen.1]
    word

/-- **`Txn.Range.contract` at `*watchableStoreTxnWrite`.** -/
theorem watchableStoreTxnWrite.Range.wp_api
    (hRange : mvcc.storeTxnCommon.Range.spec (GF := GF) (hG := hG))
    (hRangeW : mvcc.storeTxnWrite.Range.spec (GF := GF) (hG := hG)) :
    ∀ t : Loc, Txn.Range.contract (GF := GF) (go.GoType.PointerType watchableStoreTxnWrite.ty) #t := by
  intro t0 (γ : mvcc.StoreNames) trace te k ctx cd todo key endk kk e ro
  iintro %Φ ⟨#Hpkg, Htx, Htrc, #Hctx, #Hkey, #Hend⟩ HΦ
  iunfold mvccTxn at Htx
  cases k with
  | read σ =>
    simp only [mvccTxnI]
    icases Htx with ⟨%mw, %s, %n, -, -, -, Hwrap⟩
    iexfalso
    iapply roWrap_pt n t0 mw $$ Hwrap
  | write σ pend =>
    simp only [MTxn.readLog, MTxn.readRev, MTxn.state]
    icases pt_open t0 γ trace σ pend $$ Htx
      with ⟨%mw, %s, %p, %puts, %deletes, %putSize, %sw, %Hk0, Htx, Hback, #Hfree, #Htw, Hclose⟩
    iStructNamed Htw
    ihave %Hsm := isTxnWriteT_small _ _ _ _ _ _ _ _ _ _ _ _ _ $$ [$Htx]
    rw [method_unfold (t := go.GoType.PointerType watchableStoreTxnWrite.ty) (m := go!"Range")]; wp_call
    (try wp_auto)
    ihave Htx : isTxnT mw s (γ.withPhys p) trace (.write σ.log pend puts deletes putSize) σ.crev
        iprop(True) iprop(True) $$ [Htx]
    · simp only [isTxnT]; iexact Htx
    iapply (metricsTxnWrite_RangeT hRange hRangeW trace mw s (γ.withPhys p) _ ctx cd todo key endk kk
        e ro σ.crev te) $$ [Htx Htrc] [HΦ Hback Hclose]
    · iframe Hpkg Htx Htrc Hctx Hkey Hend
    inext
    iintro %r %err ⟨%Htodo, Htx, Htrc, Hout⟩
    simp only [TxnKind.readLog, TxnKind.readRev]
    iapply HΦ
    iframe Htrc Hout
    isplitr
    · ipureintro; exact Htodo
    isplitl
    · iunfold mvccTxn
      iapply Hclose $$ [Htx] Hback
      simp only [isTxnT]; iexact Htx
    ipureintro; exact range_facts _ _ Hsm

/-- **`Txn.Put.contract` at `*watchableStoreTxnWrite`.** -/
theorem watchableStoreTxnWrite.Put.wp_api
    (hPut : mvcc.storeTxnWrite.Put.spec (GF := GF) (hG := hG)) :
    watchableStoreTxnWrite.Put.spec (GF := GF) := by
  intro t0 (γ : mvcc.StoreNames) trace te σ pend key value k vv leaseID L
  iintro %Φ ⟨#Hpkg, Htx, Hte, #Hkey, #Hval, %Hklen, Hown, %Hlease⟩ HΦ
  iunfold mvccTxn at Htx
  icases pt_open t0 γ trace σ pend $$ Htx
    with ⟨%mw, %s, %p, %puts, %deletes, %putSize, %sw, %Hk0, Htx, Hback, #Hfree, #Htw, Hclose⟩
  iStructNamed Htw
  have hl : mvccLeases γ = (γ.withPhys p).leases := rfl
  rw [hl]
  rw [method_unfold (t := go.GoType.PointerType watchableStoreTxnWrite.ty) (m := go!"Put")]; wp_call
  (try wp_auto)
  iapply (metricsTxnWrite_PutT hPut trace mw s (γ.withPhys p) σ.log pend puts deletes putSize key value
      k vv leaseID L σ.crev te) $$ [Htx Hte Hown] [HΦ Hback Hclose]
  · iframe Hpkg Htx Hte Hkey Hval Hown
    ipureintro; exact ⟨Hklen, Hlease⟩
  inext
  iintro ⟨Htx, Hte, Hown⟩
  iapply HΦ
  iframe Hte Hown
  iunfold mvccTxn
  iapply Hclose $$ [Htx] Hback
  iexact Htx

/-- **`Txn.DeleteRange.contract` at `*watchableStoreTxnWrite`.** -/
theorem watchableStoreTxnWrite.DeleteRange.wp_api
    (hDel : mvcc.metricsTxnWrite.DeleteRange.spec (GF := GF) (hG := hG)) :
    ∀ t : Loc,
      Txn.DeleteRange.contract (GF := GF) (go.GoType.PointerType watchableStoreTxnWrite.ty) #t := by
  intro t0 (γ : mvcc.StoreNames) trace σ pend key endk k e L
  iintro %Φ ⟨#Hpkg, Htx, #Hkey, #Hend, Hown⟩ HΦ
  iunfold mvccTxn at Htx
  icases pt_open t0 γ trace σ pend $$ Htx
    with ⟨%mw, %s, %p, %puts, %deletes, %putSize, %sw, %Hk0, Htx, Hback, #Hfree, #Htw, Hclose⟩
  iStructNamed Htw
  have hl : mvccLeases γ = (γ.withPhys p).leases := rfl
  rw [hl]
  rw [method_unfold (t := go.GoType.PointerType watchableStoreTxnWrite.ty) (m := go!"DeleteRange")]
  wp_call
  (try wp_auto)
  iapply (hDel trace mw s (γ.withPhys p) σ.log pend puts deletes putSize key endk k e L σ.crev
      iprop(True) iprop(True)) $$ [Htx Hown] [HΦ Hback Hclose]
  · iframe Hpkg Htx Hkey Hend Hown
  inext
  iintro %n %rev ⟨Htx, Hown, %Hnr⟩
  ihave %Hsm := isTxnWriteT_small _ _ _ _ _ _ _ _ _ _ _ _ _ $$ [$Htx]
  iapply HΦ
  iframe Hown
  isplitl
  · iunfold mvccTxn
    iapply Hclose $$ [Htx] Hback
    iexact Htx
  ipureintro
  exact ⟨by rw [List.length_map]; exact Hnr, Hsm.1, Hsm.2.2.1⟩

end proof

end api
end mvcc
end EtcdGrove
end Perennial
