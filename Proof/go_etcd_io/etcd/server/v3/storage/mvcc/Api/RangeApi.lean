/-
**`Txn.Range.contract` at the three transaction types** (M4, track B, 2026-11-06). Lean-first (no
Rocq counterpart). Over the sealed definitions of `Api.lean` (imported with `import all`).

`metricsTxnWrite_RangeT`: `metricsTxnWrite.Range`'s proof with the trace lent at its emptiness `te`
(the API's transaction holds none, `Tr := True`, and `Txn.Range` gives the caller's `ownTrace trace te`
back at the same `te`; the internal spec's `isTxn` holds `∃ te`). The contract's size facts: the read
log's well-formedness and bounds (a read transaction's from its log's certificate, a write
transaction's from its index writer's, `IdxWf`, and the receipts it holds), so every state it could
read is safe to sort (`StateOk.stateOk_at`). The read-only wrapper's `Range` is its embedded
transaction's (by induction on the chain, `ro_Range`), the watchable wrapper's its inner transaction's.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.TxnHandle
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.TxnOpsApi
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.StateOk
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnCommon__Range
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__Range

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

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc

/-- What a range's caller needs of the log it reads. -/
def LogSmall (L : Log) : Prop :=
  LogWf' L ∧ L.length < 2 ^ 63 ∧ (∀ cs ∈ L, cs.length < 2 ^ 63) ∧ logCh L ≤ 2 ^ 62

/-- A read transaction's log is small (its certificate's facts and receipt). -/
theorem isTxnReadT_small (mw s : Loc) (γ : StoreNames) (trace : Loc) (log : Log) (rev : w64)
    (crev : Int) (Z Tr : IProp GF) :
    isTxnReadT (GF := GF) mw s γ trace log rev crev Z Tr ⊢ ⌜LogSmall log⌝ := by
  iintro H
  iunfold isTxnReadT at H
  iNamed H
  iunfold storeTxnReadIs at Htr
  iNamedSuffix Htr "T"
  iunfold isStore at Hs
  iNamedSuffix Hs "S"
  iunfold idxCert at HcertT
  icases HcertT with ⟨-, %Hc, -, #Hr⟩
  ihave %Hlt := preceipt_lt _ $$ Hr
  ipureintro
  exact ⟨Hc.1, Hc.2.1, Hc.2.2, by have := HrbS; omega⟩

/-- A write transaction's read log is small (its index writer's facts and receipts). -/
theorem isTxnWriteT_small (mw s : Loc) (γ : StoreNames) (trace : Loc) (ilog : Log)
    (pend : List Change) (puts deletes putSize : w64) (crev : Int) (Z : IProp GF) (ld : Bool)
    (Tr : IProp GF) :
    isTxnWriteT (GF := GF) mw s γ trace ilog pend puts deletes putSize crev Z ld Tr ⊢
      ⌜LogSmall (ilog ++ [pend])⌝ := by
  iintro H
  iunfold isTxnWriteT at H
  iNamed H
  iunfold storeTxnWriteIs at Htw
  iNamed Htw
  iunfold isStore at Hs
  iNamedSuffix Hs "S"
  ihave %Hwf := idxWriter_wf _ _ _ $$ Hw
  icases idxWriter_lt _ _ _ $$ Hw with ⟨%Hlt, -⟩
  ipureintro
  obtain ⟨h1, h2, h3, h4⟩ := Hwf
  refine ⟨h1, by simp; omega, ?_, by rw [logCh_snoc]; have := HrbS; omega⟩
  intro cs hcs
  rcases List.mem_append.1 hcs with h | h
  · exact h4 cs h
  · simp at h; subst h; exact h3

/-- **`metricsTxnWrite.Range` with the trace lent at its emptiness** (see the header). -/
theorem metricsTxnWrite_RangeT
    (hRange : mvcc.storeTxnCommon.Range.spec (GF := GF) (hG := hG))
    (hRangeW : mvcc.storeTxnWrite.Range.spec (GF := GF) (hG := hG)) :
    ∀ (trace : Loc) (mw s : Loc) (γ : StoreNames) (kind : TxnKind)
      (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (todo : Bool)
      (key endk : GoSlice) (k e : GoString) (ro : RangeOptions) (crev : Int) (te : Bool),
    {{ pkgInit ∗ isTxnT mw s γ trace kind crev iprop(True) iprop(True) ∗
        traceutil.ownTrace trace te ∗ rangeCtx todo ctx cd ∗ key ↦*□ k ∗ endk ↦*□ e }}
      (App (App (App (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"Range"))
        (Val #(GoInterface.ok ctx))) (Val #key)) (Val #endk)) (Val #ro))
    {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
        ⌜todo = true → r ≠ null⌝ ∗ isTxnT mw s γ trace kind crev iprop(True) iprop(True) ∗
        traceutil.ownTrace trace te ∗
        rangeOutcomeC r err kind.readLog kind.readRev crev (decide (endk = slice.nil)) k e ro }} := by
  intro trace mw s γ kind ctx cd todo key endk k e ro crev te
  wp_start as ⟨Htx, Hte, #Hctx, #Hkey, #Hend⟩
  cases kind with
  | read log rev =>
    simp only [isTxnT, TxnKind.readLog, TxnKind.readRev]
    iunfold isTxnReadT at Htx
    iNamed Htx
    (try wp_auto)
    wp_method_call; wp_call
    (try wp_auto)
    wp_method_call; wp_call
    (try wp_auto)
    ihave #Hs' : isStore s (γ.withPhys p) $$ []
    · rw [isStore_withPhys]; iexact Hs
    wp_apply (hRange tr s trace ti rt (γ.withPhys p) log rev ctx cd todo key endk k e ro te crev
        iprop(True))
      $$ [$Hs' $Htr $Hrd $Hti $Hctx $Hkey $Hend $Hmu $Hte]
      as %r %err ⟨%Htodo, Hti, Hmu, Hrd, Hte, Hout⟩
    (try wp_auto)
    iapply HΦ
    isplitl []
    · ipureintro; exact Htodo
    iframe Hout Hte
    iunfold isTxnReadT
    iexists p, trw, tr, ti, rt, (ranges + W64 1)
    iframe
    iframe #
  | write ilog pend puts deletes putSize =>
    simp only [isTxnT, TxnKind.readLog, TxnKind.readRev]
    iunfold isTxnWriteT at Htx
    iNamed Htx
    (try wp_auto)
    wp_apply (hRangeW trace tw s γ ilog pend ctx cd todo key endk k e ro te crev iprop(True))
      $$ [$Htw $Hctx $Hkey $Hend $Hte] as %r %err ⟨%Htodo, Htw, Hte, Hout⟩
    (try wp_auto)
    iapply HΦ
    isplitl []
    · ipureintro; exact Htodo
    iframe Hout Hte
    iunfold isTxnWriteT
    iexists tw, (ranges + W64 1)
    iframe

/-- The contract's facts from a small log. -/
theorem range_facts (L : Log) (c : Int) (h : LogSmall L) :
    (∀ r' : Nat, c ≤ (r' : Int) → r' + 1 ≤ L.length → stateOk (stateAt L r')) ∧
      (LogWf' L ∧ ∀ cs ∈ L, cs.length < 2 ^ 63) :=
  ⟨fun r' _ _ => stateOk_at L r' h.1 h.2.1 h.2.2.2, h.1, h.2.2.1⟩

/-- **`Txn.Range.contract` at `*metricsTxnWrite`.** -/
theorem metricsTxnWrite.Range.wp_api
    (hRange : mvcc.storeTxnCommon.Range.spec (GF := GF) (hG := hG))
    (hRangeW : mvcc.storeTxnWrite.Range.spec (GF := GF) (hG := hG)) :
    ∀ t : Loc, Txn.Range.contract (GF := GF) (go.GoType.PointerType metricsTxnWrite.ty) #t := by
  intro t0 (γ : mvcc.StoreNames) trace te k ctx cd todo key endk kk e ro
  iintro %Φ ⟨#Hpkg, Htx, Htrc, #Hctx, #Hkey, #Hend⟩ HΦ
  iunfold mvccTxn at Htx
  cases k with
  | read σ =>
    simp only [mvccTxnI, MTxn.readLog, MTxn.readRev, MTxn.state]
    icases Htx with ⟨%mw, %s, %n, %hre, Htx, Hback, Hwrap⟩
    ihave %Hmw := roWrap_pm n t0 mw $$ Hwrap
    obtain ⟨hm, -⟩ := Hmw
    subst hm
    ihave %Hsm := isTxnReadT_small _ _ _ _ _ _ _ _ _ $$ [$Htx]
    ihave Htx : isTxnT t0 s γ trace (.read σ.log (W64 ((σ.log.length : Int) - 1))) σ.crev
        iprop(True) iprop(True) $$ [Htx]
    · simp only [isTxnT]; iexact Htx
    iapply (metricsTxnWrite_RangeT hRange hRangeW trace t0 s γ _ ctx cd todo key endk kk e ro σ.crev te)
      $$ [Htx Htrc] [HΦ Hback]
    · iframe Hpkg Htx Htrc Hctx Hkey Hend
    inext
    iintro %r %err ⟨%Htodo, Htx, Htrc, Hout⟩
    simp only [TxnKind.readLog, TxnKind.readRev]
    ihave Hout : rangeOutcomeC r err σ.log (W64 (σ.rev : Int)) σ.crev (decide (endk = slice.nil)) kk e
        ro $$ [Hout]
    · rw [← reach_rev hre]; iexact Hout
    iapply HΦ
    iframe Htrc Hout
    isplitr
    · ipureintro; exact Htodo
    isplitl
    · iunfold mvccTxn
      simp only [mvccTxnI]
      iexists t0, s, 0
      simp only [isTxnT]
      iframe Htx Hback
      isplitr
      · ipureintro; exact hre
      iapply roWrap_zero
    ipureintro; exact range_facts _ _ Hsm
  | write σ pend =>
    simp only [mvccTxnI, MTxn.readLog, MTxn.readRev, MTxn.state]
    icases Htx with ⟨%mw, %s, %p, %puts, %deletes, %putSize, %Hk0, Htx, Hback, #Hfree, Hwrap⟩
    ihave %Hw := wrWrap_pm t0 _ s mw σ.log $$ Hwrap
    obtain ⟨hm, Hwq⟩ := Hw
    subst hm
    ihave %Hsm := isTxnWriteT_small _ _ _ _ _ _ _ _ _ _ _ _ _ $$ [$Htx]
    ihave Htx : isTxnT t0 s (γ.withPhys p) trace (.write σ.log pend puts deletes putSize) σ.crev
        iprop(True) iprop(True) $$ [Htx]
    · simp only [isTxnT]; iexact Htx
    iapply (metricsTxnWrite_RangeT hRange hRangeW trace t0 s (γ.withPhys p) _ ctx cd todo key endk kk
        e ro σ.crev te) $$ [Htx Htrc] [HΦ Hback]
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
      simp only [mvccTxnI]
      iexists t0, s, p, puts, deletes, putSize
      simp only [isTxnT]
      iframe Htx Hback Hfree
      isplitr
      · ipureintro; exact Hk0
      iunfold wrWrap; ileft; ipureintro; exact ⟨rfl, Hwq⟩
    ipureintro; exact range_facts _ _ Hsm

/-- A read-only wrapper chain's `Range`: the read transaction's. -/
theorem ro_Range
    (hRange : mvcc.storeTxnCommon.Range.spec (GF := GF) (hG := hG))
    (hRangeW : mvcc.storeTxnWrite.Range.spec (GF := GF) (hG := hG)) (n : Nat) :
    ∀ (ty : go.GoType) (v : val) (mw s : Loc) (γ : StoreNames) (trace : Loc) (log : Log)
      (rev : w64) (crev : Int) (te : Bool) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
      (todo : Bool) (key endk : GoSlice) (k e : GoString) (ro : RangeOptions),
    {{ pkgInit ∗ roWrap n (interface.mkOk ty v) mw ∗
        isTxnReadT mw s γ trace log rev crev iprop(True) iprop(True) ∗ traceutil.ownTrace trace te ∗
        rangeCtx todo ctx cd ∗ key ↦*□ k ∗ endk ↦*□ e }}
      (App (App (App (App (Val #(methods ty go!"Range" v)) (Val #(GoInterface.ok ctx))) (Val #key))
        (Val #endk)) (Val #ro))
    {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
        ⌜todo = true → r ≠ null⌝ ∗ roWrap n (interface.mkOk ty v) mw ∗
        isTxnReadT mw s γ trace log rev crev iprop(True) iprop(True) ∗ traceutil.ownTrace trace te ∗
        rangeOutcomeC r err log rev crev (decide (endk = slice.nil)) k e ro }} := by
  induction n with
  | zero =>
    intro ty v mw s γ trace log rev crev te ctx cd todo key endk k e ro
    simp only [roWrap]
    iintro %Φ ⟨#Hpkg, %h, Htx, Hte, #Hctx, #Hkey, #Hend⟩ HΦ
    have h' := h
    rw [interface_mkOk_inj] at h'
    obtain ⟨rfl, rfl⟩ := h'
    ihave Htx : isTxnT mw s γ trace (.read log rev) crev iprop(True) iprop(True) $$ [Htx]
    · simp only [isTxnT]; iexact Htx
    iapply (metricsTxnWrite_RangeT hRange hRangeW trace mw s γ (.read log rev) ctx cd todo key endk k
        e ro crev te) $$ [Htx Hte] [HΦ]
    · iframe Hpkg Htx Hte Hctx Hkey Hend
    inext
    iintro %r %err ⟨%Htodo, Htx, Hte, Hout⟩
    simp only [isTxnT, TxnKind.readLog, TxnKind.readRev]
    iapply HΦ
    iframe Htx Hte Hout
    ipureintro
    first | exact Htodo | exact ⟨Htodo, h⟩
  | succ m ih =>
    intro ty v mw s γ trace log rev crev te ctx cd todo key endk k e ro
    simp only [roWrap]
    iintro %Φ ⟨#Hpkg, ⟨%trw, %ty', %v', %h, Hf, Hw⟩, Htx, Hte, #Hctx, #Hkey, #Hend⟩ HΦ
    have h' := h
    rw [interface_mkOk_inj] at h'
    obtain ⟨rfl, rfl⟩ := h'
    rw [method_unfold (t := go.GoType.PointerType txnReadWrite.ty) (m := go!"Range")]; wp_call
    (try wp_auto)
    iapply (ih ty' v' mw s γ trace log rev crev te ctx cd todo key endk k e ro) $$ [Hw Htx Hte] [HΦ Hf]
    · iframe Hpkg Hw Htx Hte Hctx Hkey Hend
    inext
    iintro %r %err ⟨%Htodo, Hw, Htx, Hte, Hout⟩
    iapply HΦ
    iframe Htx Hte Hout
    isplitr
    · ipureintro; exact Htodo
    iexists trw, ty', v'
    iframe Hf Hw
    ipureintro; exact h

/-- **`Txn.Range.contract` at `*txnReadWrite`.** -/
theorem txnReadWrite.Range.wp_api
    (hRange : mvcc.storeTxnCommon.Range.spec (GF := GF) (hG := hG))
    (hRangeW : mvcc.storeTxnWrite.Range.spec (GF := GF) (hG := hG)) :
    ∀ t : Loc, Txn.Range.contract (GF := GF) (go.GoType.PointerType txnReadWrite.ty) #t := by
  intro t0 (γ : mvcc.StoreNames) trace te k ctx cd todo key endk kk e ro
  iintro %Φ ⟨#Hpkg, Htx, Htrc, #Hctx, #Hkey, #Hend⟩ HΦ
  iunfold mvccTxn at Htx
  cases k with
  | read σ =>
    simp only [mvccTxnI, MTxn.readLog, MTxn.readRev, MTxn.state]
    icases Htx with ⟨%mw, %s, %n, %hre, Htx, Hback, Hwrap⟩
    ihave %Hsm := isTxnReadT_small _ _ _ _ _ _ _ _ _ $$ [$Htx]
    iapply (ro_Range hRange hRangeW n _ _ mw s γ trace σ.log _ σ.crev te ctx cd todo key endk kk e ro)
      $$ [Hwrap Htx Htrc] [HΦ Hback]
    · iframe Hpkg Hwrap Htx Htrc Hctx Hkey Hend
    inext
    iintro %r %err ⟨%Htodo, Hwrap, Htx, Htrc, Hout⟩
    ihave Hout : rangeOutcomeC r err σ.log (W64 (σ.rev : Int)) σ.crev (decide (endk = slice.nil)) kk e
        ro $$ [Hout]
    · rw [← reach_rev hre]; iexact Hout
    iapply HΦ
    iframe Htrc Hout
    isplitr
    · ipureintro; exact Htodo
    isplitl
    · iunfold mvccTxn
      simp only [mvccTxnI]
      iexists mw, s, n
      iframe Htx Hback Hwrap
      ipureintro; exact hre
    ipureintro; exact range_facts _ _ Hsm
  | write σ₀ pend =>
    simp only [mvccTxnI]
    icases Htx with ⟨%mw, %s, %p, %puts, %deletes, %putSize, -, -, -, -, Hwrap⟩
    iexfalso
    iapply wrWrap_pr t0 _ s mw σ₀.log $$ Hwrap

end proof

end api
end mvcc
end EtcdGrove
end Perennial
