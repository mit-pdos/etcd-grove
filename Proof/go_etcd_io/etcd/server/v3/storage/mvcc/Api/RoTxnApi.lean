/-
**The read-only wrapper: `NewReadOnlyTxnWrite.spec` and the `Txn` contracts at `*txnReadWrite`**
(M4, track B, 2026-11-06). Lean-first (no Rocq counterpart). Over the sealed definitions of
`Api.lean` (imported with `import all`).

`NewReadOnlyTxnWrite(t)` wraps any read transaction `t` (`*metricsTxnWrite`, or a wrapper again): the
API's read transaction is the chain of wrappers down to the internal one (`roWrap`), one deeper. A
wrapper's `Rev`, `FirstRev`, `End` (and `Range`) are its embedded `TxnRead`'s: by induction on the
chain's depth (`ro_Rev`, `ro_FirstRev`, `ro_End`), each wrapper loading its field and calling the
next, down to `metricsTxnWrite`'s spec. Its `Changes` is `nil`; its `Put` and `DeleteRange` (which
panic) hold vacuously: no write transaction is a `*txnReadWrite` (`wrWrap_pr`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.TxnHandle
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.TxnOpsApi
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__End

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

/-- A chain's top is an interface value of some type. -/
theorem roWrap_mkOk (n : Nat) (t : GoInterface) (mw : Loc) :
    roWrap (GF := GF) n t mw ⊢ roWrap n t mw ∗ ⌜∃ (ty : go.GoType) (v : val), t = interface.mkOk ty v⌝ := by
  cases n with
  | zero =>
    simp only [roWrap]
    iintro %h
    isplitr
    · ipureintro; exact h
    ipureintro; exact ⟨_, _, h⟩
  | succ n =>
    simp only [roWrap]
    iintro ⟨%trw, %ty, %v, %h, Hf, Hw⟩
    isplitl
    · iexists trw, ty, v; iframe Hf Hw; ipureintro; exact h
    ipureintro; exact ⟨_, _, h⟩

/-- **`NewReadOnlyTxnWrite.spec`** (the API's). -/
theorem NewReadOnlyTxnWrite.wp_api : NewReadOnlyTxnWrite.spec (GF := GF) := by
  intro t (γ : mvcc.StoreNames) trace σ
  wp_start as Htx
  iunfold mvccTxn at Htx
  simp only [mvccTxnI]
  icases Htx with ⟨%mw, %s, %n, %hre, Htx, Hback, Hwrap⟩
  icases roWrap_mkOk n t mw $$ Hwrap with ⟨Hwrap, %Ht⟩
  obtain ⟨ty, v, rfl⟩ := Ht
  (try wp_auto)
  wp_alloc trw as Htrw
  (try wp_auto)
  iStructNamedPrefix Htrw "W"
  iapply HΦ
  iunfold mvccTxn
  simp only [mvccTxnI]
  iexists mw, s, n + 1
  iframe Htx Hback
  isplitr
  · ipureintro; exact hre
  simp only [roWrap]
  iexists trw, ty, v
  iframe Hwrap
  isplitr
  · ipureintro; rfl
  iexact WTxnRead

/-- A chain's `End`: the read transaction's. -/
theorem ro_End (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG)) (n : Nat) :
    ∀ (ty : go.GoType) (v : val) (mw s : Loc) (γ : StoreNames) (trace : Loc) (log : Log)
      (rev : w64) (crev : Int),
    {{ pkgInit ∗ roWrap n (interface.mkOk ty v) mw ∗
        isTxnReadT mw s γ trace log rev crev iprop(True) iprop(True) }}
      (App (Val #(methods ty go!"End" v)) (Val #()))
    {{ RET #(); storeReaderC s γ }} := by
  induction n with
  | zero =>
    intro ty v mw s γ trace log rev crev
    simp only [roWrap]
    iintro %Φ ⟨#Hpkg, %h, Htx⟩ HΦ
    rw [interface_mkOk_inj] at h
    obtain ⟨rfl, rfl⟩ := h
    ihave Hte : isTxnEndY mw s γ trace (.read log rev) crev iprop(True) iprop(True) iprop(True)
        $$ [Htx]
    · simp only [isTxnEndY]; iexact Htx
    ihave Hep : txnEndPreH γ (.read log rev) $$ []
    · simp only [txnEndPreH]; itrivial
    ihave Hx : txnEndX γ (.read log rev) crev iprop(True) iprop(True) iprop(True) $$ []
    · simp only [txnEndX]; itrivial
    iapply (hEnd trace mw s γ (.read log rev) crev iprop(True) iprop(True) iprop(True) iprop(True)
        iprop(True)) $$ [Hte Hep Hx] [HΦ]
    · iframe Hpkg Hte Hep Hx
    inext
    iintro ⟨Hrd, -, -, -, -⟩
    iapply HΦ; iexact Hrd
  | succ m ih =>
    intro ty v mw s γ trace log rev crev
    simp only [roWrap]
    iintro %Φ ⟨#Hpkg, ⟨%trw, %ty', %v', %h, Hf, Hw⟩, Htx⟩ HΦ
    rw [interface_mkOk_inj] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [method_unfold (t := go.GoType.PointerType txnReadWrite.ty) (m := go!"End")]; wp_call
    (try wp_auto)
    iapply (ih ty' v' mw s γ trace log rev crev) $$ [Hw Htx] [HΦ]
    · iframe Hpkg Hw Htx
    inext
    iintro Hrd
    iapply HΦ; iexact Hrd

/-- A chain's `Rev`: the read transaction's. -/
theorem ro_Rev (hRev : mvcc.metricsTxnWrite.Rev.spec (GF := GF) (hG := hG)) (n : Nat) :
    ∀ (ty : go.GoType) (v : val) (mw s : Loc) (γ : StoreNames) (trace : Loc) (log : Log)
      (rev : w64) (crev : Int),
    {{ pkgInit ∗ roWrap n (interface.mkOk ty v) mw ∗
        isTxnReadT mw s γ trace log rev crev iprop(True) iprop(True) }}
      (App (Val #(methods ty go!"Rev" v)) (Val #()))
    {{ RET #rev; roWrap n (interface.mkOk ty v) mw ∗
        isTxnReadT mw s γ trace log rev crev iprop(True) iprop(True) }} := by
  induction n with
  | zero =>
    intro ty v mw s γ trace log rev crev
    simp only [roWrap]
    iintro %Φ ⟨#Hpkg, %h, Htx⟩ HΦ
    have h' := h
    rw [interface_mkOk_inj] at h'
    obtain ⟨rfl, rfl⟩ := h'
    ihave Htx : isTxnT mw s γ trace (.read log rev) crev iprop(True) iprop(True) $$ [Htx]
    · simp only [isTxnT]; iexact Htx
    iapply (hRev trace mw s γ (.read log rev) crev iprop(True) iprop(True)) $$ [Htx] [HΦ]
    · iframe Hpkg Htx
    inext
    iintro Htx
    simp only [TxnKind.beginRev]
    iapply HΦ
    simp only [isTxnT]
    iframe Htx
    try (ipureintro; exact h)
  | succ m ih =>
    intro ty v mw s γ trace log rev crev
    simp only [roWrap]
    iintro %Φ ⟨#Hpkg, ⟨%trw, %ty', %v', %h, Hf, Hw⟩, Htx⟩ HΦ
    have h' := h
    rw [interface_mkOk_inj] at h'
    obtain ⟨rfl, rfl⟩ := h'
    rw [method_unfold (t := go.GoType.PointerType txnReadWrite.ty) (m := go!"Rev")]; wp_call
    (try wp_auto)
    iapply (ih ty' v' mw s γ trace log rev crev) $$ [Hw Htx] [HΦ Hf]
    · iframe Hpkg Hw Htx
    inext
    iintro ⟨Hw, Htx⟩
    iapply HΦ
    iframe Htx
    iexists trw, ty', v'
    iframe Hf Hw
    ipureintro; exact h

/-- A chain's `FirstRev`: the read transaction's compaction revision. -/
theorem ro_FirstRev (hFR : mvcc.metricsTxnWrite.FirstRev.spec (GF := GF) (hG := hG)) (n : Nat) :
    ∀ (ty : go.GoType) (v : val) (mw s : Loc) (γ : StoreNames) (trace : Loc) (log : Log)
      (rev : w64) (crev : Int),
    {{ pkgInit ∗ roWrap n (interface.mkOk ty v) mw ∗
        isTxnReadT mw s γ trace log rev crev iprop(True) iprop(True) }}
      (App (Val #(methods ty go!"FirstRev" v)) (Val #()))
    {{ RET #(W64 crev : w64); roWrap n (interface.mkOk ty v) mw ∗
        isTxnReadT mw s γ trace log rev crev iprop(True) iprop(True) }} := by
  induction n with
  | zero =>
    intro ty v mw s γ trace log rev crev
    simp only [roWrap]
    iintro %Φ ⟨#Hpkg, %h, Htx⟩ HΦ
    have h' := h
    rw [interface_mkOk_inj] at h'
    obtain ⟨rfl, rfl⟩ := h'
    iapply (hFR trace mw s γ log rev crev iprop(True) iprop(True)) $$ [Htx] [HΦ]
    · iframe Hpkg Htx
    inext
    iintro Htx
    iapply HΦ
    iframe Htx
    ipureintro; exact h
  | succ m ih =>
    intro ty v mw s γ trace log rev crev
    simp only [roWrap]
    iintro %Φ ⟨#Hpkg, ⟨%trw, %ty', %v', %h, Hf, Hw⟩, Htx⟩ HΦ
    have h' := h
    rw [interface_mkOk_inj] at h'
    obtain ⟨rfl, rfl⟩ := h'
    rw [method_unfold (t := go.GoType.PointerType txnReadWrite.ty) (m := go!"FirstRev")]; wp_call
    (try wp_auto)
    iapply (ih ty' v' mw s γ trace log rev crev) $$ [Hw Htx] [HΦ Hf]
    · iframe Hpkg Hw Htx
    inext
    iintro ⟨Hw, Htx⟩
    iapply HΦ
    iframe Htx
    iexists trw, ty', v'
    iframe Hf Hw
    ipureintro; exact h

/-- **`Txn.End.contract` at `*txnReadWrite`.** -/
theorem txnReadWrite.End.wp_api (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG)) :
    txnReadWrite.End.spec (GF := GF) := by
  intro t0 (γ : mvcc.StoreNames) trace k q B P Q
  iintro %Φ ⟨#Hpkg, Htx, Hk⟩ HΦ
  iapply wp_fupd
  iunfold mvccTxn at Htx
  cases k with
  | read σ =>
    simp only [mvccTxnI]
    icases Htx with ⟨%mw, %s, %n, -, Htx, Hback, Hwrap⟩
    iapply (ro_End hEnd n _ _ mw s γ trace σ.log _ σ.crev) $$ [Hwrap Htx] [HΦ Hback]
    · iframe Hpkg Hwrap Htx
    inext
    iintro Hrd
    iunfold tokBack at Hback
    imod Hback $$ Hrd with Hrt
    imodintro
    iapply HΦ
    iunfold mvccReaders
    iframe Hrt
  | write σ₀ pend =>
    simp only [mvccTxnI]
    icases Htx with ⟨%mw, %s, %p, %puts, %deletes, %putSize, -, -, -, -, Hwrap⟩
    iexfalso
    iapply wrWrap_pr t0 _ s mw σ₀.log $$ Hwrap

/-- **`Txn.Rev.contract` at `*txnReadWrite`.** -/
theorem txnReadWrite.Rev.wp_api (hRev : mvcc.metricsTxnWrite.Rev.spec (GF := GF) (hG := hG)) :
    ∀ t : Loc, Txn.Rev.contract (GF := GF) (go.GoType.PointerType txnReadWrite.ty) #t := by
  intro t0 (γ : mvcc.StoreNames) trace k
  iintro %Φ ⟨#Hpkg, Htx⟩ HΦ
  iunfold mvccTxn at Htx
  cases k with
  | read σ =>
    simp only [mvccTxnI, MTxn.state]
    icases Htx with ⟨%mw, %s, %n, %hre, Htx, Hback, Hwrap⟩
    iapply (ro_Rev hRev n _ _ mw s γ trace σ.log _ σ.crev) $$ [Hwrap Htx] [HΦ Hback]
    · iframe Hpkg Hwrap Htx
    inext
    iintro ⟨Hwrap, Htx⟩
    rw [← reach_rev hre]
    iapply HΦ
    iunfold mvccTxn
    simp only [mvccTxnI]
    iexists mw, s, n
    iframe Htx Hback Hwrap
    ipureintro; exact hre
  | write σ₀ pend =>
    simp only [mvccTxnI]
    icases Htx with ⟨%mw, %s, %p, %puts, %deletes, %putSize, -, -, -, -, Hwrap⟩
    iexfalso
    iapply wrWrap_pr t0 _ s mw σ₀.log $$ Hwrap

/-- **`Txn.FirstRev.contract` at `*txnReadWrite`.** -/
theorem txnReadWrite.FirstRev.wp_api
    (hFR : mvcc.metricsTxnWrite.FirstRev.spec (GF := GF) (hG := hG)) :
    ∀ t : Loc, Txn.FirstRev.contract (GF := GF) (go.GoType.PointerType txnReadWrite.ty) #t := by
  intro t0 (γ : mvcc.StoreNames) trace k
  iintro %Φ ⟨#Hpkg, Htx⟩ HΦ
  iunfold mvccTxn at Htx
  cases k with
  | read σ =>
    simp only [mvccTxnI]
    icases Htx with ⟨%mw, %s, %n, %hre, Htx, Hback, Hwrap⟩
    iapply (ro_FirstRev hFR n _ _ mw s γ trace σ.log _ σ.crev) $$ [Hwrap Htx] [HΦ Hback]
    · iframe Hpkg Hwrap Htx
    inext
    iintro ⟨Hwrap, Htx⟩
    iapply HΦ
    iunfold mvccTxn
    simp only [mvccTxnI]
    iexists mw, s, n
    iframe Htx Hback Hwrap
    ipureintro; exact hre
  | write σ₀ pend =>
    simp only [mvccTxnI]
    icases Htx with ⟨%mw, %s, %p, %puts, %deletes, %putSize, -, -, -, -, Hwrap⟩
    iexfalso
    iapply wrWrap_pr t0 _ s mw σ₀.log $$ Hwrap

/-- **`Txn.Changes.contract` at `*txnReadWrite`**: `nil`, of a read transaction. -/
theorem txnReadWrite.Changes.wp_api
    (hCh : mvcc.txnReadWrite.Changes.spec (GF := GF) (hG := hG)) :
    ∀ t : Loc, Txn.Changes.contract (GF := GF) (go.GoType.PointerType txnReadWrite.ty) #t := by
  intro t0 (γ : mvcc.StoreNames) trace k
  iintro %Φ ⟨#Hpkg, Htx⟩ HΦ
  cases k with
  | read σ =>
    iapply (hCh t0) $$ [] [HΦ Htx]
    · iexact Hpkg
    inext
    iintro -
    iapply HΦ
    iframe Htx
    ipureintro
    simp only [MTxn.pend, List.length_nil]
    exact ⟨rfl, by simp [slice.nil]⟩
  | write σ₀ pend =>
    iunfold mvccTxn at Htx
    simp only [mvccTxnI]
    icases Htx with ⟨%mw, %s, %p, %puts, %deletes, %putSize, -, -, -, -, Hwrap⟩
    iexfalso
    iapply wrWrap_pr t0 _ s mw σ₀.log $$ Hwrap

/-- **`Txn.Put.contract` at `*txnReadWrite`** (vacuous: no write transaction is a wrapper). -/
theorem txnReadWrite.Put.wp_api : txnReadWrite.Put.spec (GF := GF) := by
  intro t0 (γ : mvcc.StoreNames) trace te σ pend key value k vv leaseID L
  iintro %Φ ⟨#Hpkg, Htx, -⟩ HΦ
  iunfold mvccTxn at Htx
  simp only [mvccTxnI]
  icases Htx with ⟨%mw, %s, %p, %puts, %deletes, %putSize, -, -, -, -, Hwrap⟩
  iexfalso
  iapply wrWrap_pr t0 _ s mw σ.log $$ Hwrap

/-- **`Txn.DeleteRange.contract` at `*txnReadWrite`** (vacuous, as `Put`). -/
theorem txnReadWrite.DeleteRange.wp_api :
    ∀ t : Loc, Txn.DeleteRange.contract (GF := GF) (go.GoType.PointerType txnReadWrite.ty) #t := by
  intro t0 (γ : mvcc.StoreNames) trace σ pend key endk k e L
  iintro %Φ ⟨#Hpkg, Htx, -⟩ HΦ
  iunfold mvccTxn at Htx
  simp only [mvccTxnI]
  icases Htx with ⟨%mw, %s, %p, %puts, %deletes, %putSize, -, -, -, -, Hwrap⟩
  iexfalso
  iapply wrWrap_pr t0 _ s mw σ.log $$ Hwrap

end proof

end api
end mvcc
end EtcdGrove
end Perennial
