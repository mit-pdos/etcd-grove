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

end proof

end api
end mvcc
end EtcdGrove
end Perennial
