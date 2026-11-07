/-
**`Txn.End.contract` at `*metricsTxnWrite`** (M4, track B, 2026-11-06). Lean-first (no Rocq
counterpart). Over the sealed definitions of `Api.lean` (imported with `import all`).

A read transaction ends by `metricsTxnWrite.End` with no step, its reader back to the pool (`tokBack`).
A write transaction (a store without watchers) ends at the backend share's names, which are the
transaction's (the share's objects agree with the transaction's `s.mu` share's, `curAt_agree`): its
batch lock's invariant by `mvccBackend`'s `hookP`, the frozen state excluded by the share's token
(`slotF_share_excl`), the writer's slot at the begin state (`Yat`: the slot's compaction revision is the
transaction's, `muHeld_wcr`), and the commit's step from the client's nested update (`endCb_of_au`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.EndSteps
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.Instance
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.WriteCtx
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

/-- **A write transaction ready to end at its begin state**: its key-values dropped, the writer's
slot at `σ` (`Yat`, the slot's compaction revision being the transaction's), and the transaction's
physical names those of any share of the store's current objects. -/
theorem isTxnWriteT_endY (mw s : Loc) (γ : StoreNames) (p p' : PhysNames) (trace : Loc)
    (ilog : Log) (pend : List Change) (puts deletes putSize : w64) (crev : Int) (Z Tr : IProp GF)
    (σ : MvccState) (dq : DFrac) (o' : StoreObjs) (hl : σ.log = ilog) (hc : σ.crev = crev) :
    isTxnWriteT (GF := GF) mw s (γ.withPhys p) trace ilog pend puts deletes putSize crev Z false Tr ∗
      curAt (γ.withPhys p') dq o' ⊢
      isTxnEndY mw s (γ.withPhys p) trace (.write ilog pend puts deletes putSize) crev Z
        (Yat (γ.withPhys p) σ) Tr ∗ curAt (γ.withPhys p') dq o' ∗ ⌜p = p'⌝ := by
  subst hl hc
  iintro ⟨H, Hc⟩
  iunfold isTxnWriteT at H
  iNamed H
  icases storeTxnWriteIs_split tw s (γ.withPhys p) σ.log pend σ.crev Z false $$ Htw
    with ⟨%chs, %ps, Hcore, -, -⟩
  iunfold storeTxnWriteCore at Hcore
  iNamed Hcore
  -- the names: the transaction's share of the current objects and the caller's
  icases muHeld_cur s (γ.withPhys p) σ.crev ti $$ Hmu with ⟨%o, %Ho, Hpin, Hmub⟩
  ihave %Hv := curAt_agree (γ.withPhys p) (γ.withPhys p') rfl _ _ o o' $$ [Hpin Hc]
  · iframe Hpin Hc
  ihave Hmu := Hmub $$ Hpin
  -- the writer's slot at the transaction's compaction revision
  iunfold slotY at HY
  icases HY with ⟨%cy, HYa, HYp, HYr, HYw⟩
  icases muHeld_wcr s (γ.withPhys p) σ.crev ti _ cy $$ [$Hmu $HYw]
    with ⟨Hmu, HYw, %Hcy⟩
  subst Hcy
  iframe Hc
  isplitl
  · simp only [isTxnEndY]
    iexists chs, ps, false, false
    iunfold isTxnWriteCoreY
    iexists tw, ranges
    iframe Hmw Htrc
    iunfold storeTxnWriteCoreY
    iexists ti, bt, Locked, ntok, Pw, fw, Dep
    simp only [named]
    iframe Htoks Htok Htw Hcap Hlocked Hw Hclog Hcur Hbv Hwv Htko Hmu HrevMu Hti Hrt Hcres Hlrd
    iframe #
    iunfold Yat
    iframe HYa HYp HYr HYw
    ipureintro; exact ⟨Hbudget, Hps, Hne, Htrnn, Hcrev⟩
  ipureintro; exact Hv.2

/-- **`Txn.End.contract` at `*metricsTxnWrite`.** -/
theorem metricsTxnWrite.End.wp_api (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG)) :
    metricsTxnWrite.End.spec (GF := GF) := by
  intro t0 (γ : mvcc.StoreNames) trace k q B P Q
  iintro %Φ ⟨#Hpkg, Htx, Hk⟩ HΦ
  iapply wp_fupd
  iunfold mvccTxn at Htx
  cases k with
  | read σ =>
    simp only [mvccTxnI]
    icases Htx with ⟨%mw, %s, %n, -, Htx, Hback, Hwrap⟩
    ihave %Hmw := roWrap_pm n t0 mw $$ Hwrap
    obtain ⟨hm, -⟩ := Hmw
    subst hm
    ihave Hte : isTxnEndY t0 s γ trace (.read σ.log (W64 ((σ.log.length : Int) - 1))) σ.crev iprop(True)
        iprop(True) iprop(True) $$ [Htx]
    · simp only [isTxnEndY]; iexact Htx
    ihave Hep : txnEndPreH γ (.read σ.log (W64 ((σ.log.length : Int) - 1))) $$ []
    · simp only [txnEndPreH]; itrivial
    ihave Hx : txnEndX γ (.read σ.log (W64 ((σ.log.length : Int) - 1))) σ.crev iprop(True) iprop(True)
        iprop(True) $$ []
    · simp only [txnEndX]; itrivial
    iapply (hEnd trace t0 s γ (.read σ.log (W64 ((σ.log.length : Int) - 1))) σ.crev iprop(True)
        iprop(True) iprop(True) iprop(True) iprop(True)) $$ [Hte Hep Hx] [HΦ Hback]
    · iframe Hpkg Hte Hep Hx
    inext
    iintro ⟨Hrd, -, -, -, -⟩
    iunfold tokBack at Hback
    imod Hback $$ Hrd with Hrt
    imodintro
    iapply HΦ
    iunfold mvccReaders
    iframe Hrt
  | write σ₀ pend =>
    simp only [mvccTxnI]
    icases Htx with ⟨%mw, %s, %p, %puts, %deletes, %putSize, %Hk0, Htx, Hback, #Hfree, Hwrap⟩
    obtain ⟨Hpn, -⟩ := Hk0
    ihave %Hw := wrWrap_pm t0 _ s mw σ₀.log $$ Hwrap
    obtain ⟨hm, Hwq⟩ := Hw
    subst hm
    icases Hk with ⟨HB, HP, Hau⟩
    -- the backend share, at the transaction's names
    iunfold mvccBackend at HB
    icases HB with ⟨HF, %p', %o', %d, Hcur', %Hd, #Hbk, #Hrg, #Hhp, #Hwts, %Hlp⟩
    icases isTxnWriteT_endY t0 s γ p p' trace σ₀.log pend puts deletes putSize σ₀.crev iprop(True)
        iprop(True) σ₀ _ o' rfl rfl $$ [$Htx $Hcur'] with ⟨Hte, Hcur', %hpp⟩
    subst hpp
    have hwq' : (γ.withPhys p).watchQ = false := by simpa using Hwq
    -- the commit's step from the client's update
    iunfold mvccState at Hau
    have hcb := endCb_of_au (GF := GF) (γ.withPhys p) σ₀ σ₀.log pend σ₀.crev Q hwq' rfl Hpn
    simp only [endAU, StoreNames.withPhys_api] at hcb
    ihave Hcb := hcb $$ Hau
    ihave #Hx : □ (slotF (γ.withPhys p) ∗ api.shareTok γ.api q -∗ False) $$ []
    · iintro !> H
      iapply (slotF_share_excl (γ := γ.withPhys p) (a := γ.api) rfl q) $$ H
    ihave #Hok := certFree_certOkNext (γ.withPhys p) σ₀.log pend $$ Hfree
    iapply (hEnd trace t0 s (γ.withPhys p) (.write σ₀.log pend puts deletes putSize) σ₀.crev
        iprop(True) (Yat (γ.withPhys p) σ₀) (api.shareTok γ.api q) Q iprop(True))
        $$ [Hte HP HF Hcb] [HΦ Hback Hcur']
    · iframe Hpkg Hte
      isplitl [HP]
      · simp only [txnEndPreH]
        iexists P
        iframe Hhp HP Hok
        rw [logQPre_plain _ _ _ hwq']
        itrivial
      simp only [txnEndX]
      iframe HF Hcb Hx
    inext
    iintro ⟨Hrd, -, -, -, HGR⟩
    simp only [txnEndXPost]
    icases HGR with ⟨HF, HQ⟩
    iunfold tokBack at Hback
    imod Hback $$ Hrd with Hrt
    ihave Hrt : ownToks (GF := GF) γ.api.rdk 1 $$ [Hrt]
    · rw [show γ.api = (γ.withPhys p).api from rfl]; iexact Hrt
    imodintro
    iapply HΦ
    iunfold mvccReaders
    iframe Hrt HQ
    iunfold mvccBackend
    iframe HF
    iexists p, o', d
    iframe Hcur' Hbk Hrg Hhp Hwts
    ipureintro; exact ⟨Hd, Hlp⟩


end proof

end api
end mvcc
end EtcdGrove
end Perennial
