/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__End
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiLemmas
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnRead__End
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__End

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.metricsTxnWrite.End.wp_proof
    (hEnd : mvcc.storeTxnRead.End.spec (GF := GF) (hG := hG))
    (hEndW : mvcc.storeTxnWrite.End.spec (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG) := by
  intro trace mw s γ kind crev Z
  wp_start as ⟨Htx, Hpre⟩
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, ⟨%ct, #Hct, #HctS⟩, ⟨%cr, #Hcr, #HcrS⟩, ⟨%cp, #Hcp, #HcpS⟩,
    ⟨%cdl, #Hcd, #HcdS⟩, ⟨%g, #Hg, #HgS⟩, -⟩
  iunfold counterSpec at HctS HcrS HcpS HcdS
  iunfold gaugeSpec at HgS
  icases HctS with ⟨#HctI, -⟩
  icases HcrS with ⟨-, #HcrA, -⟩
  icases HcpS with ⟨-, #HcpA, -⟩
  icases HcdS with ⟨-, #HcdA, -⟩
  icases HgS with ⟨-, -, #HgA⟩
  cases kind with
  | read log rev =>
    simp only [mvcc.isTxnEnd, mvcc.txnEndPost]
    iunfold mvcc.isTxnRead at Htx
    iNamed Htx
    wp_apply wp_with_defer as %defer defer
    (try wp_auto)
    -- `if sum > 1 { txnCounter.Inc() }`
    wp_if_destruct
    all_goals
      (try wp_apply HctI)
      (try wp_auto)
      -- the counters and the gauge
      wp_apply HcrA
      (try wp_auto)
      wp_apply HcpA
      (try wp_auto)
      wp_apply HgA
      (try wp_auto)
      wp_apply HcdA
      (try wp_auto)
      -- the deferred `tw.TxnWrite.End()`: `txnReadWrite`'s promoted `End`, `storeTxnRead.End`
      rw [method_unfold (t := go.GoType.PointerType txnReadWrite.ty) (m := go!"End")]; wp_call
      (try wp_auto)
      ihave #Hs' : mvcc.isStore s (γ.withPhys p) $$ []
      · rw [mvcc.isStore_withPhys]; iexact Hs
      ihave HrevMu : sync.ownRWMutex (mvcc.revMuAddr s) (mvcc.revMuInv s (γ.withPhys p)) $$ [HrevMu]
      · rw [mvcc.revMuInv_withPhys]; iexact HrevMu
      wp_apply (hEnd tr s trace ti rt (γ.withPhys p) log rev crev Z) $$ [$Hs' $Htr $Hrd $Hmu $HrevMu $Hti] as ⟨Hrd, #HZ⟩
      (try wp_auto)
      rw [mvcc.storeReaderC_withPhys]
      iapply HΦ
      iframe Hrd HZ Htrc
      (try itrivial)
  | write ilog pend puts deletes putSize =>
    simp only [mvcc.isTxnEnd, mvcc.txnEndPost, mvcc.txnEndPre]
    icases Hpre with ⟨%P, %f, Hhook, HP⟩
    icases Htx with ⟨%chs, %ps, %sealed, %ld, Htx⟩
    iunfold mvcc.isTxnWriteCore at Htx
    iNamed Htx
    wp_apply wp_with_defer as %defer defer
    (try wp_auto)
    wp_if_destruct
    all_goals
      (try wp_apply HctI)
      (try wp_auto)
      wp_apply HcrA
      (try wp_auto)
      wp_apply HcpA
      (try wp_auto)
      wp_apply HgA
      (try wp_auto)
      wp_apply HcdA
      (try wp_auto)
      -- the deferred `tw.TxnWrite.End()`: `storeTxnWrite.End`
      wp_apply (hEndW trace tw s γ ilog pend chs ps sealed P f crev Z ld) $$ [$Htw $Hhook $HP] as ⟨Hrd, #HZ, #Hcert, Htok⟩
      (try wp_auto)
      iapply HΦ
      iframe Hrd HZ Htok Hcert Htrc

theorem mvcc.metricsTxnWrite.End.wp_proofA
    (hEnd : mvcc.storeTxnRead.End.spec (GF := GF) (hG := hG))
    (hEndW : mvcc.storeTxnWrite.End.specA (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.End.specA (GF := GF) (hG := hG) := by
  intro trace mw s γ kind crev Z Q
  wp_start as ⟨Htx, Hpre⟩
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, ⟨%ct, #Hct, #HctS⟩, ⟨%cr, #Hcr, #HcrS⟩, ⟨%cp, #Hcp, #HcpS⟩,
    ⟨%cdl, #Hcd, #HcdS⟩, ⟨%g, #Hg, #HgS⟩, -⟩
  iunfold counterSpec at HctS HcrS HcpS HcdS
  iunfold gaugeSpec at HgS
  icases HctS with ⟨#HctI, -⟩
  icases HcrS with ⟨-, #HcrA, -⟩
  icases HcpS with ⟨-, #HcpA, -⟩
  icases HcdS with ⟨-, #HcdA, -⟩
  icases HgS with ⟨-, -, #HgA⟩
  cases kind with
  | read log rev =>
    simp only [mvcc.isTxnEnd, mvcc.txnEndPostA, mvcc.txnEndPreA]
    iunfold mvcc.isTxnRead at Htx
    iNamed Htx
    wp_apply wp_with_defer as %defer defer
    (try wp_auto)
    -- `if sum > 1 { txnCounter.Inc() }`
    wp_if_destruct
    all_goals
      (try wp_apply HctI)
      (try wp_auto)
      -- the counters and the gauge
      wp_apply HcrA
      (try wp_auto)
      wp_apply HcpA
      (try wp_auto)
      wp_apply HgA
      (try wp_auto)
      wp_apply HcdA
      (try wp_auto)
      -- the deferred `tw.TxnWrite.End()`: `txnReadWrite`'s promoted `End`, `storeTxnRead.End`
      rw [method_unfold (t := go.GoType.PointerType txnReadWrite.ty) (m := go!"End")]; wp_call
      (try wp_auto)
      ihave #Hs' : mvcc.isStore s (γ.withPhys p) $$ []
      · rw [mvcc.isStore_withPhys]; iexact Hs
      ihave HrevMu : sync.ownRWMutex (mvcc.revMuAddr s) (mvcc.revMuInv s (γ.withPhys p)) $$ [HrevMu]
      · rw [mvcc.revMuInv_withPhys]; iexact HrevMu
      wp_apply (hEnd tr s trace ti rt (γ.withPhys p) log rev crev Z) $$ [$Hs' $Htr $Hrd $Hmu $HrevMu $Hti] as ⟨Hrd, #HZ⟩
      (try wp_auto)
      rw [mvcc.storeReaderC_withPhys]
      iapply HΦ
      iframe Hrd HZ Htrc Hpre
  | write ilog pend puts deletes putSize =>
    simp only [mvcc.isTxnEnd, mvcc.txnEndPostA, mvcc.txnEndPreA]
    icases Hpre with ⟨%P, %f, Hhook, HP⟩
    icases Htx with ⟨%chs, %ps, %sealed, %ld, Htx⟩
    iunfold mvcc.isTxnWriteCore at Htx
    iNamed Htx
    wp_apply wp_with_defer as %defer defer
    (try wp_auto)
    wp_if_destruct
    all_goals
      (try wp_apply HctI)
      (try wp_auto)
      wp_apply HcrA
      (try wp_auto)
      wp_apply HcpA
      (try wp_auto)
      wp_apply HgA
      (try wp_auto)
      wp_apply HcdA
      (try wp_auto)
      -- the deferred `tw.TxnWrite.End()`: `storeTxnWrite.End`
      wp_apply (hEndW trace tw s γ ilog pend chs ps sealed P f crev Z ld Q) $$ [$Htw $Hhook $HP] as ⟨Hrd, #HZ, #Hcert, Htok⟩
      (try wp_auto)
      iapply HΦ
      iframe Hrd HZ Htok Hcert Htrc

/-- **The candidate `End`** (`specC`, mvcc's candidate API): `specA`'s; a read transaction's ticket
back to the readers' pool for the thread token; a write transaction's commit update the caller's two
atomic updates (`absCommit_of_au`; a commit of nothing: both at once, no change, `commitAU_nil`),
on a store without watchers (`mvccWatchersOk`: a watched store commits only through the watchable
store's `End`). -/
theorem mvcc.metricsTxnWrite.End.wp_proofC (hA : mvcc.metricsTxnWrite.End.specA (GF := GF) (hG := hG)) :
    mvcc.metricsTxnWrite.End.specC (GF := GF) (hG := hG) := by
  intro mw γ trace k P f Q
  iintro %Φ ⟨#Hpkg, Htx, Hpre⟩ HΦ
  iapply wp_fupd
  cases k with
  | read σ =>
    icases (mvcc.mvccTxn_read_eq mw γ trace σ).1 $$ Htx with ⟨%s, -, #Hs, Hrd, Hloan⟩
    ihave #Hs1 := Hs
    iunfold mvcc.isMvccI at Hs1
    icases Hs1 with ⟨-, -, -, #Hpool, -, -⟩
    wp_apply (hA trace mw s γ.st (.read σ.log (W64 (σ.rev : Int))) σ.crev iprop(True) iprop(True))
      $$ [Hrd] as ⟨Hrdr, -, -, Htrc⟩
    · simp only [mvcc.isTxnEnd, mvcc.txnEndPreA]
      iframe Hrd
      try iframe #
    imod threadPool.giveBack mvcc.tixN γ.tl _ ⊤ (by simp) $$ [$Hpool $Hloan $Hrdr] with Htt
    imodintro
    iapply HΦ
    iframe Htt Htrc
  | write σ₀ pend =>
    icases Hpre with ⟨#Hwok, #Hhook, HP, Hau⟩
    iunfold mvcc.mvccTxn at Htx
    simp only [mvcc.mvccTxnI]
    icases Htx with ⟨%mw', %s, %puts, %deletes, %putSize, ⟨%Ht, %Hpn, -⟩, #Hs, Htxw, Hloan⟩
    simp only [interface_mkOk_inj, _root_.true_and] at Ht
    have hmw : mw' = mw := (GoGlobalContext.intoVal_inj_loc Ht).symm
    subst hmw
    ihave #Hs1 := Hs
    iunfold mvcc.isMvccI at Hs1
    icases Hs1 with ⟨-, %Hf, -, #Hpool, -, -⟩
    obtain ⟨habs, hwq, -, -⟩ := Hf
    ihave #Hhk := mvcc.mvccHook_hookOk γ P f $$ Hhook
    by_cases hp : pend = []
    · -- a commit of nothing: both updates at once, nothing changed
      subst hp
      icases mvcc.isTxnWrite_wrAt mw' s γ.st trace σ₀.log [] puts deletes putSize σ₀.crev iprop(True)
        false $$ Htxw with ⟨Hwr, Htxw⟩
      iunfold mvcc.wrAt at Hwr
      icases Hwr with ⟨HaW, HpW⟩
      imod mvcc.commitAU_nil γ habs Q $$ [Hau HpW] with ⟨HQ, HpW⟩
      · iframe HpW; iunfold mvcc.commitAU; iexact Hau
      ihave Htxw := Htxw $$ [HaW HpW]
      · iunfold mvcc.wrAt; iframe HaW HpW
      ihave Htx := mvcc.isTxn_toEnd mw' s γ.st (.write σ₀.log [] puts deletes putSize) σ₀.crev
        iprop(True) $$ [Htxw]
      · iunfold mvcc.isTxn; iexact Htxw
      wp_apply (hA trace mw' s γ.st (.write σ₀.log [] puts deletes putSize) σ₀.crev iprop(True) Q)
        $$ [Htx HP HQ] as ⟨Hrdr, -, Hpost, Htrc⟩
      · iframe Htx
        iframe #
        simp only [mvcc.txnEndPreA]
        iexists P, #f
        iframe Hhk HP
        rw [mvcc.logQPre_nil]
        isplitr; · itrivial
        unfold mvcc.absCommit
        rw [if_pos rfl]
        iexact HQ
      imod threadPool.giveBack mvcc.tixN γ.tl _ ⊤ (by simp) $$ [$Hpool $Hloan $Hrdr] with Htt
      imodintro
      iapply HΦ
      simp only [mvcc.txnEndPostA]
      icases Hpost with ⟨-, -, -, HQ⟩
      iframe Htt Htrc HQ
    · -- a commit: the caller's two updates at the bump, on a store without watchers
      iunfold mvcc.mvccWatchersOk at Hwok
      iunfold mvcc.mvccWatchersOkI at Hwok
      cases hwd : γ.watched
      · have hq : γ.st.watchQ = false := by rw [hwq, hwd]
        ihave Hac := mvcc.absCommit_of_au γ habs σ₀.log pend hp Q $$ [Hau]
        · iunfold mvcc.commitAU; iexact Hau
        ihave Htx := mvcc.isTxn_toEnd mw' s γ.st (.write σ₀.log pend puts deletes putSize) σ₀.crev
          iprop(True) $$ [Htxw]
        · iunfold mvcc.isTxn; iexact Htxw
        wp_apply (hA trace mw' s γ.st (.write σ₀.log pend puts deletes putSize) σ₀.crev iprop(True) Q)
          $$ [Htx HP Hac] as ⟨Hrdr, -, Hpost, Htrc⟩
        · iframe Htx
          try iframe #
          simp only [mvcc.txnEndPreA]
          iexists P, #f
          iframe Hhk HP Hac
          rw [mvcc.logQPre_plain γ.st σ₀.log pend hq]
          itrivial
        imod threadPool.giveBack mvcc.tixN γ.tl _ ⊤ (by simp) $$ [$Hpool $Hloan $Hrdr] with Htt
        imodintro
        iapply HΦ
        simp only [mvcc.txnEndPostA]
        icases Hpost with ⟨-, -, -, HQ⟩
        iframe Htt Htrc HQ
      · isimp only [hwd, ↓reduceIte] at Hwok
        icases Hwok with %hpe
        exact absurd hpe hp

end proof

end EtcdGrove
end Perennial
