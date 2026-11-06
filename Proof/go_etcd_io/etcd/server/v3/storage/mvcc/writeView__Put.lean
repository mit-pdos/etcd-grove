/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.writeView__Put
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Write
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Put
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__End
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ReaderSpecs

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

theorem mvcc.writeView.Put.wp_proof
    (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (hWrite : mvcc.store.Write.spec (GF := GF) (hG := hG))
    (hPut : mvcc.metricsTxnWrite.Put.spec (GF := GF) (hG := hG))
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG)) :
    mvcc.writeView.Put.spec (GF := GF) (hG := hG) := by
  have hWrite := mvcc.store.Write.spec_R hWrite
  have hEnd := mvcc.metricsTxnWrite.End.spec_R hEnd
  intro wv s γ P Pre Q Post f key value k v leaseID L I log G R
  wp_start as ⟨#Hwv, Hrd, Htok, Hwt, Hhook, Hpin, Hcs, #Hfree, #Hkey, #Hval, %Hklen, Hown, #HI, %Hlease, %Hwq, HG, #HFG, Hcb⟩
  iunfold mvcc.isWriteView at Hwv
  iNamed Hwv
  iunfold mvcc.csContract at Hcs
  icases Hcs with ⟨Hpre, #Htr, Hupd⟩
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply hTODO as %t ⟨%Ht, Htrc⟩
  (try wp_auto)
  -- `wv.kv.Write(t)`
  wp_apply (hWrite s γ t P Pre Q f true log) $$ [$Hs $Hrd $Htok $Hwt $Hhook $Hpin $Hpre $Htr $Htrc]
    as %mw ⟨⟨%ilog, %crev, Htx, -⟩, HQ, Hhook⟩
  · ipureintro; exact Ht
  -- the writer's hook back: its facts kept (D22 receiver epochs, S5b)
  icases (mvcc.hookIs_split γ P f).1 $$ Hhook with ⟨#HhookOk, Hfrag⟩
  ihave Hhook : mvcc.hookIs γ P f $$ [Hfrag]
  · iapply (mvcc.hookIs_split γ P f).2; iframe HhookOk Hfrag
  (try wp_auto)
  -- the owner's item map is the transaction's committed state's
  icases mvcc.isTxnWrite_cert _ _ _ _ _ _ _ _ _ _ _ _ $$ Htx with ⟨Htx, #Hc0⟩
  ihave %HIeq := HI $$ %ilog Hc0
  ihave Hown := lease.leaseOwn_eq HIeq.symm $$ Hown
  -- `tw.Put(key, value, lease)`
  wp_apply (hPut t mw s γ ilog [] (W64 0) (W64 0) (W64 0) key value k v leaseID L)
    $$ [$Htx $Hkey $Hval $Hown] as ⟨Htx, Hown⟩
  · ipureintro; exact ⟨Hklen, Hlease⟩
  (try wp_auto)
  -- the deferred `tw.End()`
  rw [List.nil_append]
  ihave Htx' : mvcc.isTxn mw s γ t (.write ilog [.put k v leaseID] (W64 0 + W64 1) (W64 0)
      (W64 0 + (key.len + value.len))) crev $$ [Htx]
  · simp only [mvcc.isTxn]; iexact Htx
  ihave Htx' := mvcc.isTxn_toEnd _ _ _ _ crev $$ Htx'
  ihave Htx' := mvcc.isTxnEnd_Y_write _ _ _ _ _ _ _ _ _ crev _ $$ Htx'
  ihave Hcb := Hcb $$ %ilog %crev
  -- the caller's update: the lock's invariant back for `Unlock`
  imod Hupd $$ HQ with ⟨HP, HPost⟩
  wp_apply (hEnd t mw s γ _ _ (mvcc.slotY γ ilog) G R) $$ [$Htx' Hhook HP HG Hcb] as ⟨Hrd, Hcert, -, HX⟩
  (try wp_auto)
  · isplitl [Hhook HP]
    · iapply mvcc.txnEndPre_write; iframe Hhook HP; rw [mvcc.logQPre_plain _ _ _ Hwq]
      isplitl; · iapply mvcc.certFree_certOkNext $$ Hfree
      itrivial
    simp only [mvcc.txnEndX]
    iframe HG HFG Hcb
  simp only [mvcc.txnEndPost, mvcc.txnEndXPost, mvcc.commitLog, List.cons_ne_self, ↓reduceIte]
  icases Hcert with ⟨Hcert, -, -, -⟩
  icases HX with ⟨HG, HR⟩
  iapply HΦ
  iframe Hrd HPost HG HR
  iexists ilog
  iframe Hcert Hown
  try (ipureintro; rfl)

end proof

end EtcdGrove
end Perennial
