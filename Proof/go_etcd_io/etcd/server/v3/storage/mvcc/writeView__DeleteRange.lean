/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.writeView__DeleteRange
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Write
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__DeleteRange
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

theorem mvcc.writeView.DeleteRange.wp_proof
    (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (hWrite : mvcc.store.Write.spec (GF := GF) (hG := hG))
    (hDel : mvcc.metricsTxnWrite.DeleteRange.spec (GF := GF) (hG := hG))
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG)) :
    mvcc.writeView.DeleteRange.spec (GF := GF) (hG := hG) := by
  have hWrite := mvcc.store.Write.spec_R hWrite
  have hEnd := mvcc.metricsTxnWrite.End.spec_R hEnd
  intro wv s γ P Pre Q Post f key endk k e L I
  wp_start as ⟨#Hwv, Hrd, Htok, Hwt, Hhook, Hcs, #Hfree, #Hkey, #Hend, Hown, #HI, %Hwq⟩
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
  wp_apply (hWrite s γ t P Pre Q f true) $$ [$Hs $Hrd $Htok $Hwt $Hhook $Hpre $Htr $Htrc] as %mw ⟨⟨%ilog, %crev, Htx, -⟩, HQ, Hhook⟩
  · ipureintro; exact Ht
  -- the writer's hook back: its facts kept (D22 receiver epochs, S5b)
  icases (mvcc.hookIs_split γ P f).1 $$ Hhook with ⟨#HhookOk, Hfrag⟩
  ihave Hhook : mvcc.hookIs γ P f $$ [Hfrag]
  · iapply (mvcc.hookIs_split γ P f).2; iframe HhookOk Hfrag
  (try wp_auto)
  -- `tw.DeleteRange(key, end)`
  icases mvcc.isTxnWrite_cert _ _ _ _ _ _ _ _ _ _ _ _ $$ Htx with ⟨Htx, #Hc0⟩
  ihave %HIeq := HI $$ %ilog Hc0
  ihave Hown := lease.leaseOwn_eq HIeq.symm $$ Hown
  wp_apply (hDel t mw s γ ilog [] (W64 0) (W64 0) (W64 0) key endk k e L)
    $$ [$Htx $Hkey $Hend $Hown] as %n %rev ⟨Htx, Hown, %Hnr⟩
  (try wp_auto)
  -- the deferred `tw.End()`
  rw [List.nil_append]
  ihave Htx' : mvcc.isTxn mw s γ t (.write ilog
      ((mvcc.delKeys ilog [] (decide (endk = slice.nil)) k e).map .del) (W64 0)
      (W64 0 + W64 1) (W64 0)) crev $$ [Htx]
  · simp only [mvcc.isTxn]; iexact Htx
  ihave Htx' := mvcc.isTxn_toEnd _ _ _ _ crev $$ Htx'
  -- the caller's update: the lock's invariant back for `Unlock`
  imod Hupd $$ HQ with ⟨HP, HPost⟩
  wp_apply (hEnd t mw s γ _) $$ [$Htx' Hhook HP] as ⟨Hrd, Hcert, -⟩
  (try wp_auto)
  · iapply mvcc.txnEndPre_write; iframe Hhook HP; rw [mvcc.logQPre_plain _ _ _ Hwq]
    isplitl; · iapply mvcc.certFree_certOkNext $$ Hfree
    itrivial
  simp only [mvcc.txnEndPost]
  icases Hcert with ⟨Hcert, -, -, -⟩
  iapply HΦ
  iframe Hrd HPost
  iexists ilog
  iframe Hcert Hown
  try (ipureintro; exact Hnr)

end proof

end EtcdGrove
end Perennial
