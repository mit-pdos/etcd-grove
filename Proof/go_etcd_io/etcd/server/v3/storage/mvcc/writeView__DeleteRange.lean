/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.writeView__DeleteRange
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Write
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__DeleteRange
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__End
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.FrozenSpecs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
  have hWrite := mvcc.store.Write.spec_frozen hWrite
  have hEnd := mvcc.metricsTxnWrite.End.spec_frozen hEnd
  intro wv s γ P Pre Q Post f key endk k e
  wp_start as ⟨#Hwv, Hrd, Htok, Hwt, #Hhook, Hcs, #Hkey, #Hend, %Hb⟩
  iunfold mvcc.isWriteView at Hwv
  iNamed Hwv
  iunfold mvcc.csContract at Hcs
  icases Hcs with ⟨Hpre, #Htr, Hupd⟩
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply hTODO as %t %Ht
  (try wp_auto)
  -- `wv.kv.Write(trace)`
  wp_apply (hWrite s γ t P Pre Q f) $$ [$Hs $Hrd $Htok $Hwt $Hhook $Hpre $Htr] as %mw ⟨⟨%ilog, Htx⟩, HQ⟩
  · ipureintro; exact Ht
  (try wp_auto)
  -- `tw.DeleteRange(key, end)`
  wp_apply (hDel mw s γ ilog [] (W64 0) (W64 0) (W64 0) key endk k e)
    $$ [$Htx $Hkey $Hend] as %n %rev ⟨Htx, %Hnr⟩
  · ipureintro; simp only [List.length_nil, Nat.zero_add]; exact Hb ilog
  (try wp_auto)
  -- the deferred `tw.End()`
  rw [List.nil_append]
  ihave Htx' : mvcc.isTxn mw s γ (.write ilog
      ((mvcc.delKeys ilog [] (decide (endk = slice.nil)) k e).map .del) (W64 0)
      (W64 0 + W64 1) (W64 0)) $$ [Htx]
  · simp only [mvcc.isTxn]; iexact Htx
  ihave Htx' := mvcc.isTxn_toEnd _ _ _ _ $$ Htx'
  -- the caller's update: the lock's invariant back for `Unlock`
  imod Hupd $$ HQ with ⟨HP, HPost⟩
  wp_apply (hEnd mw s γ _) $$ [$Htx' Hhook HP] as ⟨Hrd, Hcert⟩
  (try wp_auto)
  · iapply mvcc.txnEndPre_write; iframe Hhook HP
  iapply HΦ
  iframe Hrd HPost
  iexists ilog
  simp only [mvcc.txnEndPost]
  icases Hcert with ⟨Hcert, -⟩
  iframe Hcert
  try (ipureintro; exact Hnr)

end proof

end EtcdGrove
end Perennial
