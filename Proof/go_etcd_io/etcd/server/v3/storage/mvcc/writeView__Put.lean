/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.writeView__Put
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Write
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Put
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__End

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

theorem mvcc.writeView.Put.wp_proof
    (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (hWrite : mvcc.store.Write.spec (GF := GF) (hG := hG))
    (hPut : mvcc.metricsTxnWrite.Put.spec (GF := GF) (hG := hG))
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG)) :
    mvcc.writeView.Put.spec (GF := GF) (hG := hG) := by
  intro wv s γ P Pre Q Post f key value k v leaseID
  wp_start as ⟨#Hwv, Hrd, Htok, #Hhook, Hcs, #Hkey, #Hval, Hlease⟩
  iunfold mvcc.isWriteView at Hwv
  iNamed Hwv
  iunfold mvcc.csContract at Hcs
  icases Hcs with ⟨Hpre, #Htr, Hupd⟩
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply hTODO as %t %Ht
  (try wp_auto)
  -- `wv.kv.Write(trace)`
  wp_apply (hWrite s γ t P Pre Q f) $$ [$Hs $Hrd $Htok $Hhook $Hpre $Htr] as %mw ⟨⟨%ilog, Htx⟩, HQ⟩
  · ipureintro; exact Ht
  (try wp_auto)
  -- `tw.Put(key, value, lease)`
  wp_apply (hPut mw s γ ilog [] (W64 0) (W64 0) (W64 0) key value k v leaseID)
    $$ [$Htx $Hkey $Hval $Hlease] as Htx
  · ipureintro; simp
  (try wp_auto)
  -- the deferred `tw.End()`
  rw [List.nil_append]
  ihave Htx' : mvcc.isTxn mw s γ (.write ilog [.put k v leaseID] (W64 0 + W64 1) (W64 0)
      (W64 0 + (key.len + value.len))) $$ [Htx]
  · simp only [mvcc.isTxn]; iexact Htx
  -- the caller's update: the lock's invariant back for `Unlock`
  imod Hupd $$ HQ with ⟨HP, HPost⟩
  wp_apply (hEnd mw s γ _) $$ [$Htx' Hhook HP] as ⟨Hrd, Hcert⟩
  (try wp_auto)
  · iapply mvcc.txnEndPre_write; iframe Hhook HP
  iapply HΦ
  iframe Hrd HPost
  iexists ilog
  simp only [mvcc.txnEndPost, mvcc.commitLog, List.cons_ne_self, ↓reduceIte]
  icases Hcert with ⟨Hcert, -⟩
  iframe Hcert
  try (ipureintro; rfl)

end proof

end EtcdGrove
end Perennial
