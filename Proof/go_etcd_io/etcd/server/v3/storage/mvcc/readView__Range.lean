/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.readView__Range
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Read
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Range
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.readView.Range.wp_proof
    (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (hRead : mvcc.store.Read.spec (GF := GF) (hG := hG))
    (hRange : mvcc.metricsTxnWrite.Range.spec (GF := GF) (hG := hG))
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG)) :
    mvcc.readView.Range.spec (GF := GF) (hG := hG) := by
  intro rv s γ ctx cd key endk k e ro
  wp_start as ⟨#Hrv, Hrd, #Hctx, #Hkey, #Hend⟩
  iunfold mvcc.isReadView at Hrv
  iNamed Hrv
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply hTODO as %t -
  (try wp_auto)
  -- `rv.kv.Read(ConcurrentReadTxMode, trace)`: the store's
  wp_apply (hRead s γ _ t) $$ [$Hs $Hrd] as %mw ⟨%log, %rev, Htx⟩
  (try wp_auto)
  -- `tr.Range(...)`: `metricsTxnWrite.Range`
  wp_apply (hRange mw s γ log rev ctx cd key endk k e ro) $$ [$Htx $Hctx $Hkey $Hend]
    as %r %err ⟨Htx, Hout⟩
  (try wp_auto)
  iunfold mvcc.isTxnRead at Htx
  iNamed Htx
  ihave #HtrT := Htr
  iunfold mvcc.storeTxnReadIs at HtrT
  iNamedSuffix HtrT "T"
  -- the deferred `tr.End()`: `metricsTxnWrite.End`
  ihave Htx : mvcc.isTxnRead mw s γ log rev $$ [Hmw Htrw Hmu HrevMu Hti]
  · iunfold mvcc.isTxnRead
    iexists trw, tr, trace, ti, rt, ranges
    iframe
    iframe #
  wp_apply (hEnd mw s γ log rev) $$ [$Htx] as Hrd
  (try wp_auto)
  iapply HΦ
  iframe Hrd
  iexists log, rev
  iframe HcertT Hout
  ipureintro
  exact ⟨HneT, HrevT⟩

end proof

end EtcdGrove
end Perennial
