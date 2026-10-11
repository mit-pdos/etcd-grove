/-
Proof of `Spec/.../mvcc/storeTxnCommon__Range.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnCommon__Range
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnCommon__Rev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnCommon__rangeKeys

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

theorem mvcc.storeTxnCommon.Range.wp_proof (hRev : mvcc.storeTxnCommon.Rev.spec (GF := GF) (hG := hG))
    (hKeys : mvcc.storeTxnCommon.rangeKeys.spec (GF := GF) (hG := hG)) :
    mvcc.storeTxnCommon.Range.spec (GF := GF) (hG := hG) := by
  intro tr s trace ti rt γ log rev ctx cd key endk k e ro
  wp_start as ⟨#Hs, #Htr, #Hidx, Hti, #Hctx, #Hkey, #Hend⟩
  ihave #Htr0 : mvcc.storeTxnReadIs tr s rt trace γ log rev $$ []
  · iexact Htr
  iunfold mvcc.storeTxnReadIs at Htr
  iNamedSuffix Htr "T"
  (try wp_auto)
  wp_apply (hRev (mvcc.txCommon tr) rev) $$ [$HrevT]
  (try wp_auto)
  wp_apply (hKeys tr s trace ti rt γ log rev ctx cd key endk k e ro)
    $$ [$Hs $Htr0 $Hidx $Hti $Hctx $Hkey $Hend] as %r %err ⟨Hti, Hout⟩
  (try wp_auto)
  iapply HΦ
  iframe Hti Hout

end proof

end EtcdGrove
end Perennial
