/-
Proof of `Spec/.../mvcc/RevToBytes.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.RevToBytes
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newBucketKey
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.BucketKeyToBytes

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.RevToBytes.wp_proof (hNew : mvcc.newBucketKey.spec (GF := GF) (hG := hG))
    (hBK : mvcc.BucketKeyToBytes.spec (GF := GF) (hG := hG)) :
    mvcc.RevToBytes.spec (GF := GF) (hG := hG) := by
  intro rev s bs hlen
  wp_start as ⟨Hs, Hcap⟩
  (try wp_auto)
  wp_apply (hNew rev.Main' rev.Sub' false)
  (try wp_auto)
  wp_apply (hBK (BucketKey.mk (Revision.mk rev.Main' rev.Sub') false) s bs hlen) $$ [$Hs $Hcap]
    as %s' ⟨Hs, Hcap⟩
  (try wp_auto)
  iapply HΦ
  rw [mvcc.bucketKeyBytes_false, show Revision.mk rev.Main' rev.Sub' = rev from rfl]
  iframe Hs Hcap

end proof

end EtcdGrove
end Perennial
