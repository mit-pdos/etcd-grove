/-
Proof of `Spec/.../mvcc/BytesToRev.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.BytesToRev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.BytesToBucketKey

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

theorem mvcc.BytesToRev.wp_proof (hBK : mvcc.BytesToBucketKey.spec (GF := GF) (hG := hG)) :
    mvcc.BytesToRev.spec (GF := GF) (hG := hG) := by
  intro s r rest dq hrest hm hs
  wp_start as Hs
  (try wp_auto)
  wp_apply (hBK s r rest dq hrest hm hs) $$ [$Hs] as Hs
  (try wp_auto)
  iapply HΦ $$ Hs

end proof

end EtcdGrove
end Perennial
