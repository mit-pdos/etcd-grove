/-
`clientv3.ensureWatchHeader(hdr)` (`client/v3/watch.go`; the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `ensureWatchHeader(hdr)`: `hdr` if it is not nil, otherwise a fresh zero header. -/
abbrev ensureWatchHeader.spec : Prop :=
  ∀ (hdr : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.ensureWatchHeader)) (Val #hdr))
  {{ (h : Loc), RET #h; ⌜h ≠ null⌝ ∗
      (⌜hdr ≠ null ∧ h = hdr⌝ ∨ ⌜hdr = null⌝ ∗ h ↦ (zero_val etcdserverpb.ResponseHeader)) }}

end spec

end EtcdGrove
end Perennial
