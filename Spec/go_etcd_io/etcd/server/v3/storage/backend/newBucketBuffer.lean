/-
`newBucketBuffer` (`tx_buffer.go`). `newBucketBuffer()`: a writable buffer with no entries (512 slots).
Lean-first (no Rocq counterpart); see `InvBuffer.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBuffer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `newBucketBuffer()`: a writable buffer with no entries (512 slots). -/
abbrev backend.newBucketBuffer.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend }}
    (App (Val (@! newBucketBuffer)) (Val #()))
  {{ (bb : Loc), RET #bb; ownBB bb [] }}

end spec

end EtcdGrove
end Perennial
