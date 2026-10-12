/-
`v3rpc.header.fillWithoutRevision` (`header.go`). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvKV.lean` and `Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvKV

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`h.fillWithoutRevision(rh)`**: `rh` (not nil: `nil` panics) gets the header's cluster and
member ids and the server's current term and leader. -/
abbrev v3rpc.header.fillWithoutRevision.spec : Prop :=
  ∀ (hp s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64) (rh : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ v3rpc.hdrIs hp s A cid mid ∗ v3rpc.hdrW rh }}
    (App (Val (hp @!! go.GoType.PointerType v3rpc.header.ty @!! go!"fillWithoutRevision"))
      (Val #rh))
  {{ RET #(); v3rpc.hdrFilled rh cid mid }}

end spec

end EtcdGrove
end Perennial
