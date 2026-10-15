/-
`v3rpc.header.fill` (`header.go`). Lean-first (no Rocq counterpart); the vocabulary is
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

/-- **`h.fill(rh)`**: `fillWithoutRevision(rh)`, and `rh`'s revision set to the KV's (`rev()`)
if it was `0` (`hdrRevIn`/`hdrRevOut`). -/
abbrev v3rpc.header.fill.spec : Prop :=
  ∀ (hp s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64) (rh : Loc) (r : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ v3rpc.hdrIs hp s A cid mid ∗ v3rpc.hdrW rh ∗ v3rpc.hdrRevIn A.revR rh r }}
    (App (Val (hp @!! go.GoType.PointerType v3rpc.header.ty @!! go!"fill")) (Val #rh))
  {{ RET #(); v3rpc.hdrFilled rh cid mid ∗ ∃ r' : w64, v3rpc.hdrRevOut A.revR rh r r' }}

end spec

end EtcdGrove
end Perennial
