/-
`(*streamReader).resume` (`stream.go`; rafthttp stage 5b). Lean-first; the reader's predicates:
`rafthttp/Reader.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Reader

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`cr.resume()`**: `paused` set to `false` (under `mu`). -/
abbrev rafthttp.streamReader.resume.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (lid pid : w64) (γd : GName) (cr : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      srFixed Rh lid pid γd cr }}
    (App (Val (cr @!! go.GoType.PointerType rafthttp.streamReader.ty @!! go!"resume")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
