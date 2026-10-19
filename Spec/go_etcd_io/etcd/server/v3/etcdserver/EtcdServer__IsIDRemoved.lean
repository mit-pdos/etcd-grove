/-
`(*EtcdServer).IsIDRemoved` (`server.go`): `s.cluster.IsIDRemoved(id)`. Lean-first (no Rocq counterpart); D21 stage M2
(2026-10-19): the inbound path from the transport (`rafthttp.Raft`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvNet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.IsIDRemoved(x)`** returns `false`: the cluster removes no member (`rcLockInv`). -/
abbrev EtcdServer.IsIDRemoved.spec : Prop :=
  ∀ (γn : NetNames GF) (s : Loc) (id x : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvProcOk γn s id }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"IsIDRemoved")) (Val #x))
  {{ RET #false; True }}

end spec

end EtcdGrove
end Perennial
