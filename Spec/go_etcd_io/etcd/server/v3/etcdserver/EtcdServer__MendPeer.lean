/-
`(*EtcdServer).MendPeer(id)` (`server.go`): `s.r.transport.(*rafthttp.Transport).MendPeer(id)`, etcd's partition
hook (its integration tests' `InjectPartition`/`RecoverPartition`). Lean-first (no Rocq
counterpart); the partition plan's stage S2 (2026-10-20, `notes/partition-plan.md`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftHandler

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.MendPeer(id)`** on member `mid`'s server in the network `γn` (`srvNetMember`, which
`NewServer` gives): it returns; the member's transport (`srvNetMember`'s started
`*rafthttp.Transport`, which the type assertion finds) stops dropping the messages to and from the member `id` that `CutPeer` made it drop
(`rafthttp.Transport.MendPeer`'s axiom: within the network model, which lets any message be lost). -/
abbrev EtcdServer.MendPeer.spec : Prop :=
  ∀ (γn : NetNames GF) (s : Loc) (mid id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNetMember γn s mid }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"MendPeer")) (Val #id))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
