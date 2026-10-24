/-
`(*EtcdServer).CutPeer(id)` (`server.go`): `s.r.transport.(*rafthttp.Transport).CutPeer(id)`, etcd's partition
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

/-- **`s.CutPeer(id)`** on member `mid`'s server in the network `γn` (`srvNetMember`, which
`NewServer` gives, with its transport `τ`), with one of the transport's reader tokens
(`srvTrTok`): it returns the token; the member's transport (`τ.t`, which the type assertion finds)
drops the messages to and from the member `id` (until `MendPeer`) (`rafthttp.Transport.CutPeer`: within the network model, which lets any message be lost;
2026-10-24, rafthttp stage 6d: proved, with the token its read lock takes). The method set's
premise `PeerPausable` (`*peer` implements `Pausable`). -/
abbrev EtcdServer.CutPeer.spec : Prop :=
  PeerPausable → ∀ (γn : NetNames GF) (s : Loc) (mid id : w64) (τ : SrvTr GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvNetMember γn s mid τ ∗ srvTrTok γn τ }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"CutPeer")) (Val #id))
  {{ RET #(); srvTrTok γn τ }}

end spec

end EtcdGrove
end Perennial
