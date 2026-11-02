/-
`stop(m)` (`examples/restart3/restart3.go`; the restart plan's R2a, 2026-11-02; DRAFT): the
member's server stopped (`HardStop`), then its peer listener closed. Lean-first (no Rocq
counterpart).

**The triple:** from a stoppable member (`memberStop`) that was started (its request view, which
`common.memberUp` holds, at the names `ρ`), the member's data directory as the stop left it,
recording `ρ` (`srvDiskImage`, R2c), its peer address and the right to serve it with the member's raft
protocol back (`http.ListenerClose_spec`'s draft boundary), so that the member can be started
again there.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.restart3.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace restart3

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.restart3.Assumptions]

/-- See the file header. -/
abbrev stop.spec : Prop :=
  ∀ (m s : Loc) (pl : GoInterface) (γ : SrvRaft) (id : w64) (peerAddr : GoString)
    (γn : NetNames GF) (E : apply.AEnv GF) (ρ : ReqNames) (dd : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.restart3 ∗
      memberStop m s pl γ id peerAddr γn dd ∗ isServerReq s E ρ }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.restart3.stop)) (Val #m))
  {{ RET #(); srvDiskImage γ ρ id dd ∗ netAddrFree (GF := GF) peerAddr ∗
      http.httpProtoOwn peerAddr (raftProto (netRh γn)) }}

end spec

end restart3
end EtcdGrove
end Perennial
