/-
`stop(m)` (`examples/etcd/restart/etcd_restart.go`; the restart plan's R2a, 2026-11-02; DRAFT): the
member's server stopped (`HardStop`), then its peer listener closed. Lean-first (no Rocq
counterpart).

**The triple:** from a stoppable member (`memberStop`, at the request names `ρ` its stop right
records) of a cluster whose bootstrap log has at most `NBoot` entries (`stop` waits until the
member applied `NBoot`, the evidence `HardStop` takes, R2b-2 review F2), the member's data directory as the stop left it, recording `ρ` (`srvDiskImage`, R2c), its peer address and the right to serve it with the member's raft
protocol back (`http.ListenerClose_spec`'s draft boundary), as the member's restart bundle
(`etcdstart.memberRestartRes`, hub step 8's E5, its data directory `name ++ ".etcd"`), so that the
member can be started again there. (R2b-2, 2026-11-02: until then also the request view `isServerReq`, which
`HardStop` no longer takes.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart.Assumptions]

/-- See the file header. -/
abbrev stop.spec : Prop :=
  ∀ (m s : Loc) (pl : GoInterface) (γ : SrvRaft) (id : w64) (peerAddr : GoString)
    (γn : NetNames GF) (ρ : ReqNames) (name : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restart ∗
      memberStop m s pl γ id peerAddr γn ρ (name ++ go!".etcd") ∗ ⌜γ.boot.length ≤ 3⌝ }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restart.stop)) (Val #m))
  {{ RET #(); etcdstart.memberRestartRes name ⟨some peerAddr, none⟩ γn γ ρ id }}

end spec

end etcd_restart
end EtcdGrove
end Perennial
