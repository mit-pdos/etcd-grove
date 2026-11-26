/-
**A started member whose lessor is at a given name** (F2's P-L1, PROPOSED with `Serve_dist.spec_proposed`,
2026-11-26; the auth-lease review's F2, `/shared/tmp/coord-03/rev-f7c-report.md`). Lean-first (no Rocq
counterpart). Definitions only; nothing uses them but the proposed text.

`etcdstart.memberUpL s ρ E₀ lg γn id m γl` is `etcdstart.memberUp s ρ E₀ lg γn id m` with its server's
environment's lessor name `mvcc.api.mvccLeases E.γ` equal to `γl`: the name the lessor was made at
(`lease.NewLessor.specAt`, through `NewServer.specG_dist_proposed`'s `mvccLeases E.γ = γl`). Through
`Serve_dist`'s exclusive resources (the member's start), it ties the view's `Γ.ls mid` to the serving member's
real lessor; `etcdAddr_set` mints address facts for any `Γ`, so `Serve_dist`'s premise is the only place that can.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`memberUp` with the lessor at `γl`** (PROPOSED, see the file header): `memberUp`'s body verbatim, and
`mvcc.api.mvccLeases E.γ = γl` for its environment `E`. -/
def memberUpL (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) (m : lease.Mode) (γl : GName) : IProp GF :=
  iprop(∃ (E : apply.AEnv GF) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (γw : GName),
    ⌜envAgree E E₀ ∧ E.authOn = false ∧ cfg.Logger' = lg ∧ cfg.TracerOptions' = slice.nil ∧
      cfg.WatchProgressNotifyInterval' = 0 ∧ mvcc.api.mvccLeases E.γ = γl⌝ ∗
    srvServeStock s E ∗ srvRunReadStock s ρ.rd ∗
    isServerReq s E { ρ with wait := γw } ∗ isServerRead s E ρ.rd ∗ srvGoRes s ∗ srvLgReader s ∗
    ([∗list] _x ∈ List.replicate memberReadN (), srvReadReader s ρ.rd) ∗
    srvWatchBuilt s E ∗ srvServeFacts s E cfg ∗
    srvBemuReader s ∗
    srvPeerCtl γn s id ∗ srvLeaseRd s E m ∗
    (∃ dd : GoString, srvStopRight s E ρ.rd.raft.raft ρ id dd))

end defs

end etcdstart
end EtcdGrove
end Perennial
