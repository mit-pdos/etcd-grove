/-
`(*EtcdServer).adjustTicks()` (`server.go`): the trust boundary (names-only; one of the goroutines `Start`
attaches). Lean-first (the request path's unit 4c).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReqOn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.adjustTicks()` returns (names-only: it advances the raft ticks of a fresh or rejoining member, then returns). It reads `s.Logger()` and logs through it (`lg.Info`), and reads the cluster, the raft
node and `s.Cfg`: its premise is the server's request-side fields (`isServerReqM`) and its logger
(`srvLoggerOk`; premise fixes 6, family axiom #22: until then nothing on `s`). -/
abbrev EtcdServer.adjustTicks.spec : Prop :=
  ∀ (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM on s E ρ ∗ srvLoggerOk s }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"adjustTicks")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
