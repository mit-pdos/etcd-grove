/-
`(*EtcdServer).isActive()` (`server.go`): whether the raft wrapper ticked within three tick intervals
(srvloops2, 2026-11-21, with `ensureLeadership`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeadCheck
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer

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

/-- `s.isActive()`, any goroutine, with `s.Cfg.TickMs` read-only, the leadership check's view of the
server (`srvLeadCheckOk`: `tickMu` and its pools) and one level `l` of a thread token, 3 or 4
(`rnTickLvlOk`), given back: some boolean (`latestTickTs.Add(3 * TickMs ms).After(time.Now())`, the
latest tick read under `tickMu`'s read lock with a reader slot borrowed from the pool at level `l`). -/
abbrev EtcdServer.isActive.spec : Prop :=
  ∀ (s : Loc) (tm : w64) (l : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvCfgFieldAddr s go!"TickMs" ↦□ tm ∗ srvLeadCheckOk s ∗ levelTok l ∗ ⌜rnTickLvlOk l⌝ }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"isActive")) (Val #()))
  {{ (b : Bool), RET #b; levelTok l }}

end spec

end EtcdGrove
end Perennial
