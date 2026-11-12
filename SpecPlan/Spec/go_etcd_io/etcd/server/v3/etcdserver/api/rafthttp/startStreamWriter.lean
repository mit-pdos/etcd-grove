/-
## `startStreamWriter(lg, local, id, status, fs, r)`

**Users.** `startPeer` (twice).

**Proof sketch.** The literal, its channels (`msgc`: `msgChanAt`), the lock invariant (`swLocked`), the fork of `run` with `swRun`.

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rafthttp

open Iris Iris.BI Raft
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) **Starts a stream writer** for peer `pid` (its `run` goroutine), not yet working. -/
def startStreamWriter.spec : Prop :=
  ∀ (lg : Loc) (ν : Net GF) (lid pid : w64) (st fs : Loc) (r : GoInterface) (K : Msg → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ (⌜lg = null⌝ ∨ Zap.isLogger lg) ∗ statusAt st ∗ followerStatsOk fs ∗ raftOk ν lid r }}
    (App (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.startStreamWriter)) (Val #lg)) (Val #lid)) (Val #pid)) (Val #st)) (Val #fs)) (Val #r))
  {{ (cw : Loc), RET #cw; swAt cw ν lid pid K ∗ swStopRight cw }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
