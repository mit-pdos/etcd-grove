/-
## `(*EtcdServer).GoAttach(f)` (`server.go:2436-2453`)

**Users.** `Start` (ten goroutines), `revokeExpiredLeases` (2d), `sendMergedSnap` (2d), v3rpc's
`Snapshot` (2a). Snippet: none of its own (`Start`'s users).

**Proof sketch.** `isServer`'s realization holds `wgMu` and the wait group (a wait group backed by
thread tokens: the bounds plan) whose `Wait` is `run`'s stop. Under the read lock: if `stopping` is
closed, skip (the closure's resources are dropped: a goroutine that must give something back keeps
it in an invariant of its own, as the purge's right, `srvPurge`); else `wg.Add(1)` and fork `f`
with its WP, `Done` after.

**Changes** (from `specs-ref`'s `EtcdServer__GoAttach.lean`): over `isServer`.

**Round 1 (provability F6).** The goroutine's `threadTok` is the caller's (the bounds plan: the
wait group is backed by thread tokens); a skipped `f` drops it.

**Verify round (A7-provability F1, completeness F1).** The caller keeps its `threadTok` (its
level deposited at `wg.Add(1)` comes back at the `go`: Perennial's leveled `tokJoinL`), and
`f` runs with the fork's fresh token and ends with one (Perennial's `wp_fork_tok_body`): the
attached goroutines of `revokeExpiredLeases` (up to `maxPendingRevokes` at once), the `NOSPACE`
alarm, `sendMergedSnap` and `Start`'s ten each have their own. The level accounting (the
group's level-0 slot against the goroutine's whole token) is the bounds plan's: a decision
recorded in `verify/repair-server-core.md`.

**Margin.** The post does not say whether `f` ran.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Runs `f` on a goroutine the server's stop waits for**, unless the server is stopping. -/
def EtcdServer.GoAttach.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (f : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ threadTok ∗
      (threadTok -∗ WP (App (Val #f) (Val #())) {{ fun _ => threadTok }}) }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"GoAttach")) (Val #f))
  {{ RET #(); threadTok }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
