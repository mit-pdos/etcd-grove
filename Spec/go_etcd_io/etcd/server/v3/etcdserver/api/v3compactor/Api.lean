/-
# The auto-compactor (`etcdserver/api/v3compactor`): vocabulary (batch 2e)

The compactor proposes compactions on its own schedule (periodic: the revision of `retention` ago;
revision: the current revision minus `retention`), through the server's `Compact`. In W0's model
an auto-compaction is an environment step (`EnvStep.compact`, any revision above the compaction
revision and at most the current one, when the cluster's `EnvCfg.autoCompact`), so the compactor
needs no permit of its own (the old proof's `modePermit`/`compactableOk` at C1's permit served a
model without environment compactions): **its safety is that it calls `Compact` and `Rev` safely**.
That the server's `Compact`, called by the compactor, changes the state only by `EnvStep.compact`
is the server's to prove when it builds the `Compactable` it hands to `New` (`NewServer`'s proof:
from 2c's `EtcdServer.Compact.spec` and `envUpd γ ecfg` with `ecfg.autoCompact = true`, which
`bootCfg_build` gives: a step that answers an error leaves the state as it was, and the
environment's update is then aborted).

## Vocabulary

* `bootCfg mode ret ac` (sealed `Prop`, **the compactor's slot** of `NewServer`; the slot
  convention, `.claude/skills/spec/examples/compactor-slot.md`): the compactor's configuration
  (`AutoCompactionMode`, `AutoCompactionRetention`) against the environment's compaction mode `ac`
  (`EnvCfg.autoCompact`): off (`ret = 0`), or on with the environment allowing auto-compaction and,
  in periodic mode, `ret ≥ 10ns` or `ret ≤ -10ns` (`newPeriodic` divides by `ret / 10`: a smaller period panics,
  `periodic.go:getRetentions`). Intro laws `bootCfg_off`, `bootCfg_on`; one narrow elimination,
  `bootCfg_build` (what `NewServer`'s proof hands `New` and the `Compactable`'s construction).
  Kubernetes' deployment (compaction by clients, the compactor off) is `bootCfg_off` at any `ac`.
* `compactable c R` (persistent): **the interface value `c` (`Compactable`) may be called once `R`
  holds**: under `□ R`, for a child of `context.Background()` (the compactor's own context,
  `WithCancel(Background())`, `periodic.go:61`, `revision.go:58`) and a fresh, non-physical compaction request,
  `Compact` returns (any response, any error). The receiver's need (PRINCIPLES, "A contract between
  packages states the receiver's need"). Verify-round (A7 completeness F2): the gate `R` and the
  context's shape are new: the server makes the compactor in `NewServer`, before `start`, and its
  `Compact` needs the started server (`s.w` is nil before `start`: a panic) and a context with no
  incoming metadata; `R` is what `start` publishes (2d's choice, as 3c's `ckptGate`), and only
  `Run` (called by `start`) needs `□ R`.
* `revGetter rg` (persistent): `rg.Rev()` returns (any `int64`), at any time, also after the store
  is closed (3e's obligation: `req/go_etcd_io_etcd_server_v3_storage_mvcc.md`, "from 2e").
* `isCompactor cp R` (persistent): `cp` is a `Compactor` (`*Periodic` or `*Revision`) over a
  `compactable` gated by `R` and a `revGetter`: `Run` (with `□ R`), `Pause`, `Resume`, `Stop` may be
  called any number of times, from any goroutine (each takes the compactor's mutex or cancels its
  context; `Run` forks the loop, which exits once the context is cancelled).
* `isPeriodic p R`, `isRevision r R` (persistent): the concrete ones (`isCompactor` of their
  interface values: `isCompactor_periodic`, `isCompactor_revision`).

## Laws

`bootCfg_off`, `bootCfg_on`, `bootCfg_build`, `compactable_persistent`, `revGetter_persistent`,
`isCompactor_persistent`, `isPeriodic_persistent`, `isRevision_persistent`,
`isCompactor_periodic`, `isCompactor_revision`.

## Requirement snippets

`examples/specreq/etcdserverboot/compactor.go` (`ReqCompactorLifecycle`: built, run, paused and
resumed by leadership changes, stopped at the cleanup, its `Compact` calls after the stop).
-/
module

public import Spec.context.Api
public import Spec.go_etcd_io.etcd.api.v3.Wire
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3compactor

open Iris Iris.BI

/-- **The compactor's slot** (sealed; see the header). -/
opaque bootCfg (mode : GoString) (ret : w64) (ac : Bool) : Prop

section laws
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- Off: no compactor. -/
def bootCfg_off.spec : Prop := ∀ mode ret ac, ret = W64 0 → bootCfg mode ret ac

/-- On: the environment allows auto-compaction; a periodic retention of at least `10ns`. -/
def bootCfg_on.spec : Prop := ∀ mode ret ac,
  ac = true → (mode = go!"periodic" → (10 ≤ sint.Z ret ∨ sint.Z ret ≤ -10)) → bootCfg mode ret ac

/-- What `NewServer`'s proof takes from the slot when a compactor is built (`ret ≠ 0`). -/
def bootCfg_build.spec : Prop := ∀ mode ret ac,
  bootCfg mode ret ac → ret ≠ W64 0 → ac = true ∧ (mode = go!"periodic" → (10 ≤ sint.Z ret ∨ sint.Z ret ≤ -10))

end laws

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **`c.Compact(ctx, r)` may be called once `R` holds** (persistent). -/
opaque compactable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (c : GoInterface) (R : IProp GF) : IProp GF := iprop(True)

/-- **`rg.Rev()` may be called** (persistent). -/
opaque revGetter [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (rg : GoInterface) : IProp GF := iprop(True)

/-- **`cp` is a compactor whose `Compactable` is gated by `R`** (persistent). -/
opaque isCompactor [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (cp : GoInterface) (R : IProp GF) : IProp GF := iprop(True)

/-- **Provisional (the `clockwork` boundary):** `clk` is a `clockwork.Clock` whose `Now`, `After`
may be called from any goroutine (`NewRealClock()`'s: the real clock). Persistent. -/
opaque clockOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (clk : GoInterface) : IProp GF := iprop(True)

/-- `p` is a `*Periodic` compactor (persistent). -/
opaque isPeriodic [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (R : IProp GF) : IProp GF := iprop(True)

/-- `r` is a `*Revision` compactor (persistent). -/
opaque isRevision [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (r : Loc) (R : IProp GF) : IProp GF := iprop(True)

def compactable_persistent.spec : Prop := ∀ c R, Persistent (compactable (GF := GF) c R)
def revGetter_persistent.spec : Prop := ∀ rg, Persistent (revGetter (GF := GF) rg)
def isCompactor_persistent.spec : Prop := ∀ cp R, Persistent (isCompactor (GF := GF) cp R)
def isPeriodic_persistent.spec : Prop := ∀ p R, Persistent (isPeriodic (GF := GF) p R)
def isRevision_persistent.spec : Prop := ∀ r R, Persistent (isRevision (GF := GF) r R)

/-- **Introduction of `compactable`** (round 1, completeness F7; verify-round, A7 completeness
F2): once `R` holds, `Compact` at the interface's dynamic type is safe for a child of
`context.Background()` (the compactor's context), with a fresh compaction request (what the loop
builds: `&CompactionRequest{Revision: rev}`, not physical, `periodic.go:142`, `revision.go:92`; second
pass, server-core's request 2: so the server's `Compact` needs no `srvGate` share), on a goroutine
holding a thread token. The server proves it from 2c's `EtcdServer.Compact.spec`
(its `isServer` and gate share from `R`, the context's `ctxNoIncoming` and `reqPrin … none none` from
2c's `ctxNoIncoming_background`/`_child`) and `envUpd`; a test's fake from its method's WP
(`R := True`). -/
def compactable_intro.spec : Prop := ∀ (i : GoInterfaceOk) (R : IProp GF),
  (□ (R -∗ ∀ (ctx : GoInterface) (r : Loc) (rev : Int),
      Context.ctxOk ctx ∗ Context.ctxChild (GoInterface.ok context.backgroundCtxVal) ctx ∗
        EtcdWire.compactReqOwn r (DFrac.own 1) rev false ∗ threadTok -∗
      WP (App (App (Val #(methods i.ty go!"Compact" i.v)) (Val #ctx)) (Val #r))
        {{ fun _ => iprop(threadTok) }})) ⊢
  compactable (GF := GF) (interface.ok i) R

/-- **Introduction of `revGetter`**: `Rev` safe at any time on a goroutine holding a thread token,
given back (3e's store, also after `Close`: its `KV.Rev.contract` at `revRd γ true`, the persistent
`mvccRevTok γ` that `mvccRevTok_of` lends for good, with the caller's `threadTok`; integration Y/X). -/
def revGetter_intro.spec : Prop := ∀ i : GoInterfaceOk,
  (□ (threadTok -∗ WP (App (Val #(methods i.ty go!"Rev" i.v)) (Val #()))
        {{ fun _ => iprop(threadTok) }})) ⊢
  revGetter (GF := GF) (interface.ok i)

/-- **Elimination of `isCompactor`** (round 1, provability F7: the calls through the `Compactor`
interface, `start`'s `Run`, the ready handler's `Pause`/`Resume`, `Cleanup`'s `Stop`): each method
safe at any time (`Run` with the caller's thread token, which the loop keeps). -/
def isCompactor_methods.spec : Prop := ∀ (i : GoInterfaceOk) (R : IProp GF),
  isCompactor (GF := GF) (interface.ok i) R ⊢
    □ ((threadTok -∗ □ R -∗ WP (App (Val #(methods i.ty go!"Run" i.v)) (Val #())) {{ fun _ => iprop(True) }}) ∗
       WP (App (Val #(methods i.ty go!"Stop" i.v)) (Val #())) {{ fun _ => iprop(True) }} ∗
       WP (App (Val #(methods i.ty go!"Pause" i.v)) (Val #())) {{ fun _ => iprop(True) }} ∗
       WP (App (Val #(methods i.ty go!"Resume" i.v)) (Val #())) {{ fun _ => iprop(True) }})

def isCompactor_periodic.spec : Prop := ∀ p R, isPeriodic (GF := GF) p R ⊢
  isCompactor (interface.mkOk
    (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic.ty) #p) R

def isCompactor_revision.spec : Prop := ∀ r R, isRevision (GF := GF) r R ⊢
  isCompactor (interface.mkOk
    (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Revision.ty) #r) R

end res

end V3compactor
end EtcdGrove
end Perennial
