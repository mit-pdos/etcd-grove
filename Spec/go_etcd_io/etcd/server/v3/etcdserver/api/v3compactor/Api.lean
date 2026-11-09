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
* `compactable c` (persistent): **the interface value `c` (`Compactable`) may be called**: for any
  context `Context.ctxOk` and any compaction request, `Compact` returns (any response, any error).
  The receiver's need (PRINCIPLES, "A contract between packages states the receiver's need").
* `revGetter rg` (persistent): `rg.Rev()` returns (any `int64`), at any time, also after the store
  is closed (3e's obligation: `req/go_etcd_io_etcd_server_v3_storage_mvcc.md`, "from 2e").
* `isCompactor cp` (persistent): `cp` is a `Compactor` (`*Periodic` or `*Revision`) over a
  `compactable` and a `revGetter`: `Run`, `Pause`, `Resume`, `Stop` may be called any number of
  times, from any goroutine (each takes the compactor's mutex or cancels its context; `Run` forks
  the loop, which exits once the context is cancelled).
* `isPeriodic p`, `isRevision r` (persistent): the concrete ones (`isCompactor` of their interface
  values: `isCompactor_periodic`, `isCompactor_revision`).

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
variable [go_gctx : GoGlobalContext]

/-- **`c.Compact(ctx, r)` may be called** (persistent). -/
opaque compactable (c : GoInterface) : IProp GF := iprop(True)

/-- **`rg.Rev()` may be called** (persistent). -/
opaque revGetter (rg : GoInterface) : IProp GF := iprop(True)

/-- **`cp` is a compactor** (persistent). -/
opaque isCompactor (cp : GoInterface) : IProp GF := iprop(True)

/-- `p` is a `*Periodic` compactor (persistent). -/
opaque isPeriodic (p : Loc) : IProp GF := iprop(True)

/-- `r` is a `*Revision` compactor (persistent). -/
opaque isRevision (r : Loc) : IProp GF := iprop(True)

def compactable_persistent.spec : Prop := ∀ c, Persistent (compactable (GF := GF) c)
def revGetter_persistent.spec : Prop := ∀ rg, Persistent (revGetter (GF := GF) rg)
def isCompactor_persistent.spec : Prop := ∀ cp, Persistent (isCompactor (GF := GF) cp)
def isPeriodic_persistent.spec : Prop := ∀ p, Persistent (isPeriodic (GF := GF) p)
def isRevision_persistent.spec : Prop := ∀ r, Persistent (isRevision (GF := GF) r)

def isCompactor_periodic.spec : Prop := ∀ p, isPeriodic (GF := GF) p ⊢
  isCompactor (interface.mkOk
    (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic.ty) #p)

def isCompactor_revision.spec : Prop := ∀ r, isRevision (GF := GF) r ⊢
  isCompactor (interface.mkOk
    (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Revision.ty) #r)

end res

end V3compactor
end EtcdGrove
end Perennial
