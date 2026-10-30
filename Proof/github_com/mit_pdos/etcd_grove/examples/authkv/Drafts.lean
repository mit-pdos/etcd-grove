/-
**Draft statements of `Main`'s remaining callees** (`notes/authkv-main-plan.md`, "Main's
callees, draft"; 2026-10-29). Lean-first (no Rocq counterpart).

These are for review round 2, written here so that they typecheck; no proof uses them. When frozen,
each goes where it belongs (`common.Collect.spec` restated in its `Spec` file, the laws to
`Hist.lean`) and this file goes away.

- `Collect`, general in the events: now `common.Collect.spec` itself (2026-10-29).
- **An event's revision** (`revEvents_modRev`, proved): a state's event of revision `r` has
  `ModRevision = r`.
- From the invariant to `CheckHistory`'s premise: `histOk_of_evHistOk`, now in `Hist.lean`
  (2026-10-30).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Hist
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.SyncModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv
namespace draft

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver github_com.mit_pdos.etcd_grove.examples.common
  common

section pure
variable [GooseExts]

/-- **A state's event of revision `r` has `ModRevision = r`** (round 2, finding 7; mvcc's
`evsOfRevM_modRev_sm` at the state's events): what turns `stateHistOk`'s revisions into the
collected `Event`s' `Rev'` (`Collect` sets it from the key-value's `ModRevision`). -/
theorem revEvents_modRev (σ : KVState) (r : Nat)
    (hs : (σ.at (r - 1)).kvs.Pairwise etcdKvLess) :
    ∀ ev ∈ σ.revEvents r, ev.kv.modRev = W64 r :=
  mvcc.evsOfRevM_modRev_sm r _ hs _

end pure

end draft
end authkv
end EtcdGrove
end Perennial
