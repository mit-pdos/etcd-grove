/-
**Draft statements of `Main`'s remaining callees** (`notes/authkv-main-plan.md`, "Main's
callees, draft"; 2026-10-29). Lean-first (no Rocq counterpart).

These are for review round 2, written here so that they typecheck; no proof uses them. When frozen,
each goes where it belongs (`common.Collect.spec` restated in its `Spec` file, the laws to
`Hist.lean`) and this file goes away.

- `Collect`, general in the events: now `common.Collect.spec` itself (2026-10-29).
- **From the invariant to `CheckHistory`'s premise** (`histOk_of_keyHistOk`, proved): the
  collected events above `setupRev` on admitted keys are what `histOk` asks.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Hist

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

/-- **The history's check from the invariant's keys**: `histOk` asks of the events above
`setupRev` that are not `endKey`'s exactly that their key's principal was permitted, which
`keyHistOk` says. -/
theorem histOk_of_keyHistOk (evs : List wev) (setupRev : w64)
    (h : ∀ e ∈ evs, sint.Z setupRev < sint.Z e.Rev' → keyHistOk e.Key') :
    histOk evs setupRev endKey := by
  intro e he hr hne
  rcases h e he hr with h | h
  · exact h
  · exact absurd h hne

end pure

end draft
end authkv
end EtcdGrove
end Perennial
