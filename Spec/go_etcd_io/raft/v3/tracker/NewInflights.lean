/-
## `NewInflights(size, maxBytes)`

**Users.** confchange's `initProgress` (a new peer), raft's `reset` (`raft.go:817`, each peer at a
new term): with the tracker's `MaxInflight` (raft's `Config.MaxInflightMsgs`, positive by
`validate`).

**Proof sketch.** The literal; the empty ring (`count = 0`, no buffer).

**Changes** (from `specs-ref`'s `tracker/NewInflights.lean`): the bound named (`inflightsMax`).

**Margin.** The capacity bound is the model's, not Go's: below it the ring's `start + count` and
`grow`'s doubling do not wrap; a Go program could not allocate a ring that large. It is a premise
here and of the confchange specs that create a peer (they call this), not a law of the tracker.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Tracker

open Iris Iris.BI
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.tracker.Assumptions]

/-- An empty ring of capacity `size` messages, `maxBytes` bytes. -/
def NewInflights.spec : Prop :=
  ∀ (size maxBytes : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ ⌜0 ≤ sint.Z size ∧ sint.Z size ≤ inflightsMax⌝ }}
    (App (App (Val #(functions go_etcd_io.raft.v3.tracker.NewInflights [])) (Val #size))
      (Val #maxBytes))
  {{ (p : Loc), RET #p; inflightsOwn p (InflightsV.empty size maxBytes) }}

end spec
end Tracker
end EtcdGrove
end Perennial
