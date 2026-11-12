/-
## `RawNode.Advance(rd)`

**Users.** No client calls `RawNode` directly (etcd and the examples use `node`); `node.run`
calls it from its goroutine, holding the token, right after `node.Advance`'s rendezvous. A direct
caller first applies `rawNodeAt_advance` (a ghost step: R1's `Advance` post), then calls this.
**Proof sketch.** `rawNodeAdv_open`: `stepsOnAdvance` stepped, each with R2's `ackOk` (`raft.Step`
with `StepSrc.ack`), each entry cleared, the slice emptied; the closing. Not async (`ConfigOk`), so
no panic. **Changes.** As `node.Advance`'s; (round 2) over R2's phase token `rawNodeAt rn γ id k
adv`, given back with nothing queued; (verify-round, A4 P3) the client's half of the post moved to
the rendezvous (`rawNodeAt_advance`), so that `node.Advance`, which returns before the run goroutine
steps, can give it: this triple is the steps alone (`rawNodeAdv` to `rawNodeAt`).
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.Api
public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiCore

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [ctx_sem : context.Assumptions]

/-- **`RawNode.Advance`'s steps**: after the rendezvous (`rawNodeAt_advance`, which gives the
client's half of the post), the queued acknowledgements are stepped and the `RawNode` has nothing
queued. -/
def RawNode.Advance.spec : Prop :=
  ∀ (rn : Loc) (γ : Cluster) (id : w64) (k : Nat) (adv : Bool) (rd : go_etcd_io.raft.v3.Ready),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ rawNodeAdv rn γ id k adv }}
    (App (Val (rn @!! go.GoType.PointerType go_etcd_io.raft.v3.RawNode.ty @!! go!"Advance")) (Val #rd))
  {{ RET #(); rawNodeAt rn γ id k false }}

end spec
end Raft
end EtcdGrove
end Perennial
