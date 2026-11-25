/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Spec/queue.lean (lab master 915f964; notes/dsv-vr.md):
over any `GF`, on the net extension.
-/
/-
Cross-package specs of `pkg/queue`: the generic `Queue[T]` (at `T` = `events.NetworkEvent` for
the network and the replica, `events.Reply` for the client) as a concurrent bag of values each
with the resource `P v` that its pusher gives and its popper gets (`isQueue`, persistent; `P`
itself need not be persistent: exclusive resources, e.g. a decoded event's `Logs` capacity,
travel through the queue). `P` is the caller's choice (HoCAP style), the usual form for a
concurrent bag. The order of the values is not needed by any caller.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.queue.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.queue.Defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : queue.Assumptions]

/-- `q` is a `*Queue[T]` whose values (Lean type `V`) each carry `P v` (persistent).
-- sealed: the package's choice -/
@[irreducible] def queue.isQueue {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (T : go.GoType)
    [IntoValTyped (GF := GF) V T] (q : Loc) (P : V → IProp GF) :
    IProp GF := queue.isQueueDef q P

instance queue.isQueue_persistent {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (T : go.GoType) [IntoValTyped (GF := GF) V T] (q : Loc) (P : V → IProp GF) :
    Persistent (queue.isQueue T q P) := by
  rw [show queue.isQueue T q P = queue.isQueueDef q P by with_unfolding_all rfl]
  infer_instance

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : queue.Assumptions]

set_option goose.wp.extras true

/-- `New[T]()`: an empty queue, for any predicate `P` of its values. -/
abbrev queue.New.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (T : go.GoType)
    [IntoValTyped (GF := GF) V T] (P : V → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.queue }}
    (App (Val #(functions queue.New [T])) (Val #()))
  {{ (q : Loc), RET #q; queue.isQueue T q P }}

/-- `q.Push(v)`, giving `P v`. -/
abbrev queue.Queue.Push.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (T : go.GoType)
    [IntoValTyped (GF := GF) V T] (P : V → IProp GF) (q : Loc) (v : V),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.queue ∗
      queue.isQueue T q P ∗ P v }}
    (App (Val (q @!! go.GoType.PointerType (queue.Queue.ty T) @!! go!"Push")) (Val #v))
  {{ RET #(); True }}

/-- `q.Pop()`: `(v, true)` with `P v` (a value pushed and not popped), or `(zero, false)`. -/
abbrev queue.Queue.Pop.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (T : go.GoType)
    [IntoValTyped (GF := GF) V T] (P : V → IProp GF) (q : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.queue ∗
      queue.isQueue T q P }}
    (App (Val (q @!! go.GoType.PointerType (queue.Queue.ty T) @!! go!"Pop")) (Val #()))
  {{ (v : V) (ok : Bool), RET (PairV #v #ok); if ok then P v else True }}

end spec

end Perennial.github_com.tangledbytes.go_vsr.pkg
