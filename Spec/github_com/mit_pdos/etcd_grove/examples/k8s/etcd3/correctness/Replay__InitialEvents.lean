/-
Lean-first (no Rocq counterpart).

`(*Replay).InitialEvents(request, rv)` (`correctness/replay.go`) on the frozen replay `R` and the
driver's watch `x` as the request (`wreqRep`), at a resource version the replay has a state at: no
error and the state's initial events (`initialEventsR R x rv`, `Model.initialEvents`), read-only
(k8s 7g step 5). Only that case is specified: `validateInitialEvents` calls it on the accepting run
(`initialOkL`), where the state exists.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchRep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI map
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev Replay.InitialEvents.spec : Prop :=
  ∀ (rp : Loc) (R : RReplay) (x : Input)
    (req : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchRequest) (rv : w64),
  (R.states !! rv).isSome →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      replayAt rp R ∗ wreqRep req x }}
    (App (App (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Replay.ty)
      go!"InitialEvents" #rp)) (Val #req)) (Val #rv))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
      ⌜err = GoInterface.nil⌝ ∗ ∃ evs, ⌜initialEventsR R x rv = some evs⌝ ∗ evsRO sl evs }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
