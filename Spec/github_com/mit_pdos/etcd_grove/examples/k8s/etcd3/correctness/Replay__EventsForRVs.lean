/-
Lean-first (no Rocq counterpart).

`(*Replay).EventsForRVs(request, rvRange)` (`correctness/replay.go`) on the frozen replay `R`, the
driver's watch `x` as the request (`wreqRep`) and a range `[mn, mx)` (`rangeRep`, given back): no
error and a fresh read-only slice of the events of the changes in the range whose key the watch has in
scope (`eventsForRVsL R x mn mx`) (k8s 7g step 5).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchVocab

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
abbrev Replay.EventsForRVs.spec : Prop :=
  ∀ (rp : Loc) (R : RReplay) (x : Input)
    (req : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchRequest)
    (p : Loc) (mn mx : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      replayAt rp R ∗ wreqRep req x ∗ rangeRep p (some (mn, mx)) }}
    (App (App (Val #(methods (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Replay.ty)
      go!"EventsForRVs" #rp)) (Val #req)) (Val #p))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
      ⌜err = GoInterface.nil⌝ ∗ evsRO sl (eventsForRVsL R x mn mx) ∗ rangeRep p (some (mn, mx)) }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
