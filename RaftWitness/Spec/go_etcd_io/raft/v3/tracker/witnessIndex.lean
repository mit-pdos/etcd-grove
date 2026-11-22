/- The regular acknowledgements needed by one half of a witness configuration. -/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__OneLessThanQuorumInReplicationSet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Read the regular acknowledgements for one half using its selected quorum rule. -/
abbrev tracker.witnessIndex.spec : Prop :=
  ∀ (s : GSet w64) (m : Loc) (l : GoInterface) (P : IProp GF)
    (acked : w64 → Option w64) (selected : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗
      ⌜(GMap.size s : Int) ≤ 2 ^ 62⌝ ∗ ownIdsetQ m (DFrac.own 1) s ∗
      isAckedIndexer l P acked ∗ P }}
    (App (App (App (Val #(functions tracker.witnessIndex [])) (Val #m)) (Val #l)) (Val #selected))
  {{ (N : w64), RET #N; ownIdsetQ m (DFrac.own 1) s ∗ P ∗
      ⌜CountGe s (fun v => (acked v).getD (W64 0)) (witnessRegularCount s selected) N⌝ }}

end spec

end EtcdGrove
end Perennial
