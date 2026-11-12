/-
## `chain(chg, ops...)` (internal)

**Users.** `Restore`. Each op (an `opSpec`, its model `F`, run once) on the changer whose tracker
is the previous op's result, the frame `R` (what the closures read) passed through and given back on
both exits; the models composed (`Carried` composes: a fresh `Progress` with its learner mark
updated is fresh). Mirrors the code.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.confchange.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ConfChange

open Iris Iris.BI
open Classical Tracker

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.confchange.Assumptions]

/-- (internal) The ops in order, each on the previous one's result: the composed model's answer. -/
def chain.spec : Prop :=
  ∀ (chg : go_etcd_io.raft.v3.confchange.Changer) (m0 : Membership) (B : Base) (ops : GoSlice)
    (dq : DFrac) (fs : List GoFunc) (Fs : List (Membership → Option Membership)) (R : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ configOwn chg.Tracker'.Config' (DFrac.own 1) m0 ∗ progressMapOwn B.mp B.prs B.pv ∗
      ⌜BaseOf chg B ∧ TrackerOk m0 B.pv ∧ m0.Valid⌝ ∗ ops ↦*{dq} fs ∗ R ∗
      [∗list] f;F ∈ fs;Fs, opSpec f F R }}
    (App (App (Val #(functions go_etcd_io.raft.v3.confchange.chain [])) (Val #chg)) (Val #ops))
  {{ (cfg : go_etcd_io.raft.v3.tracker.Config) (trk : GoMap) (err : GoInterface),
      RET (PairV (PairV #cfg #trk) #err); ops ↦*{dq} fs ∗ R ∗
      result B (Fs.foldlM (fun m F => F m) m0) cfg trk err }}

end spec
end ConfChange
end EtcdGrove
end Perennial
