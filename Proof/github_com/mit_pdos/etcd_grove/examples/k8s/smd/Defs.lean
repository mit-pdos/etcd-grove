/-
The structured-merge-diff driver's state predicate (`examples/k8s/smd/smd.go`'s `state`), over the
scenario's model (`Scenario.lean`) and SMD's representation predicates
(`Proof/sigs_k8s_io/structured_merge_diff/v7/Own.lean`). Lean-first (2026-11-19,
notes/smd-robustness.md).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.smd.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.smd.Scenario
public import Proof.sigs_k8s_io.structured_merge_diff.v7.Own

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_smd

open Iris Iris.BI
open smd

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.smd.Assumptions]

/-- The driver's `*state` at `s`, holding the model state `st`: the schema `sc` (the scenario's,
its lazy indexes owned here), an updater without `ReturnInputOnNoop` and with an identity
converter, the stored object and its managed fields. -/
def ownState (s sc : Loc) (st : St) : IProp GF :=
  iprop(∃ (u lv : Loc) (mfm : GoMap),
    s ↦ (github_com.mit_pdos.etcd_grove.examples.k8s.smd.state.mk sc u lv mfm) ∗
    ownSchema sc k8s_smd.sc ∗ ownUpdater u false ∗ ownTV lv sc st.live ∗ ownMF mfm st.mf)

end defs

end k8s_smd
end EtcdGrove
end Perennial
