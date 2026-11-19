/-
The structured-merge-diff driver's representation predicates (`examples/k8s/smd/smd.go`'s
`state`, its map literals), over the scenario (`Scenario.lean`) and SMD's API vocabulary.
Lean-first (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.smd.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.smd.Scenario

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

/-- A `map[string]interface{}` holding the entries `kvs` (canonical): what `NewValueInterface`
of it holds. -/
def isUMap (m : GoMap) (kvs : List (GoString × UVal)) : IProp GF :=
  isIface (interface.mkOk mapStrIfaceTy #m) (.map kvs)

/-- The driver's `*state` at `s`, holding `st`: the scenario's schema at `sc`, an updater without
`ReturnInputOnNoop` and with an identity converter, the stored object (a root) and its managed
fields. -/
def ownState (s sc : Loc) (st : St) : IProp GF :=
  iprop(∃ (u lv : Loc) (mfm : GoMap) (cv : sigs_k8s_io.structured_merge_diff.v7.merge.Converter),
    s ↦ (github_com.mit_pdos.etcd_grove.examples.k8s.smd.state.mk sc u lv mfm) ∗
    isSchema sc sc0 ∗ isUpdater u cv (zero_val GoMap) (zero_val GoMap) false ∗
    isIdentityConverter cv ∗ isTV lv sc sc0 rootRef st.live ∗ isMF mfm st.mf)

end defs

end k8s_smd
end EtcdGrove
end Perennial
