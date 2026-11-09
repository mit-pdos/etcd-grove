/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `nonNil(ss...)`: the successors of a list of optional successors (`somes`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Own

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- `nonNil(ss...)`: the non-nil pointers of `ss`, in order, each still holding what the caller's
predicate `P` says of its state (`P` of a pointer implies it is not nil, as `stateRO` and `stateOwn`
do): `somes os`. -/
abbrev nonNil.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (ps : List Loc) (os : List (Option State)) (P : Loc → State → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      sl ↦*{dq} ps ∗
      ([∗list] p;o ∈ ps;os, match o with | none => ⌜p = null⌝ | some s => P p s) ∗
      □ (∀ p s, P p s -∗ ⌜p ≠ null⌝) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.nonNil)) (Val #sl))
  {{ (out : GoSlice), RET #out;
      ∃ qs : List Loc, out ↦* qs ∗ ownSliceCap Loc out (DFrac.own 1) ∗
        [∗list] q;s ∈ qs;somes os, P q s }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
