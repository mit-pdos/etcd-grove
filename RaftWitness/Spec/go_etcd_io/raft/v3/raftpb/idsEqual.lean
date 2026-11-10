/-
`idsEqual(a, b)` (`raftpb/confstate.go`; the raft fork's fourth fix, premise fixes 2, 2026-11-10):
whether two id slices hold the same ids in the same order. Lean-first.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `idsEqual(a, b)` of two id slices holding `xs` and `ys` answers whether `xs = ys`. -/
abbrev raftpb.idsEqual.spec : Prop :=
  ∀ (a b : GoSlice) (dq1 dq2 : DFrac) (xs ys : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ a ↦*{dq1} xs ∗ b ↦*{dq2} ys }}
    (App (App (Val #(functions raftpb.idsEqual [])) (Val #a)) (Val #b))
  {{ (r : Bool), RET #r; a ↦*{dq1} xs ∗ b ↦*{dq2} ys ∗ ⌜r = true ↔ xs = ys⌝ }}

end spec

end EtcdGrove
end Perennial
