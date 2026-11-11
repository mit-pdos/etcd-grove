/-
`confStatesEqual(a, b)` (`raftpb/confstate.go`; the raft fork's fourth fix, premise fixes 2,
2026-11-10): whether two conf states hold the same configuration, compared field by field (the four
id lists in order and `AutoLeave`), which `ConfState.Equivalent` calls on its sorted clones in place
of `proto.Equal` (which also compared the unknown fields). Lean-first.
-/
module

public import Proof.go_etcd_io.raft.v3.InvPb

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

/-- `confStatesEqual(a, b)` of two conf states holding `c1` and `c2` answers whether `c1 = c2`
(whatever their unknown fields). -/
abbrev raftpb.confStatesEqual.spec : Prop :=
  ∀ (p q : Loc) (dq1 dq2 : DFrac) (c1 c2 : ConfStateM) (al1 al2 : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ csPts p dq1 c1 al1 ∗
      csPts q dq2 c2 al2 }}
    (App (App (Val #(functions raftpb.confStatesEqual [])) (Val #p)) (Val #q))
  {{ (r : Bool), RET #r; csPts p dq1 c1 al1 ∗ csPts q dq2 c2 al2 ∗ ⌜r = true ↔ c1 = c2⌝ }}

end spec

end EtcdGrove
end Perennial
