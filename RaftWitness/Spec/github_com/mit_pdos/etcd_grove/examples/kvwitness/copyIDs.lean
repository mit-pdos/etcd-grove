/- Lean-first (no Rocq counterpart). (2026-10-20, W4)

`copyIDs(ids)` (witness.go): a fresh slice with `ids`' elements.
-/
module

public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]

/-- See the file header. -/
abbrev copyIDs.spec : Prop :=
  ∀ (sl : GoSlice) (l : List w64) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness ∗ sl ↦*{dq} l }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvwitness.copyIDs)) (Val #sl))
  {{ (c : GoSlice), RET #c; sl ↦*{dq} l ∗ c ↦* l ∗ ownSliceCap w64 c (DFrac.own 1) }}

end spec

end kvwitness
end EtcdGrove
end Perennial
