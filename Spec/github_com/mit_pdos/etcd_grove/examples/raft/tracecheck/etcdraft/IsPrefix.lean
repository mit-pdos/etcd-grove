/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `IsPrefix(s, t)`: SequencesExt's `IsPrefix` (`isPrefix`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Rep

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

/-- `IsPrefix(s, t)`: whether `s` is a prefix of `t`. -/
abbrev IsPrefix.spec : Prop :=
  ∀ (sl : GoSlice) (s : List Entry) (tl : GoSlice) (t : List Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      logRO sl s ∗ logRO tl t }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.IsPrefix)) (Val #sl)) (Val #tl))
  {{ RET #(isPrefix s t); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
