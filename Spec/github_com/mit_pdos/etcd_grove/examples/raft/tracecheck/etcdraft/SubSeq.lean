/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `SubSeq(s, m, n)`: `subSeq` where it is defined.
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

/-- `SubSeq(s, m, n)`: `s`'s elements `m..n` (1-indexed), sharing `s`'s array, where `subSeq` is
defined. Where it is not (TLC's evaluation error), the Go panics with an `EvalError`, which this
triple does not describe: its premise is that `subSeq` is defined (its caller, `subSeqM`, checks it
the same way). -/
abbrev SubSeq.spec : Prop :=
  ∀ (sl : GoSlice) (s : List Entry) (m n : w64) (r : List Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      logRO sl s ∗ ⌜subSeq s (sint.Z m) (sint.Z n) = some r⌝ }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.SubSeq)) (Val #sl)) (Val #m)) (Val #n))
  {{ (u : GoSlice), RET #u; logRO u r }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
