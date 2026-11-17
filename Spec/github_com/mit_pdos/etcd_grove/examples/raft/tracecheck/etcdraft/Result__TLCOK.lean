/-
Lean-first (no Rocq counterpart). Draft (2026-11-08), layer C of `notes/trace-validation-plan.md`.

`Result.TLCOK()` (`examples/raft/tracecheck/etcdraft/check.go`): `r.OK && r.Branched == 0`, TLC's
verdict. Its spec: of a result holding the Lean `res` (`resultRel`), it is `res.tlcOK`. What
`Main` checks after `CheckTrace` (review round 1 of layer C, S4).
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

/-- See the file header. -/
abbrev Result.TLCOK.spec : Prop :=
  ∀ (r : G.Result) (res : Result),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      ⌜resultRel r res⌝ }}
    (App (Val (r @!! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Result.ty @!! go!"TLCOK"))
      (Val #()))
  {{ RET #(res.tlcOK); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
