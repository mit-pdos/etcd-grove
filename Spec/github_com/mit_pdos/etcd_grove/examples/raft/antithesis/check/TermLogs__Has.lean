/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `f.Has(t)`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Rep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- `t \in DOMAIN f`. -/
abbrev TermLogs.Has.spec : Prop :=
  ∀ (sl : GoSlice) (f : TermFn (List Entry)) (t : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      termLogsRO sl f }}
    (App (Val (sl @!! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs.ty @!! go!"Has")) (Val #t))
  {{ RET #(f.has (sint.Z t)); True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
