/-
Lean-first (no Rocq counterpart). #33 S3b (2026-11-23): `stringsEqual(a, b)`: `a = b`.
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

/-- `stringsEqual(a, b)`: equality of two sequences of strings. -/
abbrev stringsEqual.spec : Prop :=
  ∀ (al : GoSlice) (a : List Str) (bl : GoSlice) (b : List Str),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      strsRO al a ∗ strsRO bl b }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.stringsEqual)) (Val #al)) (Val #bl))
  {{ RET #(decide (a = b)); True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
