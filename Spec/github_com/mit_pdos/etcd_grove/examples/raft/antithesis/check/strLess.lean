/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `strLess(a, b)`: `a < b`.
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

/-- `a < b` on strings (Go's order, `go.GoStringLt`). -/
abbrev strLess.spec : Prop :=
  ∀ (a b : Str),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.strLess)) (Val #a)) (Val #b))
  {{ RET #(strLess a b); True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
