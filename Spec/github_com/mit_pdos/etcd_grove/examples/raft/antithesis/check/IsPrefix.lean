/-
Lean-first (no Rocq counterpart). #33 S3b (2026-11-23): `IsPrefix(a, b)`: `isPrefix` where it is defined.
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

/-- `IsPrefix(a, b)` (R 130): `isPrefix a b`, where it is defined. -/
abbrev IsPrefix.spec : Prop :=
  ∀ (al : GoSlice) (a : List Entry) (bl : GoSlice) (b : List Entry) (r : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      logRO al a ∗ logRO bl b ∗ ⌜isPrefix a b = .ok r⌝ }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.IsPrefix)) (Val #al)) (Val #bl))
  {{ RET #r; True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
