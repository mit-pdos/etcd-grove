/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `validBy(by)`: B 232-233, `InMem.ok`'s first test.
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

/-- B 232-233 `ev.by \in {...}` (`InMem.ok`'s first test). -/
abbrev validBy.spec : Prop :=
  ∀ (x : Str),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.validBy)) (Val #x))
  {{ RET #(([go!"recv", go!"tick", go!"campaign", go!"propose", go!"write", go!"apply", go!"boot", go!"transfer", go!"snapstatus", go!"read"] : List Str).contains x); True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
