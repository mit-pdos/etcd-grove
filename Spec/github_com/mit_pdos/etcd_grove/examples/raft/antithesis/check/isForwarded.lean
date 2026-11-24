/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `isForwarded(t)`: B 524, `isForwarded`.
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

/-- B 524: the message types raft forwards (`isForwarded`). -/
abbrev isForwarded.spec : Prop :=
  ∀ (t : Str),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.isForwarded)) (Val #t))
  {{ RET #(isForwarded t); True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
