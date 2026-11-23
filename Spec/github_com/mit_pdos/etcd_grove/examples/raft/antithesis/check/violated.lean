/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `violated(s)`: `check.go`, `violated`.
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

/-- The invariants `s` breaks, as TLC reports them (`violated`; Go: `nil` for none). -/
abbrev violated.spec : Prop :=
  ∀ (p : Loc) (s : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      stateRO p s }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.violated)) (Val #p))
  {{ (u : GoSlice), RET #u; strsRO u (violated s) }}

end spec

end AntCheck
end EtcdGrove
end Perennial
