/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `s.MemCommit(n)`: B 139, `State.memCommit`.
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

/-- B 139 `MemCommit(n)`: `State.memCommit`, where defined. -/
abbrev State.MemCommit.spec : Prop :=
  ∀ (p : Loc) (s : State) (n : w64) (c : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      stateRO p s ∗
      ⌜0 ≤ sint.Z n ∧ sint.Z n < s.cfg.server.length ∧ s.memCommit (sint.nat n) = .ok c⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.ty @!! go!"MemCommit")) (Val #n))
  {{ (u : w64), RET #u; ⌜sint.Z u = c⌝ }}

end spec

end AntCheck
end EtcdGrove
end Perennial
