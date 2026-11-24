/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `s.GCDue()`: B 711, `State.gcDue`.
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

/-- B 711 `GCDue`: `State.gcDue`, where defined, within budget (`len(Garbage) + len(OldVotes)`). -/
abbrev State.GCDue.spec : Prop :=
  ∀ (p : Loc) (s : State) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      stateRO p s ∗
      ⌜s.Bounded ∧ s.gcDue = .ok b⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.ty @!! go!"GCDue")) (Val #()))
  {{ RET #b; True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
