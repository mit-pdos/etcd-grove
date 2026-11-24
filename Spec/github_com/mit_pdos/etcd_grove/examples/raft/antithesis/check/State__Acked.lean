/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `s.Acked(i, t, c)`.
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

/-- R 344-347 `Acked(i, t, c)`: `State.acked`. -/
abbrev State.Acked.spec : Prop :=
  ∀ (p : Loc) (s : State) (i t c : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      stateRO p s ∗ ⌜0 ≤ sint.Z i ∧ sint.Z i < s.cfg.server.length ∧ (s.cfg.server.length : Int) < 2 ^ 61⌝ }}
    (App (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.ty @!! go!"Acked")) (Val #i)) (Val #t)) (Val #c))
  {{ (u : GoSlice), RET #u; strsRO u (s.acked (sint.nat i) (sint.Z t) (sint.Z c)) }}

end spec

end AntCheck
end EtcdGrove
end Perennial
