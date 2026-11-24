/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `s.idx(n)`: `State.idx`.
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

/-- The position of server `n`, where it is one (elsewhere: an `EvalError`). -/
abbrev State.idx.spec : Prop :=
  ∀ (p : Loc) (s : State) (n : Str) (k : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      stateRO p s ∗ ⌜s.idx n = .ok k⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.ty @!! go!"idx")) (Val #n))
  {{ (w : w64), RET #w; ⌜sint.Z w = k ∧ k < s.cfg.server.length⌝ }}

end spec

end AntCheck
end EtcdGrove
end Perennial
