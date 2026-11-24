/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `m.reject()`: `Msg.reject_`.
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

/-- `m.reject`, where present (absent: an `EvalError`). -/
abbrev Msg.reject.spec : Prop :=
  ∀ (g : G.Msg) (m : Msg) (x : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      msgRO g m ∗ ⌜m.reject_ = .ok x⌝ }}
    (App (Val (g @!! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.ty @!! go!"reject")) (Val #()))
  {{ RET #x; True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
