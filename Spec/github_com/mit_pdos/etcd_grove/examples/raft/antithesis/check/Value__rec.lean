/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `v.rec()`: `Value.asRec`.
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

/-- `v` read as a record: `v` itself, where `Value.asRec` is defined (a string: an `EvalError`). -/
abbrev Value.rec.spec : Prop :=
  ∀ (g : G.Value) (v w : Value),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      valueRO g v ∗ ⌜v.asRec = .ok w⌝ }}
    (App (Val (g @!! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Value.ty @!! go!"rec")) (Val #()))
  {{ RET #g; valueRO g w }}

end spec

end AntCheck
end EtcdGrove
end Perennial
