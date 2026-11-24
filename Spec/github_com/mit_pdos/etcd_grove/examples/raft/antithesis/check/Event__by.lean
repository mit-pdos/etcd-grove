/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `ev.by()`: `need ev.byE`.
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

/-- `ev.byE`, where present (absent: an `EvalError`). -/
abbrev Event.by.spec : Prop :=
  ∀ (p : Loc) (ev : Event) (x : Str),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      eventRO p ev ∗ ⌜need ev.byE = .ok x⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event.ty @!! go!"by")) (Val #()))
  {{ RET #x; True }}

end spec

end AntCheck
end EtcdGrove
end Perennial
