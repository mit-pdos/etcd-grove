/-
Lean-first (no Rocq counterpart). #33 S3b-2 (2026-11-23): `ev.more()`: `need ev.more`.
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

/-- `ev.more`, where present (absent: an `EvalError`). -/
abbrev Event.more.spec : Prop :=
  ∀ (p : Loc) (ev : Event) (x : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      eventRO p ev ∗ ⌜need ev.more = .ok x⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event.ty @!! go!"more")) (Val #()))
  {{ (u : w64), RET #u; ⌜sint.Z u = x⌝ }}

end spec

end AntCheck
end EtcdGrove
end Perennial
