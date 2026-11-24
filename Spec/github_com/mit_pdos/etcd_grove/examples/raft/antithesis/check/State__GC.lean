/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `s.GC()`: B 713-723, `State.gc`.
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

/-- B 713-723 `GC` (without its guard): `State.gc`'s successor, owned, where defined. -/
abbrev State.GC.spec : Prop :=
  ∀ (p : Loc) (s s' : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      stateRO p s ∗
      ⌜s.gc = .ok s'⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.ty @!! go!"GC")) (Val #()))
  {{ (q : Loc), RET #q; stateOwn q s' }}

end spec

end AntCheck
end EtcdGrove
end Perennial
