/-
`(*realClock).Now()` (`clockwork.go`: `time.Now()`). Lean-first.
-/
module

public import Proof.github_com.jonboulle.clockwork.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `rc.Now()`: some time (Perennial's `time.Now`, whose readings are arbitrary). -/
abbrev clockwork.realClock.Now.spec : Prop :=
  ∀ (rc : Loc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.jonboulle.clockwork }}
      (App (Val (rc @!! go.GoType.PointerType github_com.jonboulle.clockwork.realClock.ty @!! go!"Now"))
        (Val #()))
    {{ (t : time.Time), RET #t; True }}

end spec

end EtcdGrove
end Perennial
