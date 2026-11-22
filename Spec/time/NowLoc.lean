/-
`time.Now()` (`time/time.go`), with the location of the result: Perennial's `time.Now.spec` says
only "some `Time`"; this second spec adds that the `Time`'s `loc` is the value of the global
`time.Local` (`Now` returns `Time{..., Local}` on each of its three paths), with the persistent
read-only points-to of `Local` that `time`'s `isPkgInit` holds (`Perennial/Proof/time/Base.lean`,
`isInit`). For `time.Time.Format.specBroken` (`Spec/time/Time__FormatBroken.lean`), whose
precondition asks for a `Time` whose `Location` no program can write. Proved
(`Proof/time/NowLoc.lean`) over Perennial's translation of Go's `Now`. Lean-first.
-/
module

public import Perennial.Proof.time

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- **`time.Now()`**: some `Time` whose location is the value `l` of the global `time.Local`
(read-only: `isPkgInit`'s `globalAddr time.Local ↦□ l`, given back). -/
abbrev time.Now.specLoc : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.time }}
    (App (Val (@! time.Now)) (Val #()))
  {{ (t : time.Time), RET #t; ∃ l : Loc, globalAddr time.Local ↦□ l ∗ ⌜t.loc' = l⌝ }}

end spec

end EtcdGrove
end Perennial
