/-
`strings.Contains(s, substr)`: whether `substr` occurs in `s`. Perennial translates `strings`
without it (`notes/perennial-changes.md`). The trust boundary: an axiom, `Proof/strings/Contains.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Perennial.Proof.strings.Base

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

/-- See the file header. -/
abbrev strings.Contains.spec : Prop :=
  ∀ (s sub : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
    (App (App (Val (@! strings.Contains)) (Val #s)) (Val #sub))
  {{ RET #(decide (sub <:+: s)); True }}

end spec

end EtcdGrove
end Perennial
