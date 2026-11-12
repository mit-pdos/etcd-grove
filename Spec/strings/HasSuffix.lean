/-
`strings.HasSuffix(s, suffix)`: whether `suffix` is a suffix of `s`. Perennial translates
`strings` without it (`notes/perennial-changes.md`); its Go body is
`len(s) >= len(suffix) && s[len(s)-len(suffix):] == suffix`. The trust boundary: an axiom, `Proof/strings/HasSuffix.lean`. Lean-first (no Rocq
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
abbrev strings.HasSuffix.spec : Prop :=
  ∀ (s suf : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
    (App (App (Val (@! strings.HasSuffix)) (Val #s)) (Val #suf))
  {{ RET #(decide (suf <:+ s)); True }}

end spec

end EtcdGrove
end Perennial
