/-
`strings.TrimLeft(s, cutset)` for an ASCII `cutset` (every byte below `0x80`): `s` without its
leading bytes in `cutset` (`strings.trimLeft`, `Proof/strings/CutDefs.lean`; Go's `trimLeftByte` and
`trimLeftASCII`). A non-ASCII cutset (Go's `trimLeftUnicode`, rune by rune) is outside the spec.
Pending: Perennial translates `strings.TrimLeft` as a name only at the pin; its branch
`strings-cut-lastindex` (`8ff6a1c79a`) translates Go's body for an ASCII cutset, not proved yet
(`notes/perennial-changes.md`). No proof file: the Links that reach it take this spec as a
hypothesis (`section links_pending`). Lean-first.
-/
module

public import Perennial.Proof.strings.Base
public import Proof.strings.CutDefs

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

/-- See the file header. -/
abbrev strings.TrimLeft.spec : Prop :=
  ∀ (s cutset : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.strings ∗ ⌜∀ b ∈ cutset, b.toNat < 128⌝ }}
    (App (App (Val (@! _root_.Perennial.strings.TrimLeft)) (Val #s)) (Val #cutset))
  {{ RET #(strings.trimLeft s cutset); True }}

end spec

end EtcdGrove
end Perennial
