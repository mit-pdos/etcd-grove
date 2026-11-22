/-
`internal/stringslite.HasPrefix(s, prefix)`: whether `s` begins with `prefix`. **A hypothesis** (of
`filepathlite.IsAbs`'s proof), not proved here and not an axiom: the pinned Perennial translates
`internal/stringslite` names-only but for `HasSuffix`, `TrimSuffix` (and the trusted `Clone`). The
statement is Perennial's branch `stringslite-hasprefix`'s `internal.stringslite.HasPrefix.spec`
(`d508df6ff`: `HasPrefix` translated with its body, `len(s) >= len(prefix) && s[:len(prefix)] ==
prefix`, and proved); once the pin reaches it, this file goes and `IsAbs`'s proof takes Perennial's
(`notes/perennial-changes.md`, "`internal/stringslite.HasPrefix`"). Lean-first.
-/
module

public import Perennial.Proof.internal.stringslite.Base

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

/-- `stringslite.HasPrefix(s, prefix)`: whether `s` begins with `prefix` (Perennial's statement). -/
abbrev stringslite.HasPrefix.spec : Prop :=
  ∀ (s pre : GoString),
    {{ (True : IProp GF) }}
      (App (App (Val (@! _root_.Perennial.internal.stringslite.HasPrefix)) (Val #s)) (Val #pre))
    {{ RET #(decide (pre <+: s)); True }}

end spec

end EtcdGrove
end Perennial
