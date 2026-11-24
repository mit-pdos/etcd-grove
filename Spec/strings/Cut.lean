/-
`strings.Cut(s, sep)`: the text before and after the first instance of `sep` in `s`, and `true`; or
`s`, `""` and `false` when `sep` does not occur (`strings.cut`, `Proof/strings/CutDefs.lean`). Pending:
Perennial translates `strings.Cut` as a name only at the pin; its branch `strings-cut-lastindex`
(`8ff6a1c79a`) translates Go's body, not proved yet (`notes/perennial-changes.md`). No proof file:
the Links that reach it take this spec as a hypothesis (`section links_pending`). Lean-first.
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
abbrev strings.Cut.spec : Prop :=
  ∀ (s sep : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
    (App (App (Val (@! _root_.Perennial.strings.Cut)) (Val #s)) (Val #sep))
  {{ RET (PairV (PairV #(strings.cut s sep).1 #(strings.cut s sep).2.1) #(strings.cut s sep).2.2);
      True }}

end spec

end EtcdGrove
end Perennial
