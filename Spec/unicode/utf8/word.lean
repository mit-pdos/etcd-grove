/-
`utf8.word` (`utf8.go`), at `string`: `ValidString`'s ASCII fast path loads eight bytes with it.
Lean-first.
-/
module

public import Proof.unicode.utf8.Base
public import Proof.unicode.utf8.ValidAscii

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `word(s)` on a string of at least eight bytes: its first eight bytes, little-endian. -/
abbrev utf8.word.spec : Prop :=
  ∀ (s : GoString), 8 ≤ s.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.unicode.utf8 }}
    (App (Val #(functions _root_.Perennial.unicode.utf8.word [go.string])) (Val #s))
  {{ RET #(utf8.wordOf s); True }}

end spec

end EtcdGrove
end Perennial
