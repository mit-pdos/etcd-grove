/-
`strings.TrimPrefix(s, prefix)` (Go's standard library). Perennial does not translate it: the
trust boundary (an axiom, `Proof/strings/TrimPrefix.lean`), for `client/v3/leasing`'s
`serverTxn` and `revokeLeaseKvs`. Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Proof.strings

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

/-- What `strings.TrimPrefix(s, pfx)` returns: `s` without the prefix `pfx` if it has it, else
`s`. -/
def trimPrefixResult (s pfx : GoString) : GoString := if pfx <+: s then s.drop pfx.length else s

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `strings.TrimPrefix(s, pfx)`: `trimPrefixResult s pfx`. -/
abbrev strings.TrimPrefix.spec : Prop :=
  ∀ (s pfx : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
    (App (App (Val #(functions _root_.Perennial.strings.TrimPrefix [])) (Val #s)) (Val #pfx))
  {{ RET #(trimPrefixResult s pfx); True }}

end spec

end EtcdGrove
end Perennial
