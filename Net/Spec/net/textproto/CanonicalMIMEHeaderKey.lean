/-
`textproto.CanonicalMIMEHeaderKey(s)` (Go 1.27.3) on a key its quick check accepts as it is
(`canonQuick s`, `Net/Proof/net/http/Defs.lean`: a key already canonical, e.g. `"Content-Length"`):
`s`, without the canonicalization (and the common-header table it reads). Proved in
`Net/Proof/net/textproto/CanonicalMIMEHeaderKey.lean`.
-/
module

public import Net.Proof.net.http.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.textproto

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.textproto.Assumptions]

/-- See the file header. -/
abbrev CanonicalMIMEHeaderKey.spec : Prop :=
  ∀ (s : GoString),
  {{ (⌜net.http.canonQuick s = true⌝ : IProp GF) }}
    (App (Val (@! net.textproto.CanonicalMIMEHeaderKey)) (Val #s))
  {{ RET #s; True }}

end spec

end net.textproto
end Perennial
