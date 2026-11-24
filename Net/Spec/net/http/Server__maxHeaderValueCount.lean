/-
`s.maxHeaderValueCount()`: the `Server`'s `MaxHeaderValueCount` field `n` (read with any fraction) if
it is positive, else `DefaultMaxHeaderValueCount` (500); not negative either way (`conn.readRequest`
passes it to `readRequestLimit` as the header lines' bound). Proved in
`Net/Proof/net/http/Server__maxHeaderValueCount.lean`.
-/
module

public import Net.Proof.net.http.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.http

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

/-- See the file header. -/
abbrev Server.maxHeaderValueCount.spec : Prop :=
  ∀ (s : Loc) (n : w64) (dq : DFrac),
  {{ (structFieldRef net.http.Server go!"MaxHeaderValueCount" s ↦{dq} n : IProp GF) }}
    (App (Val #(methods (go.GoType.PointerType net.http.Server.ty) go!"maxHeaderValueCount" #s))
      (Val #()))
  {{ RET #(if 0 < sint.Z n then n else W64 500);
      structFieldRef net.http.Server go!"MaxHeaderValueCount" s ↦{dq} n }}

end spec

end net.http
end Perennial
