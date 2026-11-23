/-
`readTransfer(msg, r, maxTrailerHeaders)` for a `*Response` `resp` whose header is empty (no
`Transfer-Encoding`, `Content-Length` or `Trailer`), to a request `req` other than `HEAD`: no error;
the response's body set (`NoBody`, or a body reading `r` to the connection's end), nothing read of
`r`, the status line's fields unchanged (`Status`), the header still empty. What `ReadResponse`
meets on net/rpc's answer, whose head has no header lines. `httpEnv`: `NoBody`'s value. Proved in
`Net/Proof/net/http/readTransfer.lean`.
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
abbrev readTransfer.spec : Prop :=
  ∀ (resp : Loc) (rv : net.http.Response) (r : Loc) (req : Loc) (rq : net.http.Request)
    (dq : DFrac) (maxT : w64),
  {{ httpEnv (GF := GF) ∗ resp ↦ rv ∗ rv.Header' ↦$ (∅ : GMap GoString GoSlice) ∗ ⌜rv.Request' = req⌝ ∗ req ↦{dq} rq ∗
      ⌜rq.Method' ≠ go!"HEAD"⌝ }}
    (App (App (App (Val (@! net.http.readTransfer))
      (Val #(interface.mkOk (go.GoType.PointerType net.http.Response.ty) #resp))) (Val #r)) (Val #maxT))
  {{ RET #interface.nil; ∃ rv' : net.http.Response, resp ↦ rv' ∗ ⌜rv'.Status' = rv.Status'⌝ ∗
      rv.Header' ↦$ (∅ : GMap GoString GoSlice) ∗ req ↦{dq} rq }}

end spec

end net.http
end Perennial
