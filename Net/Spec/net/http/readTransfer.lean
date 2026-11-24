/-
`readTransfer(msg, r, maxTrailerHeaders)` on a message whose header map `ms` has no
`Transfer-Encoding`, `Content-Length` or `Trailer`: no error, nothing read of `r`, and

* (`msg` a `*Response` `resp` to a request `req` other than `HEAD`, the values of its `"Connection"`
  header owned, `hdrVals`) the response's body set (`NoBody`, or a body reading `r` to the
  connection's end), its status unchanged (`Status`), the header unchanged or without its
  `"Connection"` entry (`shouldClose`'s). What `ReadResponse` meets on net/rpc's answer, whose head has
  no header lines, and on net/http's `400` answer (`Content-Type`, `Connection: close`).
* (`msg` a `*Request` `req`) the request without a body: `Body` `NoBody`, `ContentLength` `0`,
  `Trailer` `nil`, the rest unchanged (`Close` too), the header unchanged. What `readRequestLimit`
  meets on net/rpc's `CONNECT` request.

`httpEnv`: `NoBody`'s value. Proved in `Net/Proof/net/http/readTransfer.lean`.
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
  (∀ (resp : Loc) (rv : net.http.Response) (ms : GMap GoString GoSlice) (r : Loc) (req : Loc)
    (rq : net.http.Request) (dq : DFrac) (maxT : w64),
  {{ httpEnv (GF := GF) ∗ resp ↦ rv ∗ rv.Header' ↦$ ms ∗ hdrVals ms go!"Connection" ∗
      ⌜ms !! go!"Transfer-Encoding" = none ∧ ms !! go!"Content-Length" = none ∧
        ms !! go!"Trailer" = none⌝ ∗
      ⌜rv.Request' = req⌝ ∗ req ↦{dq} rq ∗ ⌜rq.Method' ≠ go!"HEAD"⌝ }}
    (App (App (App (Val (@! net.http.readTransfer))
      (Val #(interface.mkOk (go.GoType.PointerType net.http.Response.ty) #resp))) (Val #r)) (Val #maxT))
  {{ RET #interface.nil; ∃ (rv' : net.http.Response) (ms' : GMap GoString GoSlice), resp ↦ rv' ∗
      ⌜rv'.Status' = rv.Status'⌝ ∗ rv.Header' ↦$ ms' ∗ hdrVals ms go!"Connection" ∗
      ⌜ms' = ms ∨ ms' = GMap.delete go!"Connection" ms⌝ ∗ req ↦{dq} rq }}) ∧
  (∀ (req : Loc) (rqv : net.http.Request) (ms : GMap GoString GoSlice) (r : Loc) (maxT : w64),
  {{ httpEnv (GF := GF) ∗ req ↦ rqv ∗ rqv.Header' ↦$ ms ∗
      ⌜ms !! go!"Transfer-Encoding" = none ∧ ms !! go!"Content-Length" = none ∧
        ms !! go!"Trailer" = none⌝ }}
    (App (App (App (Val (@! net.http.readTransfer))
      (Val #(interface.mkOk (go.GoType.PointerType net.http.Request.ty) #req))) (Val #r)) (Val #maxT))
  {{ RET #interface.nil; ∃ (nb : net.http.noBody) (rqv' : net.http.Request), req ↦ rqv' ∗
      ⌜rqv' = reqNoBody rqv nb⌝ ∗ rqv.Header' ↦$ ms }})

end spec

end net.http
end Perennial
