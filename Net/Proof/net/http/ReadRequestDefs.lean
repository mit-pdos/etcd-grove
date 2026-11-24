/-
The vocabulary of `conn.readRequest`'s spec (`Net/Spec/net/http/conn__readRequest.lean`), net/http's
server reading net/rpc's `CONNECT` request on a connection, beside `ServerConn.lean`'s:

* `srvDflt s` (persistent): the server `s`'s fields `readRequest` reads are zero, as in the `Server`
  `http.Serve` makes (`&Server{Handler: handler}`): no read or write timeout, the default header
  limits (`MaxHeaderBytes`, `MaxHeaderValueCount`). So the head's read limit is `srvL`
  (`initialReadLimitSize()`, `DefaultMaxHeaderBytes + 4096`) and `maxHeaderValueCount()` is `500`.
* `rrReqVal path u m cl nb ctx ra`: the request `readRequest` returns, `readRequestLimit`'s
  (`connectReqVal`) with its context `ctx` and `RemoteAddr` (the connection's `remoteAddr`) set.
* `respNew w c req`: the response `readRequest` returns, the fields `conn.serve` and the handler's
  `Hijack` use (`hjPre`): its connection `c` and request `req`, no request body (`NoBody`), its
  context's cancel function (cancelable at any time, `context.cancelSpec`), `handlerDone` false, no
  expect-continue reader, nothing written, its buffered writer of 2048 bytes holding nothing, its
  handler header (an empty map), and its close notification (`respNotify`).
-/
module

public import Net.Proof.net.http.ServerConn
public import Net.Proof.net.http.RequestDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.http

/-- See the file header. -/
def srvL : Nat := 2 ^ 20 + 4096

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
def srvDflt (s : Loc) : IProp GF :=
  iprop(structFieldRef net.http.Server go!"ReadTimeout" s ↦□ (W64 0) ∗
    structFieldRef net.http.Server go!"WriteTimeout" s ↦□ (W64 0) ∗
    structFieldRef net.http.Server go!"MaxHeaderBytes" s ↦□ (W64 0) ∗
    structFieldRef net.http.Server go!"MaxHeaderValueCount" s ↦□ (W64 0))

instance srvDflt_persistent (s : Loc) : Persistent (srvDflt (GF := GF) s) := by
  unfold srvDflt; infer_instance

/-- See the file header. -/
def rrReqVal (path : List w8) (u m : Loc) (cl : Bool) (nb : net.http.noBody) (ctx : GoInterface)
    (ra : GoString) : net.http.Request :=
  { connectReqVal path u m cl nb with ctx' := ctx, RemoteAddr' := ra }

/-- See the file header. -/
def respNew (w c req : Loc) : IProp GF :=
  iprop(structFieldRef net.http.response go!"conn" w ↦□ c ∗
    structFieldRef net.http.response go!"req" w ↦□ req ∗
    structFieldRef net.http.response go!"reqBody" w ↦□ (null : Loc) ∗
    (∃ (f : GoFunc) (γc : context.ContextNames),
      structFieldRef net.http.response go!"cancelCtx" w ↦□ f ∗ context.cancelSpec f γc iprop(True)) ∗
    sync.atomic.ownBool (structFieldRef net.http.response go!"handlerDone" w) (DFrac.own 1) false ∗
    structFieldRef net.http.response go!"ecReader" w ↦ (null : Loc) ∗
    structFieldRef net.http.response go!"wroteHeader" w ↦ false ∗
    (∃ ww : Loc, structFieldRef net.http.response go!"w" w ↦ ww ∗ EtcdGrove.bufio.rawWriter ww 2048) ∗
    (∃ hh : Loc, structFieldRef net.http.response go!"handlerHeader" w ↦ hh ∗
      hh ↦$ (∅ : GMap GoString GoSlice)) ∗
    respNotify w)

end defs

end net.http
end Perennial
