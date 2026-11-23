/-
`w.Hijack()` (the model's `server.go`) on the response `w` of a connection whose head `hs` the server
read and whose background read it started (`hjPre`, what `conn.serve` has when it calls the handler):
the right to call it, `hijackOk` (its weakest precondition), with the serving thread's resources
`hjDone` given back through the handler: the handler not done, no expect-continue reader, nothing
written; under the connection's mutex `hijackLocked` (the background read aborted, the connection
returned with exactly the head read and nothing written), the response's writer put back in its
pool. Proved in `Net/Proof/net/http/response__Hijack.lean`.
-/
module

public import Net.Proof.net.http.ServerConn
public import Net.Proof.net.http.ServerDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.http

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev response.Hijack.spec : Prop :=
  ∀ (N : HjNames) (P Q : Proto GF) (hs : List w8) (Z : Nat → IProp GF),
  hjPre N P Q hs Z ⊢ hijackOk N.w N.cn N.a P Q hs (hjDone N hs)

end spec

end net.http
end Perennial
