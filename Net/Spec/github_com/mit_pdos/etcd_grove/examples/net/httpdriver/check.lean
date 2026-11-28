/- Lean-first (no Rocq counterpart).

`check(q, resp, body)` of the request `d` and an answer `resp` (its status, its header map holding its
written lines but `Connection`, `dropConn`) whose body is `body`, of which `chkPre` holds (the server's
`400`, or its handler's complete answer): it returns (no panic).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net
open net.http (HReq HProto Resp RespSlot ReqSlot HdrLine HttpProtoGS RespSt)

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : NetProtoGS] [hπ : HttpProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- See the file header. -/
abbrev check.spec : Prop :=
  ∀ (q : request) (d : DReq) (resp : Loc) (rv : net.http.Response) (hc : List HdrLine)
    (body : GoString),
    qOf q d → chkPre d rv.StatusCode' hc body →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver ∗
      drvFacts ∗ resp ↦□ rv ∗ net.http.hdrOwn (GF := GF) rv.Header' (net.http.dropConn hc) }}
    (App (App (App (Val (@! check)) (Val #q)) (Val #resp)) (Val #body))
  {{ RET #(); True }}

end spec
end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial
