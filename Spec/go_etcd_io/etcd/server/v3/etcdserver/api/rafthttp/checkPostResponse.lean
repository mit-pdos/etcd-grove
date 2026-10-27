/-
`checkPostResponse(lg, resp, body, req, to)` (`util.go`; rafthttp stage 4d). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Sender

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`checkPostResponse`** of a response of status `st`: an error of `postErr st` (`nil` for a
`204`). -/
abbrev rafthttp.checkPostResponse.spec : Prop :=
  ∀ (lg resp : Loc) (st : w64) (rd : GoInterface) (b : GoSlice) (bs : List w8) (req : Loc)
    (R : http.HReq) (to : go_etcd_io.etcd.client.pkg.v3.types.ID)
    (Hd : List (GoString × GoString) → Prop),
  lg ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      http.respAt resp st rd Hd ∗ b ↦* bs ∗ http.reqOwn req R }}
    (App (App (App (App (App (Val (@! rafthttp.checkPostResponse)) (Val #lg)) (Val #resp))
      (Val #b)) (Val #req)) (Val #to))
  {{ (err : GoInterface), RET #err; postErr st err }}

end spec

end EtcdGrove
end Perennial
