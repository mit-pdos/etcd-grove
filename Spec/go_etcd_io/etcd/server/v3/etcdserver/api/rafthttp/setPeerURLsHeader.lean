/-
`setPeerURLsHeader(req, urls)` (`util.go`; rafthttp stage 5e-3). Lean-first. Spec only for now
(as `createPostRequest`'s): its proof needs `url.URL.String` of any URL, which the HTTP boundary
states only of plain ones (`URLString_spec`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Stream

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`setPeerURLsHeader(req, urls)`** on a request being built: the request with some headers. -/
abbrev rafthttp.setPeerURLsHeader.spec : Prop :=
  ∀ (r : Loc) (R : http.HReq) (urls : GoSlice) (uvs : List net.url.URL),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ http.reqOwn r R ∗ urls ↦*□ uvs }}
    (App (App (Val (@! rafthttp.setPeerURLsHeader)) (Val #r)) (Val #urls))
  {{ RET #(); ∃ hs : List (GoString × GoString), http.reqOwn r { R with hdr := hs } }}

end spec

end EtcdGrove
end Perennial
