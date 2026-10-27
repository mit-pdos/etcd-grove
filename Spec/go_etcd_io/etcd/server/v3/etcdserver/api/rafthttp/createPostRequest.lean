/-
`createPostRequest(lg, u, path, body, ct, urls, from, cid)` (`util.go`; rafthttp stage 4d). Lean-first.
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

/-- **`createPostRequest`** of a plain URL `u` and a body reader of `bs`: a `POST` to `u`'s host
at `path` with that body (and some headers): `NewRequest` does not fail (`http.NewRequest_spec`),
so its `lg.Panic` is dead; `X-Server-From` the sender's id, and (D22 J-T, W8) `X-PeerURLs` the
transport's URLs' strings (`setPeerURLsHeader`). -/
abbrev rafthttp.createPostRequest.spec : Prop :=
  ∀ (lg : Loc) (u : net.url.URL) (path : GoString) (body : GoInterface) (K : http.Body)
    (ct : GoString) (urls : GoSlice) (uvs : List net.url.URL)
    (fr cid : go_etcd_io.etcd.client.pkg.v3.types.ID),
  lg ≠ null → urlPlain u →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      http.bodyHas body K ∗ urls ↦*□ uvs }}
    (App (App (App (App (App (App (App (App (Val (@! rafthttp.createPostRequest)) (Val #lg))
      (Val #u)) (Val #path)) (Val #body)) (Val #ct)) (Val #urls)) (Val #fr)) (Val #cid))
  {{ (req : Loc), RET #req; ∃ hdrs : List (GoString × GoString),
        http.reqOwn req ⟨go!"POST", u.Host', path, hdrs, K.bytes⟩ ∗ http.reqStream req K ∗
        ⌜http.hdrGet hdrs go!"X-Server-From" = types.idStr fr ∧
          (uvs ≠ [] → (∀ u ∈ uvs, http.urlRootPlain u) →
            http.hdrGet hdrs go!"X-PeerURLs" = peerURLsHdr uvs)⌝ }}

end spec

end EtcdGrove
end Perennial
