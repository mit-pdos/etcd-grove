/-
`setPeerURLsHeader(req, urls)` (`util.go`; rafthttp stage 5e-3). Lean-first. (Proved in stage 6e,
2026-10-24, over `url.URL.String` of any URL, `URLStringAny_spec`; its post since then says the
other headers are kept, what `createPostRequest`'s `X-Server-From` needs; since D22 J-T,
2026-10-27, the header's value, what the protocol's `X-PeerURLs` needs, W8.)
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Stream

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

/-- **`setPeerURLsHeader(req, urls)`** on a request being built: the request with some headers,
the others kept; (2026-10-27, D22 J-T, W8) of URLs of only the scheme `http` and a plain host,
`X-PeerURLs` their strings (`http://host`) joined by `,` (`peerURLsHdr`); (http-boundary-fix,
2026-11-14) no idempotency key added (`http.noIdemKey`). (fmt stage 1, 2026-11-24) The URLs within
etcd's URL length bound (`plainURLsFit`): `strings.Join` of their strings must stay below its length
bound (the transport's configured URLs are, `trURLsOk.fit`). -/
abbrev rafthttp.setPeerURLsHeader.spec : Prop :=
  ∀ (r : Loc) (R : http.HReq) (urls : GoSlice) (uvs : List net.url.URL),
  plainURLsFit uvs →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ http.reqOwn r R ∗ urls ↦*□ uvs }}
    (App (App (Val (@! rafthttp.setPeerURLsHeader)) (Val #r)) (Val #urls))
  {{ RET #(); ∃ hs : List (GoString × GoString),
      ⌜∀ k, http.canonKey k ≠ http.canonKey go!"X-PeerURLs" → http.hdrGet hs k = http.hdrGet R.hdr k⌝ ∗
      ⌜uvs ≠ [] → (∀ u ∈ uvs, http.urlRootPlain u) →
        http.hdrGet hs go!"X-PeerURLs" = peerURLsHdr uvs⌝ ∗
      ⌜http.noIdemKey R.hdr → http.noIdemKey hs⌝ ∗
      http.reqOwn r { R with hdr := hs } }}

end spec

end EtcdGrove
end Perennial
