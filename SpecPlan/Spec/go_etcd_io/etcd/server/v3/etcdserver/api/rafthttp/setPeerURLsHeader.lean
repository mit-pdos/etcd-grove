/-
## `setPeerURLsHeader(req, urls)`

**Users.** `createPostRequest`, `streamReader.dial`.

**Proof sketch.** `url.URL.String` of each, `strings.Join`, `Header.Set`. `urls.Len()` on the addressable `URLs` is 1c's `Types.URLs.Len_ptr.spec`.

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour. verify-round (second pass): the sketch cites `Types.URLs.Len_ptr.spec`.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rafthttp

open Iris Iris.BI Raft
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) Sets `X-PeerURLs` to the URLs' strings (nothing for `nil` URLs). -/
def setPeerURLsHeader.spec : Prop :=
  ∀ (r : Loc) (R : Http.HReq) (bd : GoInterface) (urls : GoSlice) (hs : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ Http.reqOwn r R bd ∗ Types.urlsAt urls hs }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.setPeerURLsHeader)) (Val #r)) (Val #urls))
  {{ RET #(); ∃ hdr', Http.reqOwn r { R with hdr := hdr' } bd ∗ ⌜peerURLsSet hs R.hdr hdr'⌝ }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
