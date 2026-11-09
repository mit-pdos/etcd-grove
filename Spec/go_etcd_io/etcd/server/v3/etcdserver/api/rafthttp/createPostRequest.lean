/-
## `createPostRequest(lg, u, path, body, ct, urls, from, cid)`

**Users.** `pipeline.post`, `snapshotSender.send`.

**Proof sketch.** `uu.Path = path`, `url.URL.String`, `http.NewRequest` (succeeds on a URL `urlOk`), five `Header.Set`s, `setPeerURLsHeader`. `types.ID`'s `String()` on an addressable `ID` (log fields, headers) is 1c's `Types.ID.String_ptr.spec` (Goose's pointer receiver).

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour. verify-round (second pass): the sketch cites `Types.ID.String_ptr.spec`.

**Margin.** The headers are opaque (`postHdrs`): only rafthttp's protocol reads them.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

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

/-- (internal) **Builds a POST request** to `u` at `path` with `body`, the content type and rafthttp's headers (`NewRequest` cannot fail on a picked URL; it would panic). -/
def createPostRequest.spec : Prop :=
  ∀ (lg : Loc) (u : _root_.Perennial.net.url.URL) (path : GoString) (body : GoInterface) (ct : GoString) (urls : GoSlice) (hs : List GoString) (frm cid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ (⌜lg = null⌝ ∨ Zap.isLogger lg) ∗ ⌜Http.urlOk u⌝ ∗ ⌜body ≠ interface.nil⌝ ∗ Types.urlsAt urls hs }}
    (App (App (App (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.createPostRequest)) (Val #lg)) (Val #u)) (Val #path)) (Val #body)) (Val #ct)) (Val #urls)) (Val #frm)) (Val #cid))
  {{ (r : Loc), RET #r; Http.reqOwn r ⟨go!"POST", u.Host', path, postHdrs ct frm cid hs⟩ body }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
