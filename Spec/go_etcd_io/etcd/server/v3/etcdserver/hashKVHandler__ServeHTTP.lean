/-
`h.ServeHTTP(w, r)` (`corrupt.go`): the peer hashKV handler, `/members/hashkv`, as PR
etcd#22243 changes it (2026-10-17): its request body is read through
`http.MaxBytesReader(w, r.Body, maxHashKVHTTPRequestSize)`, so it consumes at most 64 KiB and
one byte of the body, and a longer body gets `413 Request Entity Too Large` without being
decoded. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvHashKV

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3
  go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The peer hashKV handler** `h.ServeHTTP(w, r)`, for a request `q` with body content `c`,
the server's store hashing per `R`; the response `w` had `evs` before. It returns, having
appended `evs'` to the response, and either
* rejects the request before reading its body (the body untouched): a method other than `GET`
  (`Allow: GET`, 405), another path (400), a cluster id header that is not empty and differs
  from the server's (412; the server's id is `types.ID.String`'s, unspecified here, so the spec
  says only that the header is not empty);
* or reads the body, consuming at most `maxHashKVBody + 1` bytes of it (`bodyClosed` with
  `c.drop k`, `k ≤ maxHashKVBody + 1`), closes it, and responds as `hashKVBodyServed` says:
  413 for a body over the bound, without decoding it or hashing. -/
abbrev hashKVHandler.ServeHTTP.spec : Prop :=
  ∀ (h r : Loc) (w : GoInterface) (q : http.Req) (c : http.BodyContent)
    (R : w64 → go_etcd_io.etcd.server.v3.storage.mvcc.KeyValueHash → w64 → Prop) (evs : List http.RespEv),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      hashKVHandlerOk h R ∗ http.respWriterOk w ∗ http.respLog w evs ∗
      http.reqIs r q ∗ http.bodyOk q.body ∗ http.bodyR q.body c }}
    (App (App (Val (h @!! go.GoType.PointerType hashKVHandler.ty @!! go!"ServeHTTP")) (Val #w))
      (Val #r))
  {{ RET #(); ∃ evs' : List http.RespEv, http.respLog w (evs ++ evs') ∗
      ((⌜q.method ≠ go!"GET" ∧
          evs' = [.header go!"Allow" go!"GET", .error (W64 405) go!"Method Not Allowed"]⌝ ∗
          http.bodyR q.body c) ∨
       (⌜q.method = go!"GET" ∧ q.path ≠ go!"/members/hashkv" ∧
          evs' = [.error (W64 400) go!"bad path"]⌝ ∗ http.bodyR q.body c) ∨
       (⌜q.method = go!"GET" ∧ q.path = go!"/members/hashkv" ∧ q.clusterHdr ≠ go!"" ∧
          ∃ msg, evs' = [.error (W64 412) msg]⌝ ∗ http.bodyR q.body c) ∨
       (⌜q.method = go!"GET" ∧ q.path = go!"/members/hashkv" ∧ hashKVBodyServed c R evs'⌝ ∗
          http.bodyClosed q.body (c.drop (min c.data.length (maxHashKVBody + 1))))) }}

end spec

end EtcdGrove
end Perennial
