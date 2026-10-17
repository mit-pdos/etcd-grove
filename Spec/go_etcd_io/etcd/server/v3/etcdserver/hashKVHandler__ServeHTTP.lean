/-
`h.ServeHTTP(w, r)` (`corrupt.go`): the peer hashKV handler, `/members/hashkv`, as PR
etcd#22243 changes it (2026-10-17): its request body is read through
`http.MaxBytesReader(w, r.Body, maxHashKVHTTPRequestSize)`, so it consumes at most 64 KiB and
one byte of the body, and a longer body gets `413 Request Entity Too Large` without being
decoded. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvHashKV
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String

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
the server's cluster id `cid` and its store hashing per `R`; the response `w` had `evs` before.
It returns, having appended `evs'` to the response, and either
* rejects the request before reading its body (the body untouched): a method other than `GET`
  (`Allow: GET`, 405), another path (400), a cluster id header that is neither empty nor the
  server's id string (`types.idStr cid`; 412);
* or reads the body, reading at most `maxHashKVBody + 1` bytes of it (`bodyClosed` with
  `c.drop k` left, `k ≤ maxHashKVBody + 1`), closes it, and responds as `hashKVBodyServed` says.
  For a body over the bound the response is exactly the 413 error (that the body is not decoded
  nor a hash computed is not stated: decoding and `HashByRev` leave no trace here, but the code
  does neither). -/
abbrev hashKVHandler.ServeHTTP.spec : Prop :=
  ∀ (h r : Loc) (w : GoInterface) (q : http.Req) (c : http.BodyContent) (cid : w64)
    (R : w64 → go_etcd_io.etcd.server.v3.storage.mvcc.KeyValueHash → w64 → Prop)
    (evs : List http.RespEv),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      hashKVHandlerOk h cid R ∗ http.respWriterOk w ∗ http.respLog w evs ∗
      http.reqIs r q ∗ http.bodyOk q.body ∗ http.bodyR q.body c ∗ http.bodyErrOk c }}
    (App (App (Val (h @!! go.GoType.PointerType hashKVHandler.ty @!! go!"ServeHTTP")) (Val #w))
      (Val #r))
  {{ RET #(); ∃ evs' : List http.RespEv, http.respLog w (evs ++ evs') ∗
      ((⌜q.method ≠ go!"GET" ∧
          evs' = [.header go!"Allow" go!"GET", .error (W64 405) go!"Method Not Allowed"]⌝ ∗
          http.bodyR q.body c) ∨
       (⌜q.method = go!"GET" ∧ q.path ≠ go!"/members/hashkv" ∧
          evs' = [.error (W64 400) go!"bad path"]⌝ ∗ http.bodyR q.body c) ∨
       (⌜q.method = go!"GET" ∧ q.path = go!"/members/hashkv" ∧ q.clusterHdr ≠ go!"" ∧
          q.clusterHdr ≠ types.idStr cid ∧ ∃ msg, evs' = [.error (W64 412) msg]⌝ ∗
          http.bodyR q.body c) ∨
       (⌜q.method = go!"GET" ∧ q.path = go!"/members/hashkv" ∧
          (q.clusterHdr = go!"" ∨ q.clusterHdr = types.idStr cid) ∧
          hashKVBodyServed c R (types.idStr cid) evs'⌝ ∗
          http.bodyClosed q.body (c.drop (min c.data.length (maxHashKVBody + 1))))) }}

end spec

end EtcdGrove
end Perennial
