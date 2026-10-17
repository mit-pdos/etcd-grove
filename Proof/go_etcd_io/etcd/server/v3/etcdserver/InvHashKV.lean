/-
The peer hashKV handler's world (`corrupt.go`'s `hashKVHandler.ServeHTTP`; PR etcd#22243,
2026-10-17): what the handler sees of `net/http`, of the request body and of `encoding/json`,
all three names-only, and the premises its spec takes. Lean-first (no Rocq counterpart).

**The trust boundary** (axiomatized predicates, introduced by nothing but the caller's
premises; their operations are the postulates `Spec/net/http/*`, `Spec/io/ReadAllMaxBytes`,
`Spec/encoding/json/*`):

* `http.respLog w evs`: the response writer `w`'s state, the list `evs` of what the handler
  asked of it (`RespEv`: a header set, an `http.Error`, a body write), in order. Owned by the
  goroutine serving the request (net/http's contract: a `ResponseWriter` is not used after
  `ServeHTTP` returns, nor concurrently).
* `http.respHdr w hm` (persistent): `hm` is `w`'s header map (`w.Header()`'s result).
* `http.reqHdrGet hp k v` (persistent): the request's header map at `hp` (`&r.Header`) maps
  `k` (canonically) to the first value `v` (`Get` returns `v`; `""` if none).
* `http.bodyR body c`: the request body `body` has `c` left to read (`BodyContent`: the bytes
  `c.data` the client sends, then end of stream or a read error); owned by the serving goroutine.
* `http.bodyClosed body c`: `body` is closed with `c` left unread.
* `http.maxBytesR lr body n` (persistent): `lr` is `http.MaxBytesReader(w, body, n)`'s reader.
* `json.hashKVReqOf bs` (an uninterpreted function): the revision `json.Unmarshal(bs, req)`
  decodes into a zero `HashKVRequest`, or `none` if it fails.
* `json.hashKVRespJSON hrev h crev hashRev` (an uninterpreted function): what `json.Marshal`
  encodes a `HashKVResponse` with these four fields set (and no others) to.

**The premises of the handler's spec** (defined): `http.respWriterOk w` (the writer's methods
`Header` and `Write` act on `respLog`), `http.bodyOk body` (the body's `Close`), `http.reqIs r q`
(the request's fields, read-only), `hashKVOk kv R` (the server's KV: `HashStorage().HashByRev(rev)`
returns a hash related to `rev` by `R`, or an error whose `Error()` returns; what `R` is, is the
store's business, under the store's own concurrency: the handler takes no lock).

**What the handler does** (`hashKVServed`): the response events of each outcome, and how much
of the body it consumes (`maxHashKVBody + 1` bytes at most: `MaxBytesReader`'s bound).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Defs
public import Perennial.Proof.errors

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3
  go_etcd_io.etcd.cache.v3

/-- An event of a response: `w.Header().Set(k, v)`, `http.Error(w, msg, code)` (which sets
the error's headers, writes the status `code` and `msg`), or `w.Write(bs)`. -/
inductive http.RespEv [FfiSyntax] where
  | header (k v : GoString)
  | error (code : w64) (msg : GoString)
  | write (bs : List w8)

/-- What a request body holds: the bytes `data` it yields, then the end of the stream
(`err = none`) or a read error `err = some e` (not `nil`, not `io.EOF`). -/
structure http.BodyContent [FfiSyntax] where
  data : List w8
  err : Option GoInterfaceOk

/-- The body `c` with its first `k` bytes read. -/
def http.BodyContent.drop [FfiSyntax] (c : http.BodyContent) (k : Nat) : http.BodyContent :=
  { data := c.data.drop k, err := c.err }

/-- The request fields the handler reads. -/
structure http.Req [FfiSyntax] where
  method : GoString
  path : GoString
  clusterHdr : GoString
  body : GoInterface

/-- The handler's body bound, `maxHashKVHTTPRequestSize` (64 KiB). -/
abbrev maxHashKVBody : Nat := 65536

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

abbrev http.reqField (r : Loc) (f : GoString) : Loc :=
  structFieldRef _root_.Perennial.net.http.Request f r
abbrev http.urlPathAddr (u : Loc) : Loc := structFieldRef _root_.Perennial.net.url.URL go!"Path" u
abbrev hkvLgAddr (h : Loc) : Loc := structFieldRef hashKVHandler go!"lg" h
abbrev hkvServerAddr (h : Loc) : Loc := structFieldRef hashKVHandler go!"server" h

end addrs

/-! ### The trust boundary: axiomatized predicates and functions -/

axiom http.respLog {GF : BundledGFunctors} [FfiSyntax] (w : GoInterface)
  (evs : List http.RespEv) : IProp GF
axiom http.respHdr {GF : BundledGFunctors} [FfiSyntax] (w : GoInterface) (hm : Loc) : IProp GF
axiom http.respHdr_persistent {GF : BundledGFunctors} [FfiSyntax] (w : GoInterface) (hm : Loc) :
  Persistent (http.respHdr (GF := GF) w hm)
axiom http.reqHdrGet {GF : BundledGFunctors} [FfiSyntax] (hp : Loc) (k v : GoString) : IProp GF
axiom http.reqHdrGet_persistent {GF : BundledGFunctors} [FfiSyntax] (hp : Loc) (k v : GoString) :
  Persistent (http.reqHdrGet (GF := GF) hp k v)
axiom http.bodyR {GF : BundledGFunctors} [FfiSyntax] (body : GoInterface)
  (c : http.BodyContent) : IProp GF
axiom http.bodyClosed {GF : BundledGFunctors} [FfiSyntax] (body : GoInterface)
  (c : http.BodyContent) : IProp GF
axiom http.maxBytesR {GF : BundledGFunctors} [FfiSyntax] (lr body : GoInterface) (n : w64) :
  IProp GF
axiom http.maxBytesR_persistent {GF : BundledGFunctors} [FfiSyntax] (lr body : GoInterface)
  (n : w64) : Persistent (http.maxBytesR (GF := GF) lr body n)

attribute [instance] http.respHdr_persistent http.reqHdrGet_persistent http.maxBytesR_persistent

/-- `*http.MaxBytesError` implements `error` (its method `Error() string`), so it can be the
target type of `errors.As`. Method sets are uninterpreted in the semantics: an assumption about
`net/http`, as `context.ErrorStringIsError` is about `context`. -/
axiom http.maxBytesError_asTarget [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions] :
  _root_.Perennial.errors.AsTarget
    (go.GoType.PointerType _root_.Perennial.net.http.MaxBytesError.ty)

/-- The revision `json.Unmarshal(bs, req)` decodes into a zero `HashKVRequest`, or `none` if it
returns an error. -/
axiom json.hashKVReqOf [FfiSyntax] : List w8 → Option w64

/-- `json.Marshal` of a `HashKVResponse` whose header is a `ResponseHeader` with only `Revision`
set (`hrev`), and with `Hash`, `CompactRevision`, `HashRevision` set (and nothing else). -/
axiom json.hashKVRespJSON [FfiSyntax] : w64 → w32 → w64 → w64 → List w8

/-- The response header the handler builds: only `Revision` set. -/
def hkvRespHeader [FfiSyntax] (hrev : w64) : etcdserverpb.ResponseHeader :=
  etcdserverpb.ResponseHeader.mk zeroValDef 0 0 hrev 0 0 zeroValDef 0

/-- The response the handler builds: only `Header`, `Hash`, `CompactRevision`, `HashRevision`
set. -/
def hkvResp [FfiSyntax] (p : Loc) (h : w32) (crev hashRev : w64) : etcdserverpb.HashKVResponse :=
  etcdserverpb.HashKVResponse.mk zeroValDef p h crev hashRev zeroValDef 0

/-! ### The handler's outcomes -/

/-- The handler's response once it reads the body `c` (of a `GET` of the right path with an
acceptable cluster id), given the store's hash relation `R`. -/
def hashKVBodyServed [FfiSyntax] (c : http.BodyContent) (R : w64 → go_etcd_io.etcd.server.v3.storage.mvcc.KeyValueHash → w64 → Prop)
    (evs : List http.RespEv) : Prop :=
  -- the body is longer than the bound: 413, nothing decoded, no hash computed
  (maxHashKVBody < c.data.length ∧
    evs = [.error (W64 413) go!"request body too large"]) ∨
  -- the body fails within the bound: 413 if its error is a `MaxBytesError`, else 400
  (c.data.length ≤ maxHashKVBody ∧ c.err.isSome ∧
    (evs = [.error (W64 413) go!"request body too large"] ∨
     evs = [.error (W64 400) go!"error reading body"])) ∨
  -- the body is read whole
  (c.data.length ≤ maxHashKVBody ∧ c.err = none ∧
    match json.hashKVReqOf c.data with
    | none => evs = [.error (W64 400) go!"error unmarshalling request"]
    | some rev =>
      (∃ msg, evs = [.error (W64 400) msg]) ∨
      ∃ (kvh : go_etcd_io.etcd.server.v3.storage.mvcc.KeyValueHash) (crev : w64), R rev kvh crev ∧
        ((∃ msg, evs = [.error (W64 500) msg]) ∨
         ∃ sid, evs = [.header go!"X-Etcd-Cluster-ID" sid,
                       .header go!"Content-Type" go!"application/json",
                       .write (json.hashKVRespJSON crev kvh.Hash' kvh.CompactRevision'
                         kvh.Revision')]))

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The response writer `w`** (persistent): an interface value whose `Header()` returns its
header map and whose `Write(bs)` appends `bs` to the response (and returns some count and error). -/
def http.respWriterOk (w : GoInterface) : IProp GF :=
  iprop(∃ ii : GoInterfaceOk, ⌜w = GoInterface.ok ii⌝ ∗
    (□ ∀ (evs : List http.RespEv),
      {{ http.respLog w evs }}
        (App (Val #(methods ii.ty go!"Header" ii.v)) (Val #()))
      {{ (hm : Loc), RET #hm; http.respLog w evs ∗ http.respHdr w hm }}) ∗
    (□ ∀ (evs : List http.RespEv) (sl : GoSlice) (dq : DFrac) (bs : List w8),
      {{ http.respLog w evs ∗ sl ↦*{dq} bs }}
        (App (Val #(methods ii.ty go!"Write" ii.v)) (Val #sl))
      {{ (n : w64) (e : GoError), RET (PairV #n #e); http.respLog w (evs ++ [.write bs]) ∗
          sl ↦*{dq} bs }}))

instance http.respWriterOk_persistent (w : GoInterface) :
    Persistent (http.respWriterOk (GF := GF) w) := by
  unfold http.respWriterOk; infer_instance

/-- **The request body `body`** (persistent): an interface value whose `Close()` closes it, with
whatever is left unread. -/
def http.bodyOk (body : GoInterface) : IProp GF :=
  iprop(∃ ii : GoInterfaceOk, ⌜body = GoInterface.ok ii⌝ ∗
    □ ∀ (c : http.BodyContent),
      {{ http.bodyR body c }}
        (App (Val #(methods ii.ty go!"Close" ii.v)) (Val #()))
      {{ (e : GoError), RET #e; http.bodyClosed body c }})

instance http.bodyOk_persistent (body : GoInterface) :
    Persistent (http.bodyOk (GF := GF) body) := by
  unfold http.bodyOk; infer_instance

/-- **The request `r`** (persistent: the handler only reads it): its method, its URL's path, its
`X-Etcd-Cluster-ID` header and its body. -/
def http.reqIs (r : Loc) (q : http.Req) : IProp GF :=
  iprop(∃ u : Loc, http.reqField r go!"Method" ↦□ q.method ∗ http.reqField r go!"URL" ↦□ u ∗
    http.urlPathAddr u ↦□ q.path ∗
    http.reqHdrGet (http.reqField r go!"Header") go!"X-Etcd-Cluster-ID" q.clusterHdr ∗
    http.reqField r go!"Body" ↦□ q.body)

instance http.reqIs_persistent (r : Loc) (q : http.Req) :
    Persistent (http.reqIs (GF := GF) r q) := by
  unfold http.reqIs; infer_instance

/-- The store's `HashByRev(rev)` (persistent): returns a hash `kvh` and the current revision
`crev` related to `rev` by `R`, or an error whose `Error()` returns. -/
def hashByRevOk (hs : GoInterface) (R : w64 → go_etcd_io.etcd.server.v3.storage.mvcc.KeyValueHash → w64 → Prop) : IProp GF :=
  iprop(∃ ii : GoInterfaceOk, ⌜hs = GoInterface.ok ii⌝ ∗
    □ ∀ (rev : w64),
      {{ True }}
        (App (Val #(methods ii.ty go!"HashByRev" ii.v)) (Val #rev))
      {{ (kvh : go_etcd_io.etcd.server.v3.storage.mvcc.KeyValueHash) (crev : w64) (err : GoError), RET (PairV (PairV #kvh #crev) #err);
          (⌜err = interface.nil⌝ → ⌜R rev kvh crev⌝) ∗
          (∀ e, ⌜err = GoInterface.ok e⌝ → errorStringSpec e) }})

/-- **The server's KV `kv`** (persistent): `kv.HashStorage()` returns a hash storage whose
`HashByRev` is `hashByRevOk` with `R`. -/
def hashKVOk (kv : GoInterface) (R : w64 → go_etcd_io.etcd.server.v3.storage.mvcc.KeyValueHash → w64 → Prop) : IProp GF :=
  iprop(∃ ii : GoInterfaceOk, ⌜kv = GoInterface.ok ii⌝ ∗
    □ {{ True }}
        (App (Val #(methods ii.ty go!"HashStorage" ii.v)) (Val #()))
      {{ (hs : GoInterface), RET #hs; hashByRevOk hs R }})

instance hashByRevOk_persistent (hs : GoInterface) (R : w64 → go_etcd_io.etcd.server.v3.storage.mvcc.KeyValueHash → w64 → Prop) :
    Persistent (hashByRevOk (GF := GF) hs R) := by
  unfold hashByRevOk; infer_instance

instance hashKVOk_persistent (kv : GoInterface) (R : w64 → go_etcd_io.etcd.server.v3.storage.mvcc.KeyValueHash → w64 → Prop) :
    Persistent (hashKVOk (GF := GF) kv R) := by
  unfold hashKVOk; infer_instance

/-- **The handler `h`** (persistent): its logger `lg` (not nil) and server `s`; of the server,
the cluster `cl` (its id `cid`), the KV `kv` (its hash storage, with `R`), and `rafthttp`'s
`ErrClusterIDMismatch` (an error whose `Error()` returns). -/
def hashKVHandlerOk (h : Loc) (R : w64 → go_etcd_io.etcd.server.v3.storage.mvcc.KeyValueHash → w64 → Prop) : IProp GF :=
  iprop(∃ (lg s cl : Loc) (cid : w64) (kv : GoInterface) (em : GoInterfaceOk),
    hkvLgAddr h ↦□ lg ∗ ⌜lg ≠ null⌝ ∗ hkvServerAddr h ↦□ s ∗
    srvClusterAddr s ↦□ cl ∗ membership.clusterCid cl cid ∗
    srvKVAddr s ↦□ kv ∗ hashKVOk kv R ∗
    globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.ErrClusterIDMismatch ↦□
      GoInterface.ok em ∗ errorStringSpec em)

instance hashKVHandlerOk_persistent (h : Loc) (R : w64 → go_etcd_io.etcd.server.v3.storage.mvcc.KeyValueHash → w64 → Prop) :
    Persistent (hashKVHandlerOk (GF := GF) h R) := by
  unfold hashKVHandlerOk; infer_instance

end defs

end EtcdGrove
end Perennial
