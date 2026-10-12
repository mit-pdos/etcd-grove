/-
The gRPC KV service's heap vocabulary (unit 1 of the request path): what the checks' and the
handlers' specs say of their requests, of the response header they fill, and of the server
they call. Lean-first (no Rocq counterpart); plan: `notes/decisions.md`, "The request path".

**The requests as the checks read them** (`reqOpIs p u`, `reqOpsIs`, `txnReqIs`, persistent):
the `*pb.RequestOp` `p` denotes the checks' `ReqOp` `u` (`Defs.lean`): not nil, its `Request`
oneof the wrapper of `u`'s kind holding a non-nil request that denotes it (`txn.rangeRequestIs`,
`putRequestIs`, `deleteRangeRequestIs`, a nested `*pb.TxnRequest` recursively), or `nil` for
`ReqOp.empty`. A `nil` `*pb.RequestOp` or a wrapper holding a `nil` request is left out: the
checks dereference both (`u.Request`, `r.Key`), and protobuf-go never decodes either. As the
txn package's `requestOpIs`, but keeping a put's value and lease (what `checkPutRequest`
reads) and the empty oneof (what `checkRequestOp` rejects); `reqOpsIs_requestOpsIs`
(`CheckLemmas.lean`) gives the txn package's predicate of a request whose operations are all
non-empty. **Off the wire** (`reqOpsWire`, `txnReqWire`): every delete's `RangeEnd` is `nil` or
not empty, as protobuf-go decodes it; `checkIntervals` reads an empty one as a point
(`len == 0`), the model (`txn.rangeEndOf`, as mvcc) an empty non-`nil` one as no upper bound, so
`checkIntervals`' spec takes it.

**The response header** (`hdrW`, `hdrRevIn`, `hdrRevOut`, `hdrFilled`): `header.fill(rh)`
writes `rh`'s `ClusterId`, `MemberId`, `RaftTerm` and `LeaderId` (owned: `hdrW`), and its
`Revision` only when it is `0`, from `rev()`: so the revision is either read-only and not `0`
(the server's responses: `txn.putResponseIs` and the others hold it read-only, and every
successful response has a revision of at least `1`, `notes/STATUS.md`, unit 0's suspect 4) or
owned, with what `rev()` needs (`R`).

**The header** (`hdrIs hp s A cid mid`): the `header` at `hp` (read-only): the cluster and
member ids it was built with, `sg` the server `s` (`raftStatusOk s`: its `Term` and `Leader`
return), `rev` a closure returning the server's KV revision (with `A.revR`).

**The server, as the handlers call it** (`raftKV s A`, persistent): the triples of
`*EtcdServer`'s `Range`, `Put`, `DeleteRange`, `Txn` (the `RaftKV` methods the handlers call:
`isRaftKV`'s), `KV` (its `Rev`), `Cluster` (its `ID`), `MemberID`, `Term`, `Leader`, over
**parameters** `A : KVAns GF` that units 2 and 3 instantiate: what a call needs (`A.call ctx`:
the context, the per-request resources such as an id credit), what a successful answer holds
(`A.ok q resp h r`: the request `q`, the response `resp`, its header `h` and revision `r`), what
an error is (`A.err q err`), what `Rev()` needs (`A.revR`). The triples' fixed part is what the
handlers need: a request that passed its check (`rangeReqOk`, ..., `txnReqOk` and
`intervalsOk` of both branches), and an answer that is either a non-nil response whose header
the handler can fill (`kvAnswer`: `hdrW`, `hdrRevIn`) or a `nil` response with an error
`togRPCError` can take (`srvErrIs`: not nil, in an error tree for every target as the apply
package's `applyErrIs`, a safe map key, an `Error()` that returns).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
-- `InvServer`'s high-priority `TypeRepr` of `EtcdServer`: without it `NewKVServer` finds
-- `TypeRepr` through `EtcdServer`'s `IntoValTyped`, which reaches the `sorry` instances of its
-- axiomatized field types (`InvRequest` imported it through `InvApplier` before unit 2).
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

/-! ## Pure: the checks' outcomes the specs name -/

/-- `checkRangeStreamRequest` past `checkRangeRequest`: the default sort (`txn.IsDefaultOrdering`:
no order, or ascending by key) and no revision filter (`txn.HasRevisionFilters`). -/
def streamOk (o : OpFull) : Prop :=
  (o.sortOrder = W64 0 ∨ (o.sortTarget = W64 0 ∧ o.sortOrder = W64 1)) ∧
    txn.hasRevFilters o = false

/-- **What `kvServer.Txn` checks**, in order: `checkTxnRequest` at the budget `n`, then
`checkIntervals` of `Success`, then of `Failure` (`ErrGRPCDuplicateKey`): the first error. -/
def txnAllCheck (n : Int) (cs : List CmpModel) (ts es : List ReqOp) : Option CheckErr :=
  match txnCheck n cs ts es with
  | some e => some e
  | none =>
    match ivCheck ts, ivCheck es with
    | some _, some _ => none
    | _, _ => some .duplicateKey

section srvM
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- `*EtcdServer` `s`'s method `m`. -/
abbrev srvM (s : Loc) (m : GoString) : val :=
  #(methods (go.GoType.PointerType EtcdServer.ty) m #s)

end srvM

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ## The requests -/

mutual
/-- **The `*pb.RequestOp` `p` denotes the checked operation `u`** (read-only; see the file
header). -/
def reqOpIs (p : Loc) : ReqOp → IProp GF
  | .range o => iprop(□ (⌜p ≠ null⌝ ∗ ∃ (w r : Loc),
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestRange.ty) #w :
          GoInterface) ∗
      structFieldRef etcdserverpb.RequestOp_RequestRange go!"RequestRange" w ↦□ r ∗
      txn.rangeRequestIs r o))
  | .put o => iprop(□ (⌜p ≠ null⌝ ∗ ∃ (w r : Loc),
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestPut.ty) #w :
          GoInterface) ∗
      structFieldRef etcdserverpb.RequestOp_RequestPut go!"RequestPut" w ↦□ r ∗
      txn.putRequestIs r o))
  | .delete o => iprop(□ (⌜p ≠ null⌝ ∗ ∃ (w r : Loc),
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestDeleteRange.ty) #w :
          GoInterface) ∗
      structFieldRef etcdserverpb.RequestOp_RequestDeleteRange go!"RequestDeleteRange" w ↦□ r ∗
      txn.deleteRangeRequestIs r o))
  | .txn cs ts es => iprop(□ (⌜p ≠ null⌝ ∗ ∃ (w r : Loc),
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestTxn.ty) #w :
          GoInterface) ∗
      structFieldRef etcdserverpb.RequestOp_RequestTxn go!"RequestTxn" w ↦□ r ∗ ⌜r ≠ null⌝ ∗
      ∃ (csl ssl fsl : GoSlice) (cps sps fps : List Loc),
        structFieldRef etcdserverpb.TxnRequest go!"Compare" r ↦□ csl ∗ csl ↦*□ cps ∗
        txn.comparesIs cps cs ∗
        structFieldRef etcdserverpb.TxnRequest go!"Success" r ↦□ ssl ∗ ssl ↦*□ sps ∗
        reqOpsIs sps ts ∗
        structFieldRef etcdserverpb.TxnRequest go!"Failure" r ↦□ fsl ∗ fsl ↦*□ fps ∗
        reqOpsIs fps es))
  | .empty => iprop(□ (⌜p ≠ null⌝ ∗
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□ (GoInterface.nil : GoInterface)))

/-- The `*pb.RequestOp`s `ps` denote, in order, the checked operations `us`. -/
def reqOpsIs : List Loc → List ReqOp → IProp GF
  | [], [] => iprop(True)
  | p :: ps, u :: us => iprop(reqOpIs p u ∗ reqOpsIs ps us)
  | _, _ => iprop(False)
end

instance reqOpIs_persistent (p : Loc) (u : ReqOp) : Persistent (reqOpIs (GF := GF) p u) := by
  cases u <;> unfold reqOpIs <;> infer_instance

instance reqOpsIs_persistent (ps : List Loc) (us : List ReqOp) :
    Persistent (reqOpsIs (GF := GF) ps us) := by
  induction us generalizing ps with
  | nil => cases ps <;> unfold reqOpsIs <;> infer_instance
  | cons u us ih => cases ps <;> unfold reqOpsIs <;> infer_instance

/-- **The `*pb.TxnRequest` `rt`** (not nil, read-only): its comparisons denote `cs`, its
`Success` and `Failure` operations the checked `ts` and `es`. -/
def txnReqIs (rt : Loc) (cs : List CmpModel) (ts es : List ReqOp) : IProp GF :=
  iprop(⌜rt ≠ null⌝ ∗ ∃ (csl ssl fsl : GoSlice) (cps sps fps : List Loc),
    structFieldRef etcdserverpb.TxnRequest go!"Compare" rt ↦□ csl ∗ csl ↦*□ cps ∗
    txn.comparesIs cps cs ∗
    structFieldRef etcdserverpb.TxnRequest go!"Success" rt ↦□ ssl ∗ ssl ↦*□ sps ∗
    reqOpsIs sps ts ∗
    structFieldRef etcdserverpb.TxnRequest go!"Failure" rt ↦□ fsl ∗ fsl ↦*□ fps ∗
    reqOpsIs fps es)

instance txnReqIs_persistent (rt : Loc) (cs : List CmpModel) (ts es : List ReqOp) :
    Persistent (txnReqIs (GF := GF) rt cs ts es) := by
  unfold txnReqIs; infer_instance

mutual
/-- **The deletes' range ends are as decoded from the wire** (persistent): every delete of the
operation `u` at `p` (at any depth) has a `RangeEnd` that is `nil` or not empty. Protobuf-go
decodes an empty `bytes` field as `nil`; an empty non-`nil` `RangeEnd` (built in memory) denotes
`[0]` (`txn.rangeEndOf`, as mvcc reads it) but `checkIntervals` reads it as a point (`len == 0`),
so without this `ivCheck`'s `delIvl` would not be the code's interval. Stated over the fields'
points-tos (whatever they hold), as a wand, so that it composes with `reqOpIs`. -/
def reqOpWire (p : Loc) : ReqOp → IProp GF
  | .delete _ => iprop(□ ∀ (w r : Loc) (esl : GoSlice),
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestDeleteRange.ty) #w :
          GoInterface) -∗
      structFieldRef etcdserverpb.RequestOp_RequestDeleteRange go!"RequestDeleteRange" w ↦□ r -∗
      structFieldRef etcdserverpb.DeleteRangeRequest go!"RangeEnd" r ↦□ esl -∗
      ⌜esl = slice.nil ∨ esl.len ≠ W64 0⌝)
  | .txn _ ts es => iprop(□ ∀ (w r : Loc) (ssl fsl : GoSlice) (sps fps : List Loc),
      structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
        (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestTxn.ty) #w :
          GoInterface) -∗
      structFieldRef etcdserverpb.RequestOp_RequestTxn go!"RequestTxn" w ↦□ r -∗
      structFieldRef etcdserverpb.TxnRequest go!"Success" r ↦□ ssl -∗ ssl ↦*□ sps -∗
      structFieldRef etcdserverpb.TxnRequest go!"Failure" r ↦□ fsl -∗ fsl ↦*□ fps -∗
      reqOpsWire sps ts ∗ reqOpsWire fps es)
  | _ => iprop(True)

/-- `reqOpWire` of each operation. -/
def reqOpsWire : List Loc → List ReqOp → IProp GF
  | [], [] => iprop(True)
  | p :: ps, u :: us => iprop(reqOpWire p u ∗ reqOpsWire ps us)
  | _, _ => iprop(True)
end

instance reqOpWire_persistent (p : Loc) (u : ReqOp) : Persistent (reqOpWire (GF := GF) p u) := by
  cases u <;> unfold reqOpWire <;> infer_instance

instance reqOpsWire_persistent (ps : List Loc) (us : List ReqOp) :
    Persistent (reqOpsWire (GF := GF) ps us) := by
  induction us generalizing ps with
  | nil => cases ps <;> unfold reqOpsWire <;> infer_instance
  | cons u us ih => cases ps <;> unfold reqOpsWire <;> infer_instance

/-- **The transaction `rt`'s deletes are as decoded from the wire** (`reqOpsWire`, what
`checkIntervals` needs: a delete's `RangeEnd` is `nil` or not empty), in both branches, and
fewer than `2^63` in each branch, at every depth (`delCount`: what keeps `checkIntervals`'s
interval tree below its count bound; a decoded request is a tree, each delete at least a byte of
the message, a Go slice; nothing else bounds them, as a request built in memory may share a
nested transaction between branches, so that its unfolded size is exponential in its depth). -/
def txnReqWire (rt : Loc) (ts es : List ReqOp) : IProp GF :=
  iprop(⌜delCount ts < 2 ^ 63 ∧ delCount es < 2 ^ 63⌝ ∗ □ ∀ (ssl fsl : GoSlice) (sps fps : List Loc),
    structFieldRef etcdserverpb.TxnRequest go!"Success" rt ↦□ ssl -∗ ssl ↦*□ sps -∗
    structFieldRef etcdserverpb.TxnRequest go!"Failure" rt ↦□ fsl -∗ fsl ↦*□ fps -∗
    reqOpsWire sps ts ∗ reqOpsWire fps es)

instance txnReqWire_persistent (rt : Loc) (ts es : List ReqOp) :
    Persistent (txnReqWire (GF := GF) rt ts es) := by
  unfold txnReqWire; infer_instance

/-! ## The errors -/

/-- **An error `togRPCError` can take** (persistent): not nil, in an error tree for every
target (`applyErrIs`: what `errors.Is` needs), a safe key of the error map (comparing it with
itself does not panic: `SafeMapKey`; a pointer error is one, `safeMapKey_ptrErr`; `applyErrIs` gives all of it,
`srvErrIs_of_applyErrIs`), and its
`Error()` returns (the message of `status.Error(codes.Unknown, err.Error())`). -/
def srvErrIs (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗ ⌜SafeMapKey (GF := GF) go.error err⌝ ∗
    ∃ ei : GoInterfaceOk, ⌜err = GoInterface.ok ei⌝ ∗
      {{ True }} (App (Val #(methods ei.ty go!"Error" ei.v)) (Val #()))
      {{ (msg : GoString), RET #msg; True }})

instance srvErrIs_persistent (err : GoInterface) : Persistent (srvErrIs (GF := GF) err) := by
  unfold srvErrIs; infer_instance

/-- **A check's result** `err` for the outcome `c` of its pure check: `nil`, or the error the
`rpctypes` variable of `c` holds. -/
def checkRes : Option CheckErr → GoInterface → IProp GF
  | none, err => iprop(⌜err = GoInterface.nil⌝)
  | some e, err => txn.errVarIs e.var err

instance checkRes_persistent (c : Option CheckErr) (err : GoInterface) :
    Persistent (checkRes (GF := GF) c err) := by
  cases c <;> unfold checkRes <;> infer_instance

/-! ## The response header -/

/-- The fields of the `*pb.ResponseHeader` `h` that `fillWithoutRevision` writes, owned. -/
def hdrW (h : Loc) : IProp GF :=
  iprop(⌜h ≠ null⌝ ∗ ∃ (c m t l : w64),
    structFieldRef etcdserverpb.ResponseHeader go!"ClusterId" h ↦ c ∗
    structFieldRef etcdserverpb.ResponseHeader go!"MemberId" h ↦ m ∗
    structFieldRef etcdserverpb.ResponseHeader go!"RaftTerm" h ↦ t ∗
    structFieldRef etcdserverpb.ResponseHeader go!"LeaderId" h ↦ l)

/-- The header `h` filled by a `header` of the cluster `cid` and member `mid`: some raft term,
some leader (the server's view when it was asked: advisory, `header.go`). -/
def hdrFilled (h : Loc) (cid mid : w64) : IProp GF :=
  iprop(⌜h ≠ null⌝ ∗ ∃ (t l : w64),
    structFieldRef etcdserverpb.ResponseHeader go!"ClusterId" h ↦ cid ∗
    structFieldRef etcdserverpb.ResponseHeader go!"MemberId" h ↦ mid ∗
    structFieldRef etcdserverpb.ResponseHeader go!"RaftTerm" h ↦ t ∗
    structFieldRef etcdserverpb.ResponseHeader go!"LeaderId" h ↦ l)

/-- The header `h`'s revision `r` before `fill`: read-only and not `0` (`fill` keeps it), or
owned with what `rev()` needs (`R`). -/
def hdrRevIn (R : IProp GF) (h : Loc) (r : w64) : IProp GF :=
  iprop((⌜r ≠ W64 0⌝ ∗ structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ r) ∨
    (structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦ r ∗ R))

/-- The header `h`'s revision after `fill`, from `r` before: `r'`, which is `r` unless `r` was
`0` (then the KV's revision `rev()` returned). -/
def hdrRevOut (R : IProp GF) (h : Loc) (r r' : w64) : IProp GF :=
  iprop((⌜r ≠ W64 0 ∧ r' = r⌝ ∗
      structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ r) ∨
    (⌜r ≠ W64 0 → r' = r⌝ ∗
      structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦ r' ∗ R))

/-! ## The server -/

/-- **The server `s` as a `RaftStatusGetter`** (the header's `sg`): `Term` and `Leader` return
(persistent). -/
def raftStatusOk (s : Loc) : IProp GF :=
  iprop({{ True }} (App (Val (srvM s go!"Term")) (Val #())) {{ (t : w64), RET #t; True }} ∗
    {{ True }} (App (Val (srvM s go!"Leader")) (Val #())) {{ (l : w64), RET #l; True }})

instance raftStatusOk_persistent (s : Loc) : Persistent (raftStatusOk (GF := GF) s) := by
  unfold raftStatusOk; infer_instance

end defs

/-- The four KV requests the handlers pass on, as the checks read them. -/
inductive KVReq where
  | range (o : OpFull)
  | put (o : OpFull)
  | deleteRange (o : OpFull)
  | txn (cs : List CmpModel) (ts es : List ReqOp)

/-- **The parameters of the server's contract** (`raftKV`), which units 2 and 3 instantiate (see
the file header). -/
structure KVAns [FfiSyntax] (GF : BundledGFunctors) where
  /-- What a call needs, of its context `ctx` and per request. -/
  call : GoInterface → IProp GF
  /-- A successful answer to `q`: the response, its header, the header's revision. -/
  ok : KVReq → Loc → Loc → w64 → IProp GF
  /-- An error answer to `q`. -/
  err : KVReq → GoInterface → IProp GF
  /-- What the KV's `Rev()` needs and gives back. -/
  revR : IProp GF

section contract
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The server's answer** to `q` (`hf`: the address of the response's `Header` field): no
error and a response whose header the handler can fill, or a `nil` response and an error
`togRPCError` can take. -/
def kvAnswer (A : KVAns GF) (q : KVReq) (hf resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (r : w64),
      hf ↦□ h ∗ hdrW h ∗ hdrRevIn A.revR h r ∗ A.ok q resp h r) ∨
    (⌜resp = null⌝ ∗ srvErrIs err ∗ A.err q err))

/-- **The handler's answer** to `q` past its check (`cid`, `mid`: its header's ids): the
server's answer with the header filled, or `nil` and a non-nil error (the server's, through
`togRPCError`). -/
def kvOut (A : KVAns GF) (cid mid : w64) (q : KVReq) (hf resp : Loc) (err : GoInterface) :
    IProp GF :=
  iprop((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (r r' : w64),
      hf ↦□ h ∗ hdrFilled h cid mid ∗ hdrRevOut A.revR h r r' ∗ A.ok q resp h r) ∨
    (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ ∃ e : GoInterface, A.err q e))

/-- A handler's check error: the `rpctypes` variable of `e` holds it, no response. -/
def checkOut (e : CheckErr) (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop(⌜resp = null⌝ ∗ txn.errVarIs e.var err)

instance checkOut_persistent (e : CheckErr) (resp : Loc) (err : GoInterface) :
    Persistent (checkOut (GF := GF) e resp err) := by
  unfold checkOut; infer_instance

/-- **The server's `Range`** on a checked request (one conjunct of `raftKV`). -/
def kvRangeOk (s : Loc) (A : KVAns GF) : IProp GF :=
  iprop(∀ (ctx : GoInterface) (r : Loc) (o : OpFull),
      {{ A.call ctx ∗ txn.rangeRequestIs r o ∗ ⌜rangeReqOk o⌝ }}
        (App (App (Val (srvM s go!"Range")) (Val #ctx)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          kvAnswer A (.range o) (structFieldRef etcdserverpb.RangeResponse go!"Header" resp)
            resp err }})

/-- **The server's `Put`** on a checked request (one conjunct of `raftKV`). -/
def kvPutOk (s : Loc) (A : KVAns GF) : IProp GF :=
  iprop(∀ (ctx : GoInterface) (r : Loc) (o : OpFull),
      {{ A.call ctx ∗ txn.putRequestIs r o ∗ ⌜putReqOk o⌝ }}
        (App (App (Val (srvM s go!"Put")) (Val #ctx)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          kvAnswer A (.put o) (structFieldRef etcdserverpb.PutResponse go!"Header" resp)
            resp err }})

/-- **The server's `DeleteRange`** on a checked request (one conjunct of `raftKV`). -/
def kvDeleteOk (s : Loc) (A : KVAns GF) : IProp GF :=
  iprop(∀ (ctx : GoInterface) (r : Loc) (o : OpFull),
      {{ A.call ctx ∗ txn.deleteRangeRequestIs r o ∗ ⌜deleteReqOk o⌝ }}
        (App (App (Val (srvM s go!"DeleteRange")) (Val #ctx)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          kvAnswer A (.deleteRange o)
            (structFieldRef etcdserverpb.DeleteRangeResponse go!"Header" resp) resp err }})

/-- **The server's `Txn`** on a checked request (one conjunct of `raftKV`). -/
def kvTxnOk (s : Loc) (A : KVAns GF) : IProp GF :=
  iprop(∀ (ctx : GoInterface) (r : Loc) (cs : List CmpModel) (ts es : List ReqOp) (n : Int),
      {{ A.call ctx ∗ txnReqIs r cs ts es ∗
          ⌜txnReqOk n cs ts es ∧ intervalsOk ts ∧ intervalsOk es⌝ }}
        (App (App (Val (srvM s go!"Txn")) (Val #ctx)) (Val #r))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          kvAnswer A (.txn cs ts es) (structFieldRef etcdserverpb.TxnResponse go!"Header" resp)
            resp err }})

/-- **The header's getters** (one conjunct of `raftKV`): `KV().Rev()`, `Cluster().ID()`,
`MemberID()`, `Term()`, `Leader()`. -/
def kvGetOk (s : Loc) (A : KVAns GF) : IProp GF :=
  iprop(
    {{ True }} (App (Val (srvM s go!"KV")) (Val #()))
    {{ (kv : GoInterface), RET #kv; ∃ ki : GoInterfaceOk, ⌜kv = GoInterface.ok ki⌝ ∗
        {{ A.revR }} (App (Val #(methods ki.ty go!"Rev" ki.v)) (Val #()))
        {{ (rev : w64), RET #rev; A.revR }} }} ∗
    {{ True }} (App (Val (srvM s go!"Cluster")) (Val #()))
    {{ (c : GoInterface), RET #c; ∃ ci : GoInterfaceOk, ⌜c = GoInterface.ok ci⌝ ∗
        {{ True }} (App (Val #(methods ci.ty go!"ID" ci.v)) (Val #()))
        {{ (id : w64), RET #id; True }} }} ∗
    {{ True }} (App (Val (srvM s go!"MemberID")) (Val #())) {{ (id : w64), RET #id; True }} ∗
    raftStatusOk s)

instance kvRangeOk_persistent (s : Loc) (A : KVAns GF) : Persistent (kvRangeOk s A) := by
  unfold kvRangeOk; infer_instance
instance kvPutOk_persistent (s : Loc) (A : KVAns GF) : Persistent (kvPutOk s A) := by
  unfold kvPutOk; infer_instance
instance kvDeleteOk_persistent (s : Loc) (A : KVAns GF) : Persistent (kvDeleteOk s A) := by
  unfold kvDeleteOk; infer_instance
instance kvTxnOk_persistent (s : Loc) (A : KVAns GF) : Persistent (kvTxnOk s A) := by
  unfold kvTxnOk; infer_instance
instance kvGetOk_persistent (s : Loc) (A : KVAns GF) : Persistent (kvGetOk s A) := by
  unfold kvGetOk; infer_instance

/-- **The server `s`'s request path, as the handlers and the header call it** (persistent; see
the file header): the `RaftKV` methods (`Range`, `Put`, `DeleteRange`, `Txn`) on checked
requests, and `KV().Rev()`, `Cluster().ID()`, `MemberID()`, `Term()`, `Leader()`; one conjunct
per method (2026-10-12, unit 3a: `Put` and `DeleteRange` are proved from the server's
`EtcdServer.Put`/`DeleteRange`, `kvServer.lean`, the others are 3b's). -/
def raftKV (s : Loc) (A : KVAns GF) : IProp GF :=
  iprop(kvRangeOk s A ∗ kvPutOk s A ∗ kvDeleteOk s A ∗ kvTxnOk s A ∗ kvGetOk s A)

instance raftKV_persistent (s : Loc) (A : KVAns GF) : Persistent (raftKV s A) := by
  unfold raftKV; infer_instance

/-- **The `header` at `hp`** (read-only): built by `newHeader(s)` with the cluster id `cid` and
the member id `mid`; `sg` is `s`, `rev` the closure `s.KV().Rev()`. -/
def hdrIs (hp : Loc) (s : Loc) (A : KVAns GF) (cid mid : w64) : IProp GF :=
  iprop(∃ revf : GoFunc,
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.header go!"clusterID" hp ↦□ cid ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.header go!"memberID" hp ↦□ mid ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.header go!"sg" hp ↦□
      (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s : GoInterface) ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.header go!"rev" hp ↦□ revf ∗
    {{ A.revR }} (App (Val #revf) (Val #())) {{ (rev : w64), RET #rev; A.revR }} ∗
    raftStatusOk s)

instance hdrIs_persistent (hp s : Loc) (A : KVAns GF) (cid mid : w64) :
    Persistent (hdrIs hp s A cid mid) := by
  unfold hdrIs; infer_instance

/-- **`newHeader(s)`'s value** `hv`: the ids `cid`, `mid`, `sg` the server `s`, `rev` the
closure returning the KV's revision. -/
def hdrValIs (hv : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.header) (s : Loc)
    (A : KVAns GF) (cid mid : w64) : IProp GF :=
  iprop(⌜hv.clusterID' = cid ∧ hv.memberID' = mid ∧
      hv.sg' = (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s : GoInterface)⌝ ∗
    {{ A.revR }} (App (Val #hv.rev') (Val #())) {{ (rev : w64), RET #rev; A.revR }} ∗
    raftStatusOk s)

instance hdrValIs_persistent (hv : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.header)
    (s : Loc) (A : KVAns GF) (cid mid : w64) : Persistent (hdrValIs hv s A cid mid) := by
  unfold hdrValIs; infer_instance

/-- **The wrapped stream `stv`'s `Send`** (`grpc.ServerStreamingServer`, names-only): a contract,
`Ψ` of the chunk before, `Ξ` after. -/
def streamSendOk (stv : GoInterface) (Ψ : Loc → IProp GF) (Ξ : Loc → GoInterface → IProp GF) :
    IProp GF :=
  iprop(∃ si : GoInterfaceOk, ⌜stv = GoInterface.ok si⌝ ∗ ∀ resp : Loc,
    {{ Ψ resp }} (App (Val #(methods si.ty go!"Send" si.v)) (Val #resp))
    {{ (err : GoInterface), RET #err; Ξ resp err }})

instance streamSendOk_persistent (stv : GoInterface) (Ψ : Loc → IProp GF)
    (Ξ : Loc → GoInterface → IProp GF) : Persistent (streamSendOk stv Ψ Ξ) := by
  unfold streamSendOk; infer_instance

/-- **The `*kvServer` `p`** that `NewKVServer(s)` built (read-only): its header (`hdrIs`), `kv`
the server `s` (`isRaftKV`) with its contract, the transaction budget `n` (`MaxTxnOps`). -/
def kvServerIs (p : Loc) (s : Loc) (A : KVAns GF) (cid mid n : w64) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗
    hdrIs (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer go!"hdr" p)
      s A cid mid ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer go!"kv" p ↦□
      (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s : GoInterface) ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.kvServer go!"maxTxnOps" p ↦□ n ∗
    raftKV s A)

instance kvServerIs_persistent (p s : Loc) (A : KVAns GF) (cid mid n : w64) :
    Persistent (kvServerIs p s A cid mid n) := by
  unfold kvServerIs; infer_instance

end contract

end v3rpc
end EtcdGrove
end Perennial
