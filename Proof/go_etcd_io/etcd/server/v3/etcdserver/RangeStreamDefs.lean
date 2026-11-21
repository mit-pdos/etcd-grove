/-
**The streamed range's vocabulary** (auth-mediation M3, 2026-11-21; option (B), the user's choice):
what `EtcdServer.RangeStream` and the trust boundary `EtcdServer.rangeStream` (names only) are stated
in.

- `rangeRequestOwn`: the request, with the three fields `rangeStream` rewrites between pages (`Key`,
  `Limit`, `Revision`) owned (`txn.rangeRequestIs` has every field read-only);
- `rangeRequestBack`: the request as `rangeStream` gives it back (the three fields, no key contents);
- `rangeChunkIs`: a chunk `rangeStream` sends: a `*pb.RangeStreamResponse` whose `RangeResponse`
  holds key-values of the request's range, and a header that is `nil` or fresh (its id fields owned,
  for the gRPC layer's `fillWithoutRevision`);
- `rangeSendOk`: the stream's `Send`, a contract (`Ψ` of the chunk before, `Ξ` after), as the gRPC
  layer's `v3rpc.streamSendOk`;
- `rangeReadErr`: an error of the store's reads (`txn.Range`'s, `txn.Count`'s);
- `rangeStreamCtx`: the stream's `Context()`, which returns the request's context;
- `rangeRequestOwn_at`: `rangeRequestOwn` is `txn.rangeRequestAt` (`txn/RequestAt.lean`) at
  `DFrac.own 1`, the form the gRPC layer's checks take.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.RequestAt
public import Proof.go_etcd_io.etcd.server.v3.auth.Model
public import Proof.context.LibKeys
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadWhy

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The `*pb.RangeRequest` `r` (not nil) of the get `o`, its rewritten fields owned**: as
`txn.rangeRequestIs r o`, but `Key`, `Limit` and `Revision`, which `rangeStream` writes between
pages (`v3_server.go`: `r.Limit = initialStreamChunkLimit`, `r.Revision = headerRev`, `r.Key =
nextKey`), are owned; the others, and the key's contents, read-only. -/
def rangeRequestOwn (r : Loc) (o : OpFull) : IProp GF :=
  iprop(⌜r ≠ null⌝ ∗ ∃ (ksl esl : GoSlice) (k e : GoString) (rev limit : w64)
      (order target : w32) (ser ko co : Bool) (minM maxM minC maxC : w64),
    structFieldRef etcdserverpb.RangeRequest go!"Key" r ↦ ksl ∗ ksl ↦*□ k ∗
    structFieldRef etcdserverpb.RangeRequest go!"RangeEnd" r ↦□ esl ∗ esl ↦*□ e ∗
    structFieldRef etcdserverpb.RangeRequest go!"Limit" r ↦ limit ∗
    structFieldRef etcdserverpb.RangeRequest go!"Revision" r ↦ rev ∗
    structFieldRef etcdserverpb.RangeRequest go!"SortOrder" r ↦□ order ∗
    structFieldRef etcdserverpb.RangeRequest go!"SortTarget" r ↦□ target ∗
    structFieldRef etcdserverpb.RangeRequest go!"Serializable" r ↦□ ser ∗
    structFieldRef etcdserverpb.RangeRequest go!"KeysOnly" r ↦□ ko ∗
    structFieldRef etcdserverpb.RangeRequest go!"CountOnly" r ↦□ co ∗
    structFieldRef etcdserverpb.RangeRequest go!"MinModRevision" r ↦□ minM ∗
    structFieldRef etcdserverpb.RangeRequest go!"MaxModRevision" r ↦□ maxM ∗
    structFieldRef etcdserverpb.RangeRequest go!"MinCreateRevision" r ↦□ minC ∗
    structFieldRef etcdserverpb.RangeRequest go!"MaxCreateRevision" r ↦□ maxC ∗
    ⌜o = txn.rangeOpOf k (txn.rangeEndOf esl e) rev limit order target ser ko co minM maxM minC maxC⌝ ∗
    ⌜sint.Z ksl.len < 2 ^ 63 - 1⌝)

/-- **The request `r` as `rangeStream` gives it back**: its three rewritten fields owned, at some
values; not the new key's contents (the fork's `4416a5786` makes the next page's key a fresh copy,
`append(bytes.Clone(lastKey), 0)`; before it, the key was appended into the capacity of an mvcc
index key, which a concurrent keys-only stream wrote too:
`nonissues/etcd-rangestream-keysonly-index-key-race.md`; no caller reads it after the stream). The
other fields stay as the caller gave them (read-only in `rangeRequestOwn`). -/
def rangeRequestBack (r : Loc) : IProp GF :=
  iprop(∃ (ksl : GoSlice) (rev limit : w64),
    structFieldRef etcdserverpb.RangeRequest go!"Key" r ↦ ksl ∗
    structFieldRef etcdserverpb.RangeRequest go!"Limit" r ↦ limit ∗
    structFieldRef etcdserverpb.RangeRequest go!"Revision" r ↦ rev)

/-- **A chunk of the streamed range `o`**: the `*pb.RangeStreamResponse` `resp`, its
`RangeResponse` not nil (read-only), whose `Kvs` are key-values (`txn.kvsIs`, read-only) of keys in
`o`'s range as the auth store reads a range (`auth.inRange` of `o`'s key and range end: the key
alone, every key from it, or `[key, end)`), and whose `Header` is `nil` or a fresh header, its id
fields owned (`txn.respHdrOwn`: what the gRPC layer's `fillWithoutRevision` writes). Nothing is
stated of the header's revision, `More` or `Count`. -/
def rangeChunkIs (o : OpFull) (resp : Loc) : IProp GF :=
  iprop(∃ (rr : Loc) (sl : GoSlice) (ps : List Loc) (kvs : List EtcdKv),
    structFieldRef etcdserverpb.RangeStreamResponse go!"RangeResponse" resp ↦□ rr ∗ ⌜rr ≠ null⌝ ∗
    (structFieldRef etcdserverpb.RangeResponse go!"Header" rr ↦□ (null : Loc) ∨
      txn.respHdrOwn (structFieldRef etcdserverpb.RangeResponse go!"Header" rr)) ∗
    structFieldRef etcdserverpb.RangeResponse go!"Kvs" rr ↦□ sl ∗ sl ↦*□ ps ∗ txn.kvsIs ps kvs ∗
    ⌜∀ kv ∈ kvs, auth.inRange o.key o.base.rangeEnd kv.key⌝)

/-- **The stream `rs`'s `Send`** (`pb.KV_RangeStreamServer`, an interface): a contract, `Ψ` of the
chunk before, `Ξ` after (as the gRPC layer's `v3rpc.streamSendOk`). -/
def rangeSendOk (rs : GoInterface) (Ψ : Loc → IProp GF) (Ξ : Loc → GoInterface → IProp GF) :
    IProp GF :=
  iprop(∃ si : GoInterfaceOk, ⌜rs = GoInterface.ok si⌝ ∗ ∀ resp : Loc,
    {{ Ψ resp }} (App (Val #(methods si.ty go!"Send" si.v)) (Val #resp))
    {{ (err : GoInterface), RET #err; Ξ resp err }})

instance rangeSendOk_persistent (rs : GoInterface) (Ψ : Loc → IProp GF)
    (Ξ : Loc → GoInterface → IProp GF) : Persistent (rangeSendOk rs Ψ Ξ) := by
  unfold rangeSendOk; infer_instance

/-- **An error of the store's reads** (persistent): what `txn.Range`'s and `txn.Count`'s specs
allow (`txn.rangeResult`): mvcc's `ErrFutureRev` or `ErrCompacted`, or `rangeKeys`' wrapped context
error (`mvcc.rangeKeysErr`); `rangeWhyOut`'s last three cases. -/
def rangeReadErr (err : GoInterface) : IProp GF :=
  iprop((∃ ef : GoInterfaceOk,
      (globalAddr go_etcd_io.etcd.server.v3.storage.mvcc.ErrFutureRev ↦□ GoInterface.ok ef : IProp GF) ∗
      ⌜err = GoInterface.ok ef⌝) ∨
    (∃ ec : GoInterfaceOk,
      (globalAddr go_etcd_io.etcd.server.v3.storage.mvcc.ErrCompacted ↦□ GoInterface.ok ec : IProp GF) ∗
      ⌜err = GoInterface.ok ec⌝) ∨
    mvcc.rangeKeysErr err)

instance rangeReadErr_persistent (err : GoInterface) : Persistent (rangeReadErr (GF := GF) err) := by
  unfold rangeReadErr; infer_instance

/-- **The stream `rs`'s `Context()`** (`grpc.ServerStream`, an interface): it returns the context
`ctx` (the stream's, read-only: persistent). -/
def rangeStreamCtx (rs : GoInterface) (ctx : GoInterfaceOk) : IProp GF :=
  iprop(∃ si : GoInterfaceOk, ⌜rs = GoInterface.ok si⌝ ∗
    {{ True }} (App (Val #(methods si.ty go!"Context" si.v)) (Val #()))
    {{ RET #(GoInterface.ok ctx); True }})

instance rangeStreamCtx_persistent (rs : GoInterface) (ctx : GoInterfaceOk) :
    Persistent (rangeStreamCtx (GF := GF) rs ctx) := by
  unfold rangeStreamCtx; infer_instance

/-- `rangeRequestOwn` is `txn.rangeRequestAt` at `DFrac.own 1`. -/
theorem rangeRequestOwn_at (r : Loc) (o : OpFull) :
    rangeRequestOwn (GF := GF) r o ⊣⊢ txn.rangeRequestAt r (DFrac.own 1) o := .rfl

open Iris.ProofMode in
/-- The request owned gives it back (`rangeRequestBack`: its three fields). -/
theorem rangeRequestBack_of_own (r : Loc) (o : OpFull) :
    rangeRequestOwn (GF := GF) r o ⊢ rangeRequestBack r := by
  iunfold rangeRequestOwn
  iintro ⟨-, %ksl, %esl, %k, %e, %rev, %limit, %order, %target, %ser, %ko, %co, %minM, %maxM, %minC,
    %maxC, HK, -, -, -, Hlim, Hrev, -⟩
  iunfold rangeRequestBack
  iexists ksl, rev, limit
  iframe HK Hlim Hrev

end defs

section why
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

open Iris.ProofMode in
/-- **A store read's error is one `rangeWhyOut` allows** (its last three cases). -/
theorem rangeWhyOut_of_rangeReadErr (s : Loc) (M : auth.AuthMode) (n : Nat) (tok : Option GoString)
    (o : OpFull) (err : GoInterface) :
    rangeReadErr (GF := GF) err ⊢ rangeWhyOut s M n tok o err := by
  iunfold rangeReadErr
  iintro (⟨%ef, #Hef, %He⟩ | ⟨%ec, #Hec, %He⟩ | #Hk)
  · unfold rangeWhyOut; iright; iright; ileft; iexists ef; iframe Hef; ipureintro; exact He
  · unfold rangeWhyOut; iright; iright; iright; ileft; iexists ec; iframe Hec; ipureintro; exact He
  · unfold rangeWhyOut; iright; iright; iright; iright; iexact Hk

end why

end EtcdGrove
end Perennial
