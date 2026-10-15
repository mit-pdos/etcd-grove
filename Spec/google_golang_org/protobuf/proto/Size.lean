/-
`proto.Size`: the trust boundary (`google.golang.org/protobuf` is names-only), a case per message
type sized (as `proto.Clone`'s). Lean-first.

`proto.Size(m)` returns the length of `m`'s encoding, an `int` at least `0`; it reads the
message's fields (and its sub-messages') and stores the sizes in their size caches with atomic
stores (protobuf-go's `sizecache`). The cases:

* a put request (`proto.Size(p)`, `Put`'s and `executeTxn`'s trace fields): the request's fields
  read-only and its size cache in the invariant `putRequestIs` holds it in;
* a range response (unit P4, 2026-10-14: `txn.WarnOfExpensiveReadOnlyRangeRequest`, of the
  server's `Range`): its fields read-only (`rangeResponseIs`: the header's revision, the
  key-values, `More`, `Count`) and its header's id fields, owned by the request's goroutine
  (`respHdrOwn`), lent;
* a read-only transaction's response, complete or partly filled (unit P4:
  `txn.WarnOfExpensiveReadOnlyTxnRequest`, of the server's read-only `Txn`): its fields and its
  range responses read-only (`roTxnRespRd`), its header's id fields lent (`respHdrOwn`).

Not modelled: the messages' internal fields (`state`, `unknownFields`), which `Size` also reads
(nothing writes them after decoding or allocation); the responses' size caches, which it writes
atomically: no proof keeps them (the responses' allocations drop them), so `Size` needs no
resource for them; and the id fields of the headers of the range responses nested in a
transaction's response (allocated and dropped by `executeRange`, written by no one after).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.InvWarn
public import GeneratedProof.google_golang_org.protobuf.proto

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI google_golang_org.protobuf go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `proto.Size(m)`: a size, at least `0`, of a put request; of a range response (its header's
id fields lent); of a read-only transaction's response (its header's id fields lent). -/
abbrev proto.Size.spec : Prop :=
  (∀ (p : Loc) (o : OpFull),
    {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ txn.putRequestIs p o }}
      (App (Val (@! proto.Size))
        (Val #(interface.mkOk (go.GoType.PointerType etcdserverpb.PutRequest.ty) #p)))
    {{ (n : w64), RET #n; ⌜0 ≤ sint.Z n⌝ }}) ∧
  (∀ (r : Loc) (rev : w64) (kvs : List EtcdKv) (more : Bool) (count : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗
        txn.rangeResponseIs r rev kvs more count ∗
        txn.respHdrOwn (structFieldRef etcdserverpb.RangeResponse go!"Header" r) }}
      (App (Val (@! proto.Size))
        (Val #(interface.mkOk (go.GoType.PointerType etcdserverpb.RangeResponse.ty) #r)))
    {{ (n : w64), RET #n; ⌜0 ≤ sint.Z n⌝ ∗
        txn.respHdrOwn (structFieldRef etcdserverpb.RangeResponse go!"Header" r) }}) ∧
  (∀ (r : Loc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗
        txn.roTxnRespRd r ∗ txn.respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" r) }}
      (App (Val (@! proto.Size))
        (Val #(interface.mkOk (go.GoType.PointerType etcdserverpb.TxnResponse.ty) #r)))
    {{ (n : w64), RET #n; ⌜0 ≤ sint.Z n⌝ ∗
        txn.respHdrOwn (structFieldRef etcdserverpb.TxnResponse go!"Header" r) }})

end spec

end EtcdGrove
end Perennial
