/-
**A `*pb.RangeRequest` with its rewritable fields at a fraction** (auth-mediation M3, 2026-11-21):
`rangeRequestAt r dq o`, `rangeRequestIs` (`Requests.lean`) with `Key`, `Limit` and `Revision` at
`dq`: what the functions that only read a request take (`txn.HasRevisionFilters`, the gRPC layer's
`checkRangeRequest`/`checkRangeStreamRequest`), so that a read-only request (`DFrac.discard`) and
the streamed one whose three fields `EtcdServer.rangeStream` rewrites (`DFrac.own 1`) both pass.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Requests

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open Iris Iris.BI go_etcd_io.etcd.api.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The `*pb.RangeRequest` `r` (not nil) of the get `o`, its three rewritten fields at `dq`**:
`Key`, `Limit` and `Revision` (which `rangeStream` writes between pages) at the fraction `dq`, the
others and the key's contents read-only. At `DFrac.discard` it is `rangeRequestIs`
(`rangeRequestIs_at`), at `DFrac.own 1` `rangeRequestOwn` (`rangeRequestOwn_at`, `etcdserver/RangeStreamDefs.lean`): the form the
functions that only read the request take, so that both a read-only and a streamed request pass
them. -/
def rangeRequestAt (r : Loc) (dq : DFrac) (o : OpFull) : IProp GF :=
  iprop(⌜r ≠ null⌝ ∗ ∃ (ksl esl : GoSlice) (k e : GoString) (rev limit : w64)
      (order target : w32) (ser ko co : Bool) (minM maxM minC maxC : w64),
    structFieldRef etcdserverpb.RangeRequest go!"Key" r ↦{dq} ksl ∗ ksl ↦*□ k ∗
    structFieldRef etcdserverpb.RangeRequest go!"RangeEnd" r ↦□ esl ∗ esl ↦*□ e ∗
    structFieldRef etcdserverpb.RangeRequest go!"Limit" r ↦{dq} limit ∗
    structFieldRef etcdserverpb.RangeRequest go!"Revision" r ↦{dq} rev ∗
    structFieldRef etcdserverpb.RangeRequest go!"SortOrder" r ↦□ order ∗
    structFieldRef etcdserverpb.RangeRequest go!"SortTarget" r ↦□ target ∗
    structFieldRef etcdserverpb.RangeRequest go!"Serializable" r ↦□ ser ∗
    structFieldRef etcdserverpb.RangeRequest go!"KeysOnly" r ↦□ ko ∗
    structFieldRef etcdserverpb.RangeRequest go!"CountOnly" r ↦□ co ∗
    structFieldRef etcdserverpb.RangeRequest go!"MinModRevision" r ↦□ minM ∗
    structFieldRef etcdserverpb.RangeRequest go!"MaxModRevision" r ↦□ maxM ∗
    structFieldRef etcdserverpb.RangeRequest go!"MinCreateRevision" r ↦□ minC ∗
    structFieldRef etcdserverpb.RangeRequest go!"MaxCreateRevision" r ↦□ maxC ∗
    ⌜o = rangeOpOf k (rangeEndOf esl e) rev limit order target ser ko co minM maxM minC maxC⌝ ∗
    ⌜sint.Z ksl.len < 2 ^ 63 - 1⌝)

/-- `rangeRequestIs` is `rangeRequestAt` at `DFrac.discard`. -/
theorem rangeRequestIs_at (r : Loc) (o : OpFull) :
    rangeRequestIs (GF := GF) r o ⊣⊢ rangeRequestAt r DFrac.discard o := .rfl

instance rangeRequestAt_discard_persistent (r : Loc) (o : OpFull) :
    Persistent (rangeRequestAt (GF := GF) r DFrac.discard o) := by
  unfold rangeRequestAt; infer_instance

end defs

end txn
end EtcdGrove
end Perennial
