/-
**The gRPC layer's streamed range** (auth-mediation M3, 2026-11-21): what `kvServer.RangeStream`'s
caller receives of each chunk (`rangeChunkOut`: a chunk of the range, its header `nil` or filled by
the service's `header`, `headerFillingRangeStream.Send`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvKV
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RangeStreamDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

namespace v3rpc

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A chunk of the streamed range `o` as the gRPC layer sends it**: `rangeChunkIs`'s (a
`*pb.RangeStreamResponse` whose `RangeResponse` holds key-values of keys in `o`'s range, as the
auth store reads a range), its header `nil` or filled by the service's header of the cluster `cid`
and member `mid` (`hdrFilled`: what `headerFillingRangeStream.Send` writes). -/
def rangeChunkOut (o : OpFull) (cid mid : w64) (resp : Loc) : IProp GF :=
  iprop(∃ (rr : Loc) (sl : GoSlice) (ps : List Loc) (kvs : List EtcdKv),
    structFieldRef etcdserverpb.RangeStreamResponse go!"RangeResponse" resp ↦□ rr ∗ ⌜rr ≠ null⌝ ∗
    (structFieldRef etcdserverpb.RangeResponse go!"Header" rr ↦□ (null : Loc) ∨
      ∃ h : Loc, structFieldRef etcdserverpb.RangeResponse go!"Header" rr ↦□ h ∗ hdrFilled h cid mid) ∗
    structFieldRef etcdserverpb.RangeResponse go!"Kvs" rr ↦□ sl ∗ sl ↦*□ ps ∗ txn.kvsIs ps kvs ∗
    ⌜∀ kv ∈ kvs, auth.inRange o.key o.base.rangeEnd kv.key⌝)

end defs

end v3rpc

end EtcdGrove
end Perennial
