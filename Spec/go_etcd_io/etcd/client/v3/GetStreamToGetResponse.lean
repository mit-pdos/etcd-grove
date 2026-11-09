/-
`clientv3.GetStreamToGetResponse` (`client/v3/kv.go`).

Users: `etcdctl get --stream`; any user that wants the whole answer of a stream (Kubernetes reads the channel itself).

Proof sketch: `for r := range stream`: `streamAt_recv` per chunk, `RangeStreamResponse.Err.spec`, `proto.Merge` (protobuf's boundary: the repeated `Kvs` appended, the header, `More` and `Count` of the last chunk that sets them) into a fresh `RangeResponse`; the end gives `Q` and `streamMatches`.

Changes: none (no old spec): added for the users named above.
verify-round: the error post has `ErrCompacted` without a `Q` (A1-provability F1: `streamAt_recv`'s
terminal chunk when the revision the server pinned at the first page was compacted before a later
read; the caller relists).

Margin: as `streamMatches`.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `GetStreamToGetResponse(stream)` of a fresh `GetStream` channel: the merged reply, or the
terminal error. -/
def GetStreamToGetResponse.spec : Prop :=
  ∀ (ch : Loc) (γ : Cluster) (who : Principal) (r : RangeReq)
    (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ streamAt ch γ who r Q [] false }}
    (App (Val (@! go_etcd_io.etcd.client.v3.GetStreamToGetResponse)) (Val #ch))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (σ σ' : State) (rev : Nat) (a : RangeAns) (m : RangeRespM),
         Q σ σ' (.ok (.range rev a)) ∗ rangeRespOwn resp (DFrac.own 1) m ∗
         ⌜m.hdr.map (·.revision) = some (W64 rev) ∧
           (isDefaultOrdering r.sortTarget r.sortOrder ∧ ¬ r.hasRevFilters →
             m.kvs = a.kvs.map KeyValueM.ofKV ∧ m.more = a.more)⌝) ∨
      (⌜resp = null⌝ ∗ ((∃ (σ σ' : State) (e : EtcdErr), Q σ σ' (.err e) ∗ ⌜err = errVal e⌝) ∨
        ⌜err = errVal .compacted⌝ ∨
        indefCall err)) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
