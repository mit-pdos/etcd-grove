/- Lean-first (no Rocq counterpart).

`CompactRev(wch)` (`examples/common/watch.go`; C3's watch side, 2026-11-02): reads the first
response of a client watch channel (`isRespChan`, its responses saying the caller's `Ok`; its
consumer at position `0`, the cursor at `c0`); with `true`, the response's compaction revision, not
`0`, and the response meets `Ok` (from the cursor to some position). With `false` nothing: the
channel closed, or the response is not a compaction's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.RespChan

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver github_com.mit_pdos.etcd_grove.examples.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

/-- See the file header. -/
abbrev CompactRev.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (Ok : RespOk GF) (wch : Loc) (γ : EtcdWatchNames)
    (c0 : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.common ∗
      isRespChan wch γ Ok ∗ etcdWatchConsumer γ 0 c0 }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.common.CompactRev)) (Val #wch))
  {{ (rv : w64) (ok : Bool), RET (PairV #rv #ok);
      ⌜ok = true⌝ -∗ ∃ (c' : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel),
        Ok c0 c' v r ∗ ⌜v.CompactRevision' = rv ∧ rv ≠ W64 0⌝ }}

end spec

end common
end EtcdGrove
end Perennial
