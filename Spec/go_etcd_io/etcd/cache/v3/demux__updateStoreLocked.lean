/-
`demux.updateStoreLocked` (`cache/*.go`), an internal helper.
Users: `demux.Broadcast`.
Proof sketch: a progress notification sets `maxRev`; events are split into one-revision batches appended to the history (`ringBuffer.Append.spec`; a full ring's eviction raises `minRev`), `maxRev` the last event's revision; the invariant records the response as pending.
Changes: restated over the opaque vocabulary of `Internal.lean` (the old internal handles, ghost names and certificate parameters replaced by predicates over W0's model); the spec mirrors the code.
Margin: none known.
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cache

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `d.updateStoreLocked(resp)` under the lock, for a validated, certified response. -/
def demux.updateStoreLocked.spec : Prop :=
  ∀ (d : Loc) (γ : Cluster) (pfx : GoString) (s : Loc) (pos pos' : Option Int) (r : Nat)
    (resp : go_etcd_io.etcd.client.v3.WatchResponse) (m : WatchRespM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ demuxLocked d γ pfx s none ∗ demuxFeed d γ pfx s pos ∗ watchRespAt resp m ∗ respFact γ (prefixRange pfx) pos m pos' ∗ storeCeilLb s r ∗ ⌜m.hdrRev ≤ r ∧ ∀ e ∈ m.events, e.rev ≤ r⌝ }}
    (App (Val (d @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.demux.ty @!! go!"updateStoreLocked")) (Val #resp))
  {{ RET #(); demuxLocked d γ pfx s (some m) ∗ demuxFeed d γ pfx s pos' }}

end spec

end Cache
end EtcdGrove
end Perennial
