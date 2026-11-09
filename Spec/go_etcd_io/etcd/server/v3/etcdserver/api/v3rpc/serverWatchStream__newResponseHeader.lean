/-
`(*serverWatchStream).newResponseHeader(rev)` (`watch.go`): a response's header.

**Users.** `recvLoop` (every control response), `sendLoop`'s `sendWatch` (every mvcc response).

**Proof sketch.** The member's ids from the run's read-only fields (`swsAt`); `sws.sg.Term()`,
`sws.sg.Leader()` (the member as `apply.RaftStatusGetter`, `watchMemberAt`'s triples, 2c/2d: any
values, no panic, no thread token); a fresh `ResponseHeader` (`respHeaderOwn_unfold`, with
`protoRest_zero`).

**Changes** from `specs-ref`'s file: the run record replaced by `swsAt`; the read-only header
(`hdrFull`) by W0's `respHeaderOwn` owned in full (the caller persists it when it shares it among
fragments); the ids by an existential (no client reads them).

**Margin.** The cluster and member ids, the term and the leader are not stated.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchInternal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`sws.newResponseHeader(rev)`**: a fresh header with the revision `rev`. -/
def serverWatchStream.newResponseHeader.spec : Prop :=
  ∀ (sws : Loc) (γ : EtcdModel.Cluster) (who : Principal) (st : GoInterface) (g : WatchStreamNames)
    (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      swsAt sws γ who st g }}
    (App (Val (sws @!! go.GoType.PointerType v3rpc.serverWatchStream.ty @!! go!"newResponseHeader"))
      (Val #rev))
  {{ (h : Loc), RET #h; ∃ m : HeaderM, ⌜m.revision = rev⌝ ∗ respHeaderOwn h (DFrac.own 1) m }}

end spec

end V3rpc
end EtcdGrove
end Perennial
