/- Lean-first (no Rocq counterpart).

`c.receive(resp)` (`examples/mvccrand/mvccrand.go`): the receiver's check of the response `resp`,
the `r` it just received from the stream (`wsRecv` at `rs ++ [r]`, `wrespIs`), after it checked the
responses `rs` (its half of `γ.rcv`), under `c.mu` (`cmuInv`, `WatchLock.lean`): no compaction; a
progress response at a revision written, after every change of its watcher (if any) up to it; each
event its watcher's next expected change, at or below the response's revision, its type and fields
the change's. Every check passes; the receiver has checked `rs ++ [r]`, and `c.events` (the
receiver's) counts `r`'s events.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.WatchLock

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- See the file header. -/
abbrev watchCheck.receive.spec : Prop :=
  ∀ (c : Loc) (γ : RandNames) (h : Loc) (wm : GoMap) (rs : List WResp) (r : WResp)
    (resp : go_etcd_io.etcd.server.v3.storage.mvcc.WatchResponse) (ne : w64),
  {{ wcCtx c γ h wm ∗ histRd h γ.h ∗ wsRecv γ.ws (rs ++ [r]) ∗ wrespIs resp r ∗
      ghostVar γ.rcv (1 : Qp).half rs ∗ cF go!"events" c ↦ ne }}
    (App (Val (c @!! go.GoType.PointerType watchCheck.ty @!! go!"receive")) (Val #resp))
  {{ RET #(); histRd h γ.h ∗ wsRecv γ.ws (rs ++ [r]) ∗ ghostVar γ.rcv (1 : Qp).half (rs ++ [r]) ∗
      cF go!"events" c ↦ (ne + W64 (r.evs.length : Int)) }}

end spec

end mvccrand
end EtcdGrove
end Perennial
