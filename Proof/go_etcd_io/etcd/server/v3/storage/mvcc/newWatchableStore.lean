/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newWatchableStore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewStore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newWatcherGroup
public import Spec.go_uber_org.zap.NewNop
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__Write
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchFrac
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.NewWatchableLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.newWatchableStore.wp_proof
    (hNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (hNewStore : mvcc.NewStore.spec (GF := GF) (hG := hG))
    (hNewWG : mvcc.newWatcherGroup.spec (GF := GF) (hG := hG))
    (hsplit : adt.ownIvt_split.spec (GF := GF) (hG := hG))
    (hWrite : mvcc.watchableStore.Write.spec (GF := GF) (hG := hG))
    (hTODO : traceutil.TODO.spec (GF := GF) (hG := hG)) :
    mvcc.newWatchableStore.spec (GF := GF) (hG := hG) := by
  -- B3 Prove (mvccfull's Freeze, 2026-11-10): over `NewStore.spec`'s restated pre (an image at the
  -- records `r`); the post's closer by the mode at `r.crev` (`storeCloserM`), the client parts at the
  -- restored log, the lessor's part and `resumeBackM` passed through. The proof of the fresh
  -- statement is at commit `ae30739dde` (this file); the watchers' structures start empty as there.
  sorry

end proof

end EtcdGrove
end Perennial
