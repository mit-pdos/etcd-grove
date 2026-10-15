/-
**The clients' range watcher, derived for etcd's client over etcd's server** (the watch slice's
unit W-C, 2026-10-15; `notes/STATUS.md`, "W-C"). Lean-first, no Rocq counterpart.

`isEtcdRangeWatcher_of_watcher`: a `*watcher` (`isClientWatcher V w`, what `NewWatcher` and
`NewWatchFromWatchClient` return over a stub on a connection to a server serving etcd's `Watch`
stream) meets the clients' closable range-watch contract (`isEtcdRangeWatcher`,
`cache/v3/InvEtcdTxn.lean`) at the server's model (`v3rpc.etcdModelOfServer V.R.E`), from
`watcher.Watch`'s spec. `newWatcher_isEtcdRangeWatcher`: `NewWatcher(c)`'s result does.
`srvLogsSmall_of_read`, `watchSrvLink_of_server`: two of the premises (`watchConnFacts`) from the
server's facts (`isServerRead`, `isWatchServer`).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watcher__Watch
public import Spec.go_etcd_io.etcd.client.v3.NewWatcher
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3
  go_etcd_io.etcd.server.v3.etcdserver

section proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **etcd's client's watcher meets the clients' range-watch contract** at the server's model
(the closable one: the channel may be closed). -/
theorem isEtcdRangeWatcher_of_watcher (wp_Watch : watcher.Watch.spec (GF := GF) (hG := hG))
    (V : WEnv GF) (w : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ isClientWatcher V w ⊢
    isEtcdRangeWatcher (EM := V.EM) (watcherIfaceOf w) V.pfx := by
  iintro ⟨#P1, #P2, #P3, #Hw⟩
  unfold isEtcdRangeWatcher
  iintro !> %ctx %cs %key %sl %gs %rev %Φ !> ⟨#Hctx, #Hopts, %Hpre⟩ HΦ
  iapply (wp_Watch V w ctx cs key sl gs rev) $$ [] HΦ
  iframe #
  ipureintro; exact Hpre

/-- The server's certified logs are small (the read side's `storeSmall`), so `srvLogsSmall`. -/
theorem srvLogsSmall_of_read (R : v3rpc.WSrv GF) (s : Loc) (γr : ReadNames)
    (h : R.γ.st = R.E.γ) :
    isServerRead (GF := GF) s R.E γr ⊢ srvLogsSmall R := by
  iintro #Hsrd
  ihave #Hsm := storeSmall_of_read s R.E γr $$ Hsrd
  unfold srvLogsSmall
  iunfold storeSmall at Hsm
  rw [h]
  iexact Hsm

/-- The watch server's store names are its environment's (`watchSrvOk`). -/
theorem watchSrvLink_of_server (p : Loc) (R : v3rpc.WSrv GF) :
    v3rpc.isWatchServer (GF := GF) p R ⊢ ⌜R.γ.st = R.E.γ⌝ := by
  iintro #H
  iunfold v3rpc.isWatchServer at H
  icases H with ⟨-, -, -, -, -, -, -, -, Hok⟩
  iunfold v3rpc.watchSrvOk at Hok
  icases Hok with ⟨-, %h, -⟩
  ipureintro; exact h

end proofs

end client
end EtcdGrove
end Perennial
