/-
**The clients' range watcher, derived for etcd's client over etcd's server** (the watch slice's
unit W-C, 2026-10-15; `notes/STATUS.md`, "W-C"). Lean-first, no Rocq counterpart.

`isEtcdRangeWatcher_of_watcher`: a `*watcher` (`isClientWatcher V w`, what `NewWatcher` and
`NewWatchFromWatchClient` return over a stub on a connection to a server serving etcd's `Watch`
stream) meets the clients' closable range-watch contract (`isEtcdRangeWatcher`,
`cache/v3/InvEtcdTxn.lean`) at the server's model (`v3rpc.etcdModelOfServer V.R.E`), from
`watcher.Watch`'s spec (linked in `Results.lean`: `client_watcher_rangeWatcher`, and
`client_newWatcher_rangeWatcher` for `NewWatcher(c)`'s result).
`srvLogsSmall_of_read`, `watchSrvLink_of_server`: two of the premises (`watchConnFacts`) from the
server's facts (`isServerRead`, `isWatchServer`).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watcher__Watch
public import Spec.go_etcd_io.etcd.client.v3.watcher__RequestProgress
public import Spec.go_etcd_io.etcd.client.v3.NewWatcher
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead
public import Proof.go_etcd_io.etcd.client.v3.PrefixRange

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- A range watch response's header, owned, made read-only: the cache's `hdrAt`. -/
theorem hdrAt_of_watchHdrOwn [EM : EtcdModel GF] (h : Loc) (r : RespModel) :
    watchHdrOwn (GF := GF) h r ⊢ |==> hdrAt h r.hdrRev := by
  unfold watchHdrOwn
  split
  · iintro #H; imodintro; iexact H
  · iintro ⟨%hn, H⟩
    ipersist H
    imodintro
    unfold hdrAt
    iright
    iframe H
    ipureintro; exact hn

/-- **A response of a range watch that promises completeness is etcd's** (K2e-8): the `i`-th
response of a range watch of `o` (with `o.key` the prefix `pfx`) whose `γ.cpl` is set satisfies the
cache's contract at the second cursor (`etcdWatchElem` at `γ.cur2`). -/
theorem etcdWatchElem_of_rangeWatchElem [EM : EtcdModel GF] (γ : EtcdWatchNames) (pfx : GoString)
    (o : OpFull) (rev : w64) (hcpl : γ.cpl = true) (hk : o.key = pfx) (i : Int)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) :
    rangeWatchElem (GF := GF) γ pfx o rev i v ⊢
      |==> etcdWatchElem ⟨γ.spsc, γ.cur2, γ.cur2, γ.cpl⟩ pfx i v := by
  unfold rangeWatchElem
  iintro ⟨%r, %c, %c', #He, Hh, %Hf, -, -, -, -, Hcp⟩
  icases Hcp with (%Hc | ⟨%c2, %c2', #H2, #H2', #Hok⟩)
  · rw [hcpl] at Hc; cases Hc
  imod hdrAt_of_watchHdrOwn v.Header' r $$ Hh with #Hh
  imodintro
  unfold etcdWatchElem respAt
  iexists r, c2, c2'
  rw [← hk]
  iframe #
  ipureintro; exact Hf

/-- **etcd's client's watcher is the cache's progress notifier** (K2e-9): `RequestProgress`
returns an error whose `Error()` gives a string (grpc's `status` accepts it). -/
theorem isEtcdProgressNotifier_of_watcher
    (wp_RP : watcher.RequestProgress.spec (GF := GF) (hG := hG)) (V : WEnv GF) (w : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ isClientWatcher V w ⊢
    isEtcdProgressNotifier (watcherIfaceOf w) := by
  iintro ⟨#P1, #P2, #P3, #Hw⟩
  unfold isEtcdProgressNotifier
  iintro !> %ctx %cs %Φ !> #Hctx HΦ
  iapply (wp_RP V w ctx cs) $$ [] [HΦ]
  · iframe #
  inext
  iintro %err #Hse
  iapply HΦ
  ihave #Hs := errStrOk_of_statusErrOk err $$ Hse
  iunfold errStrOk at Hs
  iexact Hs

/-- The server's sealed logs are small (the read side's `storeSmall`), so `srvLogsSmall`. -/
theorem srvLogsSmall_of_read (R : v3rpc.WSrv GF) (s : Loc) (γr : ReadNames)
    (h : R.γ.st = R.E.γ) :
    isServerRead (GF := GF) s R.E γr ⊢ srvLogsSmall R := by
  iintro #Hsrd
  ihave #Hsm := storeSmall_of_read s R.E γr $$ Hsrd
  ihave #Hs := storeSmall_small R.E.γ $$ Hsm
  unfold srvLogsSmall
  rw [h]
  iexact Hs

/-- **The server's sealed logs are small, from the receipts' bound** (G2's follow-up, 2026-10-30:
in any auth mode, with no read view; `storeSmall_of_receipts`). -/
theorem srvLogsSmall_of_receipts [go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (R : v3rpc.WSrv GF) (h : R.γ.st = R.E.γ) (hrb : receiptBound GF ≤ 2 ^ 62) :
    ⊢ srvLogsSmall R := by
  iintro
  ihave #Hsm := storeSmall_of_receipts R.E.γ hrb
  ihave #Hs := storeSmall_small R.E.γ $$ Hsm
  unfold srvLogsSmall
  rw [h]
  iexact Hs

/-- The watch server's watch-token pool (`watchSrvOk`; D19b's method, 2026-10-18). -/
theorem watchTokPool_of_server (p : Loc) (R : v3rpc.WSrv GF) :
    v3rpc.isWatchServer (GF := GF) p R ⊢ mvcc.watchTokPool R.γ := by
  iintro #H
  iunfold v3rpc.isWatchServer at H
  icases H with ⟨-, -, -, -, -, -, -, -, Hok⟩
  iunfold v3rpc.watchSrvOk at Hok
  icases Hok with ⟨-, -, -, -, -, #Hp, -⟩
  iexact Hp

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
