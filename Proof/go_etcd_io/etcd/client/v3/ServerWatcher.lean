/-
**The clients' range watcher, derived for etcd's client over etcd's server** (the watch slice's
unit W-C, 2026-10-15; `notes/STATUS.md`, "W-C"). Lean-first, no Rocq counterpart.

`isEtcdRangeWatcher_of_watcher`: a `*watcher` (`isClientWatcher V w`, what `NewWatcher` and
`NewWatchFromWatchClient` return over a stub on a connection to a server serving etcd's `Watch`
stream) meets the clients' closable range-watch contract (`isEtcdRangeWatcher`,
`cache/v3/InvEtcdTxn.lean`) at the server's model (`v3rpc.etcdModelOfServer V.R.E γr false`), from
`watcher.Watch`'s spec (linked in `Results.lean`: `client_watcher_rangeWatcher`, and
`client_newWatcher_rangeWatcher` for `NewWatcher(c)`'s result).
(Strict M1, 2026-11-06: `srvLogsSmall_of_read`, `srvLogsSmall_of_receipts`, `watchTokPool_of_server`
and `watchSrvLink_of_server` are gone with what they gave: the logs' smallness is `srvWOk`'s law,
`srvWLaws`; the API's `Watch` takes no token; `WSrv` has no store names.)
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
  iintro !> %ctx %cs %Φ !> ⟨#Hctx, #HctxO⟩ HΦ
  iapply (wp_RP V w ctx cs) $$ [] [HΦ]
  · iframe #
  inext
  iintro %err #Hse
  iapply HΦ
  ihave #Hs := errStrOk_of_statusErrOk err $$ Hse
  iunfold errStrOk at Hs
  iexact Hs

end proofs

end client
end EtcdGrove
end Perennial
