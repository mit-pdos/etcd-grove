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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The cache's watch start, as the client's `Watch` takes it** (K2e-7d): `startOk` of a
start-read watch from `etcdRead (rev - 1)`. -/
theorem startOk_of_etcdRead (V : WEnv GF) (rev : w64) (hst : V.R.γ.st = V.R.E.γ)
    (h1 : 0 < sint.Z rev) :
    etcdRead (EM := V.EM) (rev - W64 1) ⊢ startOk V true rev := by
  iintro #H
  unfold startOk
  iright; iapply etcdRead_reached (EM := V.EM) (rev - W64 1) $$ H

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
  iapply (wp_Watch V w ctx cs key sl gs rev false) $$ [] [HΦ]
  · iframe #
    isplitr
    · ipureintro; exact Hpre
    unfold startOk; ileft; ipureintro; rfl
  inext
  iintro %ch %γ ⟨#Hs, Hc, #Hi, -, -⟩
  iapply HΦ
  iframe Hc
  iframe #

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

/-- **etcd's client's watcher meets the cache's watcher contract** at the server's model
(K2e-8), for a cache whose prefix is not all `0xff` (`cplCond`'s condition, with the prefix
non-empty, which `watchConnFacts` says: the client promises completeness only for such a prefix
watch): the channel `Watch` returns, at its second cursor. -/
theorem isEtcdWatcher_of_watcher (wp_Watch : watcher.Watch.spec (GF := GF) (hG := hG))
    (V : WEnv GF) (w : Loc) (hff : prefixRangeEnd V.pfx ≠ [W8 0]) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ isClientWatcher V w ⊢
    isEtcdWatcher (EM := V.EM) (watcherIfaceOf w) V.pfx := by
  iintro ⟨#P1, #P2, #P3, #Hw⟩
  ihave %hf : ⌜V.R.γ.st = V.R.E.γ ∧ V.pfx ≠ []⌝ $$ [Hw]
  · iunfold isClientWatcher at Hw
    icases Hw with ⟨%cs, %vs, -, -, -, -, -, -, -, Hsf, -⟩
    iunfold watchSrvFacts at Hsf
    icases Hsf with ⟨-, Hcf⟩
    iunfold watchConnFacts at Hcf
    icases Hcf with ⟨-, -, -, -, -, -, -, -, -, -, %h⟩
    ipureintro; exact h
  obtain ⟨hst, hp⟩ := hf
  unfold isEtcdWatcher
  iintro !> %ctx %cs %key %sl %gs %rev %Φ !> ⟨#Hctx, #Hopts, %Hpre, #Hrd⟩ HΦ
  obtain ⟨hpw, hnp, hrev⟩ := Hpre
  unfold OpFull.isPrefixWatch at hpw
  simp only [decide_eq_true_eq, hp, if_false] at hpw
  obtain ⟨ht, hr, -, -, hpk, hfr, hfp, hfd, hkey, hend⟩ := hpw
  iapply (wp_Watch V w ctx cs key sl gs rev true) $$ [] [HΦ]
  · iframe #
    isplitr
    · ipureintro
      refine ⟨?_, hnp, by omega, ?_⟩
      · unfold OpFull.isRangeWatch; simp only [decide_eq_true_eq]
        exact ⟨ht, hr, hpk, hfr, hfp, hfd⟩
      · rw [hkey, hend]; exact concurrency.keyRangeUnder_prefix V.pfx hp
    iapply startOk_of_etcdRead V rev hst hrev $$ Hrd
  inext
  iintro %ch %γ ⟨#Hs, Hc, #Hi, #Hi2, %Hcpl⟩
  have hc : γ.cpl = true := by
    rw [Hcpl]; unfold cplCond
    have : rev ≠ W64 0 := fun h => by subst h; simp at hrev
    simp only [hkey, hend, Bool.true_and, decide_eq_true_eq]
    exact ⟨hp, trivial, hff, this⟩
  ispecialize HΦ $$ %ch %(⟨γ.spsc, γ.cur2, γ.cur2, γ.cpl⟩ : EtcdWatchNames)
  iapply HΦ
  isplitr
  · unfold isEtcdWatchChan
    iexists rangeWatchElem (EM := V.EM) γ V.pfx (opWatchModel key gs) rev
    iframe Hs
    iintro !> %i %v H
    iapply etcdWatchElem_of_rangeWatchElem (EM := V.EM) γ V.pfx (opWatchModel key gs) rev hc hkey
      i v $$ H
  unfold etcdWatchConsumer
  iexists []
  iframe Hc Hi2
  ipureintro; rfl

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
  ihave #Hsm : storeSmall R.E.γ $$ [Hsrd]
  · iunfold isServerRead at Hsrd
    icases Hsrd with ⟨%v, Hsrd⟩
    iunfold srvReadFieldsAt at Hsrd
    icases Hsrd with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hsm, -⟩
    iexact Hsm
  unfold srvLogsSmall
  iunfold storeSmall at Hsm
  rw [h]
  iexact Hsm

/-- The watch server's watch-token pool (`watchSrvOk`; D19b's method, 2026-10-18). -/
theorem watchTokPool_of_server (p : Loc) (R : v3rpc.WSrv GF) :
    v3rpc.isWatchServer (GF := GF) p R ⊢ mvcc.watchTokPool R.γ := by
  iintro #H
  iunfold v3rpc.isWatchServer at H
  icases H with ⟨-, -, -, -, -, -, -, -, Hok⟩
  iunfold v3rpc.watchSrvOk at Hok
  icases Hok with ⟨-, -, -, -, -, #Hp⟩
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
