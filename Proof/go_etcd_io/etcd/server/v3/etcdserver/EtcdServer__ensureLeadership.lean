/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__ensureLeadership.lean` (srvloops2,
2026-11-21; until then a names-only contract, the lease-renew plan's C2): `isActive` (the latest tick,
under `tickMu`'s read lock with a slot of its pool, `srvLeadCheckOk`); if active, a debug log of the
latest tick (read again) and the time; else a linearizable read on a `WithTimeout` child of `s.ctx`,
then raft's `Status().Lead` against the member's id. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__ensureLeadership
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__isActive
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__raftStatus
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__getLatestTickTs
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__ReqTimeout
public import Spec.go_uber_org.zap.Time
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Uint64
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.Logger__Warn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxHeartbeats 2000000 in
theorem EtcdServer.ensureLeadership.wp_proof
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hIA : EtcdServer.isActive.spec (GF := GF) (hG := hG))
    (hGLT : raftNode.getLatestTickTs.spec (GF := GF) (hG := hG))
    (hZT : zap.Time.spec (GF := GF) (hG := hG))
    (hDbg : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (hReqT : config.ServerConfig.ReqTimeout.spec (GF := GF) (hG := hG))
    (hRS : EtcdServer.raftStatus.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hU64 : zap.Uint64.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    EtcdServer.ensureLeadership.spec (GF := GF) (hG := hG) := by
  intro s E ρ γr l
  wp_start as ⟨#Hq, #Hr, Hlgr, Hrrd, Hl, %Hlok⟩
  ihave ⟨⟨%rv, #Hrf⟩, -⟩ := (isServerReqM_split _ _ _ _).1 $$ Hq
  ihave #Hrf' := Hrf
  iunfold srvReqFieldsAtM at Hrf'
  icases Hrf' with ⟨-, -, -, -, -, -, -, -, -, #Het, #Htm, -, -, -, -, #Hmid, -, -, -, -, -, -, -, -,
    -, %Hcfg⟩
  ihave #Hr' := Hr
  iunfold isServerReadM at Hr'
  icases Hr' with ⟨%w, #Hw⟩
  iunfold srvReadFieldsAtM at Hw
  icases Hw with ⟨#Hread, #HisRead, -, -, -, -, -, -, -, #Hlgf, #Hlgn, -, -, -, -, -, -, -, -, -,
    -, -, -, -, #Hlck⟩
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Ptime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hlck' := Hlck
  iunfold srvLeadCheckOk at Hlck'
  icases Hlck' with ⟨⟨%mu, #Hmu, #Htp⟩, -, ⟨%ctx, %cd, #Hctxf, #Hctxi, -⟩⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  wp_apply hLg s w.lg $$ [Hlgr] as ⟨#Hl0, Hlgr⟩
  · iframe #; iframe Hlgr
  (try wp_auto)
  -- `if s.isActive()`
  wp_apply hIA s rv.tickMs l $$ [Hl] as %act Hl
  · iframe #; iframe Hl; ipureintro; exact Hlok
  cases act with
  | true =>
    -- the debug log: `s.r.getLatestTickTs()` again, with a slot of `tickMu`'s pool at level `l`
    iunfold rnTickPool at Htp
    ihave ⟨%γ, #Hp⟩ := Htp $$ %l %Hlok
    wp_auto_lc 1
    iapply wp_fupd
    imod threadPool.borrowL_lc (rnTickPoolN l) l γ _ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hlc1 Hp Hl]
      with ⟨HR, Hloan⟩
    · iframe Hlc1 Hl; iexact Hp
    wp_apply hGLT (srvRAddr s) mu $$ [HR] as %t HR
    · iframe #; iframe HR
    imod threadPool.giveBackL (rnTickPoolN l) l γ _ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp Hloan HR]
      with Hl
    · iframe Hloan HR; iexact Hp
    (try wp_auto)
    wp_apply hZT as %f1 -
    (try wp_auto)
    wp_apply _root_.Perennial.time.wp_Now as %now -
    (try wp_auto)
    wp_apply hZT as %f2 -
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply hDbg w.lg $$ []
    · iframe #
    (try wp_auto)
    (try imodintro)
    (try wp_auto)
    iapply HΦ
    iframe Hlgr Hrrd Hl
  | false =>
    (try wp_auto)
    -- `ctx, cancel := context.WithTimeout(s.ctx, s.Cfg.ReqTimeout())`
    wp_apply hReqT (structFieldRef EtcdServer go!"Cfg" s) rv.electionTicks rv.tickMs as %tmo -
    · iframe #
    (try wp_auto)
    wp_apply context.wp_WithTimeout ctx cd tmo $$ [] as %cctx %γc %cancel %dl ⟨#Hcancel, #Hcctx, -⟩
    · iframe #
    (try wp_auto)
    -- `s.read.LinearizableReadNotify(ctx)`, with the read loop's slot, at the committed index `0`
    ihave #HisRead' := HisRead
    iunfold isReadNotify at HisRead'
    iunfold srvReadReader at Hrrd
    icases Hrrd with ⟨%rd, #Hrd0, Hrrd⟩
    icombine Hread Hrd0 gives %Hrdeq
    subst Hrdeq
    imod (monoNatLbOwn_0 (GF := GF) γr.committed) with #H0
    ihave #Hc0 : committedAtLeast γr (W64 0) $$ []
    · unfold committedAtLeast; ileft
      rw [show uint.nat (W64 0) = 0 from rfl]
      iexact H0
    imod saved_pred_alloc (fun (_ : List EntryModel) => iprop(True)) DFrac.discard trivial
      with ⟨%g, #Hg⟩
    ihave #Hdep : kvDep (GF := GF) γr.kv (fun (_ : List EntryModel) => iprop(True))
        (kvStM E.authOn γr.kv) $$ []
    · iunfold kvDep; iright; ipureintro; rfl
    wp_apply HisRead' $$ %cctx %_ %(W64 0) %g %(fun (_ : List EntryModel) => iprop(True)) [Hrrd]
      as %rerr ⟨Hrrd, -, -, -⟩
    · iframe Hdep Hg Hc0; iframe Hrrd; iunfold mvcc.txnCtx; iright; iexact Hcctx
    ihave Hrrd : srvReadReader s γr $$ [Hrrd]
    · iunfold srvReadReader; iexists _; iframe Hread Hrrd
    (try wp_auto)
    cases rerr with
    | ok rei =>
      -- `lg.Warn("Failed to check current member's leadership", zap.Error(err)); return false`
      (try wp_auto)
      wp_apply hZE as %f1 -
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      (try wp_auto)
      wp_apply hWarn w.lg $$ []
      · iframe #
      (try wp_auto)
      wp_apply Hcancel
      (try wp_auto)
      (try imodintro)
      (try wp_auto)
      iapply HΦ
      iframe Hlgr Hrrd Hl
    | nil =>
      (try wp_auto)
      -- `newLeaderID := s.raftStatus().Lead`
      wp_apply hRS s as %st -
      · iframe #
      (try wp_auto)
      wp_apply hMID s rv.memberID $$ []
      · iframe #
      (try wp_auto)
      by_cases hl : st.BasicStatus'.SoftState'.Lead' = rv.memberID
      · rw [decide_eq_true hl]
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        (try imodintro)
        (try wp_auto)
        iapply HΦ
        iframe Hlgr Hrrd Hl
      · rw [decide_eq_false hl]
        (try wp_auto)
        wp_apply hMID s rv.memberID $$ []
        · iframe #
        (try wp_auto)
        wp_apply hU64 as %f1 -
        (try wp_auto)
        wp_apply hU64 as %f2 -
        (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %fsl ⟨-, -⟩
        (try wp_auto)
        wp_apply hWarn w.lg $$ []
        · iframe #
        (try wp_auto)
        wp_apply Hcancel
        (try wp_auto)
        (try imodintro)
        (try wp_auto)
        iapply HΦ
        iframe Hlgr Hrrd Hl

end proof

end EtcdGrove
end Perennial
