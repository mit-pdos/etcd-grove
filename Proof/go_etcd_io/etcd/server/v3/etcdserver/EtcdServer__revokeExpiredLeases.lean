/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__revokeExpiredLeases.lean`
(revoke-open pass 2, 2026-11-06; `notes/revoke-open-plan.md`). Lean-first (no Rocq counterpart).

The thread levels (`RevokeCtx.lean`'s header): the caller lends level 1 to the round's `GoAttach`
and borrows the outer pool `B` with level 2 for its `wgMu` slot. The outer goroutine (levels 1–3
of its token) borrows `raftPool` with level 1 for `Logger()`, `B` with level 2 for its loop
(`wgMu` for its `GoAttach`es, the read loop's lock for `ensureLeadership`), and gives
`ensureLeadership` level 3; it lends level 1 to each inner `GoAttach`. An inner goroutine borrows
the inner pool `I` with level 1 (`leadTimeMu`, `E.RD`: `WithRoot` and `LeaseRevoke`). The channel
`c` (capacity `maxPendingRevokes`) only bounds the pending revocations: a bag of `()` with `True`.
The error `LeaseRevoke` returns is only passed to `zap.Error` (no `fmt.Errorf` here).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__revokeExpiredLeases
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__GoAttach
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__ensureLeadership
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__LeaseRevoke
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__WithRoot
public import Spec.go_uber_org.zap.Uint64
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.fmt.SprintfID
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StopChan
public import Perennial.Golang.Theory.Chan.Idioms.Bag

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_uber_org

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.revokeExpiredLeases.wp_proof
    (hGA : EtcdServer.GoAttach.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hEL : EtcdServer.ensureLeadership.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hLR : EtcdServer.LeaseRevoke.spec (GF := GF) (hG := hG))
    (hWR : auth.authStore.WithRoot.spec (GF := GF) (hG := hG))
    (hU64 : zap.Uint64.spec (GF := GF) (hG := hG))
    (hStr : zap.String.spec (GF := GF) (hG := hG))
    (hErr : zap.Error.spec (GF := GF) (hG := hG))
    (hW : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hSpf : fmt.SprintfID.spec (GF := GF) (hG := hG)) :
    EtcdServer.revokeExpiredLeases.spec (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ v γr γg γcx rv SP ls
  wp_start as ⟨#Hf, #Hrf, #Hexp, #Hrvk, %Hpre, Htok⟩
  obtain ⟨hlm, hlev⟩ := Hpre
  have hlevK : srvRevokeK ≤ threadBound GF := hlev
  -- auth off, from the slice's grant guard
  ihave %Hg := srvGrantGuard_expired E.lg E.authMode.isOn ls $$ Hexp
  have hoff : E.authOn = false := Hg.2
  have hRL : srvRevokesLeases E ρ := ⟨hlm, hoff⟩
  -- the bundle's laws
  ihave %Hbnd30 := srvRevokeCtx_bound s E ρ γr γg $$ Hrvk
  ihave ⟨#Hreq, #Hrd⟩ := srvRevokeCtx_views s E ρ γr γg hoff $$ Hrvk
  -- `LeaseRevoke.spec`'s `srvAuthAt s E` (framed by its call's `iframe #`)
  ihave #Hauth := srvAuthAt_of_views s E ρ γr $$ [$Hreq $Hrd]
  ihave #HrP := srvRevokeCtx_raftPool s E ρ γr γg $$ Hrvk
  ihave #Hcred := srvRevokeCtx_cred s E ρ γr γg $$ Hrvk
  ihave ⟨%ctx, %cd, #Hctxf, #Hctx, #Hspc, #Hcst⟩ := srvRevokeCtx_ctx s E ρ γr γg $$ Hrvk
  ihave ⟨%stl, #Hauf, #HEn⟩ := srvRevokeCtx_withRoot s E ρ γr γg hoff $$ Hrvk
  iunfold srvFieldsAt at Hf
  icases Hf with ⟨#Hlgf, #Hlgnn, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hmid, -, -, -, -, -, -⟩
  iunfold srvRunFieldsAt at Hrf
  icases Hrf with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hgok⟩
  ihave ⟨%sch, #Hsch, #Hstop⟩ := srvGoAttachOk_stopping s γg $$ Hgok
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Hauthpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth $$ []
  · iPkgInit
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, ⟨-, -, -, ⟨%cnt, #Hcnt, #Hcnts⟩⟩⟩
  -- the caller's levels: 0, 1 (lent to `GoAttach`), 2 (`B`), the rest
  icases (threadTok_level0 (GF := GF)).1 $$ Htok with ⟨H0, Ht1⟩
  icases (threadTokFrom_succ (GF := GF) 1 (by word)).1 $$ Ht1 with ⟨H1, Ht2⟩
  icases (threadTokFrom_succ (GF := GF) 2 (by word)).1 $$ Ht2 with ⟨H2, Ht3⟩
  wp_auto_lc 1
  imod srvRevokeCtx_outerBorrow s E ρ γr γg ⊤ (fun _ _ => CoPset.mem_full)
    $$ [Hlc1 Hrvk H2] with ⟨⟨Hwr, Hrdr⟩, HloanB⟩
  · iframe Hlc1 H2; iexact Hrvk
  ipersist s
  ipersist leases
  iapply wp_fupd
  wp_apply hGA s γg _ iprop(True) $$ [Hwr H1] as ⟨Hwr, H1⟩
  · iframe Hwr H1
    isplitr
    · itrivial
    -- the outer goroutine
    iintro !> %Φ' ⟨-, Hrun, Hfr⟩ HΦ'
    iapply wp_fupd
    icases (threadTokFrom_succ (GF := GF) 1 (by word)).1 $$ Hfr with ⟨G1, Gt2⟩
    icases (threadTokFrom_succ (GF := GF) 2 (by word)).1 $$ Gt2 with ⟨G2, Gt3⟩
    icases (threadTokFrom_succ (GF := GF) 3 (by word)).1 $$ Gt3 with ⟨G3, Gt4⟩
    wp_auto_lc 2
    imod srvRevokeCtx_outerBorrow s E ρ γr γg ⊤ (fun _ _ => CoPset.mem_full)
      $$ [Hlc1 Hrvk G2] with ⟨⟨Gwr, Grdr⟩, GloanB⟩
    · iframe Hlc1 G2; iexact Hrvk
    imod raftPool_borrowL (srvLgReader s) ⊤ (fun _ _ => CoPset.mem_full) $$ [Hlc2 HrP G1]
      with ⟨Glr, GloanR⟩
    · iframe Hlc2 G1; iexact HrP
    wp_apply hLg s v.lg $$ [Glr] as ⟨#Hl, Glr⟩
    · iframe #; iframe Glr
    (try wp_auto)
    wp_apply hEL s E ρ γr 3 $$ [Glr Grdr G3] as %b ⟨Glr, Grdr, G3⟩
    · rw [hoff, isServerReqM_false, isServerReadM_false]
      iframe #; iframe Glr Grdr G3
      ipureintro; omega
    imod raftLoanL_giveBack (srvLgReader s) ⊤ (fun _ _ => CoPset.mem_full) $$ [GloanR Glr]
      with G1
    · iframe
    ipersist lg
    -- the goroutine's exit: `B` given back, its levels recombined
    ihave Hexit : iprop(srvWgReaderAt s γg ∗ srvReadReader s γr ∗ srvRevokeOuterLoan s γr γg ∗
        levelTok 1 ∗ levelTok 3 ∗ threadTokFrom 4 ∗ goRunning γg -∗ |={⊤}=> Φ' #()) $$ [HΦ']
    · iintro ⟨Gwr, Grdr, GloanB, G1, G3, Gt4, Hrun⟩
      imod srvRevokeOuterLoan_giveBack s γr γg ⊤ (fun _ _ => CoPset.mem_full)
        $$ [GloanB Gwr Grdr] with G2
      · iframe GloanB Gwr Grdr
      imodintro
      iapply HΦ'
      iframe Hrun
      iapply (threadTokFrom_succ (GF := GF) 1 (by word)).2
      iframe G1
      iapply (threadTokFrom_succ (GF := GF) 2 (by word)).2
      iframe G2
      iapply (threadTokFrom_succ (GF := GF) 3 (by word)).2
      iframe
    cases b
    · -- not the leader: a warning, and the round ends
      (try wp_auto)
      wp_apply hMID s v.memberID $$ []
      · iexact Hmid
      wp_apply hU64 $$ [] as %fld -
      wp_apply wp_slice_literal (V := zap.zapcore.Field) [fld]
      isplitr
      · ipureintro; rfl
      iintro %fl ⟨-, -⟩
      (try wp_auto)
      wp_apply hW v.lg _ _ $$ []
      · iexact Hl
      (try wp_auto)
      iapply Hexit
      iframe
    -- the leader: one `GoAttach` per lease, at most `maxPendingRevokes` pending
    (try wp_auto)
    wp_apply (chan.wp_make2 (V := Unit) (W64 16)) as %ch %γc ⟨#Hch, %Hcap, Hoc⟩
    · ipureintro; decide
    imod start_bag (fun _ : Unit => iprop(True)) _ ch γc (by decide) $$ Hch Hoc with #Hbag
    (try wp_auto)
    ipersist c
    icases lease.expiredLeases_read _ ls $$ Hexp with ⟨%ps, #Hls, #Hps⟩
    ihave %Hlsl := ownSlice_len _ _ _ $$ Hls
    (try wp_auto)
    ihave IH : iprop(∃ (j : w64) (cl : Loc),
        "i" ∷ i_ptr ↦ j ∗ "curLease" ∷ curLease_ptr ↦ cl ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j⌝) $$ [i curLease]
    · iexists W64 0, _
      iframe i curLease
      ipureintro; decide
    wp_for IH
    wp_if_destruct
    · -- an iteration: wait for room in `c` (or the stop), then the lease's `GoAttach`
      have hjl : (sint.Z j).toNat < ps.length := by
        unfold sint.nat at Hlsl; word
      have Hbnd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ls.len := ⟨Hj, Hif⟩
      obtain ⟨p, Hp⟩ : ∃ p, ps[(sint.Z j).toNat]? = some p :=
        ⟨_, List.getElem?_eq_getElem hjl⟩
      ihave ⟨%Hpnn, %id, #Hid⟩ := BigSepL.bigSepL_lookup Hp $$ Hps
      simp only [Hbnd, _root_.and_self, ↓reduceIte]
      wp_apply (lc := 2) wp_load_slice_index ls (sint.Z j) _ _ p Hj $$ [] as -
      · iframe #; ipureintro; exact Hp
      wp_apply_core chan.wp_select_blocking
      iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc, ()
        isplitr
        · ipureintro; exact ⟨rfl, rfl⟩
        isplitr
        · iapply is_bag_is_chan $$ Hbag
        iapply bag_send_au γc ch (fun _ : Unit => iprop(True)) () _ $$ [$Hlc1 $Hlc2] Hbag []
        · itrivial
        inext
        (try wp_auto)
        -- `f(int64(curLease.ID))`: the inner goroutine
        ipersist lid
        wp_apply hGA s γg _ iprop(True) $$ [Gwr G1] as ⟨Gwr, G1⟩
        · iframe Gwr G1
          isplitr
          · itrivial
          iintro !> %Ψ ⟨-, Irun, Ifr⟩ HΨ
          iapply wp_fupd
          icases (threadTokFrom_succ (GF := GF) 1 (by word)).1 $$ Ifr with ⟨I1, It2⟩
          wp_auto_lc 1
          imod srvRevokeCtx_innerBorrow s E ρ γr γg ⊤ (fun _ _ => CoPset.mem_full)
            $$ [Hlc1 Hrvk I1] with ⟨⟨Ilt, IRD⟩, IloanI⟩
          · iframe Hlc1 I1; iexact Hrvk
          -- (`wp_apply hWR stl E.RD …` aborts without an error: the call by hand)
          wp_bind (App (Val _) (Val #(GoInterface.ok ctx)))
          iapply hWR stl E.RD (GoInterface.ok ctx) $$ [IRD] [Irun HΨ It2 Ilt IloanI]
          · iframe #; iframe IRD
          inext
          iintro IRD
          (try wp_auto)
          ihave ⟨Hr, %Hrnn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$a1»
          iStructNamed Hr
          ipersist ID
          wp_apply hLR s E ρ ctx cd _ id hRL $$ [Ilt IRD] as %resp %err ⟨Ilt, IRD, Hres⟩
          · iframe #; iframe Ilt IRD
            iunfold leaseRevokeReqRO
            iframe ID
            ipureintro; exact Hrnn
          (try wp_auto)
          ihave Hdone : iprop(|={⊤}=> Ψ #()) $$ [HΨ Irun It2 IloanI Ilt IRD]
          · imod srvRevokeInnerLoan_giveBack s E ⊤ (fun _ _ => CoPset.mem_full)
              $$ [IloanI Ilt IRD] with I1
            · iframe IloanI Ilt IRD
            imodintro
            iapply HΨ
            iframe Irun
            iapply (threadTokFrom_succ (GF := GF) 1 (by word)).2
            iframe
          icases Hres with (⟨%Herr, -⟩ | ⟨%Herr, -⟩)
          · -- revoked: the counter
            obtain ⟨rfl, -⟩ := Herr
            (try wp_auto)
            ihave #Hcnts' := Hcnts
            iunfold go_etcd_io.etcd.server.v3.storage.mvcc.counterSpec at Hcnts'
            icases Hcnts' with ⟨#HInc, -⟩
            wp_apply HInc $$ []
            (try wp_auto)
            wp_apply (wp_bag_receive γc ch (fun _ : Unit => iprop(True))) $$ [] as %u -
            · iexact Hbag
            (try wp_auto)
            iexact Hdone
          · -- not revoked: a warning with the lease's id and the error
            obtain ⟨-, Hne⟩ := Herr
            cases err with
            | nil => exact absurd rfl Hne
            | ok ei =>
            (try wp_auto)
            wp_apply wp_slice_literal (V := GoInterface) [interface.mkOk go.int64 #id]
            isplitr
            · ipureintro; rfl
            iintro %al ⟨Hal, -⟩
            (try wp_auto)
            wp_apply hSpf _ _ _ (DFrac.own 1) $$ [$Hal] as %msg ⟨-, -⟩
            · iframe #
              ipureintro
              intro x hx
              simp only [List.mem_cons, List.mem_nil_iff, _root_.or_false] at hx
              subst hx
              left
              exact _root_.Perennial.fmt.ArgsWf.cons_int _ _ []
                (_root_.Perennial.fmt.IntArgValue.int64 id) _root_.Perennial.fmt.ArgsWf.nil _
                (List.mem_singleton_self _)
            wp_apply hStr $$ [] as %f1 -
            wp_apply hErr $$ [] as %f2 -
            wp_apply wp_slice_literal (V := zap.zapcore.Field) [f1, f2]
            isplitr
            · ipureintro; rfl
            iintro %fl ⟨-, -⟩
            (try wp_auto)
            wp_apply hW v.lg _ _ $$ []
            · iexact Hl
            (try wp_auto)
            wp_apply (wp_bag_receive γc ch (fun _ : Unit => iprop(True))) $$ [] as %u -
            · iexact Hbag
            (try wp_auto)
            iexact Hdone
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, p
        iframe
        ipureintro; word
      iapply BigAndL.bigAndL_cons.2
      isplit
      · -- the server stops: the round ends
        simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sch, γg.ch
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply ownStopChan_is_chan $$ Hstop
        iapply stop_chan_receive _ _ _ _ _ $$ Hstop
        iintro ⟨-, -⟩
        (try wp_auto)
        wp_for_post
        iapply Hexit
        iframe
      iapply BigAndL.bigAndL_nil.2
      itrivial
    · -- the loop ends
      iapply Hexit
      iframe
  -- the caller: `B` given back, its token recombined
  imod srvRevokeOuterLoan_giveBack s γr γg ⊤ (fun _ _ => CoPset.mem_full)
    $$ [HloanB Hwr Hrdr] with H2
  · iframe HloanB Hwr Hrdr
  imodintro
  iapply HΦ
  iapply (threadTok_level0 (GF := GF)).2
  iframe H0
  iapply (threadTokFrom_succ (GF := GF) 1 (by word)).2
  iframe H1
  iapply (threadTokFrom_succ (GF := GF) 2 (by word)).2
  iframe

end proof

end EtcdGrove
end Perennial
