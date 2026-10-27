/-
**`Transport.Stop`, over the transport's lock** (rafthttp stage 6c; its axiom's statement is
restated over this in 6d). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportInv
public import Proof.net.http.Axioms
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer__stop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.remote__stop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

set_option hygiene false in
/-- `if tr, ok := rt.(*http.Transport); ok { tr.CloseIdleConnections() }` of a round tripper of
`roundTripperOk` (`Hrtk`, cleared): two goals, as its dynamic type is `*http.Transport` or not. -/
local macro "close_rt" : tactic => `(tactic| (
  ihave Hrt' := Hrtk
  iunfold http.roundTripperOk at Hrt'
  icases Hrt' with ⟨%rti, %Hrti, -⟩
  subst Hrti
  by_cases hty : rti.ty = go.GoType.PointerType _root_.Perennial.net.http.Transport.ty
  all_goals first
    | (have hty' : rti.ty = go.GoType.PointerType _root_.Perennial.net.http.Transport.ty := hty
       ihave ⟨%tr, %Htv, #HCI⟩ := http.CloseIdleConnections_ok (raftHttpNet Rh) rti hty' $$ Hrtk
       simp only [hty', ↓reduceIte, decide_true]
       rw [Htv]
       (try wp_auto)
       wp_apply HCI
       (try wp_auto)
       iclear Hrtk HCI)
    | (simp only [hty, ↓reduceIte, decide_false]
       (try wp_auto)
       iclear Hrtk)))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
/-- **`t.Stop()`** with the write lock's guard and the right to set the stopped flag (`HSF`: the
owner's half of `γr`, `Stop_live`, or the frozen record's invariant, `Stop_full`; D43 M5c):
it returns, every peer and remote stopped (their stop rights taken from the stop invariant), the
probers emptied, the round trippers' idle connections closed, the maps `nil` and the transport
marked stopped (`γr`'s flag). A second `Stop` finds nothing to stop. -/
theorem rafthttp.Transport.Stop_core
    (hPeerStop : rafthttp.peer.stop.spec (GF := GF) (hG := hG))
    (hRemoteStop : rafthttp.remote.stop.spec (GF := GF) (hG := hG))
    (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF) (γs γr : GName)
    (L : List w64) (γk γo : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trFixed Rh t lid γd R ∗ trProbers t ∗ trStopInv Rh R γs L γk γo ∗
        sync.isRWMutexGuard (t.[rafthttp.Transport, go!"mu"]) (trLockP Rh t lid γd R γs γr) ∗
        (∀ (rs' : trIds) (sb : Bool), ghostVar γr (1 : Qp).half (rs', sb) ={⊤}=∗
          ghostVar γr (1 : Qp).half (rs', true)) }}
      (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"Stop")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Htr, #Hprb, #Hst, #Hgd, HSF⟩
  ihave #Htr' := Htr
  iunfold trFixed at Htr'
  icases Htr' with ⟨%lg, %ls, %ss0, %turls, %tuvs, %cid, %r, %ec, %srt, %prt, %drf, %ppr, %spr,
    #Hlg, %Hlgnn, #Hlid, #HtURLs, #Htuvs, #Hcid, #Hr, #Hraft, #Hec, #Hsrt, #Hsrtok, #Hprt, #Hprtok,
    #Hdrf, #Hls, %Hlsnn, #Hss, %Hssnn, #Hppr, #Hspr, #Hreg, #Hpreg, #HPfx, %HmemU⟩
  obtain ⟨Hmem, Hturls⟩ := HmemU
  iunfold trProbers at Hprb
  icases Hprb with ⟨%pp, %sp, #Hppf, #Hppok, #Hspf, #Hspok⟩
  iunfold probing.proberOk at Hppok Hspok
  icases Hppok with ⟨%pti, %Hpti, #Hprm, -⟩
  icases Hspok with ⟨%sti, %Hsti, #Hsrm, -⟩
  subst Hpti Hsti
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [] as ⟨Hwl, HP⟩
  · iframe #
  iunfold trLockP at HP
  icases HP with ⟨%pm, %rm, %PM, %RM, %T, %rs', %sb, Hp, Hr, Hpm, Hrm, Hg, Hgr, %Hrs, #Hpo, #Hro,
    Hts⟩
  wp_auto_lc 2
  imod trStop_take Rh R γs L γk γo pm rm PM RM T $$ Hst Hg Hlc1 Hlc2 with ⟨Hg, HPs, HRs⟩
  imod HSF $$ %rs' %sb Hgr with Hgr
  -- the remotes' `stop`s
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_range_mapOrNil _ _ rm _ RM _ (fun id g => remoteStop Rh id R g)
    iprop(∃ x : Loc, r_ptr ↦ x) $$ Hrm HRs [r]
  · iexists _; iexact r
  isplitr
  · imodintro
    iintro %k %g %Hk ⟨%x, r⟩ Hs
    iunfold remotesOk at Hro
    ihave #Hgok := BigSepM.bigSepM_lookup (Φ := fun id g => remoteOk Rh lid id R g) Hk $$ Hro
    (try wp_auto)
    wp_apply hRemoteStop Rh lid k R g $$ [Hs] as -
    · iframe; iframe #
    (try wp_auto)
    isplitr
    · ipureintro; rfl
    iexists _; iexact r
  iintro Hrm -
  (try wp_auto)
  -- the peers' `stop`s
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_range_mapOrNil _ _ pm _ PM _ (fun id pi => iprop(∃ p : Loc,
      ⌜pi = interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p⌝ ∗ peerStop Rh id R p))
    iprop(∃ x : GoInterface, p_ptr ↦ x) $$ Hpm HPs [p]
  · iexists _; iexact p
  isplitr
  · imodintro
    iintro %k %pi %Hk ⟨%x, p⟩ ⟨%p, %Hp, Hs⟩
    iunfold peersOk at Hpo
    ihave Hpi := BigSepM.bigSepM_lookup (Φ := fun id pi => iprop(∃ p : Loc,
      ⌜pi = interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p⌝ ∗
      peerOk Rh lid id γd R p)) Hk $$ Hpo
    icases Hpi with ⟨%p', %Hp', #Hpok⟩
    subst Hp
    have hpp : p = p' := by
      simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at Hp'
      exact GoGlobalContext.intoVal_inj_loc Hp'
    subst hpp
    (try wp_auto)
    wp_apply hPeerStop Rh lid k γd R p $$ [Hs] as -
    · iframe; iframe #
    (try wp_auto)
    isplitr
    · ipureintro; rfl
    iexists _; iexact p
  iintro Hpm -
  (try wp_auto)
  -- the probers, the round trippers
  wp_apply Hprm
  (try wp_auto)
  wp_apply Hsrm
  (try wp_auto)
  ihave #Hrtk := Hsrtok
  close_rt
  all_goals (ihave #Hrtk := Hprtok; close_rt)
  all_goals (
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [Hwl Hp Hr Hg Hgr Hts]
    · iframe #; iframe Hwl
      inext
      iunfold trLockP
      iexists null, null, ∅, ∅, T, rs', true
      iframe
      isplitr
      · iunfold mapOrNil; ileft; ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iunfold mapOrNil; ileft; ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · ipureintro
        exact ⟨fun h => (by cases h), fun h => absurd rfl h, fun h => absurd rfl h⟩
      isplitr
      · imodintro; iunfold peersOk; iapply BigSepM.bigSepM_empty.2; itrivial
      imodintro; iunfold remotesOk; iapply BigSepM.bigSepM_empty.2; itrivial
    (try wp_auto)
    iapply HΦ; itrivial)
