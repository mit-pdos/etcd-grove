/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/newReplica.lean`. Lean-first
(no Rocq counterpart).

kvreconf's `newReplica.lean`, with kvdurable's additions: the `dmu` names allocated first (the
pending batch's claim at `(none, S)` and the image's hard state at `hs`, both halved between `dmu`
and `run`; the image's frozen bound at `len l` and its snapshot index), which the snapshot requests'
bag cites; the stored hard state read from the image (`run`'s argument); the configuration's clone
(`nil` cloned to `nil`); `dmu`'s invariant idle at the image `M` (the file's commit at most the
image's: the file is the image); `run`'s start (`runStart`) from the premises; the running token
halved between `run` and the snapshotter.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.newReplica
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__run
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__ticker
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__snapshotter
public import Spec.google_golang_org.protobuf.proto.CloneConfState
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Halves
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.DefsLaws

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- `proto.Clone` of a read-only conf state that may be `nil`. -/
theorem wp_cloneOpt (wp_Clone : proto.CloneConfState.spec (GF := GF) (hG := hG))
    (p : Loc) (c : ConfStateM) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ csOpt p DFrac.discard c }}
    (App (Val (@! google_golang_org.protobuf.proto.Clone))
      (Val #(interface.mkOk (go.GoType.PointerType raftpb.ConfState.ty) #p)))
  {{ (p' : Loc), RET #(interface.mkOk (go.GoType.PointerType raftpb.ConfState.ty) #p');
      csOpt p' DFrac.discard c }} := by
  unfold csOpt
  iintro %Φ ⟨#Hpkg, Hc⟩ HΦ
  icases Hc with (⟨%Hnull, %Hc⟩ | #Hc)
  · subst Hnull
    wp_apply wp_Clone.2 $$ [$Hpkg]
    iapply HΦ
    ileft; ipureintro; exact ⟨rfl, Hc⟩
  · iapply wp_fupd
    wp_apply wp_Clone.1 p DFrac.discard c $$ [$Hpkg $Hc] as %p' ⟨-, Hp'⟩
    imod csPts_persist p' (DFrac.own 1) c false $$ Hp' with #Hp'
    imodintro
    iapply HΦ
    iright; iexact Hp'

theorem newReplica.wp_proof (wp_run : Replica.run.spec (GF := GF) (hG := hG))
    (wp_ticker : Replica.ticker.spec (GF := GF) (hG := hG))
    (wp_snapshotter : Replica.snapshotter.spec (GF := GF) (hG := hG))
    (wp_Clone : proto.CloneConfState.spec (GF := GF) (hG := hG)) :
    newReplica.spec (GF := GF) (hG := hG) := by
  intro γ vs dir id n st sts sq ms γs K mK mA csp Kv A ap l m cfg ip hs S o M rafted tick f
    Htick HMhs Hok Hholds Hap61 Hrafted Ho Hlap Hpl Hlc Hid1 Hid9 Hsz Hapsi
  wp_start as ⟨#Hcci, #Hcl, #Hstats, #Hseqs, #HfInv, #HisNode, Hdrv, Hcfg, Hrun, #Hrec, #HmsInv,
    Hmeta, #Himg, Himage, #Hcert, Hwr, #Hcomp, #Hfz, #Hfro, #HsnLbM, HK, HA, #Hcs0, %Hcsm, #Hap,
    #Hca, %Hval, %HAok, #Hsend⟩
  ihave #Hproto : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  -- the `dmu` names
  imod ghostVar_alloc (GF := GF) ((none : Option GName), S) with ⟨%γph, Hph⟩
  icases (ghostVar_split_half (GF := GF) γph 1 ((none : Option GName), S)).1 $$ Hph with ⟨Hph1, Hph2⟩
  imod ghostVar_alloc (GF := GF) hs with ⟨%γcm, Hcm⟩
  icases (ghostVar_split_half (GF := GF) γcm 1 hs).1 $$ Hcm with ⟨Hcm1, Hcm2⟩
  imod mono_nat_own_alloc (GF := GF) l.length with ⟨%γic, Hic, #HicLb⟩
  imod mono_nat_own_alloc (GF := GF) (uint.nat M.snap.Metadata'.Index') with ⟨%γis, His, #HisLb⟩
  -- the image's hard state, `run`'s argument
  iunfold ownImage at Himage
  icases Himage with ⟨%hsp, %sp, %es, Hhs, #HhsO, Hsnap, #HsnapO, Hprev, HprevTerm, Hents, #HentsO,
    %Hwf⟩
  try wp_auto
  -- the channels
  wp_apply chan.wp_make1 (V := Unit) as %sc %γsc ⟨#Hsc, %_, Hsoc⟩
  imod alloc_broadcast_chan (E := ⊤) (iprop(True) : IProp GF) γsc sc $$ Hsc Hsoc with Hpend
  icases ownBroadcastChan_open _ _ _ _ $$ Hpend with ⟨%γbi, #Hbi, Hpend⟩
  ihave #Hunk := ownBroadcastChan_close sc γsc iprop(True) Broadcast.Unknown γbi $$ [$Hbi]
  ihave Hpend := ownBroadcastChan_close sc γsc iprop(True) Broadcast.Pending γbi $$ [$Hbi $Hpend]
  wp_apply chan.wp_make2 (V := KSnapReq) (W64 1) as %snc %γsn ⟨#Hsnc, %_, Hsnoc⟩
  · ipureintro; decide
  ihave Hsnoc : ownChan γsn KSnapReq (.Buffered []) $$ Hsnoc
  imod start_bag (snapReqOk γ K γs ⟨γph, γic, γis, γcm⟩) (.Buffered []) snc γsn trivial
    $$ Hsnc Hsnoc with #HsnB
  wp_apply chan.wp_make2 (V := Unit) (W64 1) as %rdc %γrc ⟨#Hrdc, %_, Hroc⟩
  · ipureintro; decide
  ihave Hroc : ownChan γrc Unit (.Buffered []) $$ Hroc
  imod start_handoff rdc (fun _ => iprop(nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half ∗
      ∃ v : Option GName × RaftState, ghostVar γph (1 : Qp).half v)) iprop(True) iprop(False) γrc
    $$ Hrdc Hroc with ⟨%γrd, -, #HrdH, HrdP, HrdC⟩
  wp_apply chan.wp_make2 (V := Unit) (W64 1) as %tdc %γtc ⟨#Htdc, %_, Htoc⟩
  · ipureintro; decide
  ihave Htoc : ownChan γtc Unit (.Buffered []) $$ Htoc
  imod start_handoff tdc (fun _ => iprop(True)) iprop(True) iprop(False) γtc
    $$ Htdc Htoc with ⟨%γtd, -, #HtdH, HtdP, HtdC⟩
  wp_apply chan.wp_make2 (V := Unit) (W64 1) as %sdc %γdc ⟨#Hsdc, %_, Hsdoc⟩
  · ipureintro; decide
  ihave Hsdoc : ownChan γdc Unit (.Buffered []) $$ Hsdoc
  imod start_handoff sdc (fun _ => nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half) iprop(True)
    iprop(False) γdc $$ Hsdc Hsdoc with ⟨%γsd, -, #HsdH, HsdP, HsdC⟩
  try wp_auto
  wp_apply wp_cloneOpt wp_Clone csp cfg $$ [$Hproto $Hcs0] as %csp' #HcsO
  try wp_auto
  wp_apply wp_map_make1 (K := List w8) (V := Loc) as %mW HW
  wp_apply wp_map_make1 (K := w64) (V := Loc) as %mRd HRd
  iStructNamed «$r0»
  ipersist id
  ipersist file
  ipersist node
  ipersist storage
  ipersist stats
  ipersist tick
  ipersist stopc
  ipersist snapc
  ipersist runDone
  ipersist tickDone
  ipersist snapDone
  ipersist seqs
  icases (typedPointsto_half_split _ _ 1).1 $$ applied with ⟨applied1, applied2⟩
  icases (typedPointsto_half_split _ _ 1).1 $$ cs with ⟨cs1, cs2⟩
  icases (typedPointsto_half_split _ _ 1).1 $$ index with ⟨index1, index2⟩
  icases (typedPointsto_half_split _ _ 1).1 $$ crashed with ⟨crashed1, crashed2⟩
  icases kvreconf.ownMap_halves_split mA A $$ HA with ⟨HA1, HA2⟩
  have hrun := (nodeRunning_fractional (GF := GF) n γ.r.cluster kdRaftN).fractional
    (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at hrun
  icases hrun.1 $$ Hrun with ⟨Hrun1, Hrun2⟩
  -- the replica's `mu`
  imod sync.init_Mutex (lockInv γ id «$r0_ptr») ⊤ («$r0_ptr».[KReplica, go!"mu"])
    $$ mu [waiters HW reads HRd applied2 HA2 cs2 index2] with #Hmu
  · inext
    unfold lockInv
    iexists mW, ∅, mRd, ∅
    simp only [named]
    iframe waiters HW reads HRd
    isplitl [applied2 HA2 cs2 index2]
    · unfold repShared
      iexists mA, A, csp', cfg, _, ap
      simp only [named]
      iframe applied2 HA2 cs2 index2 HcsO Hap
      ipureintro; exact HAok
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    iapply BigSepM.bigSepM_empty.2; itrivial
  -- the replica's `dmu`, idle at the image
  imod sync.init_Mutex (kdDmuInv γ id «$r0_ptr» n st ms γs ⟨γph, γic, γis, γcm⟩) ⊤
    («$r0_ptr».[KReplica, go!"dmu"])
    $$ dmu [crashed1 Hhs Hsnap Hprev HprevTerm Hents Hmeta Hic His Hcm1 Hwr Hph1] with #Hdmu
  · inext
    unfold kdDmuInv
    iexists false, ip, M, l.length
    simp only [named]
    iframe crashed1 Himg Hic His
    isplitl [Hhs Hsnap Hprev HprevTerm Hents]
    · unfold ownImage
      iexists hsp, sp, es
      simp only [named]
      iframe
      iframe HhsO HsnapO HentsO
      ipureintro; exact Hwf
    isplitl [Hmeta]
    · rw [HMhs]; iexact Hmeta
    isplitr
    · iexact Hfz
    isplitr
    · ipureintro; left; exact Hlc
    isplitl [Hcm1]
    · rw [HMhs]; iexact Hcm1
    iexists S, o, KdPhase.idle
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hwr Hcert
    isplitr
    · ipureintro; exact Hok
    isplitr
    · ipureintro; intro f' hf; rw [Ho f' hf]; exact Nat.le_refl _
    simp only [kdPhaseInv]
    iframe Hph1
    ipureintro; exact Hholds
  ihave #HsnLb0 := memSnapLb_mono γs _ 0 (Nat.zero_le _) $$ HsnLbM
  ihave #Hrep : isReplica γ vs dir id «$r0_ptr» n st sts sq ms γs ⟨γph, γic, γis, γcm⟩ $$ []
  · unfold isReplica
    simp only [named]
    iframe #
    ipureintro; exact ⟨Hid1, Hid9⟩
  ihave #HR : isReplicaR γ vs dir id «$r0_ptr» n st sts sq
      ⟨ms, γs, sc, γsc, rdc, γrd, tdc, γtd, snc, γsn, sdc, γsd, K, ⟨γph, γic, γis, γcm⟩⟩ $$ []
  · unfold isReplicaR
    simp only [named]
    iframe #
    ipureintro; exact Htick
  have Hterm : S.term = hs.Term' ∧ S.vote = hs.Vote' := by
    obtain ⟨-, -, -, Ht, Hv, -⟩ := Hholds
    rw [← HMhs]; exact ⟨Ht.symm, Hv.symm⟩
  ihave #HhsO' : hsOpt hsp hs $$ []
  · rw [← HMhs]; iexact HhsO
  try wp_auto
  wp_apply wp_fork $$ [Hdrv Hcfg Hrun1 kv HK applied1 HA1 cs1 index1 HrdP Hph2 Hcm2]
  · wp_apply wp_run γ vs dir id «$r0_ptr» n st sts sq
      ⟨ms, γs, sc, γsc, rdc, γrd, tdc, γtd, snc, γsn, sdc, γsd, K, ⟨γph, γic, γis, γcm⟩⟩ f l ap hs
      hsp S m (W64 ap.length) rafted Hrafted (Or.inr rfl)
      $$ [$HR $Hsend $HhsO' Hdrv Hcfg Hrun1 kv HK applied1 HA1 cs1 index1 HrdP Hph2 Hcm2]
    · unfold runStart
      iexists csp', mA, A
      iframe Hdrv Hcfg Hrun1 HrdP Hph2 Hcm2 HicLb
      isplitl [kv HK applied1 HA1 cs1 index1]
      · unfold repOwn
        iexists mK, Kv, cfg
        simp only [named]
        iframe kv HK applied1 HA1 cs1 index1 Hap HcsO Hca
        ipureintro
        exact ⟨Hap61, Hval, HAok, Hcsm, Hsz⟩
      isplitr
      · ipureintro; exact Hterm
      isplitr
      · ipureintro; exact Hlap
      iexists uint.nat M.prev
      iframe Hcomp Hfro
      ipureintro; exact Hpl
    itrivial
  try wp_auto
  wp_apply wp_fork $$ [HtdP]
  · wp_apply wp_ticker γ vs dir id «$r0_ptr» n st sts sq
      ⟨ms, γs, sc, γsc, rdc, γrd, tdc, γtd, snc, γsn, sdc, γsd, K, ⟨γph, γic, γis, γcm⟩⟩
      $$ [$HR $HtdP]
    itrivial
  try wp_auto
  wp_apply wp_fork $$ [HsdP Hrun2]
  · wp_apply wp_snapshotter γ vs dir id «$r0_ptr» n st sts sq
      ⟨ms, γs, sc, γsc, rdc, γrd, tdc, γtd, snc, γsn, sdc, γsd, K, ⟨γph, γic, γis, γcm⟩⟩
      (W64 ap.length) $$ [$HR $HsdP $Hrun2]
    · have Hk : uint.nat (W64 ap.length) = uint.nat M.snap.Metadata'.Index' := by
        rw [← Hapsi]; word
      rw [Hk]
      iframe HsnLbM HisLb
    itrivial
  try wp_auto
  iapply HΦ
  isplitr
  · iexists n, st, sts, sq,
      ⟨ms, γs, sc, γsc, rdc, γrd, tdc, γtd, snc, γsn, sdc, γsd, K, ⟨γph, γic, γis, γcm⟩⟩
    iexact HR
  unfold repStop repStopper
  iframe crashed2
  iexists n, st, sts, sq,
    ⟨ms, γs, sc, γsc, rdc, γrd, tdc, γtd, snc, γsn, sdc, γsd, K, ⟨γph, γic, γis, γcm⟩⟩
  iframe HR Hpend HrdC HtdC HsdC

end proof

end kvdurable
end EtcdGrove
end Perennial
