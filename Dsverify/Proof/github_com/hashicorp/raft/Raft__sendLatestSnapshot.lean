/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__sendLatestSnapshot.lean (241f27e).
-/
/-
The proof of `Raft__sendLatestSnapshot` (replication subsystem).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__sendLatestSnapshot
public import Perennial.Spec.fmt.Errorf
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__getRPCHeader
public import Dsverify.Spec.github_com.hashicorp.raft.EncodeConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__handleStaleTerm
public import Dsverify.Spec.github_com.hashicorp.raft.followerReplication__setLastContact
public import Dsverify.Spec.github_com.hashicorp.raft.commitment__match
public import Dsverify.Proof.github_com.hashicorp.raft.ReplSnap

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft github_com.hashicorp.raft.gprot proto

theorem github_com.hashicorp.raft.Raft.sendLatestSnapshot.wp_proof
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (wp_StoreUint64 : sync.atomic.StoreUint64.spec (GF := GF) (hG := hG))
    (wp_getRPCHeader : github_com.hashicorp.raft.Raft.getRPCHeader.spec (GF := GF) (hG := hG))
    (wp_EncodeConfiguration : github_com.hashicorp.raft.EncodeConfiguration.spec (GF := GF) (hG := hG))
    (wp_getCurrentTerm : github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_handleStaleTerm : github_com.hashicorp.raft.Raft.handleStaleTerm.spec (GF := GF) (hG := hG))
    (wp_setLastContact : github_com.hashicorp.raft.followerReplication.setLastContact.spec (GF := GF) (hG := hG))
    (wp_match : github_com.hashicorp.raft.commitment.match.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.sendLatestSnapshot.spec (GF := GF) (hG := hG) :=
  fun r γ rc i T j s tid => by
  wp_start as ⟨#Hr, #Hs, #Hl, #Hlb, Hf, Htok⟩
  ihave ⟨%x, %eof, #Hsnaps, #Hss, #Heof⟩ := isRaft_snapshotStore r γ rc i $$ Hr
  ihave #Hcell := isRaft_durInv r γ rc i $$ Hr
  ihave ⟨%fsmI, -, #Hfsm, -⟩ := isRaft_fsm r γ rc i $$ Hr
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  unfold isSnapStore
  icases Hss with ⟨-, #HList, #HOpen⟩
  wp_bind (App (Val #(methods x.ty _ x.v)) _)
  iapply HList $$ Htok
  unfold snapCell
  iinv Hcell with Hi Hclose
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  icases Hi with ⟨%lat, %pend, Hown, Hlat, Hpend, Hm⟩
  iexists lat
  iframe Hown
  iintro Hown
  imod Hmask with -
  imod Hclose $$ [Hown Hlat Hpend Hm] with -
  · inext; iexists lat, pend; iframe
  imodintro
  iintro %sl %ps Hsl Hps Htok
  ihave %Hlen := ownSlice_len $$ Hsl
  wp_auto
  rcases lat with _ | ⟨m0, b0⟩
  · -- no snapshot
    icases Hps with %Hps
    subst Hps
    wp_if_destruct
    · wp_apply (wp_Errorf _ slice.nil [] (DFrac.own 1)) as %e ⟨-, %s, -, He⟩
      · isplitl
        · iapply ownSlice_nil
        · iapply (fmt.argsOk_of_argsWf (by intro ii h; simp at h))
      iapply HΦ
      iframe
    exfalso; apply Hif; simp at Hlen; word
  icases Hps with ⟨%p, %Hps, Hp⟩
  subst Hps
  wp_if_destruct
  · exfalso; simp at Hlen; word
  rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len by simp at Hlen; word)]
  wp_apply (wp_load_slice_index sl (sint.Z (W64 0)) [p] (DFrac.own 1) p (by word)) $$ [Hsl] as Hsl
  · iframe; ipureintro; simp
  -- Open the snapshot with that id: the latest's facts (`latestGood`), read off `snapCell`
  wp_bind (App (Val #(methods x.ty _ x.v)) _)
  iapply HOpen $$ Htok
  iinv Hcell with Hi Hclose
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  icases Hi with ⟨%lat, %pend, Hown, Hlat, Hpend, Hm⟩
  ihave ⟨Hlat, Hm, #Hgood⟩ := latest_good γ rc i fsmI lat pend $$ [Hlat Hm]
  · iframe #; iframe
  iexists lat
  iframe Hown
  iintro Hown
  imod Hmask with -
  imod Hclose $$ [Hown Hlat Hpend Hm] with -
  · inext; iexists lat, pend; iframe
  imodintro
  iintro %v Hv Htok
  by_cases hid : ∃ m b, lat = some (m, b) ∧ m.ID' = m0.ID'
  rotate_left
  · -- no snapshot any more, or replaced meanwhile
    ihave ⟨%err, %Hv⟩ := openPost_miss lat _ eof v (fun m b h1 h2 => hid ⟨m, b, h1, h2⟩) $$ Hv
    obtain ⟨rfl, Herr⟩ := Hv
    wp_auto
    cases err with
    | nil => exact absurd rfl Herr
    | ok e =>
    try wp_auto
    iapply HΦ
    iframe
  obtain ⟨m, b, rfl, hid⟩ := hid
  ihave ⟨%mp, %rd, %R, %Hv, Hmp, #Hrc, HR, %Hwt⟩ := openPost_hit m b _ eof v hid $$ Hv
  subst Hv
  unfold readCloserOk
  icases Hrc with ⟨#Hrd, #HClose⟩
  iunfold latestGood at Hgood
  icases Hgood with ⟨⟨%e, #HC, %He⟩, #Hsp, #Hcfg, %Hmeta, #Hdf⟩
  wp_auto
  -- the term check (fix `5894fa2`, D31): before it, the snapshot is a valid install of `T` or the
  -- term moved on
  ihave ⟨#HcurT, ⟨%psf, #Hpeer⟩, #Hvj, #Hpl, ⟨%cm, #Hcm, #Hcmt⟩, -⟩ := replShared_core r γ i T j s $$ Hs
  ihave ⟨#HInv, #Hvi⟩ := isRaft_proto r γ rc i $$ Hr
  ihave #Htc := isRaft_termCell r γ rc i $$ Hr
  imod termLb_bound r γ i T $$ [] with %hT
  · iframe #
  imod snap_valid γ i T (uint.nat m.Index') (uint.nat m.Term') e He.2 $$ [] with (#Hae | #Hstale)
  · iframe #; ipureintro; exact He.1
  rotate_left
  · wp_apply wp_getCurrentTerm.2 $$ [$Htc $Hstale] as %t ⟨#Hlbt, %Ht⟩
    wp_if_destruct
    · exfalso
      have h1 : uint.nat (W64 (T : Int)) ≤ T := by word
      omega
    wp_bind (App (Val #(methods rd.ty _ rd.v)) _)
    iapply HClose
    wp_auto
    iapply HΦ
    iframe
  wp_apply wp_getCurrentTerm.2 $$ [$Htc $Hlb] as %t ⟨#Hlbt, %Ht⟩
  wp_if_destruct
  rotate_left
  · wp_bind (App (Val #(methods rd.ty _ rd.v)) _)
    iapply HClose
    wp_auto
    iapply HΦ
    iframe
  -- build the request
  wp_apply wp_getRPCHeader $$ [$Hr] as %h #Hh
  ihave ⟨%transI, %rpcCh, #Htrans, #HrpcCh, #Htr⟩ := isRaft_transport r γ rc i $$ Hr
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  unfold raftImm
  icases Himm with ⟨-, #Hid, #Haddr, -, ⟨%nlt, #Hnlt⟩, -⟩
  wp_auto
  unfold isTransport
  icases Htr with ⟨-, -, -, #HEnc, -, -, -, -, -, -, #HIS, -⟩
  wp_bind (App (App (Val #(methods transI.ty _ transI.v)) _) _)
  iapply HEnc
  iintro %lsl Hlsl
  ipersist Hlsl
  wp_auto_lc 1
  unfold cfgVal
  icases Hcfg with ⟨%ss, ⟨#Hss, %Hssok⟩, #Hsc⟩
  wp_apply wp_EncodeConfiguration $$ [$Hss] as %cb ⟨-, Hcb⟩
  ipersist Hcb
  -- the peer, under its read lock
  unfold rwLock
  icases Hpl with ⟨%γpl, #Hplg, #Hplp⟩
  imod qpool.borrow_lc peerLockN γpl _ ⊤ (by solve_ndisj) tid $$ [$Hlc1 $Hplp $Htok] with ⟨Hown, Hloan⟩
  wp_apply (sync.RWMutex.wp_RLock _ _) $$ [$Hown] as ⟨Hrl, HP⟩
  wp_apply (sync.RWMutex.wp_RUnlock _ _) $$ [$Hrl $HP] as Hown
  imod qpool.giveBack peerLockN γpl _ ⊤ (by solve_ndisj) tid $$ [$Hplp $Hloan $Hown] with Htok
  -- the call: a valid install request of `T` with the snapshot's stream
  ihave %Hji := replShared_ne r γ rc i T j s $$ Hs
  obtain ⟨Hver, Hsize, Hblen, Hpeers⟩ := Hmeta
  wp_bind (App (App (App (App (App (Val #(methods transI.ty _ transI.v)) _) _) _) _) _)
  ispecialize HIS $$ %j %j %req_ptr %resp_ptr %_ %_ %(DFrac.own 1) %i %T %(uint.nat m.Index')
    %(uint.nat m.Term') %b %rd %tid
  iapply HIS $$ Hvj req [] resp [HR] Htok
  · unfold isReq
    rw [Hpeers]
    iframe #
    isplitr
    · ipureintro
      refine ⟨by word, rfl, rfl, Hver, Hsize, fun h => Hji h.symm, He.2⟩
    iexists []; iapply ownSlice_nil
  · unfold snapStream
    iexists R, eof
    iframe #
    iframe
    ipureintro; exact ⟨Hwt, Hblen⟩
  iintro %err req Htok Hres
  icases replFields_elim s $$ Hf with ⟨%fv, %ap, %nv, Hfl, Hap, Hn⟩
  icases Hres with (⟨%Herr, %rp, resp, Hresp⟩ | ⟨%Herr, %rp, resp⟩)
  rotate_left
  · -- the RPC failed
    cases err with
    | nil => exact absurd rfl Herr
    | ok erri =>
    wp_auto
    wp_bind (App (Val #(methods rd.ty _ rd.v)) _)
    iapply HClose
    wp_auto
    iapply HΦ
    iframe Htok
    iapply replFields_intro; iframe
  subst Herr
  rcases rp with ⟨hdr1, tm1, succ1⟩
  wp_auto
  generalize (!nlt) = bnl
  wp_join with [Hfl]
  wp_if_destruct
  · -- the follower has a newer term
    wp_apply wp_handleStaleTerm $$ [$Hr $Hs]
    wp_bind (App (Val #(methods rd.ty _ rd.v)) _)
    iapply HClose
    wp_auto
    iapply HΦ
    iframe Htok
    iapply replFields_intro; iframe
  wp_apply wp_setLastContact $$ [$Hs]
  ihave #Hnc := replShared_nextCell r γ rc i T j s $$ Hs
  dsimp only
  wp_if_destruct
  · -- failure
    wp_bind (App (Val #(methods rd.ty _ rd.v)) _)
    iapply HClose
    wp_auto
    iapply HΦ
    iframe Htok
    iapply replFields_intro; iframe
  -- success: the follower installed the snapshot; the commitment counts it (`lciOk`)
  wp_apply (wp_storeUint64_cell wp_StoreUint64 s nv _) $$ [Hn] as Hn
  · iframe; iframe #
  wp_apply wp_match $$ [$Hcmt]
  · iright; iright; iapply aeValid_lciOk γ T _ _ [] _ $$ Hae
  wp_bind (App (Val #(methods rd.ty _ rd.v)) _)
  iapply HClose
  wp_auto
  iapply HΦ
  iframe Htok
  iapply replFields_intro; iframe
/- stage-3 broken proof, kept (stage 2: no snapshots):
  fun r γ rc i s tid => by
  wp_start as ⟨#Hr, Htok⟩
  ihave ⟨%x, #Hsnaps, #Hss⟩ := isRaft_snapshotStore r γ rc i $$ Hr
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  unfold isSnapshotStore
  wp_bind (App (Val #(methods x.ty _ x.v)) _)
  iapply Hss $$ Htok
  iintro %sl Hsl Htok
  ihave %Hlen := ownSlice_len $$ Hsl
  wp_auto
  wp_if_destruct
  · wp_apply (wp_Errorf _ slice.nil [] (DFrac.own 1)) as %e ⟨-, %s, -, He⟩
    · isplitl
      · iapply ownSlice_nil
      · iapply (fmt.argsOk_of_argsWf (by intro ii h; simp at h))
    iapply HΦ
    iframe Htok
    ipureintro; exact ⟨rfl, by simp⟩
  exfalso; apply Hif; simp at Hlen; word
  -/

end proof

end Perennial
