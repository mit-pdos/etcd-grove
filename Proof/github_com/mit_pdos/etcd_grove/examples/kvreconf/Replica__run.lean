/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Replica__run.lean`. Lean-first
(no Rocq counterpart).

The loop keeps `runInv` (`RunInv.lean`). Each iteration `select`s on the node's `Ready` channel
(`isReadyChan_recvAu`) and `stopc` (the broadcast). On `stopc`'s close it sends the loop's
`nodeRunning 1` on `runDone` (the handoff's producer) and returns; it does the same when a `Ready`'s
entries do not fit (`fits`).

A `Ready` without a snapshot: its entries appended with its committed ones frozen (`RunAppend.lean`),
its committed entries applied in order (`applyEntry` needs the log below `2^61`: `frozenTo_len`,
`RunApply.lean`), with a snapshot request at random (`request`, to the snapshot goroutine), then
`answer`, `Advance` (its stopped answer refuted by the loop's `nodeRunning`) and a request of a
snapshot or a compaction at random (kvreconf-snapshot-thread, 2026-10-30: `run` no longer calls
`CreateSnapshot` or `Compact`). A snapshot `Ready`
(`RunSnap.lean`): its data decodes (the registry's record, `kvr_snap_recv`), the storage and the
replicated state take it (`ApplySnapshot`, `install`), the entries after it are appended
(`snapReceipt`), and `Advance` gives the node's configuration at it: the invariant at the snapshot's
log, compacted at its index.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__run
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__applyEntry
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__install
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__answer
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__request
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.fits
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.oneIn
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.decodeState
public import Spec.go_etcd_io.raft.v3.node__Ready
public import Spec.go_etcd_io.raft.v3.node__Advance
public import Spec.go_etcd_io.raft.v3.IsEmptySnap
public import Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetData
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.KvrStorageApi
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.RunInv
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.RunSnap
public import Proof.go_etcd_io.raft.v3.Base
public import Proof.go_etcd_io.raft.v3.FrameH

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

set_option hygiene false in
/-- `run`'s exit: the loop's `nodeRunning 1` sent on `runDone`, then `return`. -/
local macro "run_exit" : tactic => `(tactic| (
    try wp_auto
    wp_apply wp_handoff_send ρ.rd ρ.rdc (fun _ => nodeRunning n γr.cluster kvrRaftN 1) iprop(True)
      iprop(False) () $$ [$(frameH `HrdH) $(frameH `Hprod) Hrun] as -
    · isplitl [Hrun]
      · iexact Hrun
      · itrivial
    try wp_auto
    wp_for_post
    try wp_auto
    iapply HΦ
    itrivial
  ))

theorem Replica.run.wp_proof
    (wp_applyEntry : Replica.applyEntry.spec (GF := GF) (hG := hG))
    (wp_install : Replica.install.spec (GF := GF) (hG := hG))
    (wp_answer : Replica.answer.spec (GF := GF) (hG := hG))
    (wp_request : Replica.request.spec (GF := GF) (hG := hG))
    (wp_fits : fits.spec (GF := GF) (hG := hG))
    (wp_oneIn : oneIn.spec (GF := GF) (hG := hG))
    (wp_decodeState : decodeState.spec (GF := GF) (hG := hG))
    (wp_Ready : node.Ready.spec (GF := GF) (hG := hG))
    (wp_Advance : node.Advance.spec (GF := GF) (hG := hG))
    (wp_IsEmptySnap : IsEmptySnap.spec (GF := GF) (hG := hG))
    (wp_IsEmptyHardState : IsEmptyHardState.spec (GF := GF) (hG := hG))
    (wp_GetData : raftpb.Snapshot.GetData.spec (GF := GF) (hG := hG))
    (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_MdGetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_Append : MemoryStorage.Append.spec (GF := GF) (hG := hG))
    (wp_ApplySnapshot : MemoryStorage.ApplySnapshot.spec (GF := GF) (hG := hG))
    (wp_SetHardState : MemoryStorage.SetHardState.spec (GF := GF) (hG := hG)) :
    Replica.run.spec (GF := GF) (hG := hG) := by
  intro γr vs id r n st sts ρ f
  wp_start as ⟨#Hrr, Hstart, #Hsend⟩
  ihave #Hrr' := Hrr
  iunfold isReplicaR at Hrr'
  iNamed Hrr'
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  try wp_auto
  ihave Hinv := runInv_init γr vs id r n st ρ pending_ptr snapIndex_ptr $$ [Hstart pending snapIndex]
  · iframe
  wp_for Hinv
  wp_apply (lc := 2) wp_Ready γr.cluster kvrRaftN id n $$ [$Hraft $HisNode] as %ch #Hch
  try wp_auto
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- a `Ready`
    simp only [chan.blockingClausePre]
    icases isReadyChan_recvAu n ch γr.cluster kvrRaftN id _ _ rfl $$ Hch HisNode Hdrv
      with ⟨%γc, #Hchan, Hau⟩
    iexists Ready, inferInstance, inferInstance, inferInstance, inferInstance, ch, γc
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact Hchan
    iapply Hau $$ [$Hlc1 $Hlc2]
    inext
    iintro %rdv ⟨%ce, %es, %h, %L, #Hce, #Hcomm, Hrs, Hrest, Hdrv⟩
    ihave ⟨%Hidx, Hrest⟩ := readyRest_indices _ _ _ _ _ _ _ _ _ $$ Hrest
    try wp_auto
    cases L with
    | none =>
      ihave ⟨%Hin, Hrest⟩ := readyRest_ceInBatch _ _ _ _ _ _ _ _ $$ Hrest
      iunfold readyRest at Hrest
      icases Hrest with ⟨%msl, #Hes, Hmsl, Hmsok, #Hhs, #Hss, %Hbnd, Hsnap⟩
      iunfold readySnap at Hsnap
      icases Hsnap with ⟨%Hnull, Happ, #Hcef, -⟩
      wp_apply wp_fits rdv.Entries' es DFrac.discard $$ [$Hpkg $Hes] as %b ⟨-, %Hfit⟩
      cases b
      · run_exit
      have Hfit' := Hfit rfl
      try wp_auto
      wp_apply wp_IsEmptySnap rdv.Snapshot' DFrac.discard none $$ [$Hraft] as %b2 ⟨%Hb2, -⟩
      · unfold snapOpt; ipureintro; exact Hnull
      subst Hb2
      simp only [Option.elim]
      try wp_auto
      wp_apply wp_IsEmptyHardState rdv.HardState' h $$ [$Hraft $Hhs]
      try wp_auto
      wp_join iprop(∃ hs' : HardStateM, memStorMeta ρ.ms ρ.γs hs' ∗ r_ptr ↦ r ∗ rd_ptr ↦ rdv)
        with [Hmeta r rd] as ⟨%hs0, Hmeta, r, rd⟩
      · try wp_auto
        wp_apply Storage.wp_SetHardState wp_SetHardState st ρ.ms ρ.γs hs rdv.HardState' h
          $$ [$HstRec $Hraft $Hmeta $Hhs] as Hmeta
        wp_join_done
      · icases append_none_pre st ρ.ms ρ.γs es $$ HstRec Happ with ⟨%k, %old, ⟨%Hk, %Hk0⟩, Hrange⟩
        have h1 : ∀ (j : Nat) (e : EntryM), es[j]? = some e → uint.nat e.Index' = k + j := by
          intro j e hj
          cases hes : es with
          | nil => rw [hes] at hj; cases hj
          | cons e0 rest =>
            rw [Hk e0 (by rw [hes]; rfl)]
            exact Hidx e0 (by rw [hes]; rfl) j e hj
        have h2 : k + es.length ≤ 2 ^ 61 := by
          cases hes : es with
          | nil => rw [Hk0 hes]; simp
          | cons e0 rest =>
            have := Hfit' e0 (by rw [hes]; rfl)
            rw [Hk e0 (by rw [hes]; rfl)]
            rw [hes] at this
            word
        ihave #HmsInv' := HmsInv
        iunfold memStorInvP at HmsInv'
        icases HmsInv' with ⟨#Hlock, -, -⟩
        wp_apply Storage.wp_Append wp_Append st ρ.ms ρ.γs k old es rdv.Entries' DFrac.discard h1 h2
          $$ [$HstRec $Hraft $Hlock $Hrange $Hes] as ⟨-, Hb⟩
        imod append_none_post st ρ.ms ρ.γs c D ce es k Hsi.2 (Hin) Hidx Hk
          $$ HstRec Hfz Hcef Hb with ⟨#Hfz', Hrcpt⟩
        -- `send(rd.Messages)`
        try wp_auto
        wp_bind (App (Val #f) _)
        iunfold sendSpec at Hsend
        iapply Hsend $$ [Hmsl Hmsok]
        · iframe; iexact Hpkg
        iintro !> -
        try wp_auto
        -- the read states, noted
        icases Hrs with ⟨%rsts, #Hsts, #Hstsok⟩
        ihave Hvs := kvr_readStatesPts_rsOk γr.cluster rdv.ReadStates' rsts $$ [Hsts Hstsok]
        · iframe Hsts Hstsok
        icases Hvs with ⟨%vls, #Hvls, #Hvlsok⟩
        wp_apply wp_slice_append $$ [$Hpv $Hpcap $Hvls] as %pv' ⟨Hpv, Hpcap, -⟩
        ihave #Hps' : iprop([∗list] v ∈ ps ++ vls, rsOk γr.cluster v) $$ []
        · iapply (BigSepL.bigSepL_append (Φ := fun _ v => rsOk (GF := GF) γr.cluster v)).2
          iframe Hps Hvlsok
        iclear Hps
        -- applying the committed entries, in order
        iunfold committedEntriesAt at Hce
        icases entsPts_elim _ _ _ $$ Hce with ⟨%cls, #Hcel, #Hceb⟩
        ihave %Hcelen := ownSlice_len $$ Hcel
        ihave %Hcebl := entsBig_length $$ Hceb
        rw [kvr_toEntries_length] at Hcebl
        ihave ⟨Hdrv, #Hdl⟩ := nodeDriver_deliveredLogLb _ _ _ _ $$ Hdrv
        ihave %Hlen61 := frozenTo_len _ _ _ $$ Hfz'
        ihave Hview := appNode_extend γr n D (D ++ ce) D.length m (List.prefix_append _ _)
          (Nat.le_refl _) $$ [Hview Hdl]
        · iframe Hview Hdl
        ihave IH : iprop(∃ (k : w64) (ev : Loc) (si : w64) (csp' : Loc)
            (m' : Membership) (A' : GMap (List w8) (List w8)),
            "i" ∷ i_ptr ↦ k ∗ "e" ∷ e_ptr ↦ ev ∗ "r" ∷ r_ptr ↦ r ∗ "snapIndex" ∷ snapIndex_ptr ↦ si ∗
            "Hown" ∷ repOwn γr r (D ++ ce.take (sint.nat k)) (W64 (D ++ ce.take (sint.nat k)).length)
              csp' m' mA A' ∗
            "Hview" ∷ appNode γr n (D ++ ce) (D ++ ce.take (sint.nat k)).length m' ∗
            "Hrun" ∷ nodeRunning n γr.cluster kvrRaftN 1 ∗
            "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ce.length : Int) ∧ c ≤ uint.nat si⌝)
          $$ [i e r snapIndex Hown Hview Hrun]
        · iexists W64 0, _, snapIndex, csp, m, A
          simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.append_nil]
          iframe
          ipureintro
          exact ⟨by word, by word, Hsi.1⟩
        wp_for IH
        wp_if_destruct
        · have Hlt : sint.nat k < ce.length := run_lt k _ _ _ Hif Hcelen.1 Hcebl Hk.1
          obtain ⟨en, Hen⟩ : ∃ en, ce[sint.nat k]? = some en := ⟨_, List.getElem?_eq_getElem Hlt⟩
          have Hplen : (D ++ ce.take (sint.nat k)).length = D.length + sint.nat k := by
            rw [List.length_append, List.length_take_of_le (by omega)]
          have Hget : (LogEntry.toEntries ce D.length)[sint.nat k]? =
              some (en.toEntryM (W64 ((D ++ ce.take (sint.nat k)).length + 1))) := by
            rw [kvr_toEntries_get _ _ _ _ Hen, Hplen]; push_cast; rfl
          ihave ⟨%ln, %Hln, #Hent⟩ := entsBig_lookup cls _ (sint.nat k) _ Hget $$ Hceb
          simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z rdv.CommittedEntries'.len from ⟨Hk.1, Hif⟩,
            _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index rdv.CommittedEntries' (sint.Z k) _ DFrac.discard ln Hk.1 $$ [Hcel] as -
          · iframe Hcel; ipureintro; rw [show (sint.Z k).toNat = sint.nat k by word]; exact Hln
          have Htk : ce.take (sint.nat k + 1) = ce.take (sint.nat k) ++ [en] := by
            rw [List.take_add_one, Hen]; rfl
          have Hpre : (D ++ ce.take (sint.nat k)) ++ [en] <+: D ++ ce := by
            rw [List.append_assoc, ← Htk]
            exact (List.prefix_append_right_inj _).mpr (List.take_prefix _ _)
          have Hb61 : ((D ++ ce.take (sint.nat k)).length : Int) + 1 < 2 ^ 61 := by
            have := Hlen61 (by rw [List.length_append]; omega)
            rw [Hplen]; simp only [List.length_append] at this; omega
          wp_apply wp_applyEntry γr vs id r n st sts 1 (D ++ ce.take (sint.nat k)) _ csp' m' mA A'
              (D ++ ce) en ln Hpre Hb61
            $$ [$Hrep $Hown $Hview $Hent $Hcomm $Hrun] as ⟨%csp2, %m2, %A2, Hown, Hview, Hrun⟩
          have Hl1 : ((D ++ ce.take (sint.nat k + 1)).length : Int) =
              ((D ++ ce.take (sint.nat k)).length : Int) + 1 := by
            rw [Htk]; simp only [List.length_append, List.length_singleton]; omega
          have Hl1n : (D ++ ce.take (sint.nat k + 1)).length = (D ++ ce.take (sint.nat k)).length + 1 := by
            rw [Htk]; simp only [List.length_append, List.length_singleton]; omega
          have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by
            have := Hb61; rw [Hplen] at this; word
          rw [← Hl1, ← Hl1n, List.append_assoc, ← Htk]
          wp_apply wp_oneIn (W64 8) (by decide) $$ [$Hpkg] as %b -
          wp_if_destruct
          · wp_for_post
            iframe
            iexists k + W64 1, ln, si, csp2, m2, A2
            rw [Hk1]
            iframe
            ipureintro
            exact ⟨by word, by word, Hk.2.2⟩
          · wp_apply wp_request γr vs id r n st sts ρ (D ++ ce.take (sint.nat k + 1)) csp2 m2 mA A2
                (D ++ ce) c si true false ((List.prefix_append_right_inj _).mpr (List.take_prefix _ _))
                Hk.2.2
              $$ [$Hrr $Hown $Hcp $Hfz' $Hdl] as %ret ⟨Hown, %Hsv1⟩
            · ileft; ipureintro; rfl
            wp_for_post
            iframe
            iexists k + W64 1, ln, ret, csp2, m2, A2
            rw [Hk1]
            iframe
            ipureintro
            refine ⟨by word, by word, ?_⟩
            rcases Hsv1 with h | ⟨h, h'⟩
            · rw [h]; exact Hk.2.2
            · rw [h]; have := Hk.2.2; have : uint.nat (W64 ((D ++ ce.take (sint.nat k + 1)).length : Int)) =
                (D ++ ce.take (sint.nat k + 1)).length := by rw [Hl1n, Hplen] at *; word
              omega
        · have Hfull : sint.nat k = ce.length := run_eq k _ _ _ Hif Hcelen.1 Hcebl Hk.2.1
          rw [Hfull, List.take_of_length_le (Nat.le_refl _)]
          have H64 : (D ++ ce).length < 2 ^ 64 := run_len64 c _ si Hlen61 Hk.2.2
          wp_apply wp_answer γr vs id r n st sts (D ++ ce) _ csp' m' mA A' pv' (ps ++ vls) (DFrac.own 1)
              (by word) $$ [$Hrep $Hown $Hpv $Hps'] as %rest ⟨Hown, %ps', Hrest, Hcap2, #Hps2⟩
          -- `r.node.Advance()`
          ihave #Hcl' := Hcl
          iunfold kvrCluster at Hcl'
          icases Hcl' with ⟨#Hic, -⟩
          icases appNode_open γr n (D ++ ce) (D ++ ce).length m' $$ Hview with ⟨%v, Hcfg, #Hsk, Hback⟩
          wp_apply wp_Advance n γr.cluster kvrRaftN id _ es none v rfl (fun _ h => by cases h)
            $$ [$Hraft $Hic $HisNode $Hdrv $Hrcpt $Hcfg $Hsk] as Hadv
          icases Hadv with (⟨Hdrv, #Hal', Hcfg⟩ | ⟨#Hstop, -⟩)
          · ihave Hview := Hback $$ Hcfg
            -- `snapIndex = r.request(snapIndex, oneIn(4), oneIn(4))`
            wp_apply wp_oneIn (W64 4) (by decide) $$ [$Hpkg] as %b1 -
            wp_apply wp_oneIn (W64 4) (by decide) $$ [$Hpkg] as %b2 -
            wp_apply wp_request γr vs id r n st sts ρ (D ++ ce) csp' m' mA A'
                (D ++ ce) c si b1 b2 (List.prefix_refl _) Hk.2.2
              $$ [$Hrr $Hown $Hcp $Hfz' $Hdl] as %ret ⟨Hown, %Hsv1⟩
            · iright; iexact Hal'
            have Hc2 : c ≤ uint.nat ret := by
              rcases Hsv1 with h' | ⟨h', h''⟩
              · rw [h']; exact Hk.2.2
              · rw [h']; have := Hk.2.2
                have : uint.nat (W64 ((D ++ ce).length : Int)) = (D ++ ce).length := by word
                omega
            -- the loop's invariant, at `D ++ ce`
            wp_for_post
            iframe
            unfold runInv
            iexists D ++ ce, phsNext hd h, hs0, csp', mA, m', A', ret, c, rest, ps'
            iframe
            iframe Hcp Hfz' Hal' Hps2
            ipureintro
            exact ⟨Hc2, by rw [List.length_append]; omega⟩
          · iexfalso
            iapply nodeRunning_stopped n γr.cluster kvrRaftN 1
            iframe Hrun Hstop
    | some l =>
      iunfold readyRest at Hrest
      icases Hrest with ⟨%msl, #Hes, Hmsl, Hmsok, #Hhs, #Hss, %Hbnd, Hsnap⟩
      iunfold readySnap at Hsnap
      icases Hsnap with ⟨%Hl, Hss4, #HcL, #Hcert, ⟨%k, %old, %Hk, Hlog, Hend⟩, #Hgiven⟩
      obtain ⟨Hdlv, Hptr, Hce0, Hpre, Hlt, Hdlen, Hpos, H61, -, Hli⟩ := Hl
      subst Hce0
      wp_apply wp_fits rdv.Entries' es DFrac.discard $$ [$Hpkg $Hes] as %b ⟨-, %Hfit⟩
      cases b
      · run_exit
      have Hfit' := Hfit rfl
      have Hne : l.snap.Metadata'.Index' ≠ W64 0 := by intro h; rw [h] at Hpos; simp at Hpos
      have Hslen : (strip l.dlv).length = uint.nat l.snap.Metadata'.Index' := by
        unfold strip; rw [List.length_map]; exact Hdlen
      ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
      · iPkgInit
      -- the snapshot: a quarter for the reads, a quarter for `ApplySnapshot`
      icases ownSnapS_split l.ptr (DFrac.own (Qp.half (Qp.half 1))) (DFrac.own (Qp.half (Qp.half 1)))
        l.snap $$ [Hss4] with ⟨Hs1, Hs2⟩
      · rw [← dfrac_own_half_half]; iexact Hss4
      ihave Hs1 := ownSnapS_M _ _ _ $$ Hs1
      try wp_auto
      rw [← Hptr]
      wp_apply wp_IsEmptySnap l.ptr _ (some l.snap) $$ [$Hraft Hs1] as %b2 ⟨%Hb2, Hs1⟩
      · unfold snapOpt; iexact Hs1
      unfold snapOpt at Hb2
      subst Hb2
      ihave Hs1 : ownSnapM l.ptr (DFrac.own (Qp.half (Qp.half 1))) l.snap $$ [Hs1]
      · unfold snapOpt; iexact Hs1
      simp only [Option.elim, decide_eq_false Hne]
      -- the snapshot's facts: valid, its data the state of the delivered log
      imod kvr_snap_recv γr vs l.snap (strip l.dlv) Hpos H61 Hslen $$ Hcl HcL Hcert
        with ⟨#Hsv, %mL, #HcaL, %HmL⟩
      obtain ⟨HcsL, HszL, HdatL⟩ := HmL
      obtain ⟨kvs, ops, Hdat, Hwk, Hwo, Hkv, Hans⟩ := HdatL
      -- `decodeState(rd.Snapshot.GetData())`
      try wp_auto
      rw [← Hptr]
      wp_apply wp_GetData.1 l.ptr _ l.snap $$ [$Hpb $Hs1] as %ds ⟨Hds, Hs1back⟩
      rw [Hdat]
      wp_apply wp_decodeState ds _ kvs ops Hwk Hwo $$ [$Hpkg $Hds] as %mK %mA2 ⟨Hds, %K', %A', HK', HA', %HKA⟩
      ihave Hs1 := Hs1back $$ Hds
      -- `r.storage.ApplySnapshot(rd.Snapshot)`
      ihave #Hinit := isInitialized_access $$ Hraft
      iunfold isInitialized at Hinit
      iNamed Hinit
      icases ErrSnapOOD with ⟨%eood, #Heood⟩
      ihave Hlog := kvrStorLog_to st ρ.ms ρ.γs _ _ _ $$ HstRec Hlog
      ihave Hend := kvrStorEnd_to st ρ.ms ρ.γs _ $$ HstRec Hend
      ihave ⟨Hdrv, #Hdl⟩ := nodeDriver_deliveredLogLb _ _ _ _ $$ Hdrv
      try wp_auto
      rw [← Hptr]
      wp_apply Storage.wp_ApplySnapshot wp_ApplySnapshot st ρ.ms ρ.γs (kvrJ γr.cluster id) k old l.ptr
          (DFrac.own (Qp.half (Qp.half 1))) l.snap eood Hk (by word)
        $$ [$HstRec $Hraft $HmsInv $Hlog $Hend $HsnLb $Heood Hs2] as ⟨Hs2, #HcpS, #Hdum, HendS, -⟩
      · simp only [kvrJ]
        isplitl []
        · iright; iexact Hgiven
        isplitl []
        · iexact Hsv
        isplitl []
        · unfold storDL
          iexists n, kvrRaftN, strip l.dlv
          iframe HisNode Hdl
          ipureintro; omega
        unfold snapArg
        iright; iexact Hs2
      -- `r.install(rd.Snapshot.GetMetadata(), kv, ops)`
      have Hkv' : ∀ k, (K' !! k).getD [] = kvFold (logHist (strip l.dlv)) k := by
        intro k; rw [HKA.1 k]; exact Hkv k
      have Hans' : AppliedOk A' (logHist (strip l.dlv)) := by
        unfold AppliedOk
        have : (fun d => A' !! d) = (fun o => List.lookup o ops) := funext HKA.2
        rw [this]; exact Hans
      try wp_auto
      rw [← Hptr]
      wp_apply wp_GetMetadata.1 l.ptr _ l.snap $$ [$Hpb $Hs1] as %pm ⟨Hpm, Hs1back⟩
      wp_apply wp_install γr vs id r n st sts D _ csp m mA A pm _ l.snap.Metadata' mK mA2 K' A'
          (strip l.dlv) mL Hslen (by rw [Hslen]; word) Hkv' Hans' HcsL HszL
        $$ [$Hrep $Hown $Hpm $HK' $HA' $HcL $HcaL] as ⟨Hpm, %csp2, Hown⟩
      ihave Hs1 := Hs1back $$ Hpm
      -- `snapIndex = rd.Snapshot.GetMetadata().GetIndex()`
      try wp_auto
      rw [← Hptr]
      wp_apply wp_GetMetadata.1 l.ptr _ l.snap $$ [$Hpb $Hs1] as %pm2 ⟨Hpm2, Hs1back⟩
      wp_apply wp_MdGetIndex pm2 _ _ $$ [$Hpb $Hpm2] as Hpm2
      ihave Hs1 := Hs1back $$ Hpm2
      try wp_auto
      -- the hard state
      wp_apply wp_IsEmptyHardState rdv.HardState' h $$ [$Hraft $Hhs]
      try wp_auto
      wp_join iprop(∃ hs' : HardStateM, memStorMeta ρ.ms ρ.γs hs' ∗ r_ptr ↦ r ∗ rd_ptr ↦ rdv)
        with [Hmeta r rd] as ⟨%hs0, Hmeta, r, rd⟩
      · try wp_auto
        wp_apply Storage.wp_SetHardState wp_SetHardState st ρ.ms ρ.γs hs rdv.HardState' h
          $$ [$HstRec $Hraft $Hmeta $Hhs] as Hmeta
        wp_join_done
      -- `r.storage.Append(rd.Entries)`, after the snapshot's index
      ihave ⟨Hrange, Hkeep⟩ := snapAppend_pre ρ.γs (uint.nat l.snap.Metadata'.Index' + 1) es $$ HendS
      have h1 : ∀ (j : Nat) (e : EntryM), es[j]? = some e →
          uint.nat e.Index' = (uint.nat l.snap.Metadata'.Index' + 1) + j := by
        intro j e hj
        have := Hli j e hj
        simp only [snapId] at this
        word
      have h2 : uint.nat l.snap.Metadata'.Index' + 1 + es.length ≤ 2 ^ 61 := by
        cases hes : es with
        | nil => simp only [List.length_nil, Nat.add_zero]; word
        | cons e0 rest =>
          have Hf := Hfit' e0 (by rw [hes]; rfl)
          have He0 := h1 0 e0 (by rw [hes]; rfl)
          rw [hes] at Hf
          simp only [List.length_cons] at Hf ⊢
          word
      ihave #HmsInv' := HmsInv
      iunfold memStorInvP at HmsInv'
      icases HmsInv' with ⟨#Hlock, -, -⟩
      wp_apply Storage.wp_Append wp_Append st ρ.ms ρ.γs (uint.nat l.snap.Metadata'.Index' + 1) [] es
          rdv.Entries' DFrac.discard h1 h2
        $$ [$HstRec $Hraft $Hlock $Hrange $Hes] as ⟨-, Hb⟩
      ihave ⟨Hb, HendB⟩ := snapAppend_post ρ.γs _ es $$ [Hb Hkeep]
      · iframe Hb Hkeep
      ihave Hs := ownSnapM_combine l.ptr _ _ l.snap $$ [Hs1 Hs2]
      · iframe Hs1 Hs2
      ihave Hs : ownSnapM l.ptr (DFrac.own (Qp.half 1)) l.snap $$ [Hs]
      · rw [dfrac_own_half_half (Qp.half 1)]; iexact Hs
      ihave Hrcpt := kvr_snapReceipt st ρ.ms ρ.γs l es $$ HstRec Hs HcpS Hdum Hb HendB
      -- `send(rd.Messages)`
      try wp_auto
      wp_bind (App (Val #f) _)
      iunfold sendSpec at Hsend
      iapply Hsend $$ [Hmsl Hmsok]
      · iframe; iexact Hpkg
      iintro !> -
      try wp_auto
      -- the read states, noted
      icases Hrs with ⟨%rsts, #Hsts, #Hstsok⟩
      ihave Hvs := kvr_readStatesPts_rsOk γr.cluster rdv.ReadStates' rsts $$ [Hsts Hstsok]
      · iframe Hsts Hstsok
      icases Hvs with ⟨%vls, #Hvls, #Hvlsok⟩
      wp_apply wp_slice_append $$ [$Hpv $Hpcap $Hvls] as %pv' ⟨Hpv, Hpcap, -⟩
      ihave #Hps' : iprop([∗list] v ∈ ps ++ vls, rsOk γr.cluster v) $$ []
      · iapply (BigSepL.bigSepL_append (Φ := fun _ v => rsOk (GF := GF) γr.cluster v)).2
        iframe Hps Hvlsok
      iclear Hps
      -- no committed entries
      iunfold committedEntriesAt at Hce
      icases entsPts_elim _ _ _ $$ Hce with ⟨%cls, #Hcel, #Hceb⟩
      ihave %Hcelen := ownSlice_len $$ Hcel
      ihave %Hcebl := entsBig_length $$ Hceb
      rw [kvr_toEntries_length] at Hcebl
      ihave IH : iprop(∃ ev : Loc, "i" ∷ i_ptr ↦ W64 0 ∗ "e" ∷ e_ptr ↦ ev) $$ [i e]
      · iexists _; iframe
      wp_for IH
      wp_if_destruct
      · exfalso
        simp only [List.length_nil] at Hcebl
        have := Hcelen.1; word
      have Hidxeq : l.snap.Metadata'.Index' = W64 ((strip l.dlv).length : Int) := by rw [Hslen]; word
      ihave Hown : repOwn γr r (strip l.dlv) (W64 (strip l.dlv).length) csp2 mL mA2 A' $$ [Hown]
      · rw [← Hidxeq]; iexact Hown
      wp_apply wp_answer γr vs id r n st sts (strip l.dlv) _ csp2 mL mA2 A' pv' (ps ++ vls) (DFrac.own 1)
          (by rw [Hslen]; word) $$ [$Hrep $Hown $Hpv $Hps'] as %rest ⟨Hown, %ps', Hrest, Hcap2, #Hps2⟩
      -- `r.node.Advance()`: the node's configuration at the snapshot's
      ihave #Hcl' := Hcl
      iunfold kvrCluster at Hcl'
      icases Hcl' with ⟨#Hic, -⟩
      iunfold appNode at Hview
      icases Hview with ⟨%v, Hcfg, -, -, -⟩
      wp_apply wp_Advance n γr.cluster kvrRaftN id _ es (some l) v rfl
          (fun l' h => by cases h; exact Hdlen)
        $$ [$Hraft $Hic $HisNode $Hdrv Hrcpt $Hcfg] as Hadv
      · simp only [advReceipt]
        iframe Hrcpt Hcert
      icases Hadv with (⟨Hdrv, #Hal', %m2, Hcfg, #Hca2, %Hcs2⟩ | ⟨#Hstop, -⟩)
      · ihave #HcaL' : confAt γr.cluster (uint.nat l.snap.Metadata'.Index') mL $$ []
        · rw [← Hslen]; iexact HcaL
        ihave %Hm := confAt_agree γr.cluster _ m2 mL $$ [Hca2 HcaL']
        · iframe Hca2 HcaL'
        subst Hm
        ihave Hview := appNode_snap γr n (strip l.dlv) _ m2 Hslen $$ [Hcfg Hdl]
        · iframe Hcfg Hdl
        ihave #Hfz2 := frozenTo_snap (GF := GF) ρ.γs (strip l.dlv) _ Hslen
        -- `snapIndex = r.request(snapIndex, oneIn(4), oneIn(4))`
        wp_apply wp_oneIn (W64 4) (by decide) $$ [$Hpkg] as %b1 -
        wp_apply wp_oneIn (W64 4) (by decide) $$ [$Hpkg] as %b2 -
        wp_apply wp_request γr vs id r n st sts ρ (strip l.dlv) csp2 m2 mA2 A'
            (strip l.dlv) (uint.nat l.snap.Metadata'.Index') l.snap.Metadata'.Index' b1 b2
            (List.prefix_refl _) (Nat.le_refl _)
          $$ [$Hrr $Hown $HcpS $Hfz2 $Hdl] as %ret ⟨Hown, %Hsv1⟩
        · iright; iexact Hal'
        have Hc2 : uint.nat l.snap.Metadata'.Index' ≤ uint.nat ret := by
          rcases Hsv1 with h' | ⟨h', h''⟩
          · rw [h']; exact Nat.le_refl _
          · rw [h']
            have : uint.nat (W64 ((strip l.dlv).length : Int)) = (strip l.dlv).length := by
              rw [Hslen]; word
            omega
        -- the loop's invariant, at the snapshot's log
        wp_for_post
        iframe
        unfold runInv
        iexists strip l.dlv, phsNext hd h, hs0, csp2, mA2, m2, A', ret,
          uint.nat l.snap.Metadata'.Index', rest, ps'
        iframe
        iframe HcpS Hfz2 Hal' Hps2
        ipureintro
        exact ⟨Hc2, by omega⟩
      · iexfalso
        iapply nodeRunning_stopped n γr.cluster kvrRaftN 1
        iframe Hrun Hstop
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `stopc` closed: `nodeRunning 1` sent on `runDone`
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ρ.stopc, ρ.sc
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ HstopB
    iapply broadcast_chan_receive _ _ _ _ _ $$ HstopB
    iintro ⟨-, -⟩
    run_exit
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end kvreconf
end EtcdGrove
end Perennial
