/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Replica__run.lean`. Lean-first
(no Rocq counterpart).

The loop keeps `runInv` (`RunInv.lean`). Each iteration `select`s on the node's `Ready` channel
(`isReadyChan_recvAu`) and `stopc` (the broadcast). On `stopc`'s close it sends the loop's
`nodeRunning 1` on `runDone` (the handoff's producer) and returns; it does the same when a `Ready`'s
entries do not fit (`fits`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__run
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__applyEntry
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__install
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__answer
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__maybeSnapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__maybeCompact
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
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.RunApply
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
    (wp_maybeSnapshot : Replica.maybeSnapshot.spec (GF := GF) (hG := hG))
    (wp_maybeCompact : Replica.maybeCompact.spec (GF := GF) (hG := hG))
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
        imod append_none_post st ρ.ms ρ.γs c D ce es k Hsi.2.2 (Hin) Hidx Hk
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
        ihave IH : iprop(∃ (k : w64) (ev : Loc) (si : w64) (sv : SnapshotM) (csp' : Loc)
            (m' : Membership) (A' : GMap (List w8) (List w8)),
            "i" ∷ i_ptr ↦ k ∗ "e" ∷ e_ptr ↦ ev ∗ "r" ∷ r_ptr ↦ r ∗ "snapIndex" ∷ snapIndex_ptr ↦ si ∗
            "Hown" ∷ repOwn γr r (D ++ ce.take (sint.nat k)) (W64 (D ++ ce.take (sint.nat k)).length)
              csp' m' mA A' ∗
            "Hview" ∷ appNode γr n (D ++ ce) (D ++ ce.take (sint.nat k)).length m' ∗
            "Hsx" ∷ memSnapExact ρ.γs sv ∗ "Hrun" ∷ nodeRunning n γr.cluster kvrRaftN 1 ∗
            "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ce.length : Int) ∧ sv.Metadata'.Index' = si ∧
              c ≤ uint.nat si⌝)
          $$ [i e r snapIndex Hown Hview Hsx Hrun]
        · iexists W64 0, _, snapIndex, sv0, csp, m, A
          simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.append_nil]
          iframe
          ipureintro
          exact ⟨by word, by word, Hsi.1, Hsi.2.1⟩
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
            iexists k + W64 1, ln, si, sv, csp2, m2, A2
            rw [Hk1]
            iframe
            ipureintro
            exact ⟨by word, by word, Hk.2.2.1, Hk.2.2.2⟩
          · wp_apply wp_maybeSnapshot γr vs id r n st sts ρ (D ++ ce.take (sint.nat k + 1)) csp2 m2 mA A2
                (D ++ ce) c sv si ((List.prefix_append_right_inj _).mpr (List.take_prefix _ _))
                Hk.2.2.2 Hk.2.2.1
              $$ [$Hrr $Hown $Hsx $Hfz' $Hdl] as %ret ⟨%sv1, Hown, Hsx, %Hsv1⟩
            wp_for_post
            iframe
            iexists k + W64 1, ln, ret, sv1, csp2, m2, A2
            rw [Hk1]
            iframe
            ipureintro
            refine ⟨by word, by word, Hsv1.1, ?_⟩
            rcases Hsv1.2 with h | ⟨h, h'⟩
            · rw [h]; exact Hk.2.2.2
            · rw [h]; have := Hk.2.2.2; have : uint.nat (W64 ((D ++ ce.take (sint.nat k + 1)).length : Int)) =
                (D ++ ce.take (sint.nat k + 1)).length := by rw [Hl1n, Hplen] at *; word
              omega
        · have Hfull : sint.nat k = ce.length := run_eq k _ _ _ Hif Hcelen.1 Hcebl Hk.2.1
          rw [Hfull, List.take_of_length_le (Nat.le_refl _)]
          have H64 : (D ++ ce).length < 2 ^ 64 := run_len64 c _ si Hlen61 Hk.2.2.2
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
            -- `if oneIn(4) { snapIndex = r.maybeSnapshot(snapIndex) }`
            wp_apply wp_oneIn (W64 4) (by decide) $$ [$Hpkg] as %b -
            wp_join iprop(∃ (si' : w64) (sv' : SnapshotM), snapIndex_ptr ↦ si' ∗ memSnapExact ρ.γs sv' ∗
                repOwn γr r (D ++ ce) (W64 (D ++ ce).length) csp' m' mA A' ∗ r_ptr ↦ r ∗
                ⌜sv'.Metadata'.Index' = si' ∧ c ≤ uint.nat si'⌝)
              with [snapIndex Hsx Hown r] as ⟨%si2, %sv2, snapIndex, Hsx, Hown, r, %Hsv2⟩
            · iexists si, sv
              iframe
              ipureintro; exact ⟨Hk.2.2.1, Hk.2.2.2⟩
            · wp_apply wp_maybeSnapshot γr vs id r n st sts ρ (D ++ ce) csp' m' mA A'
                  (D ++ ce) c sv si (List.prefix_refl _) Hk.2.2.2 Hk.2.2.1
                $$ [$Hrr $Hown $Hsx $Hfz' $Hdl] as %ret ⟨%sv1, Hown, Hsx, %Hsv1⟩
              wp_join_done
              iexists ret, sv1
              iframe
              ipureintro
              refine ⟨Hsv1.1, ?_⟩
              rcases Hsv1.2 with h' | ⟨h', h''⟩
              · rw [h']; exact Hk.2.2.2
              · rw [h']; have := Hk.2.2.2
                have : uint.nat (W64 ((D ++ ce).length : Int)) = (D ++ ce).length := by word
                omega
            -- `if oneIn(4) { r.maybeCompact(snapIndex) }`
            wp_apply wp_oneIn (W64 4) (by decide) $$ [$Hpkg] as %b -
            wp_join iprop(snapIndex_ptr ↦ si2 ∗ memSnapExact ρ.γs sv2 ∗
                repOwn γr r (D ++ ce) (W64 (D ++ ce).length) csp' m' mA A' ∗ r_ptr ↦ r)
              with [snapIndex Hsx Hown r] as ⟨snapIndex, Hsx, Hown, r⟩
            · wp_apply wp_maybeCompact γr vs id r n st sts ρ (D ++ ce) csp' m' mA A' c sv2 si2 Hsv2.1
                $$ [$Hrr $Hown $Hsx $Hcp $Hfz' $Hal'] as ⟨Hown, Hsx⟩
              wp_join_done
            -- the loop's invariant, at `D ++ ce`
            wp_for_post
            iframe
            unfold runInv
            iexists D ++ ce, phsNext hd h, hs0, csp', mA, m', A', sv2, si2, c, rest, ps'
            iframe
            iframe Hcp Hfz' Hal' Hps2
            ipureintro
            exact ⟨Hsv2.1, Hsv2.2, by rw [List.length_append]; omega⟩
          · iexfalso
            iapply nodeRunning_stopped n γr.cluster kvrRaftN 1
            iframe Hrun Hstop
    | some l =>
      sorry
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
