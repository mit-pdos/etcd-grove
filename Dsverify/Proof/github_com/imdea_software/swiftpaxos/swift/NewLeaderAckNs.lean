/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/NewLeaderAckNs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.handleNewLeaderAckNs(_, msgs)` (recovery.go): the new leader of ballot `b'`, with a
majority's reports, computes the `MSync` (`recoveredSync`), takes ballot `b'`'s `MSync` step in
its node state (`computeSync_stepD`: `syncIs`, its order's `locAt`s and row tokens), sends the
`MSync` to all (change log C18: `SendToAllP`, the wire `MSync` chosen at the write among
`swift.syncCands`, each with `msgOk (.sync m)`), and takes it itself (`handleSync`).

* `MSync.Marshal`: the hypothesis `swift.MSync.marshalHG` (SyncFits.lean; proved:
  `swift.MSync.marshal_proofG`, MarshalSync.lean), at gob's package and `codecSet` (a premise
  here); its size premise `swift.syncFits` from the reports' registrations (`swift.repsOk_inv2`:
  D13's bound and the values' `Cmd.wf`) and `sp.recoverSync_deps_len` (round 18).
* `swift.Replica.handleNewLeaderAckNs.specI` and its proof over the callees' specs.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecSync
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RepsOkInv
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.WriterSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncFits
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncSeq
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GhostSteps2

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## Pure -/

theorem swift.LView.computed_locAt (w : swift.LView) (b' : Nat) (o : List sp.CmdId) (b : Nat) :
    (w.computed b' o).locAt b = if b = b' then o else w.locAt b := by
  unfold swift.LView.computed swift.LView.locAt
  by_cases h : b = b'
  · subst h; simp
  · simp [h, Ne.symm h]

theorem swift.localOkS_computed {N r : Nat} {ld : Bool} {v : swift.RunV} {M : Option sp.SyncMsg}
    {w : swift.LView} {b' : Nat} (o : List sp.CmdId) (h : swift.localOkS N r ld v M w b')
    (hb : w.2.1 < b') : swift.localOkS N r ld v M (w.computed b' o) b' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  have e : ∀ b, b ≠ b' → (w.computed b' o).locAt b = w.locAt b := fun b hb' => by
    rw [swift.LView.computed_locAt, if_neg hb']
  have hc : (w.computed b' o).2.1 = w.2.1 := rfl
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, ?_, ?_, h11⟩
  · rw [hc, e _ (by omega)]; exact h8
  · rw [hc, e _ (by omega)]; exact h9
  · intro b o' hb1 hb2 hmem
    change (b, o') ∈ (b', o) :: w.2.2.2 at hmem
    rcases List.mem_cons.mp hmem with e' | e'
    · exact hb2 (congrArg Prod.fst e')
    · exact h10 b o' hb1 hb2 e'

/-- An `MSync` lists at most the reports' entries (its ids are distinct reported ids). -/
theorem sp.recoverSync_len (N : Nat) (reps : List (Nat × sp.Report))
    (hnd : ((sp.recoverSync N reps).map Prod.fst).Nodup) :
    (sp.recoverSync N reps).length ≤ (reps.flatMap (·.2.entries)).length := by
  have hsub : (sp.recoverSync N reps).map Prod.fst ⊆ (reps.flatMap (·.2.entries)).map (·.id) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    obtain ⟨a, ha, re, hre, h1, -⟩ := sp.recoverSync_cmd N reps p hp
    exact List.mem_map.mpr ⟨re, List.mem_flatMap.mpr ⟨a, ha, hre⟩, h1⟩
  have := (List.subperm_of_subset hnd hsub).length_le
  simpa using this

section ghost
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]
variable [swift.Assumptions]

instance swift.syncSent_persistent (ls : Loc) (me bl : w32) (M : sp.SyncMsg) :
    Persistent (swift.syncSent ls me bl M) := by
  unfold swift.syncSent; infer_instance

/-- The run loop's state with its view taken out (to step the node state). -/
theorem swift.runStS_view (γ : sp.Names) (γv : GName) (rp : Loc) (N r : Nat) (ld : Bool)
    (v : swift.RunV) (M : Option sp.SyncMsg) (bs hd : sp.Seq) (w : swift.LView) (b' : Nat)
    (o : List sp.CmdId) (hb : w.2.1 < b') :
    swift.runStS γ γv rp N r ld v M bs hd w b' ⊢
      ghostVar γv (1 : Qp).half w ∗ ⌜swift.localOkS N r ld v M w b'⌝ ∗
      (ghostVar γv (1 : Qp).half (w.computed b' o) -∗
        swift.runStS γ γv rp N r ld v M bs hd (w.computed b' o) b') := by
  unfold swift.runStS
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, Hw, #Hlb, %Hok⟩
  iframe Hw
  isplitr
  · ipureintro; exact Hok.1
  iintro Hw
  rw [show (w.computed b' o).2.1 = w.2.1 from rfl]
  iframe
  iframe #
  ipureintro
  exact ⟨swift.localOkS_computed o Hok.1 hb, Hok.2⟩

/-- The run loop's state with its ballot field taken out (`recoveredSync` reads it). -/
theorem swift.runStS_ballot (γ : sp.Names) (γv : GName) (rp : Loc) (N r : Nat) (ld : Bool)
    (v : swift.RunV) (M : Option sp.SyncMsg) (bs hd : sp.Seq) (w : swift.LView) (b' : Nat) :
    swift.runStS γ γv rp N r ld v M bs hd w b' ⊢
      typedPointsto (swift.fld rp go!"ballot") v.ballot (DFrac.own (1 : Qp).half.half) ∗
      ⌜swift.localOkS N r ld v M w b'⌝ ∗
      (typedPointsto (swift.fld rp go!"ballot") v.ballot (DFrac.own (1 : Qp).half.half) -∗
        swift.runStS γ γv rp N r ld v M bs hd w b') := by
  unfold swift.runStS
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, Hw, #Hlb, %Hok⟩
  iframe H1
  isplitr
  · ipureintro; exact Hok.1
  iintro H1
  iframe
  iframe #
  ipureintro; exact Hok

end ghost

/-! ## Specs -/

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

/-- **`r.handleNewLeaderAckNs(lm, msgs)`** (the handler of `newLeaderAckNs`'s quorum): the new
leader `r` of `b'` (recovering in `b'`, without a row of `b'`), with the reports `reps` of a
majority (`reported` for `b'`), ends as `handleSync` of `recoverSync N reps` leaves it. Round 47
(sv-swb, 45-b, D61 (1)): `handleSync.specIR`'s persistent `PC`, passed through. -/
abbrev swift.Replica.handleNewLeaderAckNs.specI (EpR : GMap swift.CommandId Loc → IProp netDistGF)
    (EpS : sp.SyncMsg → List sp.CmdId → IProp netDistGF) (DF : Nat → Loc → IProp netDistGF)
    (PS : Nat → GMap GoString GoInterface → IProp netDistGF)
    (γ : sp.Names) (γc γm γl γw γv γd γe γo : GName) (n : swift.SyncN) (rp rr : Loc)
    (PC : IProp netDistGF) : Prop :=
  ∀ (qs : Loc) (N r k : Nat) (me : w32)
    (ld : Bool) (v : swift.RunV) (M0 : Option sp.SyncMsg) (bs hd : sp.Seq) (w : swift.LView)
    (lm : GoInterface) (msl : GoSlice) (ms : List GoInterface) (reps : List (Nat × sp.Report))
    (b' : Nat),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.slices ∗
      swift.runCtxD γ γc γm γl γw γv γe γo (n.sn N r) n.γdl rp N r k ∗
      inv swift.nodeN (swift.nodeInvD γ γv γe γo (n.sn N r) k) ∗
      swift.sendCtxN γ γc γm rp N me ∗
      swift.fld rp go!"Replica" ↦□ rr ∗ replica.fld rr go!"N" ↦□ (W64 N) ∗
      replica.fld rr go!"Id" ↦□ me ∗ swift.fld rp go!"qs" ↦□ qs ∗ replica.quorum.isQS qs N ∗
      swift.syncCtx γ N r n rp ∗ □ PC ∗ swift.runReader rp n.γdl ∗
      swift.runStS γ γv rp N r ld v M0 bs hd w b' ∗
      (if w.2.2.1 then EpR v.propsM else swift.epStopped n γe γd DF PS rp rr) ∗
      swift.syncFieldsOwn rp ∗ swift.syncSendCtx γ γc γm rp N ∗
      encoding.gob.codecSet (GF := netDistGF) ∗
      msl ↦*□ ms ∗ swift.acksIs ms reps ∗ ([∗list] p ∈ reps, sp.reported γ p.1 b' p.2) ∗
      ⌜sp.isMajority N (reps.map Prod.fst) ∧ sp.rid me = r ∧ sp.leaderOf N b' = r ∧
        w.1 = b' ∧ 0 < b' ∧ b' < 2 ^ 31 ∧ w.2.2.1 = false ∧ (∀ o, (b', o) ∉ w.2.2.2) ∧
        w.2.1 < b' ∧ 0 ≤ sint.Z me⌝ }}
    (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleNewLeaderAckNs"))
      (Val #lm)) (Val #msl))
  {{ RET #(); swift.runReader rp n.γdl ∗
      ∃ (v' : swift.RunV) (w' : swift.LView),
        swift.runSt γ γv rp N r true v' (some (sp.recoverSync N reps))
          (sp.syncSeq (sp.recoverSync N reps)) [] w' ∗
        EpS (sp.recoverSync N reps) (sp.syncOrder (sp.recoverSync N reps)) ∗
        swift.syncFieldsOwnE rp ∗
        ⌜w'.1 = b' ∧ w'.2.1 = b' ∧ w'.2.2.1 = true⌝ }}

end specs

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

theorem swift.Replica.handleNewLeaderAckNs.wp_proof (EpR : GMap swift.CommandId Loc → IProp netDistGF)
    (EpS : sp.SyncMsg → List sp.CmdId → IProp netDistGF) (DF : Nat → Loc → IProp netDistGF)
    (PS : Nat → GMap GoString GoInterface → IProp netDistGF)
    (γ : sp.Names) (γc γm γl γw γv γd γe γo : GName) (n : swift.SyncN) (rp rr : Loc)
    (PC : IProp netDistGF)
    (wp_recSync : swift.Replica.recoveredSync.specI (hG := hG))
    (wp_send : replica.Sender.SendToAllP.spec (hG := hG))
    (wp_hsync : swift.Replica.handleSync.specIR (hG := hG) EpR EpS DF PS γ γc γm γl γw γv γd γe γo n rp rr PC)
    (hmarsh : swift.MSync.marshalHG (hG := hG)) :
    swift.Replica.handleNewLeaderAckNs.specI (hG := hG) EpR EpS DF PS γ γc γm γl γw γv γd γe γo n rp rr PC := by
  intro qs N r k me ld v M0 bs hd w lm msl ms reps b'
  wp_start as ⟨#Hctx, #Hninv, #Hsend, #Hrr, #HN, #Hme, #Hqs, #HQS, #Hsctx, #HPC, Hrdr, Hst, Hep, Hsf, #Hssc,
    #Hcset, #Hmsl, #Hacks, #Hreps, %Hpre⟩
  obtain ⟨hmaj, hme, hL, hw1, hb0, hb31, hnorm, hrow, hcb, hme0⟩ := Hpre
  ihave #Hctx0 := Hctx
  iunfold swift.runCtxD at Hctx
  icases Hctx with ⟨%rr', %me', %fr, %l, %dm, #Hrr', #HisR', %Hcf, #Hinv, #Hcfg, -, -, -, -, -, #Hng⟩
  obtain ⟨-, -, hrN, hN1, hN7, hnode⟩ := Hcf
  iapply fupd_wp
  imod swift.repsOk_inv2 (γ := γ) (γc := γc) (γm := γm) (γl := γl) ⊤ (by simp) N fr l b' reps hmaj
    ⟨hN1, hN7⟩ hb31 $$ [Hinv Hcfg Hreps] with ⟨%Hrok, %Hreg⟩
  · iframe #
  imodintro
  ihave ⟨Hbal, %Hok, Hst⟩ := swift.runStS_ballot γ γv rp N r ld v M0 bs hd w b' $$ Hst
  wp_auto
  wp_apply (wp_recSync rp rr qs N me v.ballot (DFrac.own (1 : Qp).half.half) msl ms reps)
    $$ [$Hbal] as %ls ⟨Hbal, #Hsent⟩
  · iframe #; ipureintro; exact Hrok
  try wp_auto
  ihave Hst := Hst $$ Hbal
  have hw1' : w.1 = sp.bal v.ballot := Hok.2.2.1
  ihave ⟨Hw, %Hok', Hst⟩ := swift.runStS_view γ γv rp N r ld v M0 bs hd w b'
    (sp.syncOrder (sp.recoverSync N reps)) hcb $$ Hst
  -- L2: the new leader's `MSync` at its resolution (`ghostComputeSync`, `computeSync_stepD`)
  ihave #Hcpk : isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client
    $$ []
  · iPkgInit
  have hbb : sp.bal v.ballot = b' := by rw [← hw1', hw1]
  have hvb : 0 ≤ sint.Z v.ballot := by
    have : 0 < sp.bal v.ballot := by rw [hbb]; exact hb0
    show 0 ≤ v.ballot.toInt
    unfold sp.bal at this; omega
  wp_bind (App (App (Val (@! swift.ghostComputeSync)) (Val _)) (Val _))
  iapply (swift.wp_ghostComputeSync γ k v.ballot msl DFrac.discard ms reps
    iprop(ghostVar γv (1 : Qp).half (w.computed b' (sp.syncOrder (sp.recoverSync N reps))) ∗
      sp.syncIs γ b' (sp.recoverSync N reps) ∗
      ([∗list] i ↦ x ∈ sp.syncOrder (sp.recoverSync N reps), sp.locAt γ (sp.leaderOf N b') b' i x) ∗
      ([∗list] y ∈ sp.syncOrder (sp.recoverSync N reps), swift.rowTok γo b' y swift.rowEmpty) ∗
      [∗list] y ∈ sp.syncOrder (sp.recoverSync N reps), swift.xTixK (n.sn N r).γxu (b', y)))
    $$ [Hw]
  · iframe Hpkg Hcpk Hng Hmsl Hacks
    isplitr
    · ipureintro; exact hvb
    iunfold swift.ghostUpd
    iintro %W' Hpre
    rw [hbb]
    imod swift.computeSync_stepD γ γc γm γl γv γe γo N k fr l w b' reps (by rw [hL]; exact hrN)
      (by rw [hL]; exact hnode) hb0 hw1 hnorm hrow hmaj hcb W' $$ [Hw Hpre]
      with ⟨Hw, Hpost, #HM, #Hlocs, Htoks, Htix⟩
    · iframe #; iframe Hw Hpre
    imodintro
    iframe Hpost Hw Htoks Htix HM Hlocs
  inext
  iintro ⟨-, Hw, #HM, #Hlocs, Htoks, Htix⟩
  try wp_auto
  iapply fupd_wp
  -- round 54 (D74 (2), 53-4): the leader's `locLb` of the `MSync`'s sequence, for `msgOk (.sync)`
  imod sp.syncIs_cmdIs ⊤ (by simp) b' (sp.recoverSync N reps) $$ [Hinv HM] with #Hcmds
  · iframe Hinv HM
  imod sp.syncIs_seq ⊤ (by simp) b' (sp.recoverSync N reps) $$ [Hinv HM] with %Hseq
  · iframe Hinv HM
  ihave #HlbL := sp.locLb_syncSeq (sp.leaderOf N b') b' (sp.recoverSync N reps) Hseq.1
    $$ [Hlocs Hcmds]
  · iframe Hlocs Hcmds
  imodintro
  ihave Hst := Hst $$ Hw
  -- the `MSync` fits a frame (round 18: D13's bound, the values' `Cmd.wf`)
  ihave #Hsent2 := Hsent
  iunfold swift.syncSent at Hsent2
  icases Hsent2 with ⟨#HMaps, -⟩
  ihave #HMaps2 := HMaps
  iunfold swift.syncMaps at HMaps2
  icases HMaps2 with ⟨%-, %-, %-, %-, %-, %-, %-, %-, -, -, -, -, %HMf, -⟩
  have hfits : swift.syncFits me v.ballot (sp.recoverSync N reps) := by
    apply swift.syncFits_of
    · have := Hreg.1 _ HMf.2.1 (fun x hx => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        obtain ⟨a, ha, re, hre, h1, -⟩ := sp.recoverSync_cmd N reps p hp
        exact ⟨a, ha, re, hre, h1⟩)
      simpa using this
    · intro p hp
      obtain ⟨a, ha, re, hre, -, h2⟩ := sp.recoverSync_cmd N reps p hp
      rw [← h2]; exact Hreg.2 a ha re hre
    · exact sp.recoverSync_deps_len N reps
  -- the `MSync` to all (C18: the wire `MSync` chosen at the write)
  ihave #Hgob : isPkgInit (PROP := IProp netDistGF) pkg_id.encoding.gob $$ []
  · iPkgInit
  ihave #Hmar := hmarsh ls me v.ballot _ $$ [Hgob Hcset Hsent]
  · iframe #; ipureintro; exact hfits
  iunfold swift.sendCtxN at Hsend
  icases Hsend with ⟨%rr2, %s, %γw2, %γs, %csv, #Hrr2, #HisR2, #Hsnd, #Hbag, #Hcs, %Hcodes⟩
  ihave #Hcs2 := Hcs
  iStructNamedPrefix Hcs2 "CS"
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_send rr2 γ γc γm γw2 N me γs s
    (interface.mkOk (go.GoType.PointerType swift.MSync.ty) #ls)
    (swift.syncCands me v.ballot (sp.recoverSync N reps)) csv.syncRPC' iprop(True)
    $$ [$HisR2 $Hbag]
  · unfold replica.toSendP
    isplitl
    · isplitr
      · iexact Hmar
      isplitr
      · itrivial
      isplitr
      · unfold sp.msgsOk
        imodintro
        iintro %mm %Hc
        obtain ⟨m, rfl, Hmf1, Hmf2, Hmf3, -⟩ := Hc
        simp only [sp.msgOk]
        iexists sp.recoverSync N reps, N, fr, l
        rw [Hmf2, ← hw1', hw1]
        ihave #HlbM : sp.locLb γ (sp.rid m.rep) b' (sp.syncSeq (sp.recoverSync N reps)) $$ []
        · rw [Hmf1, hme, ← hL]; iexact HlbL
        iframe #
        ipureintro
        refine ⟨⟨by rw [Hmf1]; exact hme0, ?_⟩, Hmf3, ?_⟩
        · have := Hok.1; exact this
        · rw [Hmf1, hme, hL]
      isplitr
      · unfold replica.freeOk; ileft; ipureintro; rfl
      ipureintro
      refine ⟨⟨_, swift.syncWireOf me v.ballot _, rfl, rfl, rfl,
        ⟨⟨_, rfl, List.Perm.refl _⟩, ⟨_, rfl, List.Perm.refl _⟩, ⟨_, rfl, List.Perm.refl _⟩⟩,
        hfits⟩, fun mm hc => ?_⟩
      obtain ⟨m, rfl, -, -, -, h4⟩ := hc
      refine ⟨h4, ?_⟩
      rw [Hcodes.2.2.2.2.2.2.2.2.2.1]; rfl
    ipureintro
    intro mm hc
    obtain ⟨m, rfl, -⟩ := hc
    trivial
  -- the leader takes its `MSync`
  rw [← hw1', hw1]
  have hlen := sp.recoverSync_len N reps HMf.2.1
  have hsize := Hrok.size
  rw [hL]
  wp_apply (wp_hsync ls N r k ld v M0 bs hd
    (w.computed b' (sp.syncOrder (sp.recoverSync N reps))) b' (sp.recoverSync N reps))
    $$ [Hrdr Hst Hep Hsf Htoks Htix] as ⟨Hrdr, Hpost⟩
  · iframe #
    iframe Hrdr Hst Hsf
    isplitl [Hep]
    · rw [show (w.computed b' (sp.syncOrder (sp.recoverSync N reps))).2.2.1 = w.2.2.1 from rfl]
      iexact Hep
    isplitr
    · rw [hL]; iexact HlbL
    isplitl [Htoks Htix]
    · iright
      isplitr
      · ipureintro; rw [swift.LView.computed_locAt, if_pos rfl]
      iframe Htoks
      iExactEq Htix; rfl
    ipureintro
    refine ⟨?_, by omega, hb0, fun _ => ?_⟩
    · show w.2.1 ≤ w.1
      omega
    · show w.2.1 < w.1
      omega
  icases Hpost with (⟨%Hc, -, -, -⟩ | ⟨%v', %w', Hrs, HEp, Hsf, %Hw'⟩)
  · exfalso
    rw [hw1, hnorm] at Hc
    simp at Hc
  iapply HΦ
  iframe Hrdr
  iexists v', w'
  rw [hL, show decide (r = r) = true from decide_eq_true rfl]
  iframe
  ipureintro; exact Hw'


end proof

end Perennial.github_com.imdea_software.swiftpaxos
