/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/HandleSyncEntry.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**`r.handleMsg(&syncEntry{…}, desc, cmdId)`, `handleSyncEntry`** (round 48, descriptor side; table
T24, plan R11.4 (4) 4; D61 (2), D64): every Go statement of the sync-entry case of `handleMsg`
(recovery.go:707-722) from the owner state and the entry's `syncMP`.

* The ghost core first (`swift.install_sync`, SyncEntryTok.lean): the entry's `.sync` claim takes
  `x`'s row token of the new ballot out of the store (a token already at the descriptor is
  refuted): row `rvSync`, `syncIn`, and the stored closures' `storedOk2`. L2: the commit (the
  entry's `sp.accepted`) is at `ghostCommit`'s resolution after the writes: row
  `(none, none, true, true)`, `sp.committed`.
* `proposeDep`'s old writer (`pdOk`): nobody or a sync entry (`hs` nil); a proposal message's is
  refuted by the base (`swift.pdOk_sync`: `baseIs γ b B`, `0 < b`, is the `MSync`'s order, which
  holds `x`, while a proposal's `x` is not in its sequence before it, and `B` is a prefix of
  that). So `hs` is nil and the descriptor has no hashes (`dv.Hs = []`).
* The writes `propose`, `cmd`, `dep`, `proposeDep`, `phase = COMMIT`; the new `pdOk` is the sync
  disjunct.
* `repPre` at the new values (`swift.repPre_sync`): `replyPre` from `propIs` with no hashes
  (`Ps = []`), `c.wf` from `propIs`, `D`'s bound `< 2^62` (`syncSeq M`'s ids are small and
  distinct, `D ~ depsIn (syncSeq M) x`), and `ldrPrefix` from `syncMP`'s `locLb γ r b (syncSeq M)`
  (47-a, D64) with `sp.syncIs_seq` (`(x, c) ∈ syncSeq M`, `D ~ depsIn (syncSeq M) x`).
* The dependency loop (`depSpecR`, `successorsL`), as the acks handler's.
* `deliver` (`deliver.specE`) from the rebuilt owner state through `swift.descOwn_deliver`
  (`tixD`: the token's `slotT` ticket).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleDescProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncEntryTok
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleProposeProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncSeq
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GhostSteps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

/-- **The reply facts of a sync entry** (round 48; `descSt`'s `repPre` at `handleSyncEntry`): the
proposal read-only with its client id, no hashes, and the replica's sequence `s` (`locLb`, the
`MSync`'s `syncSeq`) with `x` and its dependencies, at any replica. -/
theorem swift.repPre_sync (γ : sp.Names) (N r b : Nat) (x : swift.CommandId) (dv : swift.DescV)
    (pp w mu : Loc) (addr : GoString) (s : sp.Seq)
    (hHs : dv.Hs = []) (hwf : dv.c.wf) (hD : dv.D.length < 2 ^ 62)
    (hs : (toCmdId x, dv.c) ∈ s ∧ (dv.D.map toCmdId).Perm (sp.depsIn s (toCmdId x))) :
    dv.propose ↦□ replica.defs.GPropose.mk pp w mu false addr ∗
      typedPointsto (pp.[replica.defs.Propose, go!"ClientId"]) x.ClientId' DFrac.discard ∗
      sp.locLb γ r b s ∗ swift.propIs γ dv.propose (toCmdId x) dv.c ⊢
    swift.repPre γ N r b x dv := by
  iintro ⟨#Hg, #Hcl, #Hlb, #HpI⟩
  iunfold swift.repPre
  iright
  isplitr
  · iunfold swift.replyPre
    iexists [], pp, w, mu, addr
    iframe Hg Hcl
    isplitr
    · ipureintro
      refine ⟨by rw [hHs]; rfl, ⟨by simp, fun h hh => by simp at hh⟩, by simp, hD⟩
    iright
    iexists []
    isplitr
    · iunfold sp.pathHashes
      isplitr
      · ipureintro; exact ⟨rfl, fun P hP => by simp at hP⟩
      iapply BigSepL.bigSepL_nil.2; itrivial
    ileft; ipureintro; rfl
  isplitr
  · ipureintro; exact hwf
  iframe HpI
  iunfold swift.ldrPrefix
  iright
  iexists s
  iframe Hlb
  ipureintro; exact hs

/-- **A proposal's `proposeDep` is refuted at a sync entry** (round 48): the proposal's base `B`
(`baseIs γ b B`, `0 < b`) is `b`'s `MSync`'s order, which holds `x` (the entry's `syncOrder`
index), and is a prefix of the proposal's sequence before `x`, which does not hold `x`. -/
theorem swift.propFacts_sync_false (γ : sp.Names) (N r b : Nat) (ld : Bool) (x : sp.CmdId)
    (c : sp.Cmd) (s : sp.Seq) (B D P : List sp.CmdId) (H : swift.SHash) (M : sp.SyncMsg)
    (hb : 0 < b) (hx : x ∈ sp.syncOrder M) :
    swift.propFacts γ N r b ld x c s B D P H ∗ sp.syncIs γ b M ⊢ (False : IProp netDistGF) := by
  iintro ⟨#Hf, #HsI⟩
  iunfold swift.propFacts at Hf
  icases Hf with ⟨-, #HB, -, %Hpf⟩
  obtain ⟨-, g2, -, -, -, -, -, g8, -⟩ := Hpf
  iunfold swift.baseIs at HB
  icases HB with (%Hb0 | ⟨%M', #HsI', %HB'⟩)
  · exact absurd Hb0.1 (by omega)
  iunfold sp.syncIs at HsI HsI'
  icombine HsI HsI' gives %Hag
  obtain ⟨-, hM⟩ := Hag
  subst hM
  subst HB'
  exfalso
  exact g2 (g8.subset hx)

end lemmas

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [hook.Assumptions] [github_com.orcaman.concurrent_map.Assumptions]

set_option maxHeartbeats 4000000 in
/-- **`handleMsg`'s sync entry case, `handleSyncEntry`** (see the file header). -/
theorem swift.Replica.handleMsg.wp_proofSync (RC : Loc → w32 → IProp netDistGF)
    [hRC : ∀ l bw, Persistent (RC l bw)] (MP : GoInterface → IProp netDistGF)
    (str0 : swift.CommandId → GoString)
    (wp_deliver0 : ∀ γdl, swift.Replica.deliver.specE str0 γdl MP) :
    ∀ c : swift.DC, c.str = str0 → RC = swift.RCh c.γ c.γc c.γm c.rp →
      swift.Replica.handleMsg.syncSpecIc RC MP c := by
  intro c hc hRCe γd d x b Do m
  have wp_deliver : swift.Replica.deliver.specE c.str c.γdl MP := hc ▸ wp_deliver0 c.γdl
  wp_start as ⟨#Hctx, #Hpc, #HdR, Hown, Hm⟩
  iunfold swift.syncMP at Hm
  icases Hm with ⟨%se, %gp, %cc, %vs, %dsl, %D, %M, %i, %Hm, Hse, #Hvs, #Hdsl, #Hprop, #HsI, #HlA,
    #Hacc, Hcl, #Hlb, #HlbL, %Hfacts⟩
  subst Hm
  obtain ⟨hmem, hord, hb0, hdslnn⟩ := Hfacts
  have hxO : toCmdId x ∈ sp.syncOrder M := List.mem_of_getElem? hord
  -- the context's facts
  ihave #Hctx2 := Hctx
  iunfold swift.DC.ctx at Hctx2
  iunfold swift.descCtxE at Hctx2
  icases Hctx2 with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, -, -, %Hids, -, -,
    -, #Hinv, #Hcfg, #Hninv, -⟩
  ihave #Htl : swift.takeLaw c $$ [Hpc]
  · iunfold swift.proposeCtx at Hpc; icases Hpc with ⟨-, #Htl, -⟩; iexact Htl
  -- the owner state, opened
  iunfold swift.descOwnF at Hown
  icases Hown with ⟨Hown, Hocf⟩
  iunfold swift.descOwn at Hown
  icases Hown with ⟨%msS, %msF, %qS, %qF, %szS, %szF, %memS, %memF, %hd, #HhS, #HhF, HdS, HR⟩
  iunfold swift.setR at HR
  iunfold swift.descSt at HR
  icases HR with ⟨%qe, %bw, %stp, %rcp, %dv, %rv, Hrd, Hsh, HRC, Hd, Htok, -, -, -, -, -, %Hrp, #HsB,
    ⟨HsF, HfF, HdF, ⟨Hcore, ⟨Hrest, HDo⟩⟩⟩⟩
  iunfold swift.descF at Hd
  icases Hd with ⟨Hph', Hcmd, -, Hdep, -, Hhs1, #HHs, Hprop', Hseq, Hmsgs, #Hmb, #HsL, -⟩
  iunfold swift.descRest at Hrest
  icases Hrest with ⟨%pd, %hs0, %sq0, %df, Hpd, Hsq, Hhs0, Hdf, #Hpdok⟩
  icombine Hhs1 Hhs0 gives %Hhe
  subst Hhe
  iunfold swift.descOcf at Hocf
  icases Hocf with ⟨%cf, %cond, %fs, %v, Hocfr, #Hcond, -, #Hfs⟩
  iunfold swift.ocfRes at Hocfr
  icases Hocfr with ⟨Hapf, Hocf, HPc, %sb, %bs, Hsb, Hbs, Hbsc, %Hb⟩
  iunfold swift.proposeHalf at HPc
  icases HPc with ⟨%p1, Hp1, -⟩
  icombine Hprop' Hp1 gives %Hpe
  subst Hpe
  ihave Hpf := (swift.pt_halves (swift.dfld d go!"propose") dv.propose).2 $$ [Hprop' Hp1]
  · iframe Hprop' Hp1
  -- `proposeDep`'s old writer: nobody or a sync entry (a proposal's is refuted by the base), so
  -- `hs` is nil and there are no hashes
  ihave %Hhsn : iprop(⌜dv.hs = slice.nil⌝) $$ []
  · iunfold swift.pdOk at Hpdok
    icases Hpdok with (%Hn | ⟨%cc0, %ld0, %s0, %B0, %D0, %P0, %H0, -, -, -, #Hf0, -⟩ |
      ⟨%Ds, %Hn, -, -⟩)
    · ipureintro; exact Hn.2
    · iexfalso
      iapply swift.propFacts_sync_false c.γ c.N c.r b ld0 (toCmdId x) cc0 s0 B0 D0 P0 H0 M hb0 hxO
      iframe Hf0 HsI
    · ipureintro; exact Hn.2
  ihave %HHl := ownSlice_len _ _ _ $$ HHs
  have hHs : dv.Hs = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [HHl.1, Hhsn]; rfl
  -- the ghost core: the entry's token installed and committed
  ihave ⟨%st, %fq, %szF', %memF', Hst, HFQ, #HqF, %HAQ, Henv, Hshb⟩ := swift.shOwn_openE c d b qe $$ Hsh
  iapply fupd_wp
  imod (swift.install_sync c RC MP γd d x b iprop(swift.descRest c b x d ∗ Do) dv rv qe bw stp rcp
      fs) $$ [Hrd Htok Hcl Henv] with ⟨Hrd, Henv, Htok, Hslt, #HsyIn, #Hfs2⟩
  · iframe Hctx Htl Hrd Htok Hfs Hcl Henv Hacc
  -- the `MSync` against its sequence, the command registered, `D`'s bound
  imod (sp.syncIs_seq (γc := c.γc) (γm := c.γm) (γl := c.γl) ⊤ (by simp) b M) $$ [Hinv HsI]
    with %Hseq
  · iframe Hinv HsI
  ihave #HpI := Hprop
  iunfold swift.propIs at Hprop
  icases Hprop with ⟨%pp, %w, %mu, %addr, %ts, %vsP, #Hgp, #Hpx, -, #Hcis, %Hpp⟩
  ihave Hcok := sp.cmdIs_ok (γ := c.γ) (γc := c.γc) (γm := c.γm) (γl := c.γl) (toCmdId x) cc
    $$ [Hinv Hcis]
  · iframe Hinv Hcis
  imod (fupd_mask_mono (E1 := ↑sp.spN) (E2 := ⊤) (by simp)) $$ Hcok with %Hcok
  ihave Hsm := swift.locLb_small (γ := c.γ) (γc := c.γc) (γm := c.γm) (γl := c.γl) c.r b
    (sp.syncSeq M) $$ [Hinv Hlb]
  · iframe Hinv Hlb
  imod (fupd_mask_mono (E1 := ↑sp.spN) (E2 := ⊤) (by simp)) $$ Hsm with %Hsm
  imodintro
  have Hcop : cc.op ≠ W8 3 := by
    rcases Hcok.1 with h | h
    · unfold sp.Cmd.isPut sp.opPUT at h; simp at h; rw [h]; decide
    · unfold sp.Cmd.isGet sp.opGET at h; simp at h; rw [h]; decide
  obtain ⟨hxs, hperm⟩ := Hseq.2 (toCmdId x) cc D hmem
  have hlenS : (sp.syncSeq M).length ≤ 6 * 2 ^ 32 := by
    have := swift.small_ids_len ((sp.syncSeq M).map Prod.fst)
      (by rw [Hseq.1]; exact sp.syncOrder_nodup M)
      (by intro y hy; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy; exact Hsm p hp)
    simpa using this
  have hDlen : D.length < 2 ^ 62 := by
    rw [hperm.length_eq]
    have := sp.depsIn_length (sp.syncSeq M) (toCmdId x)
    omega
  have hDD : (D.map ofCmdId).map toCmdId = D := by simp [List.map_map, Function.comp_def]
  ihave %Hgpnn := typedPointsto_not_null _ _ _ $$ Hgp
  ihave #Hpx2 := Hpx
  iStructNamedPrefix Hpx2 "PX"
  ihave #HclId : typedPointsto (pp.[replica.defs.Propose, go!"ClientId"]) x.ClientId' DFrac.discard
    $$ [PXClientId]
  · iExactEq PXClientId; rfl
  -- the writes: `propose`, `cmd`, `dep`, `proposeDep`, `phase = COMMIT`
  iStructNamedPrefix Hse "SE"
  wp_auto
  wp_method_call
  try wp_auto
  -- L2: `ghostCommit(r.ballot, cmdId)`, the commit at its resolution (`commit_dstep'` in its
  -- update, justified by the entry's `sp.accepted`)
  obtain ⟨-, -, hrN, -, -, hk⟩ := Hids
  iunfold swift.epochRd at Hrd
  icases Hrd with ⟨Hbal, HStf, Hrcf, Het, Hxe, %Hbw⟩
  ihave #Hng := swift.DC.ctx_ng c $$ Hctx
  ihave #Hcpkg : isPkgInit (PROP := IProp netDistGF)
    pkg_id.github_com.imdea_software.swiftpaxos.client $$ []
  · iPkgInit
  try wp_auto
  wp_bind (App (App (Val (@! swift.ghostCommit)) (Val _)) (Val _))
  iapply (swift.wp_ghostCommit c.γ c.k bw x iprop(swift.epochTok c.γe qe (b, b) ∗
    swift.rowTok c.γo b (toCmdId x) (swift.rvSync.1, swift.rvSync.2.1, swift.rvSync.2.2.1, true) ∗
    sp.committed c.γ c.r b (toCmdId x))) $$ [Het Htok]
  · iframe #
    isplitr
    · ipureintro; exact Hbw.2
    iunfold swift.ghostUpd
    iintro %W' Hpp
    rw [Hbw.1]
    imod (swift.commit_dstep' c.γ c.γc c.γm c.γl c.γv c.γe c.γo c.N c.r c.k fr lg qe b
        (toCmdId x) swift.rvSync hrN hk rfl W') $$ [Het Htok Hpp] with ⟨Het, Htok, Hpost, #Hc⟩
    · iframe Hinv Hcfg Hninv Het Htok Hpp
      iright; ileft; iexact Hacc
    imodintro
    iframe Hpost Het Htok Hc
  inext
  iintro ⟨Het, Htok, #Hcm⟩
  ihave Hrd : swift.epochRd c.γe c.γxe c.rp c.rr qe b bw stp rcp $$ [Hbal HStf Hrcf Het Hxe]
  · iunfold swift.epochRd; iframe Hbal HStf Hrcf Het Hxe; ipureintro; exact Hbw
  ihave Htok : swift.rowTok c.γo b (toCmdId x) (none, none, true, true) $$ [Htok]
  · rw [show ((none, none, true, true) : swift.RowV) =
        (swift.rvSync.1, swift.rvSync.2.1, swift.rvSync.2.2.1, true) from rfl]
    iexact Htok
  try wp_auto
  icases (swift.pt_halves (swift.dfld d go!"propose") gp).1 $$ Hpf with ⟨Hprop, Hp1⟩
  -- the dependency loop (as the acks handler's): `x` a successor of each dependency's descriptor
  ihave %HDlen := ownSlice_len _ _ _ $$ Hdsl
  ihave Hsh := Hshb $$ Hst HFQ Henv
  iunfold swift.shOwn at Hsh
  icases Hsh with ⟨Hshe, HshR⟩
  ihave HL : (∃ (i : w64) (dcid : swift.CommandId),
      "i" ∷ i_ptr ↦ i ∗ "dcid" ∷ d_ptr ↦ dcid ∗
      "Hrd" ∷ swift.epochRd c.γe c.γxe c.rp c.rr qe b bw stp rcp ∗
      "HshR" ∷ swift.shOwnR c d b qe ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ (D.map ofCmdId).length⌝ : IProp netDistGF)
    $$ [i d Hrd HshR]
  · iexists (W64 0), _
    iframe
    ipureintro; exact ⟨by decide, by simp⟩
  wp_for HL
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z dsl.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif) | simpa using Hif
    have hiD : sint.nat i < (D.map ofCmdId).length := by rw [HDlen.1]; word
    obtain ⟨dj, hdj⟩ : ∃ dj, (D.map ofCmdId)[sint.nat i]? = some dj :=
      ⟨(D.map ofCmdId)[sint.nat i], List.getElem?_eq_getElem hiD⟩
    have hbi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z dsl.len := ⟨Hi.1, hlt⟩
    rw [if_pos hbi]
    wp_apply wp_load_slice_index (t := swift.CommandId.ty) dsl (sint.Z i) (D.map ofCmdId) _ dj Hi.1
      $$ [Hdsl] as -
    · iframe Hdsl; ipureintro; exact hdj
    ihave #HdR' := HdR
    iunfold swift.depSpecR at HdR'
    ihave #Hgcd := HdR' $$ %d %qe %b %bw %stp %rcp %dj
    wp_apply Hgcd $$ [Hrd HshR] as %dd ⟨Hrd, HshR, Hdd⟩
    · iframe Hrd Hctx HshR
    wp_if_destruct
    · wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro; exact ⟨by word, by word⟩
    icases Hdd with (%Hnull | #HdL)
    · exact absurd Hnull Hif
    wp_apply sync.Mutex.wp_Lock $$ [$HdL] as ⟨HdLk, HS⟩
    iunfold swift.succInv at HS
    icases HS with ⟨%ssl, %sl0, Hsucc, Hssl, Hsslcap⟩
    wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType swift.CommandId.ty))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := swift.CommandId) (t := swift.CommandId.ty) [x]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %lsl ⟨Hlsl, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [Hssl Hsslcap Hlsl] as %nsl ⟨Hssl, Hsslcap, -⟩
    · iframe
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$HdL $HdLk Hsucc Hssl Hsslcap]
    · iunfold swift.succInv; iexists _, _; iframe
    try wp_auto
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro; exact ⟨by word, by word⟩
  -- the loop's exit (L2: with the client package imported, `wp_if_destruct` leaves the
  -- condition as a value equality)
  have hnI : ¬ sint.Z i < sint.Z dsl.len := by
    first | exact Hif | simpa using Hif | exact fun h => Hif (by simp [h])
  try rw [show decide (sint.Z i < sint.Z dsl.len) = false from decide_eq_false hnI]
  try rw [if_pos (decide_eq_true rfl)]
  -- the owner state at the new values
  let dv' : swift.DescV := { dv with propose := gp, c := cc, vs := vs, dep := dsl, D := D.map ofCmdId, phase := swift.phCOMMIT }
  let rv' : swift.RowV := (none, none, true, true)
  have hrp' : swift.rowPhaseOk c.N c.r b dv' rv' := by
    unfold swift.rowPhaseOk
    simp only [dv', rv', swift.phCOMMIT]
    refine ⟨fun h => absurd h Hgpnn, fun _ => ⟨by decide, fun h0 => absurd h0 (by decide),
      fun h0 => absurd h0 (by decide), fun h0 => absurd h0 (by decide), fun _ => by decide,
      fun _ => Or.inl (by decide)⟩⟩
  ihave #HrP' : swift.repPre c.γ c.N c.r b x dv' $$ []
  · iapply (swift.repPre_sync c.γ c.N c.r b x dv' pp w mu addr (sp.syncSeq M) hHs Hpp.1
      (by show (D.map ofCmdId).length < 2 ^ 62; rw [List.length_map]; exact hDlen)
      ⟨hxs, by show ((D.map ofCmdId).map toCmdId).Perm _; rw [hDD]; exact hperm⟩)
    iframe Hgp HclId Hlb HpI
  ihave HDo : iprop(swift.descRest c b x d ∗ Do) $$ [Hpd Hsq Hhs0 Hdf HDo]
  · iframe HDo; iunfold swift.descRest; iexists dsl, dv.hs, sq0, df
    iframe Hpd Hsq Hhs0 Hdf
    iunfold swift.pdOk
    iright; iright
    iexists D
    iframe Hdsl Hacc
    isplitr
    · ipureintro; exact ⟨hdslnn, Hhsn⟩
    -- round 58 (D82 (2)): the entry's `MSync` and the replica's prefix `syncSeq M`
    iexists M
    iframe HsI Hlb
    ipureintro
    exact ⟨List.mem_map.mpr ⟨_, hxs, rfl⟩, fun d' hd' => hperm.subset hd', hDlen⟩
  ihave Hown : swift.descOwn c RC MP γd d x b
      iprop(swift.descCore c d x b ∗ (swift.descRest c b x d ∗ Do))
      $$ [HdS Hrd Hshe HshR HRC Htok Hslt HsF HfF HdF Hcore HDo Hph' Hcmd Hdep Hhs1 Hprop Hseq Hmsgs]
  · iunfold swift.descOwn
    iexists msS, msF, qS, qF, szS, szF, memS, memF, hd
    iframe HhS HhF HdS
    iunfold swift.setR
    iunfold swift.descSt
    iexists qe, bw, stp, rcp, dv', rv'
    simp only [if_true, ↓reduceIte]
    ihave Htok := swift.rowTokO_of2 c b x dv' rv' $$ Htok Hslt
    iframe HRC Htok HsB HsF HfF HdF Hcore HDo HrP' Hrd
    isplitl [Hshe HshR]
    · iunfold swift.shOwn; iframe Hshe HshR
    isplitl [Hph' Hcmd Hdep Hhs1 Hprop Hseq Hmsgs]
    · iunfold swift.descF
      iframe Hcmd Hdep Hhs1 Hprop Hseq Hmsgs Hvs Hdsl HHs Hmb HsL
      isplitl [Hph']
      · iExactEq Hph'; rfl
      ipureintro; exact Hcop
    isplitr
    · iright; iexact Hcm
    isplitr
    · iunfold swift.rowAcc
      isplitr
      · iright; iexact Hacc
      isplitr
      · ipureintro; intro _; exact Hgpnn
      iright; iexists _; iexact Hgp
    isplitr
    · ipureintro; intro _; left; rfl
    isplitr
    · iapply swift.phaseWhy_ne1; show swift.phCOMMIT ≠ W64 1; unfold swift.phCOMMIT; decide
    isplitr
    · -- round 54 (D74 (2), 53-4): at the leader the sync disjunct; at a follower the leader's
      -- prefix (`syncMP`'s leader `locLb` of `syncSeq M`, `D ~ depsIn (syncSeq M) x`)
      iunfold swift.depWhy
      by_cases hl : c.r = sp.leaderOf c.N b
      · iright; iright; ileft
        isplitr
        · ipureintro; exact ⟨hl, rfl⟩
        iexact HsyIn
      · iright; iright; iright
        isplitr
        · ipureintro; exact hl
        iexists D
        isplitr
        · iunfold sp.locDeps
          iexists sp.syncSeq M
          iframe HlbL
          ipureintro
          exact ⟨List.mem_map.mpr ⟨_, hxs, rfl⟩, hperm⟩
        ipureintro
        show ((D.map ofCmdId).map toCmdId).Perm D
        rw [hDD]
    ipureintro; exact ⟨hrp', Hrp.2⟩
  ihave Hocfr : swift.ocfRes d cf cond fs true $$ [Hapf Hocf Hp1 Hsb Hbs Hbsc]
  · iunfold swift.ocfRes; iframe Hapf Hocf
    isplitl [Hp1]
    · iunfold swift.proposeHalf; iexists gp; iframe Hp1; ipureintro; simp [Hgpnn]
    iexists sb, bs; iframe Hsb Hbs Hbsc; ipureintro; exact Hb
  -- `r.deliver(desc, cmdId)`
  ihave ⟨%q, %bw', %stp', %rcp', %dv'', %Rs, %Rk, Hrd, HrdR, Hpin, #HRC', #HsB', Hd, HRs, HRk, Hcf,
    #Hwhy, #Hrep, Htix, Hsl, Hback, Hgone⟩ :=
    swift.descOwn_deliver c RC MP γd d x b iprop(swift.descCore c d x b ∗ (swift.descRest c b x d ∗ Do))
      cf cond fs true $$ [Hown Hocfr]
  · iframe Hown Hocfr
  ihave #HRCh : swift.RCh c.γ c.γc c.γm c.rp rcp' bw' $$ []
  · rw [← hRCe]; iexact HRC'
  wp_apply (wp_deliver c.γ c.γc c.γm c.γl c.γw c.γv c.γe c.γo c.γx c.γxe c.γxm c.γxp c.γxu c.γrp c.γcg c.γout c.γcl
      c.γdc γd c.rp c.rr d c.N c.r c.k q q b bw' stp' rcp' dv'' x Rs
      iprop(⌜c.sq = true⌝ ∗ c.ret d x ∗ c.env d q)) $$ [Hrd HrdR Hpin Hd HRs Hcf Htix Hsl] as %fin Hfin
  · iframe Hrd HrdR Hpin HRCh HsB' Hd HRs Hcf Hwhy Hrep Htix Hsl
    iunfold swift.DC.ctx at Hctx; iexact Hctx
  icases Hfin with ⟨Hrd, HrdR, Hpin, Hfin⟩
  try wp_auto
  cases fin
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hfin with ⟨Hd, HRs, Htix⟩
    ihave ⟨Hown, Hocfr⟩ := Hback $$ Hrd HrdR Hpin Hd HRs Htix HRk
    iapply HΦ; ileft; iunfold swift.descOwnF; iframe Hown
    iunfold swift.descOcf; iexists cf, cond, fs, true; iframe Hocfr Hcond Hfs
    iunfold swift.ocfV; iright; iexact Hfs2
  · simp only [↓reduceIte]
    icases Hfin with ⟨#Hex, HRet⟩
    iapply HΦ; iright
    iunfold swift.descDone
    iapply Hgone $$ Hrd HrdR Hpin HRk Hex HRet

end proof

end Perennial.github_com.imdea_software.swiftpaxos
