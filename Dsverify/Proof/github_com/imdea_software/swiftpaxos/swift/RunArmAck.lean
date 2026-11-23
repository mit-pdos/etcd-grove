/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RunArmAck.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The run loop's `ackHash` arm (round 19, sv-swc; change log C22, M3): `r.leaderAckHash(f)` over
`swift.runInv` (RunInvD.lean): an ack of this ballot's leader (not this replica) goes to
`recordLeaderHash` (`swift.Replica.recordLeaderHash.specT`, RecordLeaderHash.lean), its witness
(`runAckW`: the leader's number `numIs`, path `pathIs` and the path's hash) from the ack's
`fastAckOk`, or `ackOk` of an `MOptAcks` entry (a slow entry is not the leader's, C16).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunInvD
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecordLeaderHash
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.LeaderM
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Leader
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.BeTheLeader
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.HandlerInv

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

/-- One path's hashes: one hash, its start hash. -/
theorem swift.pathHashes_one (P : List sp.CmdId) (cs : List sp.Hash) :
    sp.pathHashes [P] cs ⊢ ∃ h, ⌜cs = [h]⌝ ∗ sp.startHash P h := by
  iintro H
  iunfold sp.pathHashes at H
  icases H with ⟨%Hl, Hb⟩
  icases BigSepL.bigSepL_cons.1 $$ Hb with ⟨⟨%h, %Hh, Hs⟩, -⟩
  iexists h
  iframe Hs
  ipureintro
  match cs, Hl.1, Hh with
  | [h'], _, Hh => simp at Hh; rw [Hh]

/-- **The leader's ack's witness** (change log C22): from `runAckW` of an ack of ballot
`bal f.bal`'s leader, its number, path and the path's hash. -/
theorem swift.runAckW_lead0 (γ : sp.Names) (γc γm : GName) (N : Nat) (fr : Bool)
    (l : List GoString) (f : sp.FastAck) (hL : sp.rid f.rep = sp.leaderOf N (sp.bal f.bal)) :
    sp.cfg γc γm N fr l ∗ swift.runAckW γ γc γm f ⊢
      ∃ (P : List sp.CmdId) (h : sp.Hash),
        sp.numAck γ (sp.rid f.rep) (sp.bal f.bal) f.id f.seqnum ∗
        sp.pathIs γ (sp.rid f.rep) (sp.bal f.bal) f.id P ∗ sp.startHash P h ∗ ⌜f.cs = [h]⌝ := by
  iintro ⟨#Hcfg, #Hw⟩
  iunfold swift.runAckW at Hw
  icases Hw with (#Hf | ⟨%a, %Ha, #Hack, #Hdis⟩)
  · iunfold sp.fastAckOk at Hf
    icases Hf with ⟨-, -, %P, #Hpath, #Hph, #Hnum, -⟩
    ihave ⟨%h, %Hh, #Hs⟩ := swift.pathHashes_one P f.cs $$ Hph
    iexists P, h
    iframe Hnum Hpath Hs
    ipureintro; exact Hh
  · obtain ⟨Hf, -⟩ := Ha
    have e1 : f.id = a.id := by rw [Hf]; rfl
    have e2 : f.seqnum = a.seqnum := by rw [Hf]; rfl
    have e3 : f.cs = a.cs := by rw [Hf]; rfl
    rw [e1, e2, e3]
    by_cases hd : a.dep = [a.id]
    · icases Hdis with (%Hne | ⟨%N', %fr', %l', #Hcfg', %Hne⟩)
      · exact absurd hd Hne
      · ihave %Hag := sp.cfg_agree (γc := γc) (γm := γm) N N' fr fr' l l' $$ [Hcfg Hcfg']
        · isplitl []
          · iexact Hcfg
          · iexact Hcfg'
        obtain ⟨rfl, -, -⟩ := Hag
        exact absurd hL Hne
    · have hA : sp.ackOk γ (sp.rid f.rep) (sp.bal f.bal) a ⊢ iprop(
          sp.preacc γ (sp.rid f.rep) (sp.bal f.bal) a.id a.dep ∗
          ∃ P, sp.pathIs γ (sp.rid f.rep) (sp.bal f.bal) a.id P ∗ sp.pathHashes [P] a.cs ∗
            sp.numAck γ (sp.rid f.rep) (sp.bal f.bal) a.id a.seqnum ∗
            sp.locDeps γ (sp.rid f.rep) (sp.bal f.bal) a.id a.dep) := by
        unfold sp.ackOk; rw [if_neg hd]
      ihave #Hack2 := hA $$ Hack
      icases Hack2 with ⟨-, %P, #Hpath, #Hph, #Hnum, -⟩
      ihave ⟨%h, %Hh, #Hs⟩ := swift.pathHashes_one P a.cs $$ Hph
      iexists P, h
      iframe Hnum Hpath Hs
      ipureintro; exact Hh

/-- **The leader's ack's witness** (decisions D22/D23): `runAckW_lead0` with the leader's number
(`numAck` at the leader: its numbers are non-negative, `sp.num_nonneg`). -/
theorem swift.runAckW_lead (E : CoPset) (hE : ↑sp.spN ⊆ E) (γ : sp.Names) (γc γm γl : GName)
    (N : Nat) (fr : Bool) (l : List GoString) (f : sp.FastAck)
    (hL : sp.rid f.rep = sp.leaderOf N (sp.bal f.bal)) :
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗ swift.runAckW γ γc γm f ⊢
      |={E}=> ∃ (P : List sp.CmdId) (h : sp.Hash),
        sp.numIs γ (sp.rid f.rep) (sp.bal f.bal) f.id f.seqnum ∗
        sp.pathIs γ (sp.rid f.rep) (sp.bal f.bal) f.id P ∗ sp.startHash P h ∗ ⌜f.cs = [h]⌝ := by
  iintro ⟨#Hinv, #Hcfg, #Hw⟩
  ihave ⟨%P, %h, #Hna, #Hpath, #Hsh, %Hcs⟩ := swift.runAckW_lead0 γ γc γm N fr l f hL $$ [Hcfg Hw]
  · iframe Hcfg Hw
  iunfold sp.numAck at Hna
  icases Hna with ⟨%s', #Hn, %Hs'⟩
  rcases Hs' with rfl | hneg
  · imodintro
    iexists P, h
    iframe Hn Hpath Hsh
    ipureintro; exact Hcs
  · ihave Hn2 : sp.numIs γ (sp.leaderOf N (sp.bal f.bal)) (sp.bal f.bal) f.id s' $$ [Hn]
    · rw [← hL]; iexact Hn
    imod sp.num_nonneg E hE N fr l (sp.bal f.bal) f.id s' $$ [Hinv Hcfg Hn2] with %H0
    · iframe Hinv Hcfg Hn2
    rw [hneg] at H0
    exact absurd H0 (by decide)

end lemmas

section arm
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

/-- **The `ackHash` arm** (change log C22, M3): `r.leaderAckHash(f)`: an acknowledgement of this
ballot's leader, not this replica, goes to `recordLeaderHash` (`specT`, as a follower; its
witness from `runAckW_lead`). -/
theorem swift.runArm_ackHash (wp_Leader : replica.Leader.spec)
    (wp_record : swift.Replica.recordLeaderHash.specT (hG := hG))
    (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (l : Loc) (fa : swift.MFastAck)
    (f : sp.FastAck) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
        swift.runInv rp γ γc γm x ∗
        l ↦□ fa ∗ swift.fastAckRepr fa f ∗ swift.runAckW γ γc γm f }}
      (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"leaderAckHash")) (Val #l))
    {{ RET #(); swift.runInv rp γ γc γm x }} := by
  wp_start as ⟨HI, #Hl, #Hrepr, #Hw⟩
  ihave ⟨#Hctx, HI⟩ := BI.persistent_entails_right (swift.runInv_ctx rp γ γc γm x) $$ HI
  iunfold swift.runInv at HI
  icases HI with ⟨#Hd, Hs, Hrl, ⟨%ld, %v, %M, %bs, %hd, %w, Hrun, Hpd, %Hn⟩, Hseq, Hdr, Hrf, Hds⟩
  iunfold swift.runCtxD at Hctx
  icases Hctx with ⟨%rr, %me, %fr, %l', %dm, #Hrr, #Hrep, %Hids, #Hinv, #Hcfg, -, -, -, -, -⟩
  ihave #Hrep2 := Hrep
  iunfold replica.isReplica at Hrep2
  icases Hrep2 with ⟨%lg, %cfgp, %tbl, %pc, %fr', %nid, %ents, %γpc, %pwsl, %alsl, %latsl,
    %pws, %cwm, #Hlg, #Hq, #HN, #Hid, -⟩
  iunfold swift.runSt at Hrun
  icases Hrun with ⟨Hbal, Hcbal, Hstat, Hhd, Hhdsl, Hhdcap, Hpf, Hprops, Hkf, Hkeys, Hhf, HhlogE,
    Hpendf, Hpend, Hlsf, #Hls, Hgv, #Hlb, %Hok⟩
  iunfold swift.fastAckRepr at Hrepr
  icases Hrepr with ⟨%Hfa, #Hdep, #Hcs⟩
  obtain ⟨Hfrep, Hfbal, Hfid, Hfsq⟩ := Hfa
  have hloc := Hok.1
  obtain ⟨hb0, -, hw1, -, -, hnw, -, -, -, -, hldr, -⟩ := hloc
  have hNr : 1 ≤ x.N ∧ x.N < 2 ^ 31 := ⟨Hids.2.2.2.1, by have := Hids.2.2.2.2.1; omega⟩
  have hme0 : 0 ≤ me.toInt := Hids.2.1
  -- the run loop's invariant back, with the hash logs and the pending entries changed
  ihave Hback : (∀ (hM' : GMap w64 Loc) (pdM' : GMap swift.CommandId Loc),
      typedPointsto (swift.fld rp go!"ballot") v.ballot (DFrac.own (1 : Qp).half.half) -∗
      swift.fld rp go!"hlog" ↦ v.hlog -∗
      (∃ Λ, swift.hlogOwn v.hlog hM' ld hd (swift.propsK v.propsM) Λ ∗
        swift.ldSound γ (sp.leaderOf x.N w.2.1) w.2.1 Λ) -∗
      swift.fld rp go!"proposes" ↦ v.props -∗ swift.propsOwn γ v.props v.propsM -∗
      swift.fld rp go!"pendingHashUpds" ↦ v.pend -∗
      swift.pendOwnH γ (sp.leaderOf x.N w.2.1) w.2.1 v.pend pdM' -∗
      swift.runInv rp γ γc γm x) $$ [Hd Hs Hrl Hseq Hdr Hrf Hpd Hds Hcbal Hstat Hhd Hhdsl Hhdcap Hkf Hkeys Hlsf Hgv]
  · iintro %hM' %pdM' Hbal Hhf HhlogE Hpf Hprops Hpendf Hpend
    iunfold swift.runInv
    iframe Hd Hs Hrl Hseq Hdr Hrf Hds
    iexists ld, { v with hlogM := hM', pendM := pdM' }, M, bs, hd, w
    isplitr [Hpd]
    · iunfold swift.runSt
      iframe
      iframe Hls Hlb
      ipureintro; exact Hok
    · iframe Hpd; ipureintro; exact Hn
  ihave #Hl2 := Hl
  iStructNamed Hl2
  wp_auto
  wp_apply (swift.Replica.wp_leader wp_Leader rp rr v.ballot _ x.N
    ⟨Hids.2.2.2.1, Hids.2.2.2.2.1⟩) $$ [$Hbal $Hrr $HN] as Hbal
  wp_if_destruct
  · wp_apply (swift.Replica.wp_leader wp_Leader rp rr v.ballot _ x.N
      ⟨Hids.2.2.2.1, Hids.2.2.2.2.1⟩) $$ [$Hbal $Hrr $HN] as Hbal
    wp_if_destruct
    · iapply HΦ
      ihave HI := Hback $$ %v.hlogM %v.pendM Hbal Hhf HhlogE Hpf Hprops Hpendf Hpend
      iexact HI
    · wp_if_destruct
      · -- an acknowledgement of this ballot's leader, not this replica: `recordLeaderHash`
        rename_i h1 h2
        have h3 := Hif
        have hLs := swift.srem_nonneg v.ballot x.N ⟨Hids.2.2.2.1, Hids.2.2.2.2.1⟩ hb0
        have hL : sp.rid f.rep = sp.leaderOf x.N (sp.bal f.bal) := by
          rw [← Hfrep, ← Hfbal, h1, h3]
          exact (replica.leader.srem_leader v.ballot x.N hNr hb0 _ hLs.1).mp rfl
        have hld : ld = false := by
          cases h : ld
          · rfl
          · exfalso; apply h2
            refine ((replica.leader.srem_leader v.ballot x.N hNr hb0 _ hme0).mpr ?_).symm
            rw [Hids.1, ← hw1, ← hnw Hn]; exact (hldr.mp h).symm
        subst hld
        have hbw : sp.bal f.bal = w.2.1 := by rw [← Hfbal, h3, hnw Hn, hw1]
        ihave Hlead := swift.runAckW_lead ⊤ (by simp) γ γc γm x.γl x.N fr l' f hL $$ [Hinv Hcfg Hw]
        · iframe Hinv Hcfg Hw
        iapply fupd_wp
        imod Hlead with ⟨%P, %h, #Hnum, #Hpath, #Hsh, %Hcsh⟩
        imodintro
        ihave #Hcs1 : fa.Checksum' ↦*□ [swift.handler.shashOf h] $$ [Hcs]
        · rw [Hcsh]; simp only [List.map_cons, List.map_nil]; iexact Hcs
        ihave #Hsh1 : sp.startHash P (swift.handler.shashOf h).H'.arr $$ [Hsh]
        · rw [show (swift.handler.shashOf h).H'.arr = h from rfl]; iexact Hsh
        rw [hL, hbw, ← Hfid, ← Hfsq]
        icases HhlogE with ⟨%Λ, Hhlog, #HΛ⟩
        wp_apply (wp_record γ γc γm x.γl x.N fr l' rp v.hlog v.props v.pend v.hlogM v.propsM
            v.pendM hd Λ w.2.1 fa.CmdId' fa.Seqnum' fa.Checksum' (swift.handler.shashOf h) P)
          $$ [Hhf Hhlog Hpf Hprops Hpendf Hpend]
          as %hM' %pdM' %Λ' ⟨Hhf, Hhlog, #HΛ', Hpf, Hprops, Hpendf, Hpend, -⟩
        · iframe Hhf Hhlog Hpf Hprops Hpendf Hpend Hinv Hcfg HΛ Hcs1 Hsh1 Hnum Hpath
        ihave HE : (∃ Λ, swift.hlogOwn v.hlog hM' false hd (swift.propsK v.propsM) Λ ∗
            swift.ldSound γ (sp.leaderOf x.N w.2.1) w.2.1 Λ) $$ [Hhlog]
        · iexists Λ'; iframe Hhlog HΛ'
        iapply HΦ
        ihave HI := Hback $$ %hM' %pdM' Hbal Hhf HE Hpf Hprops Hpendf Hpend
        iexact HI
      · iapply HΦ
        ihave HI := Hback $$ %v.hlogM %v.pendM Hbal Hhf HhlogE Hpf Hprops Hpendf Hpend
        iexact HI
  · iapply HΦ
    ihave HI := Hback $$ %v.hlogM %v.pendM Hbal Hhf HhlogE Hpf Hprops Hpendf Hpend
    iexact HI

end arm

end Perennial.github_com.imdea_software.swiftpaxos
