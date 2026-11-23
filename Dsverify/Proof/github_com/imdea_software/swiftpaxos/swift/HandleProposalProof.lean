/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/HandleProposalProof.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The proof of `r.handleProposal(propose)` (spec: Proof/swift/HandleProposal.lean), over its
callees' specs (Proof/swift/RunSpecs.lean).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GhostSteps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleProposal
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Fatal
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ConnDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.LeaderM
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleStep
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SeqBound
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.IdBound
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecordLeaderHashDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleStepN
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.LeaderDefs
@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [github_com.orcaman.concurrent_map.Assumptions]
  [sync.Assumptions]

theorem swift.ownSlice_halves {V : Type} [ZeroVal V] [TypedPointsto (GF := netDistGF) V]
    (s : GoSlice) (vs : List V) :
    (s ↦* vs : IProp netDistGF) ⊢ s ↦*{DFrac.own (1 : Qp).half} vs ∗ s ↦*{DFrac.own (1 : Qp).half} vs := by
  have h := (ownSlice_fractional (GF := netDistGF) s vs).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h.1


theorem swift.Replica.handleProposal.wp_proofN
    (wp_String : swift.CommandId.String.specI)
    (wp_HasV : ∀ dm γdl, swift.cmapHasV.spec dm γdl)
    (wp_getDep : swift.Replica.getDepAndHashes.specI)
    (wp_record : swift.Replica.recordLeaderHash.specT)
    (DS : sp.Names → GName → GName → Nat → Nat → Loc → IProp netDistGF)
    (wp_getDesc : swift.Replica.getCmdDescWith.propSpecIN DS)
    (wp_Leader : replica.Leader.spec)
    (wp_Fatal : dlog.Logger.Fatal.spec (GF := netDistGF) (hG := hG)) :
    swift.Replica.handleProposal.specIN DS := by
  intro γ γc γm γl γw γv γe γo sn γdl rp gp N r k ld v M bs hd w
  haveI := swift.hlog.cmdId_intoValInj (sem := sem)
  wp_start as ⟨#Hctx, Hrdr, Hrun, Hseq, Hdesc, Hpd, Hprop, %Hnorm⟩
  iunfold swift.runCtxD at Hctx
  icases Hctx with ⟨%rr, %me, %fr, %l, %dm, #Hrr, #Hrep, %Hids, #Hinv, #Hcfg, #Hninv, #Hdm,
    #Hcm, ⟨%γx, %γxp, %γxm, %γa, %γxe, %γrm, %str0, #HdI⟩, ⟨%dmc, %γn, %dd, #HcntL⟩, #Hng⟩
  ihave #Hrep2 := Hrep
  iunfold replica.isReplica at Hrep2
  icases Hrep2 with ⟨%lg, %cfgp, %tbl, %pc, %fr', %nid, %ents, %γpc, %pwsl, %alsl, %latsl, %pws,
    %cwm, #Hlg, #Hq, #HN, #Hid, -⟩
  iunfold swift.runSt at Hrun
  icases Hrun with ⟨Hbal, Hcbal, Hstat, Hhd, Hhdsl, Hhdcap, Hpf, Hprops, Hkf, Hkeys, Hhf, HhlogE,
    Hpendf, Hpend, Hlsf, #Hls, Hw, #Hlb, %Hok⟩
  iunfold sp.proposeP at Hprop
  icases Hprop with ⟨%p, %wr, %mu, %addr, %seq, %cl, %c, %ts, %vs, #Hgp, #Hp, #Hvs, #Hc, %Hwf⟩
  ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hp
  -- D16: the proposal is read-only; the run loop and the descriptor share `propIs`
  ihave #Hpi : swift.propIs γ gp (toCmdId ⟨cl, seq⟩) c $$ []
  · iunfold swift.propIs
    iexists p, wr, mu, addr, ts, vs
    simp only [toCmdId]
    iframe Hgp Hp Hvs Hc
    ipureintro; exact ⟨Hwf, Hpnn⟩
  ihave #Hgp2 := Hgp
  iStructNamed Hgp2
  ihave #Hp2 := Hp
  iStructNamed Hp2
  wp_auto
  iunfold swift.propsOwn at Hprops
  icases Hprops with ⟨Hpm, Hpents⟩
  have hx : ({ ClientId' := ({ ClientId' := cl, SeqNum' := (Perennial.zero_val swift.CommandId).SeqNum' } : swift.CommandId).ClientId', SeqNum' := seq } : swift.CommandId) = ⟨cl, seq⟩ := rfl
  rw [hx]
  wp_apply wp_map_lookup2 $$ [$Hpm] as Hpm
  wp_if_destruct
  · -- a duplicate: nothing changes
    iapply HΦ
    iexists v, hd, w
    iframe Hdesc Hrdr Hpd Hseq
    isplitl
    · iunfold swift.runSt; iunfold swift.propsOwn
      iframe; isplitr
      · iexact Hls
      isplitr
      · iexact Hlb
      · ipureintro; exact Hok
    · ipureintro; exact ⟨rfl, rfl, Hnorm⟩
  · wp_apply wp_String $$ [$cmdId] as %str cmdId
    iunfold swift.runReader at Hrdr
    icases Hrdr with ⟨%dm', #Hdm', Hrd⟩
    ihave %Hdmeq : ⌜dm' = dm⌝ $$ [Hdm Hdm']
    · iapply typedPointsto_agree_wand _ _ _ _ _ $$ Hdm' Hdm
    subst Hdmeq
    wp_method_call
    wp_auto
    wp_apply (wp_HasV _ γdl _ ((⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ (↑swift.delivN : CoPset))
        (fun _ => iprop(True))) $$ [$Hrd] as %dl ⟨Hrd, -⟩
    · imod (inv_acc (E := ⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) (N := swift.delivN)
        swift.delivN_sub) $$ HdI with ⟨Hi, Hclose⟩
      iunfold swift.delivInv at Hi
      icases Hi with ⟨%M', %bX', %X', %Mx, %rm, >HV, >HXi, >HXeD, >HMx, >HXx, >%HM⟩
      imodintro
      iexists M'
      iframe HV
      iintro HV
      imod Hclose $$ [HV HXi HXeD HMx HXx] with -
      · inext; iunfold swift.delivInv; iexists M', bX', X', Mx, rm; iframe; ipureintro; exact HM
      imodintro
      itrivial
    ihave Hrdr : swift.runReader rp γdl $$ [Hrd]
    · iunfold swift.runReader; iexists _; iframe Hrd; iassumption
    cases dl
    · wp_auto
      -- x is new in the replica's sequence
      have e1 : (bs ++ hd).map Prod.fst = w.locAt w.2.1 := by
        obtain ⟨hlo, hhd, hbs⟩ := Hok
        rw [List.map_append, hhd, hbs, hlo.2.2.2.2.2.2.2.1]
      have hxn : toCmdId ⟨cl, seq⟩ ∉ (bs ++ hd).map Prod.fst := by
        intro hm
        obtain ⟨hlo, hhd, hbs⟩ := Hok
        rw [e1] at hm
        have := hlo.2.2.2.2.2.2.2.2.1 _ hm
        simp [ofCmdId, toCmdId] at this
        simp_all
      have hxn' : toCmdId ⟨cl, seq⟩ ∉ w.locAt w.2.1 := by rw [← e1]; exact hxn
      wp_apply wp_mapInsert $$ [$Hpm] as Hpm
      wp_bind (App (Val (GoInstruction (CompositeLiteral
        (go.GoType.SliceType swift.CommandId.ty)))) (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := swift.CommandId) (t := swift.CommandId.ty) [⟨cl, seq⟩]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %lsl ⟨Hlsl, -⟩
      wp_auto
      wp_apply wp_slice_append $$ [Hhdsl Hhdcap Hlsl] as %nsl ⟨Hhdsl, Hhdcap, -⟩
      · iframe
      iapply fupd_wp
      ihave Hcok := sp.cmdIs_ok (γ := γ) (γc := γc) (γm := γm) (γl := γl) ⟨cl, seq⟩ c $$ [Hinv Hc]
      · iframe Hinv Hc
      imod (fupd_mask_mono (E1 := ↑sp.spN) (E2 := ⊤) (by simp)) $$ Hcok with %Hcok
      ihave Hcl := swift.locLb_cl (γ := γ) (γc := γc) (γm := γm) (γl := γl) r w.2.1 (bs ++ hd)
        $$ [Hinv Hlb]
      · iframe Hinv Hlb
      imod (fupd_mask_mono (E1 := ↑sp.spN) (E2 := ⊤) (by simp)) $$ Hcl with %Hcl
      -- round N6: the ids are small (`proposeDeps`' bound, D75 (2)/(3))
      ihave Hsm := swift.locLb_small (γ := γ) (γc := γc) (γm := γm) (γl := γl) r w.2.1 (bs ++ hd)
        $$ [Hinv Hlb]
      · iframe Hinv Hlb
      imod (fupd_mask_mono (E1 := ↑sp.spN) (E2 := ⊤) (by simp)) $$ Hsm with %Hsm
      imodintro
      icases HhlogE with ⟨%Λ, Hhlog, #HΛ⟩
      wp_apply wp_getDep $$ [$Hkf $Hkeys $Hhf $Hhlog] as %dep %hs %kM' %hM' %P %H
        ⟨Hkf, Hkeys, Hhf, Hhlog, Hdep, Hdepcap, Hhs, Hhscap, #HP, %HPok, %Hdnn⟩
      · ipureintro
        -- SWB-7: the sequence is duplicate-free (`localOk`) and registered (`locLb`): shorter
        -- than 2^63 - 1
        refine ⟨hxn, ?_, Hcok.1, swift.seq_len_bound _ ?_ Hcl⟩
        · unfold swift.propsK; simp only [ofCmdId, toCmdId]; simp_all
        rw [e1]; exact Hok.1.2.2.2.2.2.2.2.2.2.2.2.1
      -- P4: the dependencies and hashes become read-only (shared by `proposeDeps` and the
      -- proposal message); `proposeDeps[x] = dep`
      imod ownSlice_persist $$ Hdep with #Hdep
      imod ownSlice_persist $$ Hhs with #Hhs
      -- round N6 (D75 (3)): `proposeDeps[x]` is `x`'s dependencies in the new sequence
      have hpdOk : swift.propDepOk (bs ++ hd ++ [(toCmdId ⟨cl, seq⟩, c)]) ⟨cl, seq⟩
          ((sp.lkDeps (bs ++ hd) c).map ofCmdId) := by
        refine ⟨by simp, fun d hd' => ?_, ?_⟩
        · rw [sp.depsIn_split (bs ++ hd) [] (toCmdId ⟨cl, seq⟩, c) hxn]
          obtain ⟨d', hd'', rfl⟩ := List.mem_map.mp hd'
          first | exact hd'' | simpa [swift.toCmdId_ofCmdId] using hd''
        · rw [List.length_map]
          have h1 := swift.small_ids_len ((bs ++ hd).map Prod.fst)
            (by rw [e1]; exact Hok.1.2.2.2.2.2.2.2.2.2.2.2.1)
            (by intro y hy; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy; exact Hsm p hp)
          have h2 := sp.lkDeps_length (bs ++ hd) c
          simp only [List.length_map] at h1
          omega
      ihave Hpd := swift.propDepsOwn_append rp (bs ++ hd) [(toCmdId ⟨cl, seq⟩, c)] $$ Hpd
      iunfold swift.propDepsOwn at Hpd
      icases Hpd with ⟨%pdm, %PD, Hpdf, Hpdmap, Hpdents⟩
      wp_auto
      wp_apply wp_mapInsert $$ [$Hpdmap] as Hpdmap
      ihave Hpd : swift.propDepsOwn rp (bs ++ (hd ++ [(toCmdId ⟨cl, seq⟩, c)]))
          $$ [Hpdf Hpdmap Hpdents]
      · rw [← List.append_assoc]
        iunfold swift.propDepsOwn; iexists pdm, _; iframe Hpdf Hpdmap
        iapply (BigSepM.bigSepM_insert_elim (Φ := fun (x : swift.CommandId) (sl : GoSlice) =>
          iprop(∃ D : List swift.CommandId, sl ↦*□ D ∗
            ⌜swift.propDepOk (bs ++ hd ++ [(toCmdId ⟨cl, seq⟩, c)]) x D⌝)))
        · iexists _; iframe Hdep; ipureintro; exact hpdOk
        · iexact Hpdents
      wp_apply (swift.Replica.wp_leader wp_Leader rp rr v.ballot _ N ⟨Hids.2.2.2.1, Hids.2.2.2.2.1⟩)
        $$ [$Hbal $Hrr $HN] as Hbal
      iunfold swift.seqOwn at Hseq
      icases Hseq with ⟨%n0, Hsq, Hhi, %Hn0⟩
      have hb0 : 0 ≤ v.ballot.toInt := Hok.1.1
      have hme0 : 0 ≤ me.toInt := Hids.2.1
      have hldme : ld = true ↔ sp.rid me = sp.leaderOf N (sp.bal v.ballot) := by
        rw [Hok.1.2.2.2.2.2.2.2.2.2.2.1, Hids.1, Hok.1.2.2.2.2.2.1 Hnorm, Hok.1.2.2.1]; exact eq_comm
      wp_join iprop(∃ sq : w64, seqnum_ptr ↦ sq ∗ r_ptr ↦ rp ∗
          typedPointsto (swift.fld rp go!"seqnum") (if ld then n0 + 1 else n0)
            (DFrac.own (1 : Qp).half) ∗ ⌜sq = if ld then n0 else W64 (-1)⌝)
        with [seqnum r Hsq] as ⟨%sqv, seqnum, r, Hsq, %Hsqv⟩
      · -- the leader: `seqnum = r.seqnum; r.seqnum++` under `cntL`
        have hld : ld = true := hldme.mpr
          ((replica.leader.srem_leader v.ballot N ⟨Hids.2.2.2.1, by omega⟩ hb0 _ hme0).mp rfl)
        simp only [hld, if_true]
        wp_apply sync.Mutex.wp_Lock $$ [$HcntL] as ⟨Hlocked, HR⟩
        iunfold swift.cntLInvR at HR
        icases HR with ⟨%n, %rc, %T, Hsn, Hrc, Hg⟩
        ihave %Heqn := typedPointsto_agree_wand _ _ _ _ _ $$ Hsn Hsq
        subst Heqn
        ihave Hsn := (swift.pt_halvesR _ _).2 $$ [Hsn Hsq]
        · iframe
        wp_auto
        icases (swift.pt_halvesR _ _).1 $$ Hsn with ⟨Hsn, Hsq⟩
        wp_apply sync.Mutex.wp_Unlock $$ [$HcntL $Hlocked Hsn Hrc Hg]
        · iunfold swift.cntLInvR; iexists _, _, _; iframe
        wp_join_done
        iexists _
        iframe
        ipureintro; rfl
      · -- a follower: no number
        have hld : ld = false := by
          cases h : ld
          · rfl
          · exfalso; apply Hif
            exact ((replica.leader.srem_leader v.ballot N ⟨Hids.2.2.2.1, by omega⟩ hb0 _ hme0).mpr
              (hldme.mp h)).symm
        simp only [hld, Bool.false_eq_true, if_false]
        iexists _
        iframe
        ipureintro; rfl
      iunfold swift.pendOwnH at Hpend
      icases Hpend with ⟨Hpdm, #Hpdents⟩
      wp_apply wp_map_lookup2 $$ [$Hpdm] as Hpdm
      -- the proposal joins `proposes`
      have hpnone : v.propsM !! (⟨cl, seq⟩ : swift.CommandId) = none := by
        cases h : v.propsM !! (⟨cl, seq⟩ : swift.CommandId) with
        | none => rfl
        | some _ => simp_all
      ihave Hpents := (BigSepM.bigSepM_insert (show Iris.Std.PartialMap.get? v.propsM
          (⟨cl, seq⟩ : swift.CommandId) = none from hpnone)).2 $$ [Hpents]
      · iframe Hpents
        iexists c
        iexact Hpi
      have hKx : swift.propsK (<[(⟨cl, seq⟩ : swift.CommandId) := gp]> v.propsM)
          (toCmdId ⟨cl, seq⟩) := by
        unfold swift.propsK
        rw [show ofCmdId (toCmdId ⟨cl, seq⟩) = (⟨cl, seq⟩ : swift.CommandId) from rfl,
          GMap.lookup_insert]
        rfl
      ihave Hhlog := swift.hlogOwn_mono v.hlog hM' ld (hd ++ [(toCmdId ⟨cl, seq⟩, c)])
        (K' := swift.propsK (<[(⟨cl, seq⟩ : swift.CommandId) := gp]> v.propsM)) (Λ' := Λ)
        (fun y hy => by
          unfold swift.propsK at hy ⊢
          rw [GMap.lookup_insert_eq_iff]
          split
          · rfl
          · exact hy)
        (fun _ _ _ h => h) $$ Hhlog
      wp_join iprop(∃ (pM' : GMap swift.CommandId Loc) (hM'' : GMap w64 Loc)
          (Λ' : w64 → w64 → List sp.CmdId → Prop),
          swift.pendOwnH γ (sp.leaderOf N w.2.1) w.2.1 v.pend pM' ∗
          swift.fld rp go!"hlog" ↦ v.hlog ∗
          swift.hlogOwn v.hlog hM'' ld (hd ++ [(toCmdId ⟨cl, seq⟩, c)])
            (swift.propsK (<[(⟨cl, seq⟩ : swift.CommandId) := gp]> v.propsM)) Λ' ∗
          swift.ldSound γ (sp.leaderOf N w.2.1) w.2.1 Λ' ∗
          swift.fld rp go!"proposes" ↦ v.props ∗
          swift.propsOwn γ v.props (<[(⟨cl, seq⟩ : swift.CommandId) := gp]> v.propsM) ∗
          typedPointsto (swift.fld rp go!"ballot") v.ballot (DFrac.own (1 : Qp).half.half) ∗
          r_ptr ↦ rp ∗ cmdId_ptr ↦ (⟨cl, seq⟩ : swift.CommandId) ∗
          swift.fld rp go!"pendingHashUpds" ↦ v.pend)
        with [Hpdm Hhf Hhlog Hpf Hpm Hpents Hbal upd r cmdId Hpendf]
        as ⟨%pM', %hM'', %Λ', Hpend, Hhf, Hhlog, #HΛ', Hpf, Hprops, Hbal, r, cmdId, Hpendf⟩
      · have hex := Hif
        wp_apply (swift.Replica.wp_leader wp_Leader rp rr v.ballot _ N
          ⟨Hids.2.2.2.1, Hids.2.2.2.2.1⟩) $$ [$Hbal $Hrr $HN] as Hbal
        wp_if_destruct
        · wp_join_done
          iexists v.pendM, _, Λ
          unfold swift.propsOwn swift.pendOwnH
          iframe
          iframe HΛ Hpdents
        · -- a follower with the leader's acknowledgement waiting: `recordLeaderHash`
          have hld : ld = false := by
            cases h : ld
            · rfl
            · exfalso; apply Hif
              exact ((replica.leader.srem_leader v.ballot N ⟨Hids.2.2.2.1, by omega⟩ hb0 _
                hme0).mpr (hldme.mp h)).symm
          obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hex
          icases (BigSepM.bigSepM_delete (show Iris.Std.PartialMap.get? v.pendM
            (⟨cl, seq⟩ : swift.CommandId) = some u from hu)).1 $$ Hpdents with ⟨Hue, Hrest⟩
          icases Hue with ⟨%sl, %sq, %H0, %P0, #Hue, #Hsl, #Hsh0, #Hnum0, #Hpath0⟩
          iStructNamed Hue
          rw [hu]
          wp_apply wp_mapDelete $$ [$Hpdm] as Hpdm
          simp only [Option.getD_some]
          wp_auto
          -- `recordLeaderHash` (change log C22: the leader's numbering, `Λ` grows)
          subst hld
          wp_apply (wp_record γ γc γm γl N fr l rp v.hlog v.props v.pend _
              (<[(⟨cl, seq⟩ : swift.CommandId) := gp]> v.propsM) (Iris.Std.delete v.pendM ⟨cl, seq⟩)
              (hd ++ [(toCmdId ⟨cl, seq⟩, c)]) Λ w.2.1 ⟨cl, seq⟩ sq sl H0 P0)
            $$ [$Hhf $Hhlog $Hpf Hpm Hpents Hpendf Hpdm Hrest]
            as %hM3 %pdM3 %Λ2 ⟨Hhf, Hhlog, #HΛ2, Hpf, Hprops, Hpendf, Hpend, -⟩
          · unfold swift.propsOwn swift.pendOwnH
            iframe
            iframe Hinv Hcfg HΛ Hsl Hsh0 Hnum0 Hpath0
            iexact Hrest
          wp_join_done
          iexists _, _, _
          iframe
          iexact HΛ2
      · iexists v.pendM, _, Λ
        unfold swift.propsOwn swift.pendOwnH
        iframe
        iframe HΛ Hpdents
      -- the ghost step (upd_handle): the replica's sequence of its ballot gets x
      have hbc : w.2.1 = w.1 := Hok.1.2.2.2.2.2.1 Hnorm
      have e1 : (bs ++ hd).map Prod.fst = w.locAt w.1 := by
        obtain ⟨hlo, hhd, hbs⟩ := Hok
        rw [List.map_append, hhd, hbs, ← hbc, hlo.2.2.2.2.2.2.2.1]
      have hxl : toCmdId ⟨cl, seq⟩ ∉ w.locAt w.1 := by rw [← e1]; exact hxn
      have hBp : (M.map sp.syncOrder).getD [] <+: w.locAt w.1 := by
        rw [← e1, List.map_append, Hok.2.2]; exact List.prefix_append _ _
      ihave #HB := swift.syncObj_base γ N v.lastSync w.2.1 M Hok.1.2.2.2.2.2.2.1 $$ Hls
      -- change log C22 (M3): the leader's number of `x` (its `seqnum`), a follower's 0; D22 (2):
      -- `r.seqnum++` does not overflow (`sp.numCnt`: the ballot is an `int32`'s)
      have hb31 : w.1 < 2 ^ 31 := by
        rw [Hok.1.2.2.1]; unfold sp.bal
        have := BitVec.toInt_lt (x := v.ballot); simp at this; omega
      have hldw : ld = true ↔ sp.leaderOf N w.1 = r := by
        rw [Hok.1.2.2.2.2.2.2.2.2.2.2.1, hbc]
      -- L2 (item 4): the step at its resolution, `ghostHandle(r.ballot, cmdId, propose.Command)`
      ihave #Hcpkg : isPkgInit (PROP := IProp netDistGF)
        pkg_id.github_com.imdea_software.swiftpaxos.client $$ []
      · iPkgInit
      try wp_auto
      wp_bind (App (App (App (Val (@! swift.ghostHandle)) (Val _)) (Val _)) (Val _))
      iapply (swift.wp_ghostHandle γ k v.ballot ⟨cl, seq⟩ c vs DFrac.discard
        iprop(ghostVar γv (1 : Qp).half (w.handled (toCmdId ⟨cl, seq⟩)) ∗
          sp.locAt γ r w.1 (w.locAt w.1).length (toCmdId ⟨cl, seq⟩) ∗
          swift.claimTok sn.γcl (w.1, toCmdId ⟨cl, seq⟩) .fresh ∗
          sp.numIs γ r w.1 (toCmdId ⟨cl, seq⟩) (if ld then n0 else W64 (-1)) ∗
          sp.numHi γ k (if ld then n0 + 1 else n0) ∗
          ⌜ld = true → sint.Z (n0 + 1) = sint.Z n0 + 1⌝)) $$ [Hw Hhi]
      · iframe #
        isplitr
        · ipureintro; exact Hok.1.1
        iunfold swift.ghostUpd
        iintro %W' Hpre
        rw [← Hok.1.2.2.1]
        imod swift.handle_stepDN γ γc γm γl γv γe γo N r k fr l w (toCmdId ⟨cl, seq⟩) c
          ((M.map sp.syncOrder).getD []) Hids.2.2.1 Hids.2.2.2.2.2 hBp hxl n0 ld hldw Hn0 hb31 hbc W'
          $$ [Hw Hhi Hpre]
          with ⟨Hw, Hpost, #Hnew, Htk, #Hnum, Hhi, %hov⟩
        · iframe Hinv Hcfg Hninv Hw Hhi Hpre
          isplitr
          · simp only [toCmdId]; iexact Hc
          · rw [← hbc]; iexact HB
        imodintro
        iframe Hpost Hw Htk Hhi Hnew Hnum
        ipureintro; exact hov
      inext
      iintro ⟨-, Hw, #Hnew, Htk, #Hnum, Hhi, %hov⟩
      try wp_auto
      have hlen : (bs ++ hd).length = (w.locAt w.1).length := by rw [← e1, List.length_map]
      ihave #Hlb' : sp.locLb γ r w.1 (bs ++ hd ++ [(toCmdId ⟨cl, seq⟩, c)]) $$ []
      · iunfold sp.locLb
        iapply BigSepL.bigSepL_snoc.2
        isplitl
        · rw [← hbc]; iunfold sp.locLb at Hlb; iexact Hlb
        · rw [hlen]; iframe Hnew; simp only [toCmdId]; iexact Hc
      have hdl : (bs ++ hd ++ [(toCmdId ⟨cl, seq⟩, c)]).dropLast = bs ++ hd := by
        rw [List.dropLast_concat]
      have hdrop : (bs ++ hd).drop ((M.map sp.syncOrder).getD []).length = hd := by
        rw [← Hok.2.2, List.length_map, List.drop_left]
      wp_alloc pm as Hpm
      ipersist Hpm
      wp_auto
      wp_apply (swift.Replica.wp_leader wp_Leader rp rr v.ballot _ N
        ⟨Hids.2.2.2.1, Hids.2.2.2.2.1⟩) $$ [$Hbal $Hrr $HN] as Hbal
      wp_apply (wp_getDesc γ sn.γcl γdl rp _ gp ⟨cl, seq⟩ c dep hs sqv _ N r w.1 ld
        (bs ++ hd ++ [(toCmdId ⟨cl, seq⟩, c)]) ((M.map sp.syncOrder).getD [])
        (sp.lkDeps (bs ++ hd) c) P H v.ballot _)
        $$ [Hdesc Hrdr Hbal Htk] as %d ⟨Hdesc, Hrdr, Hbal⟩
      · iframe Hdesc Hrdr Hbal Htk
        isplitl
        rotate_left
        · ipureintro; exact Hok.1.2.2.1.symm
        iunfold swift.propMsgR
        iframe Hdep Hhs Hpm Hpi
        isplitr
        · ipureintro; exact Hdnn
        isplitr
        rotate_left
        · have hsq : (if ld then sqv else W64 (-1)) = (if ld then n0 else W64 (-1)) := by
            cases ld <;> simp_all
          rw [hsq]; iexact Hnum
        · iunfold swift.propFacts
          iframe Hlb' HP
          isplitr
          · iunfold swift.baseIs; rw [← hbc]; iexact HB
          · ipureintro
            rw [hdl, hdrop]
            refine ⟨by simp, hxn, rfl, HPok.1, HPok.2.1, HPok.2.2,
              by first | exact hldw | (rw [← hbc]; exact hldw) | exact Hok.1.2.2.2.2.2.2.2.2.2.2.1,
              by rw [e1]; exact hBp, ?_⟩
            rw [List.map_append, List.nodup_append]
            refine ⟨?_, by simp, ?_⟩
            · rw [e1, ← hbc]; exact Hok.1.2.2.2.2.2.2.2.2.2.2.2.1
            · intro a ha b hb; simp at hb; subst hb; intro e; subst e; exact hxn ha
      wp_join with [cmdId r]
      · wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any))))
          (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := GoInterface) (t := go.any) [_, _]
        wp_auto
        isplitl []
        · ipureintro; rfl
        iintro %lsl ⟨Hlsl, -⟩
        wp_auto
        wp_method_call
        wp_auto
        wp_method_call
        wp_auto
        wp_apply wp_Fatal $$ [$Hq]
        wp_join_done
      -- the run loop's new state
      iapply HΦ
      iexists (swift.RunV.mk v.ballot v.cballot v.status nsl (v.handled ++ [⟨cl, seq⟩]) v.props
        (Std.insert v.propsM (⟨cl, seq⟩ : swift.CommandId) gp) v.keys kM' v.hlog hM'' v.pend pM'
        v.lastSync), hd ++ [(toCmdId ⟨cl, seq⟩, c)], w.handled (toCmdId ⟨cl, seq⟩)
      iframe Hdesc Hrdr Hpd
      isplitr [Hsq Hhi]
      · iunfold swift.runSt
        simp only
        rw [← List.append_assoc]
        iframe
        isplitr
        · iExactEq HΛ'; rfl
        isplitr
        · iExactEq Hls; rfl
        isplitr
        · iExactEq Hlb'; simp [swift.LView.handled, hbc]
        · ipureintro
          refine ⟨swift.localOk_handled N r ld v _ M w ⟨cl, seq⟩ gp Hnorm Hok.1 rfl rfl rfl rfl rfl
            hxn',
            by simp [Hok.2.1, toCmdId], Hok.2.2⟩
      isplitl
      · iunfold swift.seqOwn
        iexists _
        iframe Hsq Hhi
        ipureintro
        cases ld
        · exact Hn0
        · simp only [if_true]; rw [hov rfl]; omega
      · ipureintro; exact ⟨rfl, rfl, Hnorm⟩
    · wp_auto
      iapply HΦ
      iexists v, hd, w
      iframe Hdesc Hrdr Hpd Hseq
      isplitl
      · iunfold swift.runSt; iunfold swift.propsOwn
        iframe; isplitr
        · iexact Hls
        isplitr
        · iexact Hlb
        · ipureintro; exact Hok
      · ipureintro; exact ⟨rfl, rfl, Hnorm⟩

/-- `handleProposal.wp_proofN` at a `DS` independent of `N r` (round 24). -/
theorem swift.Replica.handleProposal.wp_proof
    (wp_String : swift.CommandId.String.specI)
    (wp_HasV : ∀ dm γdl, swift.cmapHasV.spec dm γdl)
    (wp_getDep : swift.Replica.getDepAndHashes.specI)
    (wp_record : swift.Replica.recordLeaderHash.specT)
    (DS : Loc → IProp netDistGF)
    (wp_getDesc : swift.Replica.getCmdDescWith.propSpecI DS)
    (wp_Leader : replica.Leader.spec)
    (wp_Fatal : dlog.Logger.Fatal.spec (GF := netDistGF) (hG := hG)) :
    swift.Replica.handleProposal.specI DS :=
  swift.Replica.handleProposal.wp_proofN wp_String wp_HasV wp_getDep wp_record (fun _ _ _ _ _ => DS)
    wp_getDesc wp_Leader wp_Fatal

end proof

end Perennial.github_com.imdea_software.swiftpaxos
