/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/DeliverProofE.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The proof of `r.deliver(desc, cmdId)` against `deliver.specE` (SWC-2, round S2; spec:
Proof/swift/DeliverE.lean). DeliverProof.lean's proof of `deliver.specI`, with:
- the execution ticket: at the lock, the ticket against the record's tickets gives
  `x ∉ X` (`swift.xTix_notin`), hence the record's `Nodup`; the ticket joins the record when
  `x` executes;
- each new entry's `exRepOk`, from `⌜dv.c.wf⌝`, `depWhy`'s leader part and `ldrPrefix`;
- the reply through `reply.specE` on `RCh`, with `replyWitE` from the record (its entries'
  `exRepOk`, `depsBefore`, `Nodup`) and the descriptor's `replyPre`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DeliverE
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.LeaderM
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AnyFlag

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

set_option hygiene false in
/-- An early `return false` of `deliver`: everything back. -/
macro "dexitE" : tactic => `(tactic| (
  ihave Htix : iprop(swift.tixD γxu γxm b x dv) $$ [Htix]
  focus
    first
    | iexact Htix
    | (iunfold swift.tixD; iright; first | iexact Htix | (ileft; iexact Htix))
  iapply HΦ
  simp only [Bool.false_eq_true, ↓reduceIte]
  iunfold swift.epochRd
  iunfold swift.descF
  iframe Hbal HStf Hrcf Het Hxe Hph Hcmd Hdep Hhs Hprop Hseq Hmsgs Hvs HD HHs Hmb HsL HRs HrdR Htix Hpin
  isplitr
  ipureintro; exact Hbw
  ipureintro; exact Hop))

set_option hygiene false in
/-- A `return false` after `x` executed: everything back, the ticket gone, `x`'s execution. -/
macro "dexitX" : tactic => `(tactic| (
  ihave Htix : iprop(swift.tixD γxu γxm b x dv) $$ []
  focus
    iunfold swift.tixD; iright; iright; iexact HexIn
  iapply HΦ
  simp only [Bool.false_eq_true, ↓reduceIte]
  iunfold swift.epochRd
  iunfold swift.descF
  iframe Hbal HStf Hrcf Het Hxe Hph Hcmd Hdep Hhs Hprop Hseq Hmsgs Hvs HD HHs Hmb HsL HRs HrdR Htix Hpin
  isplitr
  ipureintro; exact Hbw
  ipureintro; exact Hop))

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

/-- The log's per-entry facts (`exEntOkE`) with one more entry. -/
theorem swift.exEntsE_snoc (γ : sp.Names) (N r b : Nat) (X : List swift.ExE)
    (es : List swift.commandStaticDesc) (e : swift.ExE) (en : swift.commandStaticDesc)
    (hl : es.length = X.length) :
    ([∗list] i ↦ e' ∈ X, ∃ esi : swift.commandStaticDesc, ⌜es[i]? = some esi⌝ ∗
        swift.exEntOkE γ N r b e' esi) ∗ swift.exEntOkE γ N r b e en ⊢
      [∗list] i ↦ e' ∈ X ++ [e], ∃ esi : swift.commandStaticDesc, ⌜(es ++ [en])[i]? = some esi⌝ ∗
        swift.exEntOkE γ N r b e' esi := by
  refine (sep_mono (BigSepL.bigSepL_mono ?_) ?_).trans BigSepL.bigSepL_snoc.2
  · intro k e' hk
    have hk' : k < es.length := by
      rw [hl]; exact (List.getElem?_eq_some_iff.mp hk).1
    iintro ⟨%esi, %h, H⟩
    iexists esi; iframe H; ipureintro
    rw [List.getElem?_append_left hk']; exact h
  · iintro H
    iexists en; iframe H; ipureintro
    rw [← hl]; simp

/-- `swift.exIn_delivered` (Deliver.lean) giving the record's map back (round 46, gap 46-1). -/
theorem swift.exIn_deliveredK (str : swift.CommandId → GoString) (γxm : GName) (b : Nat)
    (x : swift.CommandId) (M : GMap GoString GoInterface) (X : List swift.ExE)
    (Mx : GMap (Nat × Nat) swift.ExE) (hok : swift.delivOk str M b X Mx false) {qa : Qp} :
    swift.exIn γxm b x ∗ ghostMapAuth γxm qa Mx ⊢
      ghostMapAuth γxm qa Mx ∗ ⌜(M.lookup (str x)).isSome⌝ := by
  unfold swift.exIn swift.exLb
  iintro ⟨⟨%X0, %e, #Hlb, %He⟩, Ha⟩
  ihave ⟨-, #He'⟩ := (BigSepL.bigSepL_snoc (PROP := IProp netDistGF)).1 $$ Hlb
  iunfold swift.exAt at He'
  ihave %Hl := ghost_map_lookup $$ Ha He'
  iframe Ha
  ipureintro
  have h1 := hok.2.2.1 X0.length
  rw [Hl] at h1
  have hmem : e ∈ X := List.mem_of_getElem? h1.symm
  have := hok.2.1 rfl e hmem
  rw [He] at this; exact this

/-- **An executed command is in the record** (round 55, 53-3'): `exIn γxm b x` against
`delivInv`'s record map (its epoch `b` from the record's variable `γx`, whose half `execL`
holds): `x` is among the record's commands. -/
theorem swift.exIn_inRec (γ : sp.Names) (N r : Nat) (γdl γx γxp γxm γa γxe γrm : GName)
    (str : swift.CommandId → GoString) (b : Nat) (x : swift.CommandId) (X : List swift.ExE) :
    inv swift.delivN (swift.delivInv γ N r γdl γx γxp γxm γa γxe γrm str) ∗ swift.exIn γxm b x ∗
      ghostVar γx (1 : Qp).half (b, X) ⊢
      |={⊤}=> ghostVar γx (1 : Qp).half (b, X) ∗ ⌜x ∈ X.map Prod.fst⌝ := by
  iintro ⟨#HdI, #Hex, HXl⟩
  iinv HdI with Hi Hclose
  iunfold swift.delivInv at Hi
  imod Hi
  icases Hi with ⟨%M, %bX, %X', %Mx, %rm, HV, HXi, HXp, HMx, HXx, %HM⟩
  ihave %Hag := ghostVar_agree γx (b, X) (1 : Qp).half (bX, X') (1 : Qp).half.half $$ HXl HXi
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl⟩ := Hag
  iunfold swift.exIn at Hex
  icases Hex with ⟨%X0, %e, #Hlb, %He⟩
  iunfold swift.exLb at Hlb
  ihave ⟨-, #He'⟩ := (BigSepL.bigSepL_snoc (PROP := IProp netDistGF)).1 $$ Hlb
  iunfold swift.exAt at He'
  ihave %Hl := ghost_map_lookup $$ HMx He'
  imod Hclose $$ [HV HXi HXp HMx HXx] with -
  · inext; iunfold swift.delivInv; iexists M, b, X, Mx, rm; iframe; ipureintro; exact HM
  imodintro
  iframe HXl
  ipureintro
  have h1 := HM.2.2.1 X0.length
  rw [Hl] at h1
  have hmem : e ∈ X := List.mem_of_getElem? h1.symm
  exact List.mem_map.mpr ⟨e, hmem, He⟩

/-- The entries' `exRepOk` (what `replyWitE` keeps). -/
theorem swift.exEntsE_rep (γ : sp.Names) (N r b : Nat) (X : List swift.ExE)
    (es : List swift.commandStaticDesc) :
    ([∗list] i ↦ e' ∈ X, ∃ esi : swift.commandStaticDesc, ⌜es[i]? = some esi⌝ ∗
        swift.exEntOkE γ N r b e' esi) ⊢ [∗list] e' ∈ X, swift.exRepOk γ N r b e' := by
  refine BigSepL.bigSepL_mono ?_
  intro k e' _
  iintro ⟨%esi, -, H⟩
  iunfold swift.exEntOkE at H
  icases H with ⟨-, H, -⟩
  iexact H

end lemmas

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [github_com.orcaman.concurrent_map.Assumptions]
  [sync.Assumptions] [sync.atomic.Assumptions] [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]

theorem swift.Replica.deliver.wp_proofE (str : swift.CommandId → GoString)
    (hstr : Function.Injective str)
    (γdl : GName)
    (MP : GoInterface → IProp netDistGF)
    (hMPty : ∀ m, MP m ⊢ ⌜∀ ii : GoInterfaceOk, m = GoInterface.ok ii → ii.ty = go.int →
      ∃ s : w64, ii.v = #s⌝)
    (wp_String : swift.CommandId.String.specS str)
    (wp_HasV : ∀ dm, swift.cmapHasV.spec dm γdl)
    (wp_SetV : ∀ dm, swift.cmapSetV.spec dm γdl)
    (wp_Execute : state.Command.Execute.spec (GF := netDistGF))
    (wp_Leader : replica.Leader.spec)
    (wp_reply : swift.replyChan.reply.specE (hG := hG))
    (wp_Store : sync.atomic.Bool.Store.spec (GF := netDistGF) (hG := hG)) :
    swift.Replica.deliver.specE str γdl MP := by
  intro γ γc γm γl γw γv γe γo γx γxe γxm γxp γxu γrp γcg γout γcl γdc γd rp rr d N r k q qp b bw stp rcp dv x Rs Ret
  wp_start as ⟨#Hctx, Hrd, HrdR, Hpin, #HRC, Hd, HRs, #HsB, Hwhy, #HwhyE, #Hrep0, Htix, Hslot⟩
  iunfold swift.descCtxE at Hctx
  icases Hctx with ⟨%me, %fr, %l, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, #Hrr, #Hrep, %Hids, #Hex, #Hdr, #Hoe,
    #Hinv, #Hcfg, #Hninv, #Hdm, #Hcm, #HdI, #Hdc, #Hdcb, #HexL, #Hhook, #HacL, #Hrcf, #Hrcb, #Hany, #Hng⟩
  iunfold swift.descF at Hd
  icases Hd with ⟨Hph, Hcmd, #Hvs, Hdep, #HD, Hhs, #HHs, Hprop, Hseq, Hmsgs, #Hmb, #HsL, %Hop⟩
  iunfold swift.epochRd at Hrd
  icases Hrd with ⟨Hbal, HStf, Hrcf, Het, Hxe, %Hbw⟩
  ihave #HN := Hrep
  iunfold replica.isReplica at HN
  icases HN with ⟨%lg, %cfgp, %tbl, %pc, %fr', %nid, %ents, %γpc, %pwsl, %alsl, %latsl, %pws,
    %cwm, -, -, #HN, #Hid, -⟩
  wp_auto
  wp_if_destruct
  · -- no proposal yet
    dexitE
  have hpn : dv.propose ≠ null := by
    intro h; apply Hif; simp [h]
  iunfold swift.repPre at Hrep0
  icases Hrep0 with (%Hn | ⟨#Hpre, %Hwf, #Hlp, #HpI⟩)
  · exfalso; exact hpn Hn
  iunfold swift.tixD at Htix
  icases Htix with (%Hn | Htix)
  · exfalso; exact hpn Hn
  wp_apply wp_String $$ [$cmdId] as cmdId
  ihave Hb : iprop(|={⊤}=> github_com.orcaman.concurrent_map.readerV dm γdl swift.deliveredR ∗
      (github_com.orcaman.concurrent_map.readerV dm γdl swift.deliveredR ={⊤}=∗ swift.ownRdr rp γdl)) $$ [HrdR]
  · iapply swift.ownRdr_take; iframe Hdm HrdR
  iapply fupd_wp
  imod Hb with ⟨Hrdr, Hback⟩
  imodintro
  wp_method_call
  wp_auto
  -- round 46 (gap 46-1): an executed `x` (the ticket used) is in `delivered`, by the pin
  wp_apply (wp_HasV dm _ ((⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ (↑swift.delivN : CoPset))
      (fun dl => iprop((swift.xTix γxu b x ∨ (swift.exIn γxm b x ∗ ⌜dl = true⌝)) ∗
        swift.epochPinQ γxp qp b))) $$ [$Hrdr Htix Hpin] as %dl ⟨Hrdr, Htix, Hpin⟩
  · imod (inv_acc (E := ⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) (N := swift.delivN)
      swift.delivN_sub) $$ HdI with ⟨Hi, Hclose⟩
    iunfold swift.delivInv at Hi
    icases Hi with ⟨%M, %bX', %X', %Mx, %rm, >HV, >HXi, >HXeD, >HMx, >HXx, >%HM⟩
    ihave ⟨Hpin, HXeD, %Hrm⟩ := swift.epochPinQ_agree γxp qp b bX' rm $$ [Hpin HXeD]
    · iframe Hpin HXeD
    obtain ⟨rfl, hbX⟩ := Hrm
    subst bX'
    ihave ⟨Htix, HMx⟩ : iprop((swift.xTix γxu b x ∨ (swift.exIn γxm b x ∗
        ⌜(M.lookup (str x)).isSome = true⌝)) ∗ ghostMapAuth γxm (1 : Qp).half Mx) $$ [Htix HMx]
    · icases Htix with (Htix | #Hex)
      · iframe HMx; ileft; iexact Htix
      · ihave ⟨HMx, %Hs⟩ := swift.exIn_deliveredK str γxm b x M X' Mx HM $$ [Hex HMx]
        · iframe Hex HMx
        iframe HMx
        iright; iframe Hex; ipureintro; exact Hs
    imodintro
    iexists M
    iframe HV
    iintro HV
    imod Hclose $$ [HV HXi HXeD HMx HXx] with -
    · inext; iunfold swift.delivInv; iexists M, b, X', Mx, false; iframe; ipureintro; exact HM
    imodintro
    iframe Hpin Htix
  iapply fupd_wp
  imod Hback $$ Hrdr with HrdR
  imodintro
  cases dl
  case true =>
    wp_auto
    ihave Htix : iprop(swift.xTix γxu b x ∨ swift.exIn γxm b x) $$ [Htix]
    · icases Htix with (Htix | ⟨#Hex, -⟩)
      · ileft; iexact Htix
      · iright; iexact Hex
    dexitE
  icases Htix with (Htix | ⟨-, %Hf⟩)
  rotate_left
  · cases Hf
  wp_auto
  cases ex
  case false => wp_auto; dexitE
  wp_auto
  wp_join (v := #(decide (dv.phase ≠ swift.phCOMMIT) &&
      (or (!oe) (!decide (me = BitVec.srem bw (W32 (sint.Z (W64 (N : Int))))))))) at (if: #_ then _ else #false)
    with [Hph Hbal r]
  · wp_if_destruct
    · iframe; ipureintro; simp [swift.phCOMMIT, Hif]
    · have h3 : decide (dv.phase ≠ swift.phCOMMIT) = true := decide_eq_true Hif
      cases oe
      · wp_auto
        iframe; ipureintro; rw [h3]; rfl
      · wp_auto
        wp_apply (swift.Replica.wp_leader wp_Leader rp rr bw _ N ⟨Hids.2.2.2.1, Hids.2.2.2.2.1⟩)
          $$ [$Hbal $Hrr $HN] as Hbal
        iframe; ipureintro; rw [h3]; rfl
  generalize hc : (!decide (dv.phase = swift.phCOMMIT) &&
      (or (!oe) (!decide (me = BitVec.srem bw (W32 (sint.Z (W64 (N : Int)))))))) = cb
  cases cb
  case true => wp_auto; dexitE
  wp_auto
  -- why it may execute: committed, or the leader's own optimistic execution
  have hwhy : dv.phase = swift.phCOMMIT ∨ (oe = true ∧ r = sp.leaderOf N b) := by
    by_cases h3 : dv.phase = swift.phCOMMIT
    · exact Or.inl h3
    · right
      have h3' : decide (dv.phase = swift.phCOMMIT) = false := decide_eq_false h3
      rw [h3'] at hc
      cases oe
      · simp at hc
      · refine ⟨rfl, ?_⟩
        have hme : me = BitVec.srem bw (W32 (sint.Z (W64 (N : Int)))) := by simpa using hc
        have hv := replica.quorum.leader_val bw N (by omega) Hbw.2
        have hN' : sint.Z (W64 (N : Int)) = N := by word
        rw [← Hids.1, hme, ← Hbw.1]
        unfold sp.rid sp.bal sp.leaderOf
        rw [hN']
        have hv' : (BitVec.srem bw (W32 (N : Int))).toInt = bw.toInt % (N : Int) := hv
        rw [hv', Int.toNat_emod Hbw.2 (by omega)]
        simp
  wp_apply sync.Mutex.wp_Lock $$ [$HexL] as ⟨Hlocked, HR⟩
  iunfold swift.execLInvE at HR
  icases HR with ⟨%sl, %es, %bX, %X, %stpX, Hlog, Hsl, Hslcap, HXl, HXe, Hown, #HXlb,
    #HXok, HXt, %HXp⟩
  ihave %Hag := ghostVar_agree γxe (b, stp) q (bX, stpX) (1 : Qp).half $$ Hxe HXe
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl⟩ := Hag
  -- the ticket: `x` is not executed yet
  ihave ⟨HXt, Htix, %Hnin⟩ := swift.xTix_notin γxu b X x $$ [HXt Htix]
  · iframe HXt Htix
  ihave %HDlen := ownSlice_len _ _ _ $$ HD
  ihave HL : (∃ (i : w64) (cp : swift.CommandId),
      "i" ∷ i_ptr ↦ i ∗ "cp" ∷ cmdIdPrime_ptr ↦ cp ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ dv.D.length ∧
        ∀ j (dj : swift.CommandId), j < sint.nat i → dv.D[j]? = some dj → dj ∈ X.map Prod.fst⌝ :
      IProp netDistGF) $$ [i cmdIdPrime]
  · iexists (W64 0), _; iframe; ipureintro
    refine ⟨by decide, by simp, fun j dj hj _ => absurd hj (by simp)⟩
  wp_for HL
  wp_if_destruct
  · have hiD : sint.nat i < dv.D.length := by rw [HDlen.1]; word
    obtain ⟨dj, hdj⟩ : ∃ dj, dv.D[sint.nat i]? = some dj :=
      ⟨dv.D[sint.nat i], List.getElem?_eq_getElem hiD⟩
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z dv.dep.len := ⟨Hi.1, by simpa using Hif⟩
    rw [if_pos hb]
    wp_apply wp_load_slice_index (t := swift.CommandId.ty) dv.dep (sint.Z i) dv.D _ dj Hi.1
      $$ [HD] as -
    · iframe HD; ipureintro; exact hdj
    wp_apply wp_String $$ [$cp] as cp
    wp_method_call
    wp_auto
    ihave Hb : iprop(|={⊤}=> github_com.orcaman.concurrent_map.readerV dm γdl swift.deliveredR ∗
        (github_com.orcaman.concurrent_map.readerV dm γdl swift.deliveredR ={⊤}=∗ swift.ownRdr rp γdl)) $$ [HrdR]
    · iapply swift.ownRdr_take; iframe Hdm HrdR
    iapply fupd_wp
    imod Hb with ⟨Hrdr, Hback⟩
    imodintro
    wp_apply (wp_HasV dm (str dj) ((⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ (↑swift.delivN : CoPset))
      (fun ok => iprop(⌜ok = true → dj ∈ X.map Prod.fst⌝ ∗ ghostVar γx (1 : Qp).half (b, X))))
      $$ [$Hrdr HXl] as %ok ⟨Hrdr, %Hok, HXl⟩
    · imod (inv_acc (E := ⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) (N := swift.delivN)
        swift.delivN_sub) $$ HdI with ⟨Hi, Hclose⟩
      iunfold swift.delivInv at Hi
      icases Hi with ⟨%M, %bX', %X', %Mx, %rm, >HV, >HXi, >HXeD, >HMx, >HXx, >%HM⟩
      ihave %Hag2 := ghostVar_agree γx (b, X) (1 : Qp).half (bX', X') (1 : Qp).half.half $$ HXl HXi
      simp only [Prod.mk.injEq] at Hag2
      obtain ⟨rfl, rfl⟩ := Hag2
      imodintro
      iexists M
      iframe HV
      iintro HV
      imod Hclose $$ [HV HXi HXeD HMx HXx] with -
      · inext; iunfold swift.delivInv; iexists M, b, X, Mx, rm; iframe; ipureintro; exact HM
      imodintro
      iframe HXl
      ipureintro
      intro hs
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨e, he, hk⟩ := HM.1 _ v hv
      rw [hstr hk]; exact List.mem_map_of_mem he
    iapply fupd_wp
    imod Hback $$ Hrdr with HrdR
    imodintro
    cases ok
    case false =>
      wp_auto
      wp_apply sync.Mutex.wp_Unlock $$ [$HexL $Hlocked Hlog Hsl Hslcap HXl HXe Hown HXt]
      · iunfold swift.execLInvE
        iexists sl, es, b, X, stp
        iframe; iframe HXlb HXok; ipureintro; exact HXp
      wp_for_post
      dexitE
    wp_auto
    wp_for_post
    iframe
    iexists _, dj
    iframe
    ipureintro
    refine ⟨by word, by word, fun j dj' hj hj' => ?_⟩
    by_cases hji : j < sint.nat i
    · exact Hi.2.2 j dj' hji hj'
    · have : j = sint.nat i := by word
      subst this; rw [hdj] at hj'; cases hj'; exact Hok rfl
  -- every dependency was executed before
  have hdeps : ∀ dj ∈ dv.D, dj ∈ X.map Prod.fst := by
    intro dj hdj
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hdj
    have hle : ¬ sint.Z i < sint.Z dv.dep.len := by simpa using Hif
    exact Hi.2.2 j _ (by rw [HDlen.1] at hj; word) (List.getElem?_eq_getElem hj)
  wp_apply wp_String $$ [$cmdId] as cmdId
  wp_method_call
  wp_auto
  -- why it may execute, for the record (`exOk`, `delivX`'s) and the log (`exEntOk`, D32/G-ldr)
  iunfold swift.execWhy at HwhyE
  icases HwhyE with ⟨#HE1, #HdW⟩
  ihave %hph0 : ⌜r = sp.leaderOf N b → dv.phase ≠ W64 0⌝ $$ [HE1]
  · icases HE1 with (%Hp | ⟨%Hp, -⟩ | ⟨%Hp, -⟩)
    · ipureintro; intro hl h0
      rcases Hp with Hp | Hp | Hp
      · exact hpn Hp
      · exact Hp hl
      · rw [h0] at Hp; exact absurd Hp (by decide)
    · ipureintro; intro _ h0; rw [h0] at Hp; exact absurd Hp (by decide)
    · ipureintro; intro _ h0; rw [h0] at Hp; exact absurd Hp (by decide)
  ihave #HphW : (⌜dv.phase = W64 3⌝ ∗ sp.committed γ r b (toCmdId x)) ∨
      (⌜r = sp.leaderOf N b⌝ ∗
        ((⌜dv.phase = W64 2⌝ ∗ sp.accepted γ r b (toCmdId x)) ∨
         (⌜dv.phase = W64 1⌝ ∗ sp.preacc γ r b (toCmdId x) (dv.D.map toCmdId)))) $$ [Hwhy]
  · by_cases h3 : dv.phase = swift.phCOMMIT
    · ileft; rw [if_pos (decide_eq_true ⟨h3, hpn⟩)]
      isplitr
      · ipureintro; exact h3
      iexact Hwhy
    · have hl : r = sp.leaderOf N b := by
        rcases hwhy with h | h
        · exact absurd h h3
        · exact h.2
      iright; isplitr
      · ipureintro; exact hl
      icases HE1 with (%Hp | H2 | H1)
      · exfalso
        rcases Hp with Hp | Hp | Hp
        · exact hpn Hp
        · exact Hp hl
        · exact h3 Hp
      · ileft; iexact H2
      · iright; iexact H1
  ihave #Hldr : ⌜r ≠ sp.leaderOf N b⌝ ∨ sp.preacc γ r b (toCmdId x) (dv.D.map toCmdId) ∨
      (⌜dv.phase = W64 3⌝ ∗ swift.syncIn γ b (toCmdId x)) $$ []
  · by_cases hl : r = sp.leaderOf N b
    · iunfold swift.depWhy at HdW
      icases HdW with ((%Hp | ⟨%Hl, -⟩) | ⟨-, #Hp⟩ | ⟨%Hs, #Hp⟩ | ⟨%Hl, -⟩)
      · exfalso
        rcases Hp with Hp | Hp | Hp
        · exact Hp.1 hl
        · exact hpn Hp
        · exact hph0 hl Hp
      · exfalso; exact Hl hl
      · iright; ileft; iexact Hp
      · iright; iright; isplitr
        · ipureintro; exact Hs.2
        iexact Hp
      · exfalso; exact Hl hl
    · ileft; ipureintro; exact hl
  -- round 53 (52-1): at a follower (`COMMIT`), the leader's facts of `dep` (`depWhy`)
  -- round 55 (53-3'): `depWhy`'s "executed in `b`" disjunct is refuted by the ticket (`Hnin`)
  -- against `delivInv`'s record (`swift.exIn_inRec`)
  ihave HfW : iprop(|={⊤}=> ghostVar γx (1 : Qp).half (b, X) ∗ swift.exFolW γ N r b (x, dv.c, dv.D))
      $$ [HXl]
  · iunfold swift.exFolW
    by_cases hl : r = sp.leaderOf N b
    · imodintro; iframe HXl; ileft; ipureintro; exact hl
    ihave %h3 : ⌜dv.phase = W64 3⌝ $$ []
    · icases HphW with (⟨%h, -⟩ | ⟨%h, -⟩)
      · ipureintro; exact h
      · exact absurd h hl
    iunfold swift.depWhy at HdW
    icases HdW with ((%Hp | ⟨-, #Hexx⟩) | ⟨%Hg, -⟩ | ⟨%Hs, -⟩ | ⟨-, %D, #Hld, %HD⟩)
    · exfalso
      rcases Hp with Hp | Hp | Hp
      · rw [h3] at Hp; exact absurd Hp.2 (by decide)
      · exact hpn Hp
      · rw [h3] at Hp; exact absurd Hp (by decide)
    · imod (swift.exIn_inRec γ N r γdl γx γxp γxm γa γxe γrm str b x X) $$ [HXl] with ⟨-, %Hin⟩
      · iframe HdI Hexx HXl
      exfalso; exact Hnin Hin
    · exfalso
      rcases Hg with Hg | Hg
      · exact hl Hg
      · rw [h3] at Hg; exact absurd Hg (by decide)
    · exfalso; exact hl Hs.1
    · imodintro; iframe HXl; iright; iexists D; iframe Hld; ipureintro; exact HD
  iapply fupd_wp
  imod HfW with ⟨HXl, #HfW⟩
  imodintro
  ihave #Hok1 : swift.exOk γ N r b (x, dv.c, dv.D) $$ []
  · iunfold swift.exOk
    icases HphW with (⟨-, #Hc⟩ | ⟨%hl, -⟩)
    · ileft; iexact Hc
    · iright; ipureintro; exact hl
  -- the linearization point: `x` joins `delivered` and the record
  wp_apply (wp_SetV dm (str x) (interface.mkOk (go.StructType []) #(Perennial.zero_val Unit))
    ((⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ (↑swift.delivN : CoPset))
    iprop(ghostVar γx (1 : Qp).half (b, X ++ [(x, dv.c, dv.D)]) ∗
      swift.exAt γxm b X.length (x, dv.c, dv.D) ∗
      ghostVar γxe q (b, stp) ∗ ghostVar γxe (1 : Qp).half (b, stp) ∗ swift.epochPinQ γxp qp b))
    $$ [$Hcm HXl Hxe HXe Hpin] as ⟨HXl, #Hnew, Hxe, HXe, Hpin⟩
  · imod (inv_acc (E := ⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) (N := swift.delivN)
      swift.delivN_sub) $$ HdI with ⟨Hi, Hclose⟩
    iunfold swift.delivInv at Hi
    icases Hi with ⟨%M, %bX', %X', %Mx, %rm, >HV, >HXi, >HXeD, >HMx, >HXx, >%HM⟩
    icases HXx with ⟨HXx, HFz⟩
    ihave %Hag2 := ghostVar_agree γx (b, X) (1 : Qp).half (bX', X') (1 : Qp).half.half $$ HXl HXi
    simp only [Prod.mk.injEq] at Hag2
    obtain ⟨rfl, rfl⟩ := Hag2
    -- round 52: not frozen (the pin), so `delivFz`'s quarter and half join `delivInv`'s
    ihave ⟨Hpin, HXeD, HXi, HMx, #HlbX⟩ := swift.delivFz_get γx γxp γxm b X Mx rm
      (swift.epochPinQ γxp qp b) (swift.pin_noFz γxp qp b b rm) $$ [Hpin HXeD HXi HMx HFz]
    · iframe
    -- not in removal mode: `γxe`'s shares (this `epochRd`'s, `execLInv`'s) with `delivX`'s
    ihave ⟨Hxe, HXe, HXx, %Hrm⟩ := swift.delivX_noRm γ N r γa γxe γrm b X M rm q (b, stp) (b, stp)
      $$ [Hxe HXe HXx]
    · iframe Hxe HXe HXx
    subst Hrm
    ihave HXx := swift.delivX_snoc γ N r γa γxe γrm b X (x, dv.c, dv.D) M
      (M.insert (str x) (interface.mkOk (go.StructType []) #(Perennial.zero_val Unit))) $$ [HXx Hok1]
    · iframe HXx Hok1
    imod ghostVar_update_halves (b, X ++ [(x, dv.c, dv.D)]) γx (b, X) (b, X) $$ HXl HXi
      with ⟨HXl, HXi⟩
    -- the record's new entry
    have hfreshX : Mx.lookup (b, X.length) = none := by rw [HM.2.2.1]; simp
    imod ghost_map_insert_persist (b, X.length) (x, dv.c, dv.D) hfreshX $$ HMx with ⟨HMx, #Hnew⟩
    -- round 55 (53-3'): the record's prefix with the new entry
    ihave #HlbX' : swift.exLb γxm b (X ++ [(x, dv.c, dv.D)]) $$ []
    · iunfold swift.exLb
      iunfold swift.exLb at HlbX
      iapply (BigSepL.bigSepL_snoc (PROP := IProp netDistGF)).2
      iframe HlbX
      iunfold swift.exAt; iexact Hnew
    ihave ⟨HXi, HMx, HFz⟩ := swift.delivFz_put γx γxp γxm b (X ++ [(x, dv.c, dv.D)])
      (Mx.insert (b, X.length) (x, dv.c, dv.D)) $$ [HXi HMx]
    · iframe HXi HMx; iexact HlbX'
    imodintro
    iexists M
    iframe HV
    iintro HV
    imod Hclose $$ [HV HXi HXeD HMx HXx HFz] with -
    · inext; iunfold swift.delivInv; iexists _, b, _, _, false; iframe; ipureintro
      refine ⟨fun k v hk => ?_, fun hrm e he => ?_, fun j => ?_, fun b' j hb' => ?_⟩
      · rw [GMap.lookup_insert_eq_iff] at hk
        by_cases e : str x = k
        · exact ⟨(x, dv.c, dv.D), by simp, e.symm⟩
        · rw [if_neg e] at hk
          obtain ⟨e', he', hk'⟩ := HM.1 k v hk
          exact ⟨e', List.mem_append_left _ he', hk'⟩
      · rw [GMap.lookup_insert_eq_iff]
        by_cases e' : str x = str e.1
        · rw [if_pos e']; rfl
        · rw [if_neg e']
          rcases List.mem_append.mp he with he | he
          · exact HM.2.1 hrm e he
          · simp at he; subst he; exact absurd rfl e'
      · rw [GMap.lookup_insert_eq_iff]
        by_cases e : (b, X.length) = (b, j)
        · rw [if_pos e]; simp only [Prod.mk.injEq] at e; rw [← e.2]; simp
        · rw [if_neg e, HM.2.2.1]
          have hj : j ≠ X.length := fun h => e (by rw [h])
          by_cases hlt : j < X.length
          · rw [List.getElem?_append_left hlt]
          · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
      · rw [GMap.lookup_insert_eq_iff, if_neg (by intro h; simp only [Prod.mk.injEq] at h; omega)]
        exact HM.2.2.2 b' j hb'
    imodintro
    iframe HXl Hxe HXe Hpin
    iunfold swift.exAt; iexact Hnew
  try wp_auto
  wp_apply (swift.wp_anyStore wp_Store rp true) $$ [$Hany]
  try wp_auto
  wp_apply (wp_Execute (swift.dfld d go!"cmd") (DFrac.own 1) dv.c.op dv.c.key dv.vs dv.c.val stp
    (swift.applyX X)) $$ [$Hcmd $Hvs $Hown] as %vsl ⟨Hcmd, Hown, #Hres⟩
  · ipureintro; exact Hop
  rw [← swift.applyX_snoc X (x, dv.c, dv.D)] at *
  wp_bind (App (Val (GoInstruction (CompositeLiteral
    (go.GoType.SliceType swift.commandStaticDesc.ty)))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := swift.commandStaticDesc) (t := swift.commandStaticDesc.ty) [_]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lsl ⟨Hlsl, -⟩
  wp_auto
  wp_apply wp_slice_append $$ [Hsl Hslcap Hlsl] as %nsl ⟨Hsl, Hslcap, -⟩
  · iframe
  ihave #HXlb' : swift.exLb γxm b (X ++ [(x, dv.c, dv.D)]) $$ []
  · iunfold swift.exLb
    iapply BigSepL.bigSepL_snoc.2
    isplitl
    · iunfold swift.exLb at HXlb; iexact HXlb
    · iexact Hnew
  ihave #HexIn : swift.exIn γxm b x $$ []
  · iunfold swift.exIn
    iexists X, (x, dv.c, dv.D)
    iframe HXlb'
    ipureintro; rfl
  -- the new entry's facts for the leader's reply
  ihave #HrepN : swift.exRepOk γ N r b (x, dv.c, dv.D) $$ []
  · iunfold swift.exRepOk
    isplitr
    · ipureintro; exact Hwf
    by_cases hl : r = sp.leaderOf N b
    · iright
      iunfold swift.ldrPrefix at Hlp
      icases Hlp with (%Hp | #Hp)
      · exfalso; exact Hp hl
      isplitr
      · icases Hldr with (%Hq | #Hq | ⟨-, #Hq⟩)
        · exfalso; exact Hq hl
        · ileft; iexact Hq
        · iright; iexact Hq
      iexact Hp
    · ileft; ipureintro; exact hl
  have hnodup : ((X ++ [(x, dv.c, dv.D)]).map Prod.fst).Nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨HXp.2.2, by simp, ?_⟩
    intro a ha b' hb' hab
    simp at hb'; subst hb'; subst hab; exact Hnin ha
  have hdb : swift.depsBefore (X ++ [(x, dv.c, dv.D)]) := swift.depsBefore_snoc X _ HXp.2.1 hdeps
  ihave #HXrep : [∗list] e' ∈ X ++ [(x, dv.c, dv.D)], swift.exRepOk γ N r b e' $$ []
  · iapply BigSepL.bigSepL_snoc.2
    isplitl
    · iapply swift.exEntsE_rep γ N r b X es $$ HXok
    · iexact HrepN
  ihave HXt : [∗list] e' ∈ X ++ [(x, dv.c, dv.D)], swift.xTix γxu b e'.1 $$ [HXt Htix]
  · iapply BigSepL.bigSepL_snoc.2; iframe HXt Htix
  wp_apply sync.Mutex.wp_Unlock $$ [$HexL $Hlocked Hlog Hsl Hslcap HXl HXe Hown HXt]
  · iunfold swift.execLInvE
    iexists nsl, _, b, X ++ [(x, dv.c, dv.D)], stp
    iframe
    isplitr
    · iexact HXlb'
    isplitr
    · iapply (swift.exEntsE_snoc γ N r b X es _ _ HXp.1) $$ [HXok]
      iframe HXok
      iunfold swift.exEntOkE
      isplitr
      · iunfold swift.exEntOk
        isplitr
        · ipureintro; rfl
        isplitr
        · iexists dv.vs; iframe Hvs; ipureintro; rfl
        iframe HD Hldr
        iexact HphW
      iframe HrepN
      iunfold swift.propIs at HpI
      icases HpI with ⟨%pp0, %w0, %mu0, %addr0, %ts0, %vs0, -, -, -, #Hcis0, -⟩
      iframe Hcis0 HfW
    ipureintro
    exact ⟨by simp [HXp.1], hdb, hnodup⟩
  wp_apply sync.Mutex.wp_Lock $$ [$HsL] as ⟨HsLk, HS⟩
  iunfold swift.succInv at HS
  icases HS with ⟨%ssl, %sl0, Hsucc, Hssl, Hsslcap⟩
  wp_auto
  ipersist r
  wp_join with [Hsucc Hssl Hsslcap desc]
  · ihave %Hslen := ownSlice_len _ _ _ $$ Hssl
    ihave HL : (∃ (i : w64) (sc : swift.CommandId),
        "i" ∷ i_ptr ↦ i ∗ "sc" ∷ sucCmdId_ptr ↦ sc ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z ssl.len⌝ : IProp netDistGF) $$ [i sucCmdId]
    · iexists (W64 0), _; iframe; ipureintro; exact ⟨by decide, by word⟩
    wp_for HL
    wp_if_destruct
    · have hiD : sint.nat i < sl0.length := by rw [Hslen.1]; word
      have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z ssl.len := ⟨Hi.1, by simpa using Hif⟩
      rw [if_pos hb]
      wp_apply wp_load_slice_index (t := swift.CommandId.ty) ssl (sint.Z i) sl0 _ sl0[sint.nat i]
        Hi.1 $$ [Hssl] as Hssl
      · iframe Hssl; ipureintro; exact List.getElem?_eq_getElem hiD
      wp_apply wp_fork
      · -- the successor's delivery goroutine
        wp_auto
        wp_apply wp_bag_send (t := swift.CommandId.ty) γdc dc _ (fun (_ : swift.CommandId) => iprop(True))
          $$ [$Hdcb]
        itrivial
      try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro; exact ⟨by word, by word⟩
    wp_join_done
  wp_apply sync.Mutex.wp_Unlock $$ [$HsL $HsLk Hsucc Hssl Hsslcap]
  · iunfold swift.succInv; iexists _, _; iframe
  cases dr
  case false => wp_auto; dexitX
  wp_auto
  wp_apply (wp_reply γ γc γm γl γw rp rr N me bw fr l oe rcp d γd MP dv x vsl)
    $$ [Hph Hcmd Hdep Hhs Hprop Hseq Hmsgs Hres]
  · rw [Hids.1, Hbw.1]
    iframe HRC Hrr Hrep Hoe Hinv Hcfg Hpre
    iunfold swift.descF
    iframe Hph Hcmd Hdep Hhs Hprop Hseq Hmsgs Hvs HD HHs Hmb HsL
    isplitr
    · ipureintro; exact Hop
    isplitr
    · ipureintro; exact ⟨Hids.2.1, Hbw.2⟩
    isplitl [Hres]
    · iunfold swift.replyWitE
      iexists X, (x, dv.c, dv.D)
      isplitr
      · ipureintro; exact ⟨rfl, rfl, hdb, hnodup⟩
      iframe Hres
      iexact HXrep
    -- round 37 (table rev 8b K1): the reply goroutine's slot builder, from the owner's `slotB`
    -- and `x`'s execution
    imodintro
    iintro %n %Hn
    iunfold swift.slotB at HsB
    iapply HsB $$ %n %Hn
    iexact HexIn
  iintro Hd
  iunfold swift.descF at Hd
  icases Hd with ⟨Hph, Hcmd, -, Hdep, -, Hhs, -, Hprop, Hseq, Hmsgs, -, -, -⟩
  wp_auto
  cases hsq : dv.seq
  case false =>
    wp_auto
    ihave Htix : iprop(swift.tixD γxu γxm b x dv) $$ []
    · iunfold swift.tixD; iright; iright; iexact HexIn
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    iunfold swift.epochRd
    iunfold swift.descF
    rw [hsq]
    iframe Hbal HStf Hrcf Het Hxe Hph Hcmd Hdep Hhs Hprop Hseq Hmsgs Hvs HD HHs Hmb HsL HRs HrdR Htix Hpin
    isplitr
    ipureintro; exact Hbw
    ipureintro; exact Hop
  wp_auto
  -- a sequential descriptor: wait for its history slot, ignoring other messages
  wp_for
  wp_apply wp_bag_receive (t := go.InterfaceType []) γd dv.msgs MP $$ [$Hmb] as %m Hm
  ihave %Hty := hMPty m $$ Hm
  rcases m with ⟨ty, val⟩ | _
  · by_cases ht : ty = go.int
    · obtain ⟨slot, hslot⟩ := Hty ⟨ty, val⟩ rfl ht
      subst ht; subst hslot
      wp_auto
      icases Hslot with (%Hsq | Hslot)
      · cases Hsq
      iunfold swift.slotOk at Hslot
      -- `wp_apply_raw`: `wp_apply … as HRet` here leaves a silent synthetic `sorry` (an
      -- "unknown free variable" error inside its automation, swallowed)
      wp_apply_raw Hslot $$ [Hm Hph Hcmd Hdep Hhs Hprop Hseq Hmsgs HRs]
      · iframe Hm HRs
        iunfold swift.descF
        rw [hsq]
        iframe Hph Hcmd Hdep Hhs Hprop Hseq Hmsgs Hvs HD HHs Hmb HsL
        isplitr
        · ipureintro; exact Hop
        isplitr
        · ipureintro; exact ⟨rfl, hpn⟩
        iexact HexIn
      inext; iintro HRet
      wp_auto
      wp_for_post
      iapply HΦ
      simp only [↓reduceIte]
      iframe HrdR HRet Hpin
      isplitl [Hbal HStf Hrcf Het Hxe]
      · iunfold swift.epochRd; iframe Hbal HStf Hrcf Het Hxe; ipureintro; exact Hbw
      iexact HexIn
    · wp_auto
      simp only [ht, ↓reduceIte, decide_false]
      wp_auto
      wp_for_post
      iframe
  · wp_auto
    wp_for_post
    iframe

end proof

end Perennial.github_com.imdea_software.swiftpaxos
