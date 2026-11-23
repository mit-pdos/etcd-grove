/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/HandleMsg.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.handleMsg(m, desc, cmdId)` (swift.go) by `x`'s descriptor's owner, the cases of the messages
other than a proposal, a `*syncEntry` and a history slot (round 13, notes/prove-swift.md §19):

* `swift.ackMsgP c b m`: such a message for `x`'s descriptor in epoch `b` (the descriptors'
  message predicate's part for them): a fast ack (read-only) with its witness, gated by the
  ballot (`swift.fastWhy`: the sender is not `b`'s leader, or the leader's ack with
  `swift.leadWitB`), a light slow ack (read-only) with `swift.ackWhy`, or a string (`"deliver"`,
  `"recheck"`; any other string is ignored);
* `swift.Replica.handleMsg.ackSpecI`: from the owner state (`descOwnF`) and the epoch pin, the
  owner state back or the descriptor retired (`descDone`), result `false`;
* `swift.descOwn_deliver`: the owner state opened for `deliver` (its fields `descF`, its epoch
  share, the commit fact when `phase = COMMIT`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.FastAckDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleMsgDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

end defs

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [hook.Assumptions]

end specs

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [sync.Assumptions] [hook.Assumptions]
  [github_com.orcaman.concurrent_map.Assumptions]

/-- **`handleMsg`'s non-proposal cases** (see the file header). -/
theorem swift.Replica.handleMsg.wp_proofAck (RC : Loc → w32 → IProp netDistGF)
    [hRC : ∀ l bw, Persistent (RC l bw)] (MP : GoInterface → IProp netDistGF)
    (AC : swift.DC → IProp netDistGF)
    (str0 : swift.CommandId → GoString)
    (wp_hfa0 : ∀ c : swift.DC, c.str = str0 → swift.Replica.handleFastAck.specIc RC MP AC c)
    (wp_hls0 : ∀ c : swift.DC, c.str = str0 → swift.Replica.handleLightSlowAck.specIc RC MP c)
    (wp_lead0 : ∀ c : swift.DC, c.str = str0 → swift.Replica.fastAckFromLeader.specIc RC MP AC c)
    (wp_deliver0 : ∀ γdl, swift.Replica.deliver.specE str0 γdl MP)
    (hAC : ∀ c, AC c ⊢ ∃ u : Bool, globalAddr swift.useFastAckPool ↦□ u) :
    ∀ c : swift.DC, c.str = str0 → RC = swift.RCh c.γ c.γc c.γm c.rp →
      swift.Replica.handleMsg.ackSpecIc RC MP AC c := by
  intro c hc hRCe γd d x b Do m
  have wp_hfa : ∀ _c : swift.DC, swift.Replica.handleFastAck.specIc RC MP AC c := fun _ => wp_hfa0 c hc
  have wp_hls : ∀ _c : swift.DC, swift.Replica.handleLightSlowAck.specIc RC MP c := fun _ => wp_hls0 c hc
  have wp_lead : ∀ _c : swift.DC, swift.Replica.fastAckFromLeader.specIc RC MP AC c :=
    fun _ => wp_lead0 c hc
  have wp_deliver : ∀ _c : swift.DC, swift.Replica.deliver.specE c.str c.γdl MP :=
    fun _ => hc ▸ wp_deliver0 c.γdl
  wp_start as ⟨#Hctx, #Hack, Hown, #Hm⟩
  iunfold swift.ackMsgP at Hm
  icases Hm with (⟨%l, %fa, ⟨%Hm, %Hpos⟩, #Hl, #HDep, #Hwhy⟩ | ⟨%l, %sa, %Hm, #Hl, #Hwhy⟩ | %Hm)
  · subst Hm
    ihave #Hfa := Hl
    iStructNamed Hfa
    wp_auto
    wp_join (v := #(decide (fa.CmdId' = x))) iprop(True) at (if: #(decide (fa.CmdId'.ClientId' = x.ClientId')) then _ else _)
    · by_cases hc : fa.CmdId'.ClientId' = x.ClientId'
      · rw [decide_eq_true hc]
        wp_auto
        isplitr
        · ipureintro
          rw [decide_eq_decide.mpr (swift.cmdId_eq_iff _ _ hc)]
        · itrivial
      · rw [decide_eq_false hc]
        wp_auto
        isplitr
        · ipureintro
          rw [decide_eq_false (show ¬ fa.CmdId' = x by intro h; exact hc (h ▸ rfl))]
        · itrivial
    iintro -
    try wp_auto
    by_cases hx : fa.CmdId' = x
    · rw [decide_eq_true hx]
      wp_auto
      wp_apply (wp_hfa c γd d x b Do l fa) $$ [Hown] as Hres
      · iframe Hctx Hack Hown Hl HDep
        isplitr
        · ipureintro; exact ⟨hx, Hpos⟩
        iunfold swift.fastWhy at Hwhy; iexact Hwhy
      try wp_auto
      iapply HΦ; iexact Hres
    · rw [decide_eq_false hx]
      wp_auto
      iapply HΦ; ileft; iexact Hown
  · subst Hm
    ihave #Hsa := Hl
    iStructNamed Hsa
    wp_auto
    iunfold swift.descOwnF at Hown
    icases Hown with ⟨Hown, Hocf⟩
    wp_join (v := #(decide (sa.CmdId' = x))) iprop(True) at (if: #(decide (sa.CmdId'.ClientId' = x.ClientId')) then _ else _)
    · by_cases hc : sa.CmdId'.ClientId' = x.ClientId'
      · rw [decide_eq_true hc]
        wp_auto
        isplitr
        · ipureintro
          rw [decide_eq_decide.mpr (swift.cmdId_eq_iff _ _ hc)]
        · itrivial
      · rw [decide_eq_false hc]
        wp_auto
        isplitr
        · ipureintro
          rw [decide_eq_false (show ¬ sa.CmdId' = x by intro h; exact hc (h ▸ rfl))]
        · itrivial
    iintro -
    try wp_auto
    by_cases hx : sa.CmdId' = x
    · rw [decide_eq_true hx]
      wp_auto
      iunfold swift.descOcf at Hocf
      icases Hocf with ⟨%cf, %cond, %fs, %v, Hocfr, #Hcond, #Hvf, #Hfs⟩
      wp_apply (wp_hls c γd d x b iprop(swift.descCore c d x b ∗ Do) l sa cf cond fs v)
        $$ [Hown Hocfr] as Hres
      · ihave #Hufp := hAC c $$ Hack
        iframe Hctx Hufp Hown Hocfr Hl Hwhy
        ipureintro; exact hx
      try wp_auto
      iapply HΦ
      icases Hres with (⟨Hown, Hocfr⟩ | Hdone)
      · ileft; iunfold swift.descOwnF; iframe Hown
        iunfold swift.descOcf; iexists cf, cond, fs, v; iframe Hocfr Hcond Hvf Hfs
      · iright; iexact Hdone
    · rw [decide_eq_false hx]
      wp_auto
      iapply HΦ; ileft; iunfold swift.descOwnF; iframe Hown Hocf
  · obtain ⟨str, rfl⟩ := Hm
    wp_auto
    iunfold swift.descOwnF at Hown
    icases Hown with ⟨Hown, Hocf⟩
    by_cases hdl : str = go!"deliver"
    · -- "deliver"
      rw [decide_eq_true hdl]
      wp_auto
      iunfold swift.descOcf at Hocf
      icases Hocf with ⟨%cf, %cond, %fs, %v, Hocfr, #Hcond, #Hvf, #Hfs⟩
      ihave ⟨%q, %bw, %stp, %rcp, %dv, %Rs, %Rk, Hrd, HrdR, Hpin, #HRC, #HsB, Hd, HRs, HRk, Hcf, #Hwhy,
        #Hrep, Htix, Hsl, Hback, Hgone⟩ :=
        swift.descOwn_deliver c RC MP γd d x b iprop(swift.descCore c d x b ∗ Do) cf cond fs v
        $$ [Hown Hocfr]
      · iframe Hown Hocfr
      ihave #HRCh : swift.RCh c.γ c.γc c.γm c.rp rcp bw $$ []
      · rw [← hRCe]; iexact HRC
      wp_apply (wp_deliver c c.γ c.γc c.γm c.γl c.γw c.γv c.γe c.γo c.γx c.γxe c.γxm c.γxp c.γxu c.γrp c.γcg c.γout c.γcl
          c.γdc γd c.rp c.rr d c.N c.r c.k q q b bw stp rcp dv x Rs
          iprop(⌜c.sq = true⌝ ∗ c.ret d x ∗ c.env d q)) $$ [Hrd HrdR Hpin Hd HRs Hcf Htix Hsl] as %fin Hfin
      · iframe Hrd HrdR Hpin HRCh HsB Hd HRs Hcf Hwhy Hrep Htix Hsl
        iunfold swift.DC.ctx at Hctx; iexact Hctx
      icases Hfin with ⟨Hrd, HrdR, Hpin, Hfin⟩
      try wp_auto
      cases fin
      · simp only [Bool.false_eq_true, ↓reduceIte]
        icases Hfin with ⟨Hd, HRs, Htix⟩
        ihave ⟨Hown, Hocfr⟩ := Hback $$ Hrd HrdR Hpin Hd HRs Htix HRk
        iapply HΦ; ileft; iunfold swift.descOwnF; iframe Hown
        iunfold swift.descOcf; iexists cf, cond, fs, v; iframe Hocfr Hcond Hvf Hfs
      · simp only [↓reduceIte]
        icases Hfin with ⟨#Hex, HRet⟩
        iapply HΦ; iright
        iunfold swift.descDone
        iapply Hgone $$ Hrd HrdR Hpin HRk Hex HRet
    rw [decide_eq_false hdl]
    wp_auto
    by_cases hrc : str = go!"recheck"
    · -- "recheck": the waiting leader ack, if any, again
      rw [decide_eq_true hrc]
      ihave ⟨%wa, Hwa, Hw, Hback⟩ := swift.descOwn_waiting c RC MP γd d x b Do $$ Hown
      wp_auto
      icases Hw with (%Hnil | ⟨%fa, ⟨%Hx, %Hld⟩, #Hwit⟩)
      · subst Hnil
        wp_auto
        iapply HΦ; ileft; iunfold swift.descOwnF; iframe Hocf
        iapply Hback $$ Hwa
      · by_cases hn : wa = null
        · rw [decide_eq_true hn]
          wp_auto
          iapply HΦ; ileft; iunfold swift.descOwnF; iframe Hocf
          iapply Hback $$ Hwa
        rw [decide_eq_false hn]
        wp_auto
        ihave Hown := Hback $$ Hwa
        ihave #Hw2 := Hwit
        iunfold swift.leadWit at Hw2
        icases Hw2 with ⟨%fw, #Hl, -, #HDep, -⟩
        wp_apply (wp_lead c γd d x b Do wa fa) $$ [Hown Hocf] as Hres
        · iframe Hctx Hack Hl
          isplitl [Hown Hocf]
          · iunfold swift.descOwnF; iframe Hown Hocf
          isplitr
          · iexists _; iexact HDep
          isplitr
          · ipureintro; exact Hx
          isplitr
          · ipureintro; exact Hld
          iunfold swift.leadWitB; iright; iexact Hwit
        try wp_auto
        iapply HΦ; iexact Hres
    · rw [decide_eq_false hrc]
      wp_auto
      iapply HΦ; ileft; iunfold swift.descOwnF; iframe Hown Hocf

end proof

end Perennial.github_com.imdea_software.swiftpaxos
