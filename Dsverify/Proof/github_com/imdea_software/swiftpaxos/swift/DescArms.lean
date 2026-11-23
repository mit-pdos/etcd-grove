/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/DescArms.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**The descriptor arms of the run loop** (round 27, sv-swb; notes/prove-swift.md §33): the run
loop's `getCmdDesc`/`getCmdDescSeq` calls with a message (`"deliver"`/`"recheck"` strings, light slow
acks, fast acks) over `swift.runInv`, from `getCmdDescWith.coreSpecD` at the descriptors' state
`swift.descDSN` (GetDescWith.lean's `wp_coreD`), for the run-loop side to link in `swift.RunArms`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunInvD
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GetDescWith

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

set_option goose.wp.extras true

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
  [sync.Assumptions] in
/-- A fast ack's run-loop witness (`runAckW`): its sender's and ballot's wire bounds, and its
sender is not its ballot's leader or it has a fast ack's witness (an `MOptAcks` fast entry's
`ackOk` is one: `fastOfAck` keeps its fields). -/
theorem swift.runAckW_fastOk (γ : sp.Names) (γc γm : GName) (N : Nat) (fr : Bool)
    (l : List GoString) (f : sp.FastAck) :
    sp.cfg γc γm N fr l ∗ swift.runAckW γ γc γm f ⊢
      ⌜sp.wireOk f.rep f.bal⌝ ∗
        (⌜sp.rid f.rep ≠ sp.leaderOf N (sp.bal f.bal)⌝ ∨ sp.fastAckOk γ f) := by
  iintro ⟨#Hcfg, #Hw⟩
  iunfold swift.runAckW at Hw
  icases Hw with (#Hf | ⟨%a, %Ha, #Hack, #Hdis⟩)
  · ihave #Hf2 := Hf
    iunfold sp.fastAckOk at Hf2
    icases Hf2 with ⟨%Hwire, -⟩
    isplitr
    · ipureintro; exact Hwire
    iright; iexact Hf
  · obtain ⟨Hf, Hwire⟩ := Ha
    isplitr
    · ipureintro; exact Hwire
    by_cases hd : a.dep = [a.id]
    · icases Hdis with (%Hne | ⟨%N', %fr', %l', #Hcfg', %Hne⟩)
      · exact absurd hd Hne
      · ihave %Hag := sp.cfg_agree (γc := γc) (γm := γm) N N' fr fr' l l' $$ [Hcfg Hcfg']
        · isplitl []
          · iexact Hcfg
          · iexact Hcfg'
        obtain ⟨rfl, -, -⟩ := Hag
        ileft; ipureintro; exact Hne
    · iright
      have hA : sp.ackOk γ (sp.rid f.rep) (sp.bal f.bal) a ⊢ iprop(
          sp.preacc γ (sp.rid f.rep) (sp.bal f.bal) a.id a.dep ∗
          ∃ P, sp.pathIs γ (sp.rid f.rep) (sp.bal f.bal) a.id P ∗ sp.pathHashes [P] a.cs ∗
            sp.numAck γ (sp.rid f.rep) (sp.bal f.bal) a.id a.seqnum ∗
            sp.locDeps γ (sp.rid f.rep) (sp.bal f.bal) a.id a.dep) := by
        unfold sp.ackOk; rw [if_neg hd]
      ihave ⟨#Hpre, %P, #Hpath, #Hph, #Hnum, #Hld⟩ := hA $$ Hack
      have e1 : f.id = a.id := by rw [Hf]; rfl
      have e2 : f.seqnum = a.seqnum := by rw [Hf]; rfl
      have e3 : f.cs = a.cs := by rw [Hf]; rfl
      have e4 : f.dep = a.dep := by rw [Hf]; simp [swift.fastOfAck, hd]
      iunfold sp.fastAckOk
      rw [e1, e2, e3, e4]
      iframe Hpre
      isplitr
      · ipureintro; exact Hwire
      iexists P
      iframe Hpath Hph Hnum Hld

/-- **The `getDesc` arm** (`r.getCmdDesc(x, "deliver"|"recheck", nil)`, swift.go:334/337): a string
message for `x`'s descriptor. -/
theorem swift.runArm_getDesc (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX)
    (wp_core : swift.Replica.getCmdDescWith.coreSpecD (swift.descDSN γ γc γm x) x γ γc γm)
    (xid : swift.CommandId) (s : GoString) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
        swift.runInv rp γ γc γm x }}
      (App (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"getCmdDesc"))
        (Val #xid)) (Val #(interface.mkOk go.string #s))) (Val #slice.nil))
    {{ (d : Loc), RET #d; swift.runInv rp γ γc γm x }} := by
  wp_start as Hinv
  iunfold swift.runInv at Hinv
  icases Hinv with ⟨#Hd, Hs, Hrl, ⟨%ld, %v, %M, %bs, %hd, %w, Hrun, Hpd, %Hn⟩, Hseq, Hdr, Hrf, Hds⟩
  iunfold swift.runSt at Hrun
  icases Hrun with ⟨Hbal, Hrest⟩
  wp_auto
  wp_method_call
  wp_auto
  have hconv : ∀ g : swift.DescG, swift.mpOk x γ γc γm rp g → g.ev.b = sp.bal v.ballot →
      iprop(True) ⊢ g.mp xid (interface.mkOk go.string #s) := by
    intro g hmpOk _
    have hmp : _ = _ := hmpOk
    rw [hmp]
    iintro -
    iunfold swift.descMP
    ileft
    iunfold swift.ackMsgP
    iright; iright
    ipureintro; exact ⟨s, rfl⟩
  -- round 37b (table rev 8c, GAP-37b/37d): `proposeCtxB` and the history from `runLoopCtx`
  ihave ⟨#Hown, Hrl⟩ := BI.persistent_entails_right (swift.runLoopCtx_ownB rp γ γc γm x) $$ Hrl
  ihave ⟨#HdC, Hds⟩ := BI.persistent_entails_right (swift.descDS_ctx γ γc γm x rp) $$ Hds
  ihave ⟨#HpB, #Hhist⟩ := Hown $$ HdC
  ihave Hds : swift.descDSN γ γc γm x γ x.γdl x.N x.r rp $$ [Hds]
  · iunfold swift.descDSN; iframe Hds HpB Hhist
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
    unfold swift.DC.ctx; iexact Hd
  wp_apply (wp_core γ x.γdl rp xid (interface.mkOk go.string #s) false x.N x.r (sp.bal v.ballot)
    iprop(True) v.ballot _ (by simp [interface.mkOk]) hconv) $$ [Hds Hdr Hbal] as %d ⟨Hds, Hdr, Hbal⟩
  · iframe Hds Hdr Hbal
    ipureintro; rfl
  iunfold swift.descDSN at Hds
  icases Hds with ⟨Hds, -, -⟩
  iapply HΦ
  iunfold swift.runInv
  iframe Hd Hs Hrl Hdr Hrf Hds Hseq
  iexists ld, v, M, bs, hd, w
  isplitl [Hbal Hrest]
  · iunfold swift.runSt
    iframe Hbal Hrest
  iframe Hpd
  ipureintro; exact Hn

/-- **A sync entry's descriptor** (round 47, task 3: `getCmdDesc.syncSpecI`'s instance at the run
loop's names, `handleSync`'s `getCmdDesc(cmdId, &syncEntry{…}, nil)`, recovery.go:667):
`getCmdDescWith`'s core at `descDSN`, from `descEpS` (`descDS ∗ descPC`, D61 (1)); the entry is
the epoch's message `syncMP` (`mpOk`'s sync disjunct); `r = x.r` from `ridIs` against the
record's context (the same `Replica` and `Id` fields); `b'` is the epoch's ballot by the core's
`ballot` share. -/
theorem swift.Replica.getCmdDesc.syncSpecD (γ : sp.Names) (γc γm : GName) (x : swift.RunX) (rp : Loc)
    (wp_core : x.str = swift.cmdStr →
      swift.Replica.getCmdDescWith.coreSpecD (swift.descDSN γ γc γm x) x γ γc γm) :
    swift.Replica.getCmdDesc.syncSpecI (hG := hG) (swift.descEpS γ γc γm x rp) γ x.syncN.γcl
      x.syncN.γdl rp x.N := by
  intro gp se r b' i M done xid c vs dsl D bw qb
  simp only [show x.syncN.γdl = x.γdl from rfl, show x.syncN.γcl = x.γcl from rfl]
  wp_start as ⟨HEp, Hrdr, #Hrid, Hbal, %Hb, Hse, #Hvs, #Hdsl, #Hprop, #HsI, #HlA, #Hacc, Hcl, #Hlb, #HlbL, %Hmem⟩
  iunfold swift.descEpS at HEp
  icases HEp with ⟨Hds, #HPC⟩
  iunfold swift.descPC at HPC
  icases HPC with ⟨#Hd, #HpB, #Hhist, %Hstr⟩
  -- `r` is the record's replica (`ridIs` against the context's `Replica`/`Id` fields)
  ihave #Hd2 := Hd
  iunfold swift.DC.ctx at Hd2
  iunfold swift.descCtxE at Hd2
  icases Hd2 with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, #Hrr, #Hrep, %Hids,
    -⟩
  iunfold swift.ridIs at Hrid
  icases Hrid with ⟨%rr2, %me2, #Hrr2, #Hid2, %Hr2⟩
  icombine Hrr Hrr2 gives %Hrre
  subst Hrre
  ihave #HN := Hrep
  iunfold replica.isReplica at HN
  icases HN with ⟨%lg', %cfgp, %tbl, %pc, %fr', %nid, %ents, %γpc, %pwsl, %alsl, %latsl, %pws,
    %cwm, -, -, -, #Hid, -⟩
  icombine Hid Hid2 gives %Hmee
  subst Hmee
  have hr : r = x.r := Hr2.symm.trans Hids.1
  subst hr
  wp_auto
  wp_method_call
  wp_auto
  have hconv : ∀ g : swift.DescG, swift.mpOk x γ γc γm rp g → g.ev.b = b' →
      swift.syncMP γ x.γcl x.r (sp.leaderOf x.N b') b' xid
        (interface.mkOk (go.GoType.PointerType swift.syncEntry.ty) #se) ⊢
        g.mp xid (interface.mkOk (go.GoType.PointerType swift.syncEntry.ty) #se) := by
    intro g hmpOk hgb
    have hmp : _ = _ := hmpOk
    rw [hmp, hgb]
    iintro H
    iunfold swift.descMP
    iright; iright; iright
    iexact H
  ihave Hds : swift.descDSN γ γc γm x γ x.γdl x.N x.r rp $$ [Hds]
  · iunfold swift.descDSN; iframe Hds HpB Hhist
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
    iexact Hd
  ihave HPm : swift.syncMP γ x.γcl x.r (sp.leaderOf x.N b') b' xid
      (interface.mkOk (go.GoType.PointerType swift.syncEntry.ty) #se) $$ [Hse Hcl]
  · iunfold swift.syncMP
    iexists se, gp, c, vs, dsl, D, M, i
    iframe Hse Hvs Hdsl Hprop HsI HlA Hacc Hcl Hlb HlbL
    ipureintro; exact ⟨rfl, Hmem⟩
  wp_apply (wp_core Hstr γ x.γdl rp xid (interface.mkOk (go.GoType.PointerType swift.syncEntry.ty) #se)
    false x.N x.r b' _ bw qb (by simp [interface.mkOk]) hconv) $$ [Hds Hrdr Hbal HPm]
    as %d ⟨Hds, Hrdr, Hbal⟩
  · iframe Hds Hrdr Hbal HPm
    ipureintro; exact Hb
  iapply HΦ
  iframe Hrdr Hbal
  iunfold swift.descDSN at Hds
  icases Hds with ⟨Hds, -, -⟩
  iunfold swift.descEpS
  iframe Hds
  iunfold swift.descPC
  iframe Hd HpB Hhist
  ipureintro; exact Hstr

/-- **The `slowDesc` arm** (`r.getCmdDesc(ack.CmdId, ack, nil)` for an `MLightSlowAck`,
swift.go:351): the ack goes to its command's descriptor, with `ackWhy` (change log C16: a light
slow ack's sender is not its ballot's leader). -/
theorem swift.runArm_slowDesc (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX)
    (wp_core : swift.Replica.getCmdDescWith.coreSpecD (swift.descDSN γ γc γm x) x γ γc γm)
    (l : Loc) (sa : swift.MLightSlowAck) (s : sp.SlowAck) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
        swift.runInv rp γ γc γm x ∗
        l ↦□ sa ∗ ⌜swift.slowAckRepr sa s⌝ ∗ sp.msgOk γ γc γm (.lightSlowAck s) }}
      (App (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"getCmdDesc"))
        (Val #sa.CmdId')) (Val #(interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #l)))
        (Val #slice.nil))
    {{ (d : Loc), RET #d; swift.runInv rp γ γc γm x }} := by
  wp_start as ⟨Hinv, #Hl, %Hrepr, #Hok⟩
  iunfold swift.runInv at Hinv
  icases Hinv with ⟨#Hd, Hs, Hrl, ⟨%ld, %v, %M, %bs, %hd, %w, Hrun, Hpd, %Hn⟩, Hseq, Hdr, Hrf, Hds⟩
  iunfold swift.runSt at Hrun
  icases Hrun with ⟨Hbal, Hrest⟩
  ihave #Hd2 := Hd
  iunfold swift.descCtxE at Hd2
  icases Hd2 with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, -, -, -, -, -, -,
    -, #Hcfg, -⟩
  wp_auto
  wp_method_call
  wp_auto
  have hconv : ∀ g : swift.DescG, swift.mpOk x γ γc γm rp g → g.ev.b = sp.bal v.ballot →
      iprop(l ↦□ sa ∗ sp.msgOk γ γc γm (.lightSlowAck s) ∗ sp.cfg γc γm x.N fr lg) ⊢
        g.mp sa.CmdId' (interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #l) := by
    intro g hmpOk hb
    have hmp : _ = _ := hmpOk
    rw [hmp]
    iintro ⟨#Hl, #Hok, #Hcfg⟩
    iunfold swift.descMP
    ileft
    iunfold swift.ackMsgP
    iright; ileft
    iexists l, sa
    iframe Hl
    isplitr
    · ipureintro; rfl
    iunfold sp.msgOk at Hok
    icases Hok with ⟨-, -, %N', %fr', %l', #Hcfg', %Hne⟩
    ihave %Hag := sp.cfg_agree (γc := γc) (γm := γm) x.N N' fr fr' lg l' $$ [Hcfg Hcfg']
    · isplitl []
      · iexact Hcfg
      · iexact Hcfg'
    obtain ⟨rfl, -, -⟩ := Hag
    obtain ⟨h1, h2, -⟩ := Hrepr
    iunfold swift.ackWhy
    by_cases hbal : sp.bal sa.Ballot' = g.ev.b
    · iright; ipureintro
      rw [h1, ← hbal, h2]; exact Hne
    · ileft; ipureintro; exact hbal
  -- round 37b (table rev 8c, GAP-37b/37d): `proposeCtxB` and the history from `runLoopCtx`
  ihave ⟨#Hown, Hrl⟩ := BI.persistent_entails_right (swift.runLoopCtx_ownB rp γ γc γm x) $$ Hrl
  ihave ⟨#HdC, Hds⟩ := BI.persistent_entails_right (swift.descDS_ctx γ γc γm x rp) $$ Hds
  ihave ⟨#HpB, #Hhist⟩ := Hown $$ HdC
  ihave Hds : swift.descDSN γ γc γm x γ x.γdl x.N x.r rp $$ [Hds]
  · iunfold swift.descDSN; iframe Hds HpB Hhist
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
    unfold swift.DC.ctx; iexact Hd
  wp_apply (wp_core γ x.γdl rp sa.CmdId' (interface.mkOk (go.GoType.PointerType swift.MLightSlowAck.ty) #l)
    false x.N x.r (sp.bal v.ballot) _ v.ballot _ (by simp [interface.mkOk]) hconv)
    $$ [Hds Hdr Hbal] as %d ⟨Hds, Hdr, Hbal⟩
  · iframe Hds Hdr Hbal Hl Hok Hcfg
    ipureintro; rfl
  iunfold swift.descDSN at Hds
  icases Hds with ⟨Hds, -, -⟩
  iapply HΦ
  iunfold swift.runInv
  iframe Hd Hs Hrl Hdr Hrf Hds Hseq
  iexists ld, v, M, bs, hd, w
  isplitl [Hbal Hrest]
  · iunfold swift.runSt
    iframe Hbal Hrest
  iframe Hpd
  ipureintro; exact Hn

/-- **The `fastDesc` arm** (`r.getCmdDescSeq(ack.CmdId, ack, nil, nil, sq)` for an `MFastAck`,
swift.go:342-348): the ack goes to its command's descriptor with `fastWhy` (from `runAckW`). -/
theorem swift.runArm_fastDesc (rp : Loc) (γ : sp.Names) (γc γm : GName) (x : swift.RunX)
    (wp_core : swift.Replica.getCmdDescWith.coreSpecD (swift.descDSN γ γc γm x) x γ γc γm)
    (l : Loc) (fa : swift.MFastAck) (f : sp.FastAck) (sq : Bool) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
        swift.runInv rp γ γc γm x ∗
        l ↦□ fa ∗ swift.fastAckRepr fa f ∗ swift.runAckW γ γc γm f }}
      (App (App (App (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"getCmdDescSeq"))
        (Val #fa.CmdId')) (Val #(interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l)))
        (Val #slice.nil)) (Val #slice.nil)) (Val #sq))
    {{ (d : Loc), RET #d; swift.runInv rp γ γc γm x }} := by
  wp_start as ⟨Hinv, #Hl, #Hrepr, #Hw⟩
  iunfold swift.runInv at Hinv
  icases Hinv with ⟨#Hd, Hs, Hrl, ⟨%ld, %v, %M, %bs, %hd, %w, Hrun, Hpd, %Hn⟩, Hseq, Hdr, Hrf, Hds⟩
  iunfold swift.runSt at Hrun
  icases Hrun with ⟨Hbal, Hrest⟩
  ihave #Hd2 := Hd
  iunfold swift.descCtxE at Hd2
  icases Hd2 with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, -, -, -, -, -, -,
    -, #Hcfg, -⟩
  wp_auto
  have hconv : ∀ g : swift.DescG, swift.mpOk x γ γc γm rp g → g.ev.b = sp.bal v.ballot →
      iprop(l ↦□ fa ∗ swift.fastAckRepr fa f ∗ swift.runAckW γ γc γm f ∗ sp.cfg γc γm x.N fr lg) ⊢
        g.mp fa.CmdId' (interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l) := by
    intro g hmpOk hb
    have hmp : _ = _ := hmpOk
    rw [hmp]
    iintro ⟨#Hl, #Hrepr, #Hw, #Hcfg⟩
    ihave ⟨%Hwire, #Hwhy⟩ := swift.runAckW_fastOk γ γc γm x.N fr lg f $$ [Hcfg Hw]
    · iframe Hcfg Hw
    iunfold swift.fastAckRepr at Hrepr
    icases Hrepr with ⟨%Hr, #HD, #Hcs⟩
    obtain ⟨h1, h2, h3, -⟩ := Hr
    iunfold swift.descMP
    ileft
    iunfold swift.ackMsgP
    ileft
    iexists l, fa
    iframe Hl
    isplitr
    · ipureintro; refine ⟨rfl, ?_⟩; rw [h1]; exact Hwire.1
    isplitr
    · iexists _; iexact HD
    iunfold swift.fastWhy
    icases Hwhy with (%Hne | #Hok)
    · by_cases hbal : sp.bal fa.Ballot' = g.ev.b
      · ileft; ipureintro
        rw [h1, ← hbal, h2]; exact Hne
      · iright; iunfold swift.leadWitB; ileft; ipureintro; exact hbal
    · iright; iunfold swift.leadWitB; iright
      iunfold swift.leadWit
      iexists f
      iframe Hl Hok
      isplitr
      · ipureintro; exact ⟨h1, h2, h3⟩
      iframe HD
      iexists _; iexact Hcs
  -- round 37b (table rev 8c, GAP-37b/37d): `proposeCtxB` and the history from `runLoopCtx`
  ihave ⟨#Hown, Hrl⟩ := BI.persistent_entails_right (swift.runLoopCtx_ownB rp γ γc γm x) $$ Hrl
  ihave ⟨#HdC, Hds⟩ := BI.persistent_entails_right (swift.descDS_ctx γ γc γm x rp) $$ Hds
  ihave ⟨#HpB, #Hhist⟩ := Hown $$ HdC
  ihave Hds : swift.descDSN γ γc γm x γ x.γdl x.N x.r rp $$ [Hds]
  · iunfold swift.descDSN; iframe Hds HpB Hhist
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
    unfold swift.DC.ctx; iexact Hd
  wp_apply (wp_core γ x.γdl rp fa.CmdId' (interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l)
    sq x.N x.r (sp.bal v.ballot) _ v.ballot _ (by simp [interface.mkOk]) hconv)
    $$ [Hds Hdr Hbal] as %d ⟨Hds, Hdr, Hbal⟩
  · iframe Hds Hdr Hbal Hl Hrepr Hw Hcfg
    ipureintro; rfl
  iunfold swift.descDSN at Hds
  icases Hds with ⟨Hds, -, -⟩
  iapply HΦ
  iunfold swift.runInv
  iframe Hd Hs Hrl Hdr Hrf Hds Hseq
  iexists ld, v, M, bs, hd, w
  isplitl [Hbal Hrest]
  · iunfold swift.runSt
    iframe Hbal Hrest
  iframe Hpd
  ipureintro; exact Hn

end proof

end Perennial.github_com.imdea_software.swiftpaxos
