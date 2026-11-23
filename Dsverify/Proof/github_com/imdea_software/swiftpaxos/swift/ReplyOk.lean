/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/ReplyOk.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**`replyOk` from the execution record** (request SWC-2, round S1; notes/prove-swift.md
"SWC-2 (round S1)"): the leader's `MReply` witness (`swift.replyOk`, NewSpecs.lean) from the
strengthened execution witness `swift.replyWitE` and the descriptor's paths (`replyPre`'s), through
one sequence prefix of the leader (`swift.locLbs_join`: the longest of the entries' prefixes) and
`sp.exec_result` (ExecResult.lean).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ReplyDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SortedIds
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.LeaderM
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv
import all Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## Pure -/

theorem sp.sortIds_perm {D D' : List sp.CmdId} (hp : D.Perm D') : sp.sortIds D = sp.sortIds D' := by
  have hs : (sp.sortIds D).Pairwise (fun a b => (!(sp.CmdId.lt b a)) = true) :=
    List.pairwise_mergeSort (fun a b c h1 h2 => sp.CmdId.lt_le_trans a b c h1 h2)
      (fun a b => sp.CmdId.le_total a b) D
  exact (sp.sortIds_eq D' (sp.sortIds D) ((List.mergeSort_perm D _).trans hp) hs).symm

/-- The prefix facts an entry's `locLb` must have in the chosen prefix. -/
def swift.seqOk (e : swift.ExE) (s : sp.Seq) : Prop :=
  (toCmdId e.1, e.2.1) ∈ s ∧ (e.2.2.map toCmdId).Perm (sp.depsIn s (toCmdId e.1))

theorem swift.toCmdId_injective : Function.Injective toCmdId := by
  intro a b h
  have := congrArg ofCmdId h
  simpa using this

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions]

theorem sp.depsIn_prefix {s s' : sp.Seq} {y : sp.CmdId} (h : s <+: s') (hy : y ∈ s.map Prod.fst) :
    sp.depsIn s' y = sp.depsIn s y := by
  obtain ⟨u, rfl⟩ := h
  unfold sp.depsIn
  rw [sp.cmdIn_append s u y hy, sp.before_append s u y hy]

theorem swift.seqOk_mono {e : swift.ExE} {s s' : sp.Seq} (h : swift.seqOk e s) (hs : s <+: s') :
    swift.seqOk e s' := by
  refine ⟨hs.subset h.1, ?_⟩
  rw [sp.depsIn_prefix hs (List.mem_map.2 ⟨_, h.1, rfl⟩)]; exact h.2

/-- `ExecOk` of the record's execution against the leader's prefix. -/
theorem swift.execOk_of (s : sp.Seq) (Y : List swift.ExE) (hsnd : (s.map Prod.fst).Nodup)
    (hnd : (Y.map Prod.fst).Nodup) (hdb : swift.depsBefore Y) (hok : ∀ e ∈ Y, swift.seqOk e s) :
    sp.ExecOk s (Y.map swift.exY) := by
  refine ⟨hsnd, ?_, ?_, ?_⟩
  · rw [List.map_map]
    have : (Prod.fst ∘ swift.exY) = toCmdId ∘ Prod.fst := rfl
    rw [this, ← List.map_map]
    unfold List.Nodup at hnd ⊢
    exact List.pairwise_map.2 (List.Pairwise.imp (fun h1 h2 => h1 (swift.toCmdId_injective h2)) hnd)
  · intro i e' hi d hd
    rw [List.getElem?_map] at hi
    cases he : Y[i]? with
    | none => rw [he] at hi; simp at hi
    | some e =>
      rw [he] at hi; simp only [Option.map_some, Option.some.injEq] at hi; subst hi
      simp only [swift.exY, List.mem_map] at hd
      obtain ⟨d0, hd0, rfl⟩ := hd
      have := hdb i e he d0 hd0
      rw [← List.map_take, List.map_map]
      obtain ⟨e0, he0, h0⟩ := List.mem_map.1 this
      exact List.mem_map.2 ⟨e0, he0, by simp [swift.exY, h0]⟩
  · intro e' he'
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
    obtain ⟨h1, h2⟩ := hok e he
    exact ⟨h1, fun d hd => h2.symm.subset hd⟩

omit go_gctx hG sem [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [swift.Assumptions] in
theorem swift.keepPure {P : IProp netDistGF} {φ : Prop} (h : P ⊢ ⌜φ⌝) : P ⊢ P ∗ ⌜φ⌝ :=
  (and_intro .rfl h).trans persistent_and_sep_mp

/-- **One prefix of the leader's sequence for all the entries** (the longest of theirs): against
the authorities, every entry's `locLb` is a prefix of the replica's sequence (`acc_locLb`), so they
are comparable, and `seqOk` holds in the longest. -/
theorem swift.locLbs_join (γ : sp.Names) {S : sp.PState} {mC : GMap sp.CmdId sp.Cmd}
    {mL : GMap (Nat × Nat × Nat) sp.CmdId} (hC : ∀ x, mC.lookup x = S.cmds x)
    (hL : ∀ r b i, mL.lookup (r, b, i) = (S.loc r b)[i]?) (L b : Nat) :
    ∀ Y : List swift.ExE,
    ghostMapAuth γ.loc 1 mL ∗ ghostMapAuth γ.cmds 1 mC ∗
      ([∗list] e ∈ Y, ∃ s : sp.Seq, sp.locLb γ L b s ∗ ⌜swift.seqOk e s⌝) ⊢
    ghostMapAuth γ.loc 1 mL ∗ ghostMapAuth γ.cmds 1 mC ∗
      ∃ s : sp.Seq, sp.locLb γ L b s ∗
        ⌜s.map Prod.fst <+: S.loc L b ∧ s <+: S.seqOf (S.loc L b) ∧ ∀ e ∈ Y, swift.seqOk e s⌝
  | [] => by
    iintro ⟨HL, HC, -⟩
    iframe HL HC
    iexists []
    isplitr
    · iunfold sp.locLb; iapply BigSepL.bigSepL_nil.2; itrivial
    ipureintro; exact ⟨List.nil_prefix, List.nil_prefix, by simp⟩
  | e :: Y => by
    iintro ⟨HL, HC, HY⟩
    ihave ⟨⟨%s1, #Hs1, %h1⟩, HY⟩ := BigSepL.bigSepL_cons.1 $$ HY
    ihave ⟨HL, HC, %s2, #Hs2, %h2⟩ := swift.locLbs_join γ hC hL L b Y $$ [HL HC HY]
    · iframe
    ihave ⟨⟨HL, HC, -⟩, %hp1⟩ := swift.keepPure (sp.acc_locLb (γ := γ) L b s1 hC hL)
      $$ [HL HC]
    · iframe HL HC Hs1
    iframe HL HC
    rcases Nat.le_total s1.length s2.length with hle | hle
    · have h12 : s1 <+: s2 := List.prefix_of_prefix_length_le hp1.2 h2.2.1 hle
      iexists s2
      iframe Hs2
      ipureintro
      refine ⟨h2.1, h2.2.1, fun e' he' => ?_⟩
      rcases List.mem_cons.1 he' with rfl | he'
      · exact swift.seqOk_mono h1 h12
      · exact h2.2.2 e' he'
    · have h21 : s2 <+: s1 := List.prefix_of_prefix_length_le h2.2.1 hp1.2 hle
      iexists s1
      iframe Hs1
      ipureintro
      refine ⟨hp1.1, hp1.2, fun e' he' => ?_⟩
      rcases List.mem_cons.1 he' with rfl | he'
      · exact h1
      · exact swift.seqOk_mono (h2.2.2 e' he') h21

theorem swift.exRepOk_wf (γ : sp.Names) (N r b : Nat) (e : swift.ExE) :
    swift.exRepOk γ N r b e ⊢ ⌜e.2.1.wf⌝ := by
  iunfold swift.exRepOk; iintro ⟨%h, -⟩; ipureintro; exact h

theorem swift.exRepOk_ldr (γ : sp.Names) (N r b : Nat) (e : swift.ExE) (hL : r = sp.leaderOf N b) :
    swift.exRepOk γ N r b e ⊢
      (sp.preacc γ r b (toCmdId e.1) (e.2.2.map toCmdId) ∨ swift.syncIn γ b (toCmdId e.1)) ∗
      ∃ s : sp.Seq, sp.locLb γ r b s ∗ ⌜swift.seqOk e s⌝ := by
  iunfold swift.exRepOk
  iintro ⟨-, (%hn | ⟨Hw, %s, Hs, %hs⟩)⟩
  · exact absurd hL hn
  iframe Hw
  iexists s
  iframe Hs
  ipureintro; exact hs

/-- `me` leads `bw` (the reply goroutine's test) in the model's terms. -/
theorem swift.leader_of_srem (me bw : w32) (N : Nat) (hN : 1 ≤ N ∧ N ≤ 7) (hbw : 0 ≤ sint.Z bw)
    (hme : me = BitVec.srem bw (W32 (sint.Z (W64 (N : Int))))) :
    sp.rid me = sp.leaderOf N (sp.bal bw) := by
  have hv := replica.quorum.leader_val bw N (by omega) hbw
  have hN' : sint.Z (W64 (N : Int)) = N := by word
  rw [hme]
  unfold sp.rid sp.bal sp.leaderOf
  rw [hN']
  have hv' : (BitVec.srem bw (W32 (N : Int))).toInt = bw.toInt % (N : Int) := hv
  rw [hv', Int.toNat_emod hbw (by omega)]
  simp

/-- **`replyOk` from the execution record** (SWC-2): the strengthened execution witness and, at
the leader, the hashes' paths give the leader's `MReply` witness at the reply channel's ballot
`bw` (the record's epoch `bal bw`), with the result's bound. -/
theorem swift.replyOk_of (γ : sp.Names) (γc γm γl : GName) (N : Nat) (fr : Bool)
    (l : List GoString) (me bw : w32) (x : swift.CommandId) (D : List swift.CommandId)
    (Hs : List sp.Hash) (v : GoSlice) (hme : 0 ≤ sint.Z me) (hbw : 0 ≤ sint.Z bw)
    (hN : 1 ≤ N ∧ N ≤ 7) :
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗ swift.replyWitE γ N (sp.rid me) (sp.bal bw) x D v ∗
      (⌜sp.rid me ≠ sp.leaderOf N (sp.bal bw)⌝ ∨ ∃ Ps : List (List sp.CmdId), sp.pathHashes Ps Hs ∗
        (⌜Ps = []⌝ ∨ ∃ P, ⌜Ps = [P]⌝ ∗ sp.pathIs γ (sp.rid me) (sp.bal bw) (toCmdId x) P)) ⊢
    |={⊤}=> ∃ vals : List w8, v ↦*□ vals ∗ ⌜vals.length < 2 ^ 62⌝ ∗
      swift.replyOk γ γc γm N me bw x D Hs vals := by
  unfold sp.inv
  iintro ⟨#Hinv, #Hcfg, Hwit, #Hpaths⟩
  iunfold swift.replyWitE at Hwit
  icases Hwit with ⟨%X, %e, %Hp, #Hv, #Hents⟩
  obtain ⟨hex, heD, hdb, hnd⟩ := Hp
  ihave %Hwf := (BigSepL.bigSepL_mono (fun _ => swift.exRepOk_wf γ N (sp.rid me) (sp.bal bw) _)).trans
    BigSepL.bigSepL_pure_intro $$ Hents
  have hwf : ∀ e' ∈ (X ++ [e]).map swift.exY, e'.2.1.wf := by
    intro e' he'
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he'
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 he0
    exact Hwf k e0 hk
  have hvl : (state.execS e.2.1.op e.2.1.key e.2.1.val (swift.applyX X)).2.length < 2 ^ 62 := by
    rw [swift.applyX_eq_execY]
    have := sp.execS_result_wf (X.map swift.exY)
      (fun e' he' => hwf e' (by rw [List.map_append]; exact List.mem_append_left _ he')) e.2.1
    omega
  by_cases hL : sp.rid me ≠ sp.leaderOf N (sp.bal bw)
  · imodintro
    iexists _
    iframe Hv
    isplitr
    · ipureintro; exact hvl
    iunfold swift.replyOk
    imodintro
    iintro %d %hme' -
    iexfalso; ipureintro
    exact hL (swift.leader_of_srem me bw N hN hbw hme')
  have hL : sp.rid me = sp.leaderOf N (sp.bal bw) := by simpa using hL
  icases Hpaths with (%hn | ⟨%Ps, #HPs, #HPP⟩)
  · exact absurd hL hn
  -- the entries at the leader
  ihave #Hld := BigSepL.bigSepL_mono
    (fun _ => swift.exRepOk_ldr γ N (sp.rid me) (sp.bal bw) _ hL) $$ Hents
  ihave ⟨#Hw, #Hlbs⟩ := BigSepL.bigSepL_sep_eqv.1 $$ Hld
  -- one prefix of the leader's sequence (the invariant: the prefixes' facts)
  iinv Hinv with Hi Hclose
  unfold sp.invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, >HC, >HL,
    >HS, HA, >HP, HCo, HRp, HN, HH, HD, Hown, HQ, HK, >HPa, >%Hrepr, Hnodes, Hproto, HQs, >%Hcl,
    >%HDom, Hcmds, Hconns⟩
  ihave ⟨HL, HC, %s, #Hs, %Hsp⟩ := swift.locLbs_join γ Hrepr.cmds Hrepr.loc (sp.rid me) (sp.bal bw)
    (X ++ [e]) $$ [HL HC Hlbs]
  · iframe HL HC Hlbs
  obtain ⟨hpre, -, hok⟩ := Hsp
  have hxs : swift.seqOk e s := hok e (by simp)
  icases Hproto with (>%Hemp | ⟨%N0, %fr0, %l0, >#Hcfg0, >%Hpi⟩)
  · iexfalso; ipureintro
    have hx := hpre.subset (List.mem_map.2 ⟨_, hxs.1, rfl⟩)
    rw [Hemp.1.1] at hx; simp at hx
  have hsnd : (s.map Prod.fst).Nodup := hpre.sublist.nodup (Hpi.1.loc_ok _ _).1
  imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD Hown HQ HK HPa Hnodes HQs Hcmds Hconns Hcfg0]
    with -
  · inext
    iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK, mPa
    iframe
    isplitr
    · ipureintro; exact Hrepr
    isplitr
    · iright; iexists N0, fr0, l0; iframe Hcfg0; ipureintro; exact Hpi
    isplitr
    · ipureintro; exact Hcl
    ipureintro; exact HDom
  -- the result and the command in the prefix
  have hex' : sp.ExecOk s ((X ++ [e]).map swift.exY) :=
    swift.execOk_of s (X ++ [e]) hsnd hnd hdb hok
  rw [List.map_append, List.map_singleton] at hex'
  have hres := sp.exec_result hex'
  rw [← swift.applyX_eq_execY] at hres
  simp only [swift.exY] at hres
  have hcmd : sp.cmdIn s (toCmdId x) = some e.2.1 := by
    rw [← hex]; exact sp.cmdIn_mem s hsnd _ hxs.1
  imodintro
  iexists _
  iframe Hv
  isplitr
  · ipureintro; exact hvl
  iunfold swift.replyOk
  imodintro
  iintro %d %hme' #Hd
  iunfold sp.msgOk
  iexists N, fr, l, s, Ps, e.2.1
  iframe Hcfg Hs
  isplitr
  · iunfold sp.checksum
    iexists Hs, d
    isplitr
    · ipureintro; rfl
    iframe HPs
    have hp : (D.map toCmdId).Perm (sp.depsIn s (toCmdId x)) := by rw [← heD, ← hex]; exact hxs.2
    unfold sp.depHash
    rw [← sp.sortIds_perm hp, ← hp.length_eq]
    iexact Hd
  isplitr
  · ipureintro
    refine ⟨⟨hme, hbw⟩, hL, hcmd, ?_⟩
    rw [hex] at hres; exact hres
  isplitr
  · iexact HPP
  -- D33's execution witness: the record's commands
  iunfold sp.execW
  iexists (X ++ [e]).map (fun e' => toCmdId e'.1)
  isplitr
  · ipureintro; exact List.mem_map.2 ⟨e, by simp, by rw [hex]⟩
  rw [BigSepL.bigSepL_map]
  iapply BigSepL.bigSepL_mono ?_ $$ Hw
  intro k e' hk
  iintro (#Hpa | #Hsy)
  · iright
    iexists _
    iframe Hpa
    ipureintro
    intro d hd
    obtain ⟨d0, hd0, rfl⟩ := List.mem_map.1 hd
    have := hdb k e' hk d0 hd0
    obtain ⟨e0, he0, h0⟩ := List.mem_map.1 this
    exact List.mem_map.2 ⟨e0, List.mem_of_mem_take he0, by rw [h0]⟩
  · iunfold swift.syncIn at Hsy
    icases Hsy with ⟨%M, #HM, %hM⟩
    ileft
    iexists M
    iframe HM
    ipureintro; exact hM

end proof

end Perennial.github_com.imdea_software.swiftpaxos
