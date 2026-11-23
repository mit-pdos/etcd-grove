/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/client/HandleAcks.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`handleFastAndSlowAcks` (swift/client.go:253), the handler of both message sets of a command:
with a leader entry, its quorum certifies the command's decision (`HandlerInv.cert`,
`Decide.decide`), the result stored for the leader's ballot is the decided one, and the reply
is registered with a fresh delivery token.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.pkg.TimeInit
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.HandlerState
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.BufferClient__RegisterReply
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Println

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.handler

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [client.Assumptions] [time.Assumptions] [dlog.Assumptions]

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [swift.Assumptions] [client.Assumptions] [time.Assumptions]
  [dlog.Assumptions] in
/-- A command not delivered, of the client, has no delivery token yet. -/
theorem fresh_seq (H : HC) (D : GMap swift.CommandId Unit) (Dn : GMap Nat Unit)
    (x : swift.CommandId)
    (hD : ∀ x, D.lookup x = some () → x.ClientId' = H.cid ∧ 0 ≤ x.SeqNum'.toInt)
    (hDn : ∀ n, (Dn.lookup n).isSome ↔ ∃ x, D.lookup x = some () ∧ x.SeqNum'.toNat = n)
    (hx : D.lookup x = none) (hc : (cmdOf x).cl = H.cid) : Dn.lookup x.SeqNum'.toNat = none := by
  cases h : Dn.lookup x.SeqNum'.toNat with
  | none => rfl
  | some u =>
    exfalso
    obtain ⟨x', h1, h2⟩ := (hDn _).mp (by rw [h]; rfl)
    obtain ⟨c', -⟩ := hD x' h1
    have : x' = x := by
      cases x'; cases x
      simp only [cmdOf] at hc
      simp only at c' h2
      simp only [swift.CommandId.mk.injEq]
      exact ⟨c'.trans hc.symm, BitVec.eq_of_toNat_eq h2⟩
    rw [this, hx] at h1; cases h1

/-- The internal spec of `c.handleFastAndSlowAcks(leaderMsg, msgs)` as `x`'s fast or slow
message set calls it. -/
abbrev handleFastAndSlowAcks.specI : Prop :=
  ∀ (H : HC) (fast : Bool) (x : sp.CmdId) (lm : GoInterface) (sl : GoSlice)
    (ms : List GoInterface),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      ctxOk H ∗ core H ∗ sl ↦* ms ∗
      replica.mset.handlerPre (H.N / 2 + 1) (entryP H.γ H.γc H.γm H.N H.cid fast x) accA
        (leaderP H.γ H.γc H.γm H.γr H.cid fast x) lm ms }}
    (App (App (Val (H.c @!! go.GoType.PointerType swift.Client.ty @!! go!"handleFastAndSlowAcks"))
      (Val #lm)) (Val #sl))
  {{ RET #(); core H }}

theorem handleFastAndSlowAcks.wp_proof
    (wp_RegisterReply : client.BufferClient.RegisterReply.specI (hG := hG))
    (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG)) :
    handleFastAndSlowAcks.specI (hG := hG) := by
  intro H fast x lm sl ms
  haveI := cmdId_intoValInj (sem := sem)
  wp_start as ⟨#Hctx, Hcore, Hsl, #Hpre⟩
  cases lm with
  | nil =>
    wp_auto
    iapply HΦ $$ Hcore
  | ok i =>
  ihave ⟨%fa, %hs, #Hobj, ⟨%Hx, %Hcl⟩, #Hrec, #Hcert⟩ :=
    cert H.γ H.γc H.γm H.γr H.N H.cid fast x (GoInterface.ok i) ms (by simp) $$ Hpre
  unfold ackObj
  icases Hobj with ⟨%l, ⟨%Hi, %Hlen⟩, #Hl, #Hcs⟩
  cases Hi
  unfold core
  icases Hcore with ⟨%dref, %rref, %aref, %D, %Rm, %Dn, %Gr, %As, %spn, Hdel, HD, Hreps, HRm,
    HRe, HspN, Hal, HAs, HDn, HGr, %Hok⟩
  ihave #Hfa := Hl
  iStructNamed Hfa
  wp_auto
  wp_apply (wp_map_lookup2 (K := swift.CommandId) (V := Unit)) $$ [$HD] as HD
  cases hDx : D.lookup fa.CmdId' with
  | some u =>
    simp only [Option.isSome_some, decide_true]
    wp_auto
    iapply HΦ
    iexists dref, rref, aref, D, Rm, Dn, Gr, As, spn
    iframe
    ipureintro; exact Hok
  | none =>
  simp only [Option.isSome_none, Bool.false_eq_true, decide_false]
  wp_auto
  wp_apply (wp_mapInsert (K := swift.CommandId) (V := Unit)) $$ [$HD] as HD
  iunfold repRec at Hrec
  icases Hrec with ⟨%L, #Hlb, %HinL⟩
  ihave %HGp := mono_list_auth_lb_valid $$ HGr Hlb
  have HGx : (x, fa.Ballot') ∈ Gr := HGp.2.subset HinL
  obtain ⟨HokD, HokDn, HokR⟩ := Hok
  obtain ⟨ir, hir⟩ : ∃ ir, Rm.lookup fa.CmdId' = some ir := by
    have := HokR fa.CmdId' fa.Ballot' (by rw [Hx]; exact HGx) hDx
    exact Option.isSome_iff_exists.mp this
  ihave ⟨Hent, HRe⟩ := (BigSepM.bigSepM_delete (Φ := repsEntry H Gr) hir).1 $$ HRe
  unfold repsEntry
  icases Hent with ⟨%im, Him, %Himb, #Himv⟩
  obtain ⟨vsl, hvsl⟩ : ∃ vsl, im.lookup fa.Ballot' = some vsl :=
    Option.isSome_iff_exists.mp (Himb _ (by rw [Hx]; exact HGx))
  ihave ⟨%v, #Hvsl, %r', %cs', #Hw⟩ := Himv $$ %fa.Ballot' %vsl %hvsl
  wp_apply (wp_map_lookup1 (K := swift.CommandId) (V := GoMap)) $$ [$HRm] as HRm
  rw [hir]
  simp only [Option.getD_some]
  wp_apply (wp_map_lookup1 (K := w32) (V := GoSlice)) $$ [$Him] as Him
  rw [hvsl]
  simp only [Option.getD_some]
  wp_apply (wp_mapDelete (K := swift.CommandId) (V := GoMap)) $$ [$HRm] as HRm
  unfold ctxOk
  icases Hctx with ⟨#Hinv, #Hcfg, #Hb, #Hbag, #HcB, #HLg, #Hq, #Hn, #Hhook, #Hpool, %HN⟩
  wp_auto
  subst Hx
  iapply fupd_wp
  imod decide ⊤ (by simp) H.γ H.γc H.γm H.γl H.N H.fr H.l fa.Ballot' (cmdOf fa.CmdId') r' cs' v
    $$ [Hinv Hcfg Hcert Hw] with #Hdone
  · iframe #
  imod doneRes_seq_nonneg H.γ H.γc H.γm H.γl ⊤ (by simp) (cmdOf fa.CmdId') v $$ [Hinv Hdone]
    with %Hseq
  · iframe #
  have hfresh : Dn.lookup fa.CmdId'.SeqNum'.toNat = none :=
    fresh_seq H D Dn fa.CmdId' HokD HokDn hDx Hcl
  imod mint H.γd Dn fa.CmdId'.SeqNum'.toNat hfresh $$ HDn with ⟨HDn, Htok⟩
  imodintro
  wp_method_call
  wp_call
  wp_auto
  ihave #Htm := swift.time_init $$ Hpkg
  wp_apply wp_RegisterReply H.b H.bv H.γ H.cid H.γd H.γch vsl v fa.CmdId'.SeqNum' $$ [Htok]
  · iframe #
    iframe
    have hcm : ({ cl := H.cid, seq := fa.CmdId'.SeqNum' } : sp.CmdId) = cmdOf fa.CmdId' := by
      simp only [cmdOf] at Hcl ⊢; rw [Hcl]
    rw [hcm]
    iframe #
    ipureintro; exact Hseq
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %psl ⟨-, -⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  ihave #Hbf := Hb
  iStructNamed Hbf
  wp_method_call
  wp_call
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_Println $$ Hq
  iapply HΦ
  iexists dref, rref, aref, (D.insert fa.CmdId' ()), (GMap.delete fa.CmdId' Rm),
    (Dn.insert fa.CmdId'.SeqNum'.toNat ()), Gr, As, spn
  iframe
  ipureintro
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    by_cases hyx : y = fa.CmdId'
    · subst hyx; exact ⟨Hcl, Hseq⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hyx)] at hy; exact HokD y hy
  · intro n
    by_cases hn : fa.CmdId'.SeqNum'.toNat = n
    · subst hn
      simp only [GMap.lookup_insert_eq, Option.isSome_some, true_iff]
      exact ⟨fa.CmdId', GMap.lookup_insert_eq _ _ _, rfl⟩
    · rw [GMap.lookup_insert_ne _ _ hn, HokDn n]
      constructor
      · rintro ⟨y, hy1, hy2⟩
        refine ⟨y, ?_, hy2⟩
        have : y ≠ fa.CmdId' := by rintro rfl; exact hn hy2
        rw [GMap.lookup_insert_ne _ _ (Ne.symm this)]; exact hy1
      · rintro ⟨y, hy1, hy2⟩
        have : y ≠ fa.CmdId' := by rintro rfl; exact hn hy2
        rw [GMap.lookup_insert_ne _ _ (Ne.symm this)] at hy1
        exact ⟨y, hy1, hy2⟩
  · intro y b hyb hyD
    have : y ≠ fa.CmdId' := by
      rintro rfl; rw [GMap.lookup_insert_eq] at hyD; cases hyD
    rw [GMap.lookup_insert_ne _ _ (Ne.symm this)] at hyD
    rw [GMap.lookup_delete_ne _ (Ne.symm this)]
    exact HokR y b hyb hyD

end proof

end swift.handler

end Perennial.github_com.imdea_software.swiftpaxos
