/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/client/InitMsgSets.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`initMsgSets(cmdId)` (swift/client.go:76): the fast and slow message sets of a command, made
(`ReinitMsgSet` of a nil set) with the client's `accept`, `free` and `handleFastAndSlowAcks`
closures, whose specs (`replica.mset.closuresOk`) are proved here over the handler's `core`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.HandleAcks
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.SHashes

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
variable [swift.Assumptions] [replica.Assumptions] [client.Assumptions] [time.Assumptions]
  [dlog.Assumptions] [bytes.Assumptions]

/-- The internal spec of `c.initMsgSets(cmdId)`. -/
abbrev initMsgSets.specI : Prop :=
  ∀ (H : HC) (x : swift.CommandId),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      ctxOk H ∗ quorumsOk H ∗ pathsOwn H true (fun _ => True) ∗ pathsOwn H false (fun _ => True) }}
    (App (Val (H.c @!! go.GoType.PointerType swift.Client.ty @!! go!"initMsgSets")) (Val #x))
  {{ RET #(); pathsOwn H true (hasSet x) ∗ pathsOwn H false (hasSet x) }}

theorem initMsgSets.wp_proof
    (wp_Reinit : replica.mset.MsgSet.ReinitMsgSet.specI (hG := hG))
    (wp_hdl : handleFastAndSlowAcks.specI (hG := hG))
    (wp_SHashesEq : SHashesEq.specI (hG := hG))
    (wp_DepEquals : Dep.Equals.specI (hG := hG)) :
    initMsgSets.specI (hG := hG) := by
  intro H x
  haveI := cmdId_intoValInj (sem := sem)
  wp_start as ⟨#Hctx, #Hq, Hf, Hs⟩
  unfold pathsOwn
  icases Hf with ⟨%fref, %FP, Hfld, HFP, HFs, -⟩
  icases Hs with ⟨%sref, %SP, Hsld, HSP, HSs, -⟩
  simp only [↓reduceIte, Bool.false_eq_true]
  wp_auto
  wp_apply (wp_map_lookup2 (K := swift.CommandId) (V := Loc)) $$ [$HSP] as HSP
  wp_join (v := #(!hasSetB x SP)) at (if: #_ then #true else _) with [m]
  · unfold hasSetB
    cases hSx : SP.lookup x with
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false]
      wp_auto; iframe; ipureintro; rfl
    | some ms =>
      simp only [Option.isSome_some, decide_true, Bool.not_true]
      wp_auto
      by_cases hms : ms = null
      · subst hms; iframe; ipureintro; simp
      · rw [decide_eq_false hms]; iframe; ipureintro; simp [hms]
  wp_apply (wp_map_lookup2 (K := swift.CommandId) (V := Loc)) $$ [$HFP] as HFP
  wp_join (v := #(!hasSetB x FP)) at (if: #_ then #true else _) with [m]
  · unfold hasSetB
    cases hFx : FP.lookup x with
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false]
      wp_auto; iframe; ipureintro; rfl
    | some ms =>
      simp only [Option.isSome_some, decide_true, Bool.not_true]
      wp_auto
      by_cases hms : ms = null
      · subst hms; iframe; ipureintro; simp
      · rw [decide_eq_false hms]; iframe; ipureintro; simp [hms]
  by_cases hboth : hasSetB x SP = true ∧ hasSetB x FP = true
  · rw [hboth.1, hboth.2]
    wp_auto
    iapply HΦ
    isplitl [Hfld HFP HFs]
    · iexists fref, FP; iframe; ipureintro; exact (hasSetB_iff x FP).mp hboth.2
    · iexists sref, SP; iframe; ipureintro; exact (hasSetB_iff x SP).mp hboth.1
  wp_join (v := #false) iprop(initFast_ptr ↦ (!hasSetB x FP)) at (if: #_ then _ else #false)
    with [initFast]
  · cases hS : hasSetB x SP
    · wp_auto; iframe; ipureintro; trivial
    · have hF : hasSetB x FP = false := by
        cases h : hasSetB x FP
        · rfl
        · exact absurd ⟨hS, h⟩ hboth
      rw [hF]; wp_auto; iframe; ipureintro; trivial
  iintro initFast
  wp_auto
  ipersist c
  ihave ⟨%acc, accept, #Hacc⟩ : (∃ acc : GoFunc, accept_ptr ↦ acc ∗ □ ∀ fast : Bool,
      replica.mset.acceptOk acc (entryP H.γ H.γc H.γm H.N H.cid fast (cmdOf x)) accA
        (leaderP H.γ H.γc H.γm H.γr H.cid fast (cmdOf x)) (core H) : IProp netDistGF) $$ [accept]
  · iexists _; iframe accept
    imodintro
    iintro %fast
    unfold replica.mset.acceptOk
    iintro %k %m %lm
    imodintro
    iintro %Ψ ⟨HR, #HP, #HL⟩ HΨ
    wp_auto
    cases lm with
    | nil =>
      wp_auto
      iapply HΨ; iframe HR; iintro -; unfold replica.mset.accOk; ileft; ipureintro; rfl
    | ok i =>
    unfold replica.mset.leaderOk
    icases HL with (%Hn | #HL)
    · cases Hn
    iunfold leaderP at HL
    icases HL with ⟨%fa1, %hs1, %csL, %v, #Ho1, ⟨%Hx1, %Hc1, %Hd1, %Hh1⟩, #Hrep, #Hrec⟩
    iunfold entryP at HP
    icases HP with ⟨%fa2, %hs2, #Ho2, ⟨%Hk2, %Hx2, %Hc2, %Hd2, %Hnl2⟩, #Hw2⟩
    ihave #Ho1' := Ho1
    ihave #Ho2' := Ho2
    iunfold ackObj at Ho1
    iunfold ackObj at Ho2
    icases Ho1 with ⟨%l1, ⟨%Hi, %Hl1len⟩, #Hl1, #Hcs1⟩
    icases Ho2 with ⟨%l2, ⟨%Hm, %Hl2len⟩, #Hl2, #Hcs2⟩
    cases Hi
    subst Hm
    ihave #Hf1 := Hl1
    iStructNamedSuffix Hf1 "1"
    ihave #Hf2 := Hl2
    iStructNamedSuffix Hf2 "2"
    wp_auto
    by_cases hb : fa2.Ballot' = fa1.Ballot'
    rotate_left
    · rw [decide_eq_false hb]
      wp_auto
      iapply HΨ; iframe HR; iintro %h; cases h
    rw [decide_eq_true hb]
    wp_auto
    rw [Hd1, Hd2]
    wp_apply wp_DepEquals as %depEq -
    unfold core
    icases HR with ⟨%dref, %rref, %aref, %D, %Rm, %Dn, %Gr, %As, %spn, Hdel, HD, Hreps, HRm,
      HRe, HspN, Hal, HAs, HDn, HGr, %Hok⟩
    wp_auto
    wp_apply (wp_map_lookup2 (K := swift.CommandId) (V := Unit)) $$ [$HAs] as HAs
    wp_join iprop(∃ (spn' : w64) (As' : GMap swift.CommandId Unit),
        structFieldRef swift.Client go!"slowPaths" H.c ↦ spn' ∗ aref ↦$ As' ∗ fastAck_ptr ↦ l2 ∗
        structFieldRef swift.Client go!"alreadySlow" H.c ↦ aref)
      at (if: (if: _ then _ else _) then _ else _) with [HspN HAs «exists» fastAck Hal]
      as ⟨%spn', %As', HspN, HAs, fastAck, Hal⟩
    · cases depEq
      · cases hA : (As !! fa2.CmdId').isSome
        · simp only [Bool.false_eq_true, decide_false, Bool.not_false]
          wp_auto
          wp_apply (wp_mapInsert (K := swift.CommandId) (V := Unit)) $$ [$HAs] as HAs
          wp_join_done
        · simp only [_root_.decide_true, Bool.not_true]
          wp_auto
          wp_join_done
      · wp_auto
        wp_join_done
    wp_apply wp_SHashesEq $$ [] as %hashEq %Hhash
    · iframe #; ipureintro; exact ⟨Hl1len, Hl2len⟩
    cases hashEq
    · wp_auto
      iapply HΨ
      isplitl
      · iexists dref, rref, aref, D, Rm, Dn, Gr, As', spn'
        iframe; ipureintro; exact Hok
      iintro %h; cases h
    wp_auto
    have Hsh := Hhash rfl
    wp_if_destruct <;> (
      iapply HΨ
      isplitl
      · iexists dref, rref, aref, D, Rm, Dn, Gr, As', spn'
        iframe; ipureintro; exact Hok
      iintro -
      unfold replica.mset.accOk accA
      iright
      imodintro
      iexists fa1, fa2, hs1, hs2
      iframe #
      ipureintro; exact ⟨hb.symm, Hsh⟩)
  ihave ⟨%frf, free, #Hfree⟩ : (∃ frf : GoFunc, free_ptr ↦ frf ∗ □ ∀ fast : Bool,
      replica.mset.freeOk frf (entryP H.γ H.γc H.γm H.N H.cid fast (cmdOf x))
        (leaderP H.γ H.γc H.γm H.γr H.cid fast (cmdOf x)) (core H) : IProp netDistGF) $$ [free]
  · iexists _; iframe free
    imodintro
    iintro %fast
    unfold replica.mset.freeOk
    iintro %m
    imodintro
    iintro %Ψ ⟨HR, -⟩ HΨ
    -- `free` is a no-op (LT-F1: the client's sets do not return acks to the pool)
    wp_auto
    iapply HΨ $$ HR
  unfold quorumsOk
  icases Hq with ⟨#HSQ, #HFQ⟩
  wp_join iprop(∃ (sref' : GoMap) (SP' : GMap swift.CommandId Loc),
      structFieldRef swift.Client go!"slowPathH" H.c ↦ sref' ∗ sref' ↦$ SP' ∗
      ([∗map] y ↦ ms ∈ SP', setOwn H false y ms) ∗ ⌜hasSet x SP'⌝ ∗
      accept_ptr ↦ acc ∗ free_ptr ↦ frf ∗ cmdId_ptr ↦ x)
    at (if: #_ then _ else _) with [Hsld HSP HSs accept free cmdId]
    as ⟨%sref', %SP', Hsld, HSP, HSs, %HxS, accept, free, cmdId⟩
  · cases hS : hasSetB x SP
    · wp_auto
      wp_apply (wp_map_lookup1 (K := swift.CommandId) (V := Loc)) $$ [$HSP] as HSP
      have hnull : (SP !! x).getD (zero_val Loc) = null := by
        have e : SP !! x = SP.lookup x := rfl
        rw [e]
        unfold hasSetB at hS
        revert hS
        cases SP.lookup x with
        | none => intro _; rfl
        | some ms => simp
      rw [hnull]
      wp_apply wp_Reinit null (H.N / 2 + 1) (entryP H.γ H.γc H.γm H.N H.cid false (cmdOf x)) accA
        (leaderP H.γ H.γc H.γm H.γr H.cid false (cmdOf x)) (core H) acc frf
        (methods (go.GoType.PointerType swift.Client.ty) go!"handleFastAndSlowAcks" #H.c)
        $$ [] as %ms' Hms'
      · isplitr
        · ihave %HN := ctxOk_N H $$ Hctx
          ipureintro
          omega
        isplitl
        · imodintro
          unfold replica.mset.closuresOk
          isplitl []; · iapply Hacc
          isplitl []; · iapply Hfree
          unfold replica.mset.handlerOk
          iintro %lm %sl %ms
          imodintro
          iintro %Ψ Hpre HΨ
          iapply (wp_hdl H false (cmdOf x) lm sl ms) $$ [Hpre] HΨ
          iframe #
          iframe
        ileft; ipureintro; rfl
      ihave %Hnn := replica.mset.own_ne_null $$ Hms'
      wp_apply (wp_mapInsert (K := swift.CommandId) (V := Loc)) $$ [$HSP] as HSP
      isplitr; · ipureintro; rfl
      iexists sref, (<[x := ms']> SP)
      iframe
      isplitl [HSs Hms']
      · iapply bigSepM_insert_over
        iframe HSs
        unfold setOwn; iright; iexact Hms'
      ipureintro
      exact ⟨ms', GMap.lookup_insert _ _ _, Hnn⟩
    · wp_auto
      isplitr; · ipureintro; rfl
      iexists sref, SP; iframe; ipureintro; exact (hasSetB_iff x SP).mp hS
  wp_join iprop(∃ (fref' : GoMap) (FP' : GMap swift.CommandId Loc),
      structFieldRef swift.Client go!"fastPathH" H.c ↦ fref' ∗ fref' ↦$ FP' ∗
      ([∗map] y ↦ ms ∈ FP', setOwn H true y ms) ∗ ⌜hasSet x FP'⌝ ∗
      accept_ptr ↦ acc ∗ free_ptr ↦ frf ∗ cmdId_ptr ↦ x)
    at (if: #_ then _ else _) with [Hfld HFP HFs accept free cmdId]
    as ⟨%fref', %FP', Hfld, HFP, HFs, %HxF, accept, free, cmdId⟩
  · cases hF : hasSetB x FP
    · wp_auto
      wp_apply (wp_map_lookup1 (K := swift.CommandId) (V := Loc)) $$ [$HFP] as HFP
      have hnull : (FP !! x).getD (zero_val Loc) = null := by
        have e : FP !! x = FP.lookup x := rfl
        rw [e]
        unfold hasSetB at hF
        revert hF
        cases FP.lookup x with
        | none => intro _; rfl
        | some ms => simp
      rw [hnull]
      wp_apply wp_Reinit null (H.N / 2 + 1) (entryP H.γ H.γc H.γm H.N H.cid true (cmdOf x)) accA
        (leaderP H.γ H.γc H.γm H.γr H.cid true (cmdOf x)) (core H) acc frf
        (methods (go.GoType.PointerType swift.Client.ty) go!"handleFastAndSlowAcks" #H.c)
        $$ [] as %ms' Hms'
      · isplitr
        · ihave %HN := ctxOk_N H $$ Hctx
          ipureintro
          omega
        isplitl
        · imodintro
          unfold replica.mset.closuresOk
          isplitl []; · iapply Hacc
          isplitl []; · iapply Hfree
          unfold replica.mset.handlerOk
          iintro %lm %sl %ms
          imodintro
          iintro %Ψ Hpre HΨ
          iapply (wp_hdl H true (cmdOf x) lm sl ms) $$ [Hpre] HΨ
          iframe #
          iframe
        ileft; ipureintro; rfl
      ihave %Hnn := replica.mset.own_ne_null $$ Hms'
      wp_apply (wp_mapInsert (K := swift.CommandId) (V := Loc)) $$ [$HFP] as HFP
      isplitr; · ipureintro; rfl
      iexists fref, (<[x := ms']> FP)
      iframe
      isplitl [HFs Hms']
      · iapply bigSepM_insert_over
        iframe HFs
        unfold setOwn; iright; iexact Hms'
      ipureintro
      exact ⟨ms', GMap.lookup_insert _ _ _, Hnn⟩
    · wp_auto
      isplitr; · ipureintro; rfl
      iexists fref, FP; iframe; ipureintro; exact (hasSetB_iff x FP).mp hF
  iapply HΦ
  isplitl [Hfld HFP HFs]
  · iexists fref', FP'; iframe; ipureintro; exact HxF
  · iexists sref', SP'; iframe; ipureintro; exact HxS

end proof

end swift.handler

end Perennial.github_com.imdea_software.swiftpaxos
