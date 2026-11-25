/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H3/Bcast.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H3: `bcastPrepare` (a `Prepare` to each peer, in `PreferredPeerOrder`'s order) and
`replyPrepare`.

In a section with one `HeapGS` (hub request H2-R0 / H3-R0).
-/
module

public import Dsverify.Proof.gryff.Replica2.Specs
public import Dsverify.Proof.gryff.H3.Pure
public import Dsverify.Proof.gryff.Replica.Base
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2.h3

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.replica2
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF]
variable [strconvA : strconv.Assumptions] -- N-5


set_option goose.wp.extras true

/-- A `PrepareReply` whose `Command` slice is persistent is a message (`msgAt`, H3-R3). -/
theorem prepareReply_msgAt (pR : Loc) (gm : wire.gryffproto.PrepareReply.Msg) (sl : GoSlice) :
    pR ↦ wire.gryffproto.PrepareReply.goVal gm sl ∗ sl ↦*□ gm.Command ⊢
      (msgAt pR (.prepareReply (prepareReplyOf gm)) : IProp GF) := by
  iintro ⟨Hp, Hs⟩
  unfold msgAt
  iexists gm, sl
  iframe
  ipureintro; rfl

/-- What the recovery handlers read of the replica's fixed fields (persistent). -/
abbrev recFixed (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc) : IProp GF :=
  iprop(h.[src.gryff.EPaxosRMWHandler, go!"R"] ↦□ r ∗ r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗
    gR.[src.genericsmr.Replica, go!"Id"] ↦□ rid32 k ∗ gR.[src.genericsmr.Replica, go!"N"] ↦□ W64 3 ∗
    □ h2Fixed k gR h ∗ □ prepCodes h ∗ □ genericOk γ ρ k r gR h)

theorem bcastPrepare_wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc)
    (t : List Ev) (s : RState) (q i b : w32) (outs rest : List Out) (hid : s.id = rid32 k)
    (hb : model.bcastPrepare s q i b = some outs) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ recFixed γ ρ k r gR h ∗
        pendingOuts γ ρ k r t (outs ++ rest) }}
      (App (App (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!!
        go!"bcastPrepare")) (Val #q)) (Val #i)) (Val #b))
    {{ RET #(); pendingOuts γ ρ k r t rest }} := by
  wp_start as ⟨⟨#HR, #HgR, #Hid, #HN, #Hfix, #Hcodes, #Hok⟩, Hpend⟩
  iunfold h2Fixed at Hfix
  icases Hfix with ⟨%pS, %alS, %addrs, %st, %cPA, %cA, %cC, %cCS, %cPAR, %cPAO, %cAR, %cEx,
    #HThr, #HExec, #HPO, #HPOS, #HPAL, #HPALS, %HPAl, #HSt, #HStOk, #Hrest⟩
  -- `Alive` (N1-3): the lock's network side
  icases pendingOuts_alive γ ρ k r gR t _ $$ [$HgR $Hpend] with ⟨Hpend, Hal⟩
  iunfold aliveAt at Hal
  icases Hal with ⟨%aS, #HAl, #HAlS⟩
  iunfold prepCodes at Hcodes
  icases Hcodes with ⟨%cP, %cPR, #HcP, #HcPc, #HcPR, #HcPRc⟩
  have hk : s.id = BitVec.ofNat 32 k.val := by rw [hid]; rfl
  have ho := bcast_eq s k hk (.prepare { leaderId := s.id, replica := q, inst := i, ballot := b })
  simp only [model.bcastPrepare] at hb
  rw [hb, Option.some.injEq] at ho
  subst ho
  wp_apply wp_with_defer_recover
  iintro %defer %pnc Hdefer Hpnc
  wp_auto
  -- the message, as `msgAt`
  ihave Hm : msgAt «$r0_ptr» (.prepare { leaderId := s.id, replica := q, inst := i, ballot := b })
    $$ [«$r0»]
  · unfold msgAt
    iexists _; iframe «$r0»; ipureintro; simp only [prepareOf, hid]
  ihave HI : (∃ j : Nat, "%Hj" ∷ ⌜j ≤ 2⌝ ∗ "sent" ∷ sent_ptr ↦ W64 (j : Int) ∗
      "q" ∷ q_ptr ↦ W32 (((k.val + j) % 3 : Nat) : Int) ∗
      "Hm" ∷ msgAt «$r0_ptr» (.prepare { leaderId := s.id, replica := q, inst := i, ballot := b }) ∗
      "Hpend" ∷ pendingOuts γ ρ k r t
        ([kahn.Out.send (k + 1) (.prepare { leaderId := s.id, replica := q, inst := i, ballot := b }),
          kahn.Out.send (k + 2) (.prepare { leaderId := s.id, replica := q, inst := i, ballot := b })].drop j
          ++ rest) : IProp GF) $$ [sent q Hm Hpend]
  · iexists 0
    rw [List.drop_zero, Nat.add_zero, Nat.mod_eq_of_lt k.isLt]
    iframe Hm Hpend
    isplitr
    · ipureintro; omega
    iframe sent
    simp only [rid32]; iexact q
  wp_for HI
  wp_if_destruct
  · have hj2 : j < 2 := by word
    have hq : BitVec.srem (W32 (((k.val + j) % 3 : Nat) : Int) + W32 1) (W32 (sint.Z (W64 3))) =
        W32 (((k.val + (j + 1)) % 3 : Nat) : Int) ∧
        W32 (((k.val + (j + 1)) % 3 : Nat) : Int) ≠ rid32 k := by
      rcases k with ⟨_ | _ | _ | _, hk⟩ <;> (obtain rfl | rfl : j = 0 ∨ j = 1 := by omega) <;>
        first | omega | (simp only [rid32]; decide)
    rw [hq.1]
    wp_if_destruct
    · exact absurd Hif hq.2
    ihave %HaL := ownSlice_len _ _ _ $$ HAlS
    have hqn : sint.Z (W64 (sint.Z (W32 (((k.val + (j + 1)) % 3 : Nat) : Int)))) =
        (((k.val + (j + 1)) % 3 : Nat) : Int) := by
      have : (k.val + (j + 1)) % 3 < 3 := Nat.mod_lt _ (by omega)
      word
    rw [hqn]
    have hlt : (((k.val + (j + 1)) % 3 : Nat) : Int) < sint.Z aS.len := by
      have : (k.val + (j + 1)) % 3 < 3 := Nat.mod_lt _ (by omega)
      have h1 := HaL.1; have h2 := HaL.2
      simp only [aliveList, List.length_cons, List.length_nil, sint.nat, sint.Z] at h1 h2 ⊢; omega
    rw [if_pos ⟨by omega, hlt⟩]
    wp_apply wp_load_slice_index aS _ (aliveList k) DFrac.discard true (by omega) $$ [HAlS] as -
    · iframe HAlS; ipureintro
      have h3 : (k.val + (j + 1)) % 3 < 3 := Nat.mod_lt _ (by omega)
      have hne : (k.val + (j + 1)) % 3 ≠ k.val := by omega
      rw [Int.toNat_natCast]
      simpa [Fin.ext_iff, hne] using aliveList_get k ⟨_, h3⟩
    -- the send
    have hqlt : (k.val + (j + 1)) % 3 < 3 := Nat.mod_lt _ (by omega)
    let qf : Fin 3 := ⟨(k.val + (j + 1)) % 3, hqlt⟩
    have hqk : qf ≠ k := by
      intro e; have := congrArg Fin.val e; simp only [qf] at this; omega
    have hq1 : j = 0 → qf = k + 1 := by
      intro hj; apply Fin.ext; simp only [qf, Fin.val_add, hj]; simp
    have hq2 : j = 1 → qf = k + 2 := by
      intro hj; apply Fin.ext; simp only [qf, Fin.val_add, hj]; simp
    have hdrop : ∀ (M : Msg), ([kahn.Out.send (k + 1) M, kahn.Out.send (k + 2) M] : List Out).drop j =
        kahn.Out.send qf M :: ([kahn.Out.send (k + 1) M, kahn.Out.send (k + 2) M] : List Out).drop (j + 1) := by
      intro M
      obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
      · rw [hq1 rfl]; rfl
      · rw [hq2 rfl]; rfl
    rw [hdrop, List.cons_append]
    wp_method_call; wp_call
    wp_auto
    have hspec := Replica.SendMsg.wp γ ρ k qf r gR h t
      (.prepare { leaderId := s.id, replica := q, inst := i, ballot := b }) «$r0_ptr» cP
      (([kahn.Out.send (k + 1) (.prepare { leaderId := s.id, replica := q, inst := i, ballot := b }),
          kahn.Out.send (k + 2) (.prepare { leaderId := s.id, replica := q, inst := i, ballot := b })]
          : List Out).drop (j + 1) ++ rest) hqk
    simp only [genM, msgTy, msgKind, rid32, qf] at hspec
    wp_apply hspec $$ [Hm Hpend] as ⟨Hm, Hpend⟩
    · iframe Hm Hpend Hok HgR HcPc
    wp_for_post
    iframe
    iexists (j + 1)
    iframe Hm Hpend
    isplitr
    · ipureintro; omega
    isplitl [sent]
    · rw [show W64 ((j + 1 : Nat) : Int) = W64 (j : Int) + W64 1 by word]; iexact sent
    iexact q
  · have hj2 : j = 2 := by word
    subst hj2
    wp_apply wp_recoverPanic $$ [Hpnc] as Hpnc
    · iexact Hpnc
    rw [List.drop_eq_nil_of_le (by simp), List.nil_append]
    simp only []
    wp_auto
    iapply HΦ $$ Hpend

/-- `replyPrepare(q, reply)`: the reply to peer `q`. -/
theorem replyPrepare_wp (γ : GryffNames GF) (ρ : Repl2Names) (k q : Fin 3) (r gR h : Loc)
    (t : List Ev) (pr : Loc) (rm : model.PrepareReplyM) (rest : List Out) (hq : q ≠ k)
    (x : w32) (hx : x = rid32 q) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ recFixed γ ρ k r gR h ∗
        msgAt pr (.prepareReply rm) ∗ pendingOuts γ ρ k r t (.send q (.prepareReply rm) :: rest) }}
      (App (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!!
        go!"replyPrepare")) (Val #x)) (Val #pr))
    {{ RET #(); msgAt pr (.prepareReply rm) ∗ pendingOuts γ ρ k r t rest }} := by
  subst hx
  wp_start as ⟨⟨#HR, #HgR, #Hid, #HN, #Hfix, #Hcodes, #Hok⟩, Hm, Hpend⟩
  iunfold prepCodes at Hcodes
  icases Hcodes with ⟨%cP, %cPR, #HcP, #HcPc, #HcPR, #HcPRc⟩
  wp_auto
  wp_method_call; wp_call
  wp_auto
  have hspec := Replica.SendMsg.wp γ ρ k q r gR h t (.prepareReply rm) pr cPR rest hq
  simp only [genM, msgTy, msgKind] at hspec
  wp_apply hspec $$ [Hm Hpend] as ⟨Hm, Hpend⟩
  · iframe Hm Hpend Hok HgR HcPRc
  iapply HΦ; iframe

end

end Perennial.gryff.replica2.h3
