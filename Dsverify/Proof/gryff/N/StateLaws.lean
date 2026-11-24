/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/StateLaws.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N: unfolding laws of its slots in `Replica2/State.lean` (for its own proofs)
-/
module

public import Dsverify.Proof.gryff.Replica2.State

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (Msg Out)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics] [fa : src.fastrpc.Assumptions]


theorem rpcCodeIs_eq (kd : String) (code : w8) :
    rpcCodeIs (GF := GF) kd code = iprop(⌜netN.kindCode kd = some code⌝) := by
  unfold rpcCodeIs; rfl

theorem peerWriterAt_eq (γ : GryffNames GF) (k q : Fin 3) (w : Loc) (ms : List Msg) :
    peerWriterAt γ k q w ms = netN.peerWriterB γ k q w ms := by
  unfold peerWriterAt; rfl

theorem peerWriterAt_unfold (γ : GryffNames GF) (k q : Fin 3) (w : Loc) (ms : List Msg) :
    peerWriterAt γ k q w ms ⊣⊢ netN.peerWriterB γ k q w ms := by
  unfold peerWriterAt; exact .rfl

theorem rpcCodeIs_elim (kd : String) (code : w8) :
    rpcCodeIs kd code ⊢ (⌜netN.kindCode kd = some code⌝ : IProp GF) := by
  unfold rpcCodeIs; exact .rfl

/-- `pendingOuts`' body (an interface definition, `Replica2/State.lean`; unfolded by unit N's
proofs of `SendMsg` and `ConnectToPeers`). -/
theorem pendingOuts_unfold (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (t : List model.Ev) (outs : List Out) :
    pendingOuts γ ρ k r t outs ⊣⊢ netAt γ ρ k r t (fun q => sentToR q outs) ∗
      [∗list] x ∈ pure.extsIn outs, opDone γ.proto x.keyZ x.out := by
  unfold pendingOuts; exact .rfl

theorem clientsOwn_unfold (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (gR : Loc) :
    clientsOwn γ ρ k gR ⊣⊢ ((∃ C : GMap w32 Loc, ghostMapAuth (escrowName ρ) (1 : Qp) C ∗
      [∗map] hs ↦ w ∈ C, writerIs ρ hs w ∗ netN.clientWriterB γ hs w) ∗
    ∃ (dS : GoSlice) (dms : List Loc), gR.[src.genericsmr.Replica, go!"delayRPC"] ↦□ dS ∗
      dS ↦*□ dms ∗ ⌜dms.length = 3⌝ ∗
      [∗list] mp ∈ dms, ∃ M : GMap w8 Bool, mp ↦$ M ∗ ⌜∀ c b, M !! c = some b → b = false⌝) := by
  unfold clientsOwn; exact .rfl

/-- What `SendMsg` reads of the generic replica's fixed parts. -/
theorem genericOk_send (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc) :
    genericOk γ ρ k r gR h ⊢
      gR.[src.genericsmr.Replica, go!"Id"] ↦□ rid32 k ∗
      isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
      isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto := by
  unfold genericOk
  iintro #H
  icases H with ⟨%rt, %ct, %st, %mu, %cwm, %crm, %M, %CM, -, -, -, -, -, -, -, -, -, -, -, -, -,
    #HId, -, -, #Hg, #He, -⟩
  iframe #

/-- The fixed fields (`genericFixed`) are part of `genericOk`. -/
theorem genericOk_fixed (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc) :
    genericOk γ ρ k r gR h ⊢ □ genericFixed k r gR h := by
  unfold genericOk
  iintro #H
  icases H with ⟨%rt, %ct, %st, %mu, %cwm, %crm, %M, %CM, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, #Hf⟩
  unfold genericFixed
  iexact Hf

/-- What the listeners read of the generic replica's fixed parts. -/
theorem genericOk_listen (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc) :
    genericOk γ ρ k r gR h ⊢ ∃ (rt st : Loc) (M : GMap w8 Loc),
      gR.[src.genericsmr.Replica, go!"rpcTable"] ↦□ rt ∗ rt ↦${DFrac.discard} M ∗
      □ ([∗list] kd ∈ netKinds, ∃ (c : w8) (pp obj ch : Loc),
        ⌜netN.kindCode kd = some c ∧ M !! c = some pp⌝ ∗
        pp ↦□ src.genericsmr.RPCPair.mk (interface.mkOk (kindTy kd) #obj) ch ∗
        isChanBag (ρ.chans kd) ch (msgChanP γ ρ k kd)) ∗
      gR.[src.genericsmr.Replica, go!"Stats"] ↦□ st ∗ □ netN.statsOkB st ∗
      gR.[src.genericsmr.Replica, go!"Id"] ↦□ rid32 k ∗
      gR.[src.genericsmr.Replica, go!"Shutdown"] ↦□ false ∗
      isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
      isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto := by
  unfold genericOk
  iintro #H
  icases H with ⟨%rt, %ct, %st, %mu, %cwm, %crm, %M, %CM, #Hrt, #HM, #Htab, -, -, -, #Hst, #Hsto,
    -, -, -, -, -, #HId, #HSh, -, #Hg, #He, -⟩
  iexists rt, st, M
  iframe #


theorem sentToR_send_self (q : Fin 3) (m : Msg) (o : List Out) :
    sentToR q (.send q m :: o) = m :: sentToR q o := by
  unfold sentToR kahn.sentTo
  apply List.filterMap_cons_some
  dsimp only
  exact if_pos rfl

theorem sentToR_send_other (q q' : Fin 3) (m : Msg) (o : List Out) (h : q' ≠ q) :
    sentToR q' (.send q m :: o) = sentToR q' o := by
  unfold sentToR kahn.sentTo
  apply List.filterMap_cons_none
  dsimp only
  exact if_neg (fun e => h e.symm)

theorem forall2_snoc {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β} {a : α} {b : β}
    (h : List.Forall₂ R xs ys) (hab : R a b) : List.Forall₂ R (xs ++ [a]) (ys ++ [b]) := by
  induction h with
  | nil => exact .cons hab .nil
  | cons h _ ih => exact .cons h ih

theorem extsIn_send (q : Fin 3) (m : Msg) (o : List Out) :
    pure.extsIn (.send q m :: o) = pure.extsIn o := by
  simp [pure.extsIn]

theorem msgsWire_snoc {ms : List Msg} {m : Msg} {W b : List w8} (hW : msgsWire ms W)
    (hb : msgWire m b) : msgsWire (ms ++ [m]) (W ++ b) := by
  obtain ⟨bs, hbs, rfl⟩ := hW
  exact ⟨bs ++ [b], forall2_snoc hbs hb, by simp⟩

/-- One element's part of a big separating conjunction over a list without duplicates, the
others' unchanged. -/
theorem bigSepL_acc_upd {A : Type} (l : List A) (hnd : l.Nodup) (q : A) (hq : q ∈ l)
    (Φ Ψ : A → IProp GF) (h : ∀ x, x ≠ q → Φ x = Ψ x) :
    ([∗list] x ∈ l, Φ x) ⊢ Φ q ∗ (Ψ q -∗ [∗list] x ∈ l, Ψ x) := by
  induction l with
  | nil => simp at hq
  | cons a l ih =>
    have hnd' := List.nodup_cons.1 hnd
    refine BigSepL.bigSepL_cons.1.trans ?_
    by_cases ha : a = q
    · subst ha
      have hrest : ([∗list] x ∈ l, Φ x) ⊢ ([∗list] x ∈ l, Ψ x) :=
        BigSepL.bigSepL_mono fun hk => by
          rw [h _ (fun e => hnd'.1 (e ▸ List.mem_of_getElem? hk))]
      iintro ⟨Ha, Hl⟩
      iframe Ha
      iintro Hb
      iapply BigSepL.bigSepL_cons.2
      iframe Hb
      iapply hrest $$ Hl
    · have hq' : q ∈ l := by
        rcases List.mem_cons.1 hq with e | e
        · exact absurd e.symm ha
        · exact e
      iintro ⟨Ha, Hl⟩
      ihave ⟨Hq, Hw⟩ := ih hnd'.2 hq' $$ Hl
      iframe Hq
      iintro Hb
      iapply BigSepL.bigSepL_cons.2
      rw [h a ha]
      iframe Ha
      iapply Hw $$ Hb

theorem msgKind_mem (m : Msg) (h : netN.msgCode m ≠ none) : msgKind m ∈ netKinds := by
  cases m <;> simp [msgKind, netKinds, netN.msgCode] at h ⊢

theorem kindCode_msgKind (m : Msg) (h : netN.msgCode m ≠ none) :
    netN.kindCode (msgKind m) = netN.msgCode m := by
  cases m <;> first | rfl | simp [netN.msgCode] at h

theorem kindTy_msgKind (m : Msg) (h : netN.msgCode m ≠ none) : kindTy (msgKind m) = msgTy m := by
  cases m <;> first | rfl | simp [netN.msgCode] at h

theorem msgCode_same {m m1 : Msg} {c : w8} (h : netN.msgCode m = some c)
    (h1 : netN.msgCode m1 = some c) : msgKind m = msgKind m1 ∧ msgTy m = msgTy m1 := by
  have hk := netN.msgCode_kind h h1
  cases m <;> cases m1 <;> simp only [netN.msgKindIdx] at hk <;>
    first | exact ⟨rfl, rfl⟩ | exact absurd hk (by decide)

/-- The next message on a peer's stream after whole messages: its code is a message kind's, and
the bytes after the code are comparable with the message's encoding. -/
theorem peer_next (γ : GryffNames GF) (q k : Fin 3) (msV : List Msg) (V W : List w8) (c : w8)
    (D : List w8) (hV : msgsWire msV V) (hp : V ++ c :: D <+: W) :
    peerStreamOk γ.proto q k W ⊢ ⌜∃ (m1 : Msg) (e1 : List w8), netN.msgCode m1 = some c ∧
      netN.msgWireB m1 (c :: e1) ∧ (D <+: e1 ∨ e1 <+: D)⌝ := by
  unfold peerStreamOk
  iintro ⟨-, %t2, %ms2, %W2, -, %H⟩
  ipureintro
  obtain ⟨-, ⟨bs2, hbs2, rfl⟩, hW2⟩ := H
  obtain ⟨bsV, hbsV, rfl⟩ := hV
  rw [msgWire_eq] at hbs2 hbsV
  obtain ⟨m1, e1, -, -, hm1, hD⟩ := netN.flat_next hbsV hbs2 (hp.trans hW2)
  obtain ⟨c1, r1, he, hc1⟩ := netN.msgWireB_code hm1
  simp only [List.cons.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨m1, e1, hc1, hm1, hD⟩

theorem peers_nodup (k : Fin 3) : (peers k).Nodup :=
  List.Nodup.sublist (List.filter_sublist) (List.nodup_finRange 3)

theorem mem_peers (k q : Fin 3) (hq : q ≠ k) : q ∈ peers k := by
  unfold peers; simp [hq]

end

end Perennial.gryff.replica2
