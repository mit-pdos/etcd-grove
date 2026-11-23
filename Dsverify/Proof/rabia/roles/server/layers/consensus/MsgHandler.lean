/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/consensus/MsgHandler.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/roles/server/layers/consensus.(*Consensus).MsgHandler` (the message handler's
loop), given `binConMsgHandling`'s spec (`Handler.lean`).
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.consensus.HandlerDefs
public import Dsverify.Proof.rabia.roles.server.layers.consensus.Helpers
public import Perennial.Proof.sync

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.consensus

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model NetConn Dsv rabia.internal.message
  rabia.internal.config rabia.internal.ledger rabia rabia.internal.queue

set_option linter.unusedSectionVars false

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable {cf : RCfg}
variable [package_sem : rabia.roles.server.layers.consensus.Assumptions]

/-- `binConMsgHandling`'s spec (proved in `Handler.lean`, `wp_binConMsgHandling`). -/
abbrev binConMsgHandling.spec : Prop :=
  ∀ (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames)
    (ch : SrvChans) (c : Loc) (v : Msg) (m : MsgV) (X j : Nat) (l : List MsgV),
    X < cf.n → cf.Ok → l[j]? = some m →
    (m.ty = tyProposal ∨ m.ty = tyState ∨ m.ty = tyVote ∨ m.ty = tyDecision) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.consensus ∗ confRO cf ∗
        shared γ ∗ consRO γ cf k γl γc ch c ∗
        (∃ n : w64, structFieldRef Consensus go!"OlderThanTermMsg" c ↦ n) ∗
        frzRes γc ∗ ([∗list] s ↦ _e ∈ γl.slots, hSlot γl γc s) ∗
        msgRep v m ∗ bcastLb γ X l ∗ bmsgOk γ cf X m ∗ rcpt γl X j ∗ prevWit γl γc X m }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"binConMsgHandling")) (Val #v))
    {{ RET #(); (∃ n : w64, structFieldRef Consensus go!"OlderThanTermMsg" c ↦ n) ∗
        frzRes γc ∗ ([∗list] s ↦ _e ∈ γl.slots, hSlot γl γc s) ∗ msgWit γl γc X m }}

/-- The handler's loop invariant: its fields, slots, and the messages processed so far. -/
def hLoop (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (c : Loc) : IProp GF :=
  iprop((∃ n : w64, structFieldRef Consensus go!"OlderThanTermMsg" c ↦ n) ∗
    frzRes γc ∗ ([∗list] s ↦ _e ∈ γl.slots, hSlot γl γc s) ∗
    ∃ (recv : List Msg) (P : List (Nat × Nat)), spscConsumer γl.n2h recv ∗ hLb γl P ∗
      ⌜recv.length = P.length⌝ ∗ [∗list] x ∈ P, procWit γ γl γc x)

theorem hLoop_init (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans)
    (c : Loc) :
    consHandlerRes (GF := GF) γ cf k γl γc ch c ⊢ |={⊤}=> consRO γ cf k γl γc ch c ∗ hLoop γ cf k γl γc c := by
  unfold consHandlerRes hLoop
  iintro ⟨#Hro, Hold, Hfrz, Hslots, Hcons⟩
  ihave Hlb := monoListLbOwn_nil (GF := GF) (A := Nat × Nat) γl.hlog
  imod Hlb with #Hlb
  imodintro
  iframe Hro Hold
  isplitl [Hfrz]
  · unfold frzRes
    iexists ∅
    iframe Hfrz
    iapply BigSepM.bigSepM_empty.2
    itrivial
  isplitl [Hslots]
  · iapply BigSepL.bigSepL_mono_of_forall ?_ $$ Hslots
    intro s e
    unfold slotHandlerPart hSlot
    iintro ⟨Hp, Hq, He, Hpd⟩
    iexists [], [], []
    iframe
    ipureintro; rfl
  iexists [], []
  iframe Hcons
  unfold hLb
  iframe Hlb
  isplit
  · ipureintro; rfl
  · iapply BigSepL.bigSepL_nil.2; itrivial

/-- What a client request's `bmsgOk` gives. -/
theorem bmsgOk_cr (γ : Names) (X : Nat) (m : MsgV) (h : m.ty = tyClientRequest) :
    bmsgOk (GF := GF) γ cf X m ⊢ ∃ o, ⌜m.obj = some o ∧ o.proId.toNat = X⌝ ∗ objOk γ cf o := by
  unfold bmsgOk; simp only [h, ↓reduceIte]; iintro H; iexact H

/-- A `ProposalReply`-typed (or unknown) message is not in a broadcast log. -/
theorem bmsgOk_other (γ : Names) (X : Nat) (m : MsgV) (h0 : m.ty ≠ tyClientRequest)
    (h1 : m.ty ≠ tyProposal) (h2 : m.ty ≠ tyState) (h3 : m.ty ≠ tyVote)
    (h4 : m.ty ≠ tyProposalRequest) (h6 : m.ty ≠ tyDecision) :
    bmsgOk (GF := GF) γ cf X m ⊢ False := by
  unfold bmsgOk; simp only [h0, h1, h2, h3, h4, h6, ↓reduceIte]; iintro H; iexact H

/-- The processed list is the forwards' log but its last element. -/
theorem procs_snoc {P hl : List (Nat × Nat)} {n : Nat} {x : Nat × Nat}
    (hp : P <+: hl ∨ hl <+: P) (hP : P.length = n) (hhl : hl.length = n + 1)
    (hx : hl[n]? = some x) : hl = P ++ [x] := by
  have hpre : P <+: hl := by
    rcases hp with h | h
    · exact h
    · have := h.length_le; omega
  obtain ⟨t, rfl⟩ := hpre
  have ht : t.length = 1 := by simp at hhl; omega
  match t, ht with
  | [y], _ =>
    simp only [List.getElem?_append_right (by omega : P.length ≤ n), hP, Nat.sub_self] at hx
    simp at hx; rw [hx]

theorem msgRound_none_of (m : MsgV) (h1 : m.ty ≠ tyProposal) (h2 : m.ty ≠ tyState)
    (h3 : m.ty ≠ tyVote) : msgRound m = none := by
  simp [msgRound, roundOf, h1, h2, h3]

theorem msgWit_none (γl : SrvNames) (γc : ConsNames) (X : Nat) (m : MsgV) (h : msgRound m = none) :
    ⊢ msgWit (GF := GF) γl γc X m := by
  unfold msgWit; rw [h]; iintro; itrivial

/-- The loop invariant after processing `B_X[j]`. -/
theorem hLoop_next (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (c : Loc)
    (recv : List Msg) (v : Msg) (P hl : List (Nat × Nat)) (X j : Nat) (hhl : hl = P ++ [(X, j)])
    (hlen : recv.length = P.length) :
    (∃ n : w64, structFieldRef Consensus go!"OlderThanTermMsg" c ↦ n) ∗
      frzRes γc ∗ ([∗list] s ↦ _e ∈ γl.slots, hSlot γl γc s) ∗
      spscConsumer γl.n2h (recv ++ [v]) ∗ hLb γl hl ∗ ([∗list] x ∈ P, procWit γ γl γc x) ∗
      procWit γ γl γc (X, j) ⊢ hLoop (GF := GF) γ cf k γl γc c := by
  iintro ⟨Hold, Hfrz, Hslots, Hcons, Hhl, HPw, Hw⟩
  unfold hLoop
  iframe Hold Hfrz Hslots
  iexists recv ++ [v], hl
  iframe Hcons Hhl
  isplitr
  · ipureintro; subst hhl; simp [hlen]
  subst hhl
  iapply BigSepL.bigSepL_snoc.2
  iframe

/-- Server `X`'s broadcast log's invariant, from the shared state. -/
theorem mh_cf_n_le {cf : RCfg} (hc : cf.Ok) : cf.n ≤ maxS := by
  unfold RCfg.Ok at hc; unfold maxS; omega

theorem shared_bcast (γ : Names) (X : Nat) (hX : X < maxS) :
    shared (GF := GF) γ ⊢ inv (bcastN X) (bcastInv γ X) := by
  unfold shared
  iintro ⟨-, #Hb, -, -⟩
  have h : (List.range maxS)[X]? = some X := by simp [hX]
  iapply (BigSepL.bigSepL_lookup
    (Φ := fun _ X => iprop(inv (bcastN X) (bcastInv (GF := GF) γ X))) h) $$ Hb

/-- The witness of the processed message of the round before (the per-sender order). -/
theorem prevWit_of (γ : Names) (γl : SrvNames) (γc : ConsNames) (X j : Nat) (l : List MsgV)
    (m : MsgV) (P : List (Nat × Nat)) (hX : X < maxS) (hl : l[j]? = some m)
    (hP : ∀ j' < j, (X, j') ∈ P) :
    shared (GF := GF) γ ∗ bcastLb γ X l ∗ ([∗list] x ∈ P, procWit γ γl γc x) ⊢
      |={⊤}=> prevWit γl γc X m := by
  iintro ⟨#Hsh, #Hlb, #HP⟩
  unfold prevWit
  rcases hr : msgRound m with _ | ⟨s, _ | ρ⟩
  · imodintro; itrivial
  · imodintro; itrivial
  dsimp only
  by_cases hs : s < lenLedger
  case neg => simp only [hs, ↓reduceIte]; imodintro; itrivial
  simp only [hs, ↓reduceIte]
  ihave #Hinv := shared_bcast γ X hX $$ Hsh
  iinv Hinv with Hi Hclose
  unfold bcastInv
  icases Hi with ⟨%L, >Ha, Hbm, >%HRO⟩
  unfold bcastLb
  ihave %hlL := mono_list_auth_lb_valid _ _ _ _ $$ Ha Hlb
  have hLj : L[j]? = some m := prefix_getElem? hlL.2 hl
  obtain ⟨j', hj', m', hLj', hr'⟩ := HRO.1 j m s ρ hLj hr
  have hmem := hP j' hj'
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
  ihave #Hw := (BigSepL.bigSepL_lookup
    (Φ := fun _ x => iprop(procWit (GF := GF) γ γl γc x)) hi) $$ HP
  unfold procWit
  icases Hw with ⟨%l', %m'', #Hlb', %hl', #Hmw⟩
  simp only at hl'
  iunfold bcastLb at Hlb'
  ihave %hl'L := mono_list_auth_lb_valid _ _ _ _ $$ Ha Hlb'
  have : m'' = m' := by
    have := prefix_getElem? hl'L.2 hl'
    rw [hLj'] at this; exact (Option.some.inj this).symm
  subst this
  imod Hclose $$ [Ha Hbm] with -
  · inext
    iexists L
    iframe Ha Hbm
    ipureintro; exact HRO
  imodintro
  unfold msgWit
  simp only [hr', hs, ↓reduceIte]
  iexact Hmw

/-- A counted proposal's facts (round 0 of slot `s`). -/
theorem bmsgOk_prop0 (γ : Names) (X s : Nat) (m : MsgV) (hr : msgRound m = some (s, 0)) :
    bmsgOk (GF := GF) γ cf X m ⊢ ∃ o, ⌜m.obj = some o ∧ o.svrSeq.toNat = s⌝ ∗ objOk γ cf o ∗
      fact γ.rab (.prop X s) (.obj (o.proId.toNat, o.proSeq.toNat)) := by
  unfold msgRound roundOf at hr
  unfold bmsgOk
  by_cases h1 : m.ty = tyProposal
  · have h0 : m.ty ≠ tyClientRequest := by rw [h1]; decide
    rw [if_neg h0, if_pos h1]
    simp only [h1, ↓reduceIte] at hr
    iintro ⟨%o, %ho, #Hoo, #Hf⟩
    rw [ho.1] at hr
    simp only [Option.map_some, Option.getD_some, Option.some.injEq, Prod.mk.injEq] at hr
    rw [← hr.1]
    iexists o
    iframe Hoo Hf
    ipureintro; exact ⟨ho.1, rfl⟩
  · by_cases h2 : m.ty = tyState
    · have h0 : m.ty ≠ tyClientRequest := by rw [h2]; decide
      rw [if_neg h0, if_neg h1, if_pos h2]
      simp [h1, h2, tyProposal, tyState] at hr
      iintro ⟨%o, %ho, -⟩
      exfalso; have := ho.2.1; omega
    · by_cases h3 : m.ty = tyVote
      · simp [h1, h2, h3, tyProposal, tyState, tyVote] at hr
      · simp [h1, h2, h3] at hr

/-- A persistent big separating conjunction over a sublist (up to a map). -/
theorem bigSepL_sub_pers {A B : Type} (Φ : A → IProp GF) [∀ x, Persistent (Φ x)] (L : List A)
    (L' : List B) (f : B → A) (h : ∀ y ∈ L', f y ∈ L) :
    ([∗list] x ∈ L, Φ x) ⊢ [∗list] y ∈ L', Φ (f y) := by
  iintro #H
  iapply (BigSepL.bigSepL_intro (P := iprop(□ [∗list] x ∈ L, Φ x))
    (Φ := fun _ y => Φ (f y)) (fun k y hk => ?_))
  · iintro #H'
    iapply (BigSepL.bigSepL_mem (Φ := Φ) (h y (List.mem_of_getElem? hk))) $$ H'
  · iexact H

/-- The counted proposals of round 0 (of slot `s`): each has an object, with its facts. -/
theorem props_facts (γ : Names) (s : Nat) : ∀ ents : List Ent,
    (∀ e ∈ ents, msgRound e.2.2.2 = some (s, e.1)) →
    ([∗list] e ∈ ents, bmsgOk (GF := GF) γ cf e.2.1 e.2.2.2) ⊢
      ⌜∀ e ∈ tally ents 0, e.2.2.2.obj ≠ none⌝ ∗
      ([∗list] x ∈ propPairs (tally ents 0), fact γ.rab (.prop x.1 s) (.obj x.2)) ∗
      [∗list] o ∈ (tally ents 0).filterMap (fun e => e.2.2.2.obj), objOk γ cf o
  | [], _ => by
    iintro -
    simp only [tally, List.filter_nil, propPairs, List.filterMap_nil]
    isplitr
    · ipureintro; simp
    isplitr <;> (iapply BigSepL.bigSepL_nil.2; itrivial)
  | e :: ents, hwf => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨#He, H⟩
    ihave ⟨%h1, #H2, #H3⟩ := props_facts γ s ents
      (fun e' he' => hwf e' (List.mem_cons_of_mem _ he')) $$ H
    by_cases h0 : e.1 = 0
    · have ht : tally (e :: ents) 0 = e :: tally ents 0 := by
        simp [tally, List.filter_cons, h0]
      have hr : msgRound e.2.2.2 = some (s, 0) := by rw [← h0]; exact hwf e List.mem_cons_self
      ihave ⟨%o, %ho, #Hoo, #Hf⟩ := bmsgOk_prop0 γ e.2.1 s e.2.2.2 hr $$ He
      rw [ht]
      have hp : propPairs (e :: tally ents 0) = (e.2.1, objId o) :: propPairs (tally ents 0) := by
        simp [propPairs, List.filterMap_cons, ho.1]
      have hf : (e :: tally ents 0).filterMap (fun e => e.2.2.2.obj) =
          o :: (tally ents 0).filterMap (fun e => e.2.2.2.obj) := by
        simp [List.filterMap_cons, ho.1]
      rw [hp, hf]
      isplitr
      · ipureintro
        intro e' he'
        rcases List.mem_cons.1 he' with rfl | he'
        · rw [ho.1]; simp
        · exact h1 e' he'
      isplitr
      · iapply BigSepL.bigSepL_cons.2
        iframe H2
        simp only [objId]
        iexact Hf
      · iapply BigSepL.bigSepL_cons.2
        iframe H3 Hoo
    · have ht : tally (e :: ents) 0 = tally ents 0 := by
        simp [tally, List.filter_cons, h0]
      rw [ht]
      iframe H2 H3
      ipureintro; exact h1

theorem tally_mem' {ents : List Ent} {ρ : Nat} {e : Ent} (h : e ∈ tally ents ρ) : e ∈ ents :=
  (List.mem_filter.1 h).1

/-- Sorting tallies which are a permutation of tallies of distinct ids. -/
theorem sortProps_congr {xs ys : List (ObjV × Nat)} (hd : distinctIds ys) (hp : xs.Perm ys) :
    sortProps xs = sortProps ys := by
  have hdx := distinctIds_perm hd hp.symm
  apply sortProps_eq xs (sortProps ys) hdx (hp.trans (List.mergeSort_perm ys tallyLt).symm)
  intro i j xi xj hi hj hij
  have := pairwise_get? (sortProps_pairwise ys hd) i j xi xj hij hi hj
  exact tallyLt_asymm _ _ this

/-- The sorted tallies of a slot are those of its counted proposals. -/
theorem TallyOk.sorted_eq {st : SlotSt} {ents : List Ent} (h : TallyOk st ents) :
    sortProps st.props = sortProps (groupProps ((tally ents 0).filterMap (fun e => e.2.2.2.obj))) :=
  sortProps_congr (groupOk_groupProps _).1 h.2.1

theorem SlotOk.sort' {s : Nat} {st : SlotSt} {ents : List Ent} {ql : List (Option Nat)}
    {p : Option (Option Nat)} {exd : Bool} {dl rl : List Unit} (h : SlotOk cf s st ents ql p exd dl rl) :
    SlotOk cf s { st with props := sortProps st.props } ents ql p exd dl rl :=
  ⟨h.1.sort, h.2⟩

/-- Sorting the proposals keeps the slot's ghost state. -/
theorem mh_slotGhost_sort (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat)
    (st : SlotSt) :
    slotGhost (GF := GF) γ cf k γl γc s st ⊢ slotGhost γ cf k γl γc s { st with props := sortProps st.props } := by
  unfold slotGhost
  iintro ⟨%ents, %ql, %p, %exd, %dl, %rl, He, Hq, Hp, Hx, Hd, Hr, Hents, %hok⟩
  iexists ents, ql, p, exd, dl, rl
  iframe
  ipureintro; exact hok.sort'

/-- The handler's half of a slot's counted messages tells the slot's tallies. -/
theorem mh_slotGhost_tally (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat)
    (st : SlotSt) (ents : List Ent) :
    slotGhost (GF := GF) γ cf k γl γc s st ∗ monoListAuthOwn (entName γl γc s) (1 : Qp).half ents ⊢
      ⌜TallyOk st ents⌝ ∗ slotGhost γ cf k γl γc s st ∗
        monoListAuthOwn (entName γl γc s) (1 : Qp).half ents := by
  unfold slotGhost
  iintro ⟨⟨%ents', %ql, %p, %exd, %dl, %rl, He, Hq, Hp, Hx, Hd, Hr, Hents, %hok⟩, He'⟩
  ihave %he := monoListAuthOwn_agree _ _ _ _ _ $$ He He'
  obtain ⟨-, h⟩ := he
  subst h
  isplitr
  · ipureintro; exact hok.1
  isplitl [He Hq Hp Hx Hd Hr Hents]
  · iexists _, ql, p, exd, dl, rl
    iframe
    ipureintro; exact hok
  iexact He'

theorem mh_entRes_bmsg (γ : Names) (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : Ent) :
    entRes (GF := GF) γ cf γl γc s e ⊢ entRes γ cf γl γc s e ∗ bmsgOk γ cf e.2.1 e.2.2.2 := by
  unfold entRes
  iintro ⟨H1, #H2, H3, H4⟩
  iframe H1 H3 H4
  iframe H2

/-- The counted messages' facts and shape (from the slot's invariant). -/
theorem ents_info (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV)
    (he : γl.slots[s]? = some e) (ents : List Ent) :
    slotsInv (GF := GF) γ cf k γl γc ∗ monoListAuthOwn (entName γl γc s) (1 : Qp).half ents ⊢
      |={⊤}=> monoListAuthOwn (entName γl γc s) (1 : Qp).half ents ∗
        ⌜(∀ e ∈ ents, e.2.1 < cf.n ∧ msgRound e.2.2.2 = some (s, e.1)) ∧
          (∀ ρ, (tally ents ρ).length ≤ cf.q ∧ ((tally ents ρ).map (fun e => e.2.1)).Nodup)⌝ ∗
        [∗list] e ∈ ents, bmsgOk γ cf e.2.1 e.2.2.2 := by
  iintro ⟨#Hinvs, He'⟩
  ihave #Hinv := slotsInv_lookup γ k γl γc s e he $$ Hinvs
  iinv Hinv with Hi Hclose
  imod Hi with Hi
  unfold slotInv slotGhost
  icases Hi with ⟨%st, Hst, #Hd, %ents', %ql, %p, %exd, %dl, %rl, He, Hq, Hp, Hx, Hdl, Hr, Hents, %hok⟩
  ihave %hag := monoListAuthOwn_agree _ _ _ _ _ $$ He He'
  obtain ⟨-, h⟩ := hag
  subst h
  ihave ⟨Hents, #Hb⟩ := (BigSepL.bigSepL_mono_of_forall
    (fun {_ e} => mh_entRes_bmsg (GF := GF) γ γl γc s e)).trans BigSepL.bigSepL_sep_eqv.1 $$ Hents
  imod Hclose $$ [Hst He Hq Hp Hx Hdl Hr Hents] with -
  · inext
    iexists st
    iframe Hst
    isplitr
    · iexact Hd
    iexists _, ql, p, exd, dl, rl
    iframe
    ipureintro; exact hok
  imodintro
  iframe He' Hb
  ipureintro
  exact ⟨hok.2.1, hok.2.2.1⟩

/-- (A missing law of `message`: unfolds `objRep`.) Setting the slot number of a represented
object. -/
theorem mh_cons_objRep_svrSeq (ov : ConsensusObj) (o : ObjV) (x : w32) :
    objRep (GF := GF) ov o ⊢ objRep { ov with SvrSeq' := x } { o with svrSeq := x } := by
  unfold objRep
  iintro ⟨%h, H⟩
  iframe H
  ipureintro
  exact ⟨h.1, h.2.1, rfl, h.2.2.2⟩

theorem mh_objOk_svrSeq (γ : Names) (o : ObjV) (x : w32) :
    objOk (GF := GF) γ cf o ⊢ objOk γ cf { o with svrSeq := x } := by
  unfold objOk; iintro H; iexact H

theorem mh_HasEnoughMsg (hspec : Slot.HasEnoughMsg.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    (phase round : w32) (hr : round = 1 ∨ round = 2) (R : IProp GF) (Q : SlotSt → IProp GF) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗
        isSlot e.loc e.γ e.q -∗ confRO cf -∗ slotsInv γ cf k γl γc -∗ R -∗
        (∀ st, slotGhost γ cf k γl γc s st -∗ R ={⊤ \ ↑(slotN k s)}=∗
          slotGhost γ cf k γl γc s st ∗ Q st) -∗
        (∀ st, Q st -∗ Φ (#(decide (st.total phase.toNat round.toNat ≥ cf.q)))) -∗
      WP (App (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"HasEnoughMsg"))
        (Val #phase)) (Val #round)) {{ Φ }} := by
  iintro %Φ #Hp #Hs #Hc #Hi HR Hstep HΦ
  iapply wp_HasEnoughMsg_inv hspec γ k γl γc s e he phase round hr R Q
  iframe
  repeat (first | iexact Hp | iexact Hs | iexact Hi | iexact Hc | isplitr)

theorem mh_RecvProposalsMajT (hspec : Slot.RecvProposalsMajT.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    (R : IProp GF) (Q : SlotSt → IProp GF) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗
        isSlot e.loc e.γ e.q -∗ slotsInv γ cf k γl γc -∗ R -∗
        □ (∀ st, slotGhost γ cf k γl γc s st -∗ R -∗
          ⌜st.props ≠ []⌝ ∗ slotGhost γ cf k γl γc s st ∗ R) -∗
        (∀ st, slotGhost γ cf k γl γc s st -∗ R ={⊤ \ ↑(slotN k s)}=∗
          slotGhost γ cf k γl γc s ({ st with props := sortProps st.props }) ∗ Q st) -∗
        (∀ st (n : Nat), ⌜n = ((sortProps st.props).head?.map (·.2)).getD 0⌝ -∗ Q st -∗
          Φ (#(W64 (n : Nat)))) -∗
      WP (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"RecvProposalsMajT")) (Val #()))
        {{ Φ }} := by
  iintro %Φ #Hp #Hs #Hi HR #Hpre Hstep HΦ
  iapply wp_RecvProposalsMajT_inv hspec γ k γl γc s e he R Q
  iframe
  repeat (first | iexact Hp | iexact Hs | iexact Hi | iexact Hpre | isplitr)

theorem mh_RecvProposalsMajV (hspec : Slot.RecvProposalsMajV.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    (R : IProp GF) (Q : SlotSt → IProp GF) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗
        isSlot e.loc e.γ e.q -∗ slotsInv γ cf k γl γc -∗ R -∗
        □ (∀ st, slotGhost γ cf k γl γc s st -∗ R -∗
          ⌜st.props ≠ []⌝ ∗ slotGhost γ cf k γl γc s st ∗ R) -∗
        (∀ st, slotGhost γ cf k γl γc s st -∗ R ={⊤ \ ↑(slotN k s)}=∗
          slotGhost γ cf k γl γc s { st with props := sortProps st.props } ∗ Q st) -∗
        (∀ st (v : ConsensusObj), objRep v ((sortProps st.props).head?.map (·.1)).get! -∗ Q st -∗
          Φ #v) -∗
      WP (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"RecvProposalsMajV")) (Val #()))
        {{ Φ }} := by
  iintro %Φ #Hp #Hs #Hi HR #Hpre Hstep HΦ
  iapply wp_RecvProposalsMajV_inv hspec γ k γl γc s e he R Q
  iframe
  repeat (first | iexact Hp | iexact Hs | iexact Hi | iexact Hpre | isplitr)

/-- The `ProposalReply` the handler builds. -/
def replyMsg (dst seq : w32) (o : ObjV) : MsgV :=
  ⟨tyProposalReply, dst, seq, some { o with svrSeq := seq }⟩

/-- Discharge the bounds check of an `IndexRef`. -/
local macro "slice_index_if'" : tactic =>
  `(tactic| (rw [ite_eq_left_of_eq_true _ _ (eq_true (by constructor <;> word))]))

/-- `genProposalReply(seq, dst)`: the first of slot `seq`'s sorted tallies is `o`. -/
theorem wp_genProposalReply (hMajV : Slot.RecvProposalsMajV.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc) (seq dst : w32) (e : SlotV)
    (hsl : seq.toNat < lenLedger) (he : γl.slots[seq.toNat]? = some e) (ents : List Ent)
    (o1 : ObjV) (hne : (tally ents 0).filterMap (fun e => e.2.2.2.obj) ≠ [])
    (hh : ((sortProps (groupProps ((tally ents 0).filterMap (fun e => e.2.2.2.obj)))).head?.map
      (·.1)).get! = o1) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.consensus ∗ confRO cf ∗
        consRO γ cf k γl γc ch c ∗ monoListAuthOwn (entName γl γc seq.toNat) (1 : Qp).half ents }}
      (App (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"genProposalReply"))
        (Val #seq)) (Val #dst))
    {{ (rv : Msg), RET #rv; |={⊤}=> monoListAuthOwn (entName γl γc seq.toNat) (1 : Qp).half ents ∗
        msgRep rv (replyMsg dst seq o1) }} := by
  wp_start as ⟨#Hconf, #Hro, He⟩
  ihave #Hro' := Hro
  iunfold consRO at Hro'
  icases Hro' with ⟨%ledger, %ql, %wg, #HsvrId, #Hwg, #Hdone, #Hn2h, #Hh2n, #Hn2e, #He2n, #Hql,
    #Hledger, #Hqlock, #Hstat, #Hchans, #HledRO, #Hslinv, #HslCh, #Hkeys⟩
  ihave ⟨%ps, #Hc⟩ := confRO_val $$ Hconf
  ihave Hc2 := Hc
  iStructNamed Hc2
  ihave #HledRO' := HledRO
  iunfold ledgerRO at HledRO'
  icases HledRO' with ⟨#Hsl, %Hlen, #Hslots⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  rw [List.length_map, Hlen] at Hl
  ihave #Hse := (BigSepL.bigSepL_lookup
    (Φ := fun _ e => iprop(isSlot (GF := GF) e.loc e.γ e.q)) he) $$ Hslots
  ihave #Hpl : isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger $$ []
  · iPkgInit
  unfold lenLedger at hsl Hl
  wp_auto
  wp_apply (wp_PanicTermNotMatched γ k γl γc ch c seq hsl) $$ [$Hconf $Hro]
  have hmod : seq % W32 10000 = seq := by word
  rw [hmod]
  slice_index_if'
  wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z seq))) _ _ e.loc (by word) $$ [Hsl]
  · iframe Hsl; ipureintro
    rw [show (sint.Z (W64 (uint.Z seq))).toNat = seq.toNat by word]
    simp [he]
  iintro -
  wp_apply (mh_RecvProposalsMajV hMajV γ k γl γc seq.toNat e he
    (monoListAuthOwn (entName γl γc seq.toNat) (1 : Qp).half ents)
    (fun st => iprop(monoListAuthOwn (entName γl γc seq.toNat) (1 : Qp).half ents ∗
      ⌜((sortProps st.props).head?.map (·.1)).get! = o1⌝))) $$ Hpl Hse Hslinv He [] []
    as %st %ov Hov ⟨He, %hq⟩
  · iintro !> %st Hg He
    ihave ⟨%ht, Hg, He⟩ := mh_slotGhost_tally γ k γl γc seq.toNat st ents $$ [Hg He]
    · iframe
    iframe
    ipureintro; exact (ht.props_head hne).1
  · iintro %st Hg He
    ihave ⟨%ht, Hg, He⟩ := mh_slotGhost_tally γ k γl γc seq.toNat st ents $$ [Hg He]
    · iframe
    imodintro
    iframe He
    isplitl [Hg]
    · iapply mh_slotGhost_sort $$ Hg
    ipureintro; rw [ht.sorted_eq]; exact hh
  ihave #Hov' : objRep ov o1 $$ [Hov]
  · rw [← hq]; iexact Hov
  iapply HΦ
  ipersist obj
  imodintro
  iframe He
  iapply cons_msgRep_intro
  · simp [replyMsg, tyProposalReply]
  simp only [replyMsg]
  iexists _
  iframe obj
  iapply mh_cons_objRep_svrSeq $$ Hov'

theorem hSlots_acc (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV)
    (he : γl.slots[s]? = some e) :
    ([∗list] s ↦ _e ∈ γl.slots, hSlot (GF := GF) γl γc s) ⊢
      hSlot γl γc s ∗ (hSlot γl γc s -∗ [∗list] s ↦ _e ∈ γl.slots, hSlot γl γc s) := by
  iintro H
  ihave ⟨Hs, Hb⟩ := (BigSepL.bigSepL_lookup_acc
    (Φ := fun s (_ : SlotV) => iprop(hSlot (GF := GF) γl γc s)) he).1 $$ H
  iframe Hs
  iintro Hs
  ihave H := Hb $$ %e Hs
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp he
  have : γl.slots.set s e = γl.slots := by rw [← heq]; exact List.set_getElem_self hlt
  rw [this] at *
  iexact H

/-- What a proposal request's `bmsgOk` gives. -/
theorem bmsgOk_preq (γ : Names) (X : Nat) (m : MsgV) (h : m.ty = tyProposalRequest) :
    bmsgOk (GF := GF) γ cf X m ⊢ ⌜m.phase.toNat = X⌝ ∗ ∃ b, fact γ.rab (.preq X m.value.toNat) (.bit b) := by
  unfold bmsgOk
  rw [if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide),
    if_neg (by rw [h]; decide), if_pos h]
  all_goals (iintro ⟨%hp, H⟩; iframe H; ipureintro; exact hp.1)

set_option hygiene false in
/-- Close an iteration of the handler's loop after a message with no round (names of the main
proof). -/
local macro "close_none" : tactic => `(tactic| (
  ihave HI := hLoop_next (cf := cf) γ k γl γc c recv v P hl X j hPhl HPl $$ [Hold Hfrz Hslots Hcons]
  · iframe Hold Hfrz Hslots Hcons Hhl HPw
    unfold procWit
    iexists l, m
    iframe Hlb
    isplitr
    · ipureintro; exact hlj
    iapply msgWit_none γl γc X m hmn
  wp_for_post
  iframe))

set_option hygiene false in
/-- Put slot `s`'s handler part back (names of the main proof). -/
local macro "restore_slot" : tactic => `(tactic| (
  ihave Hslots := Hback $$ [Hprod Hq He Hp]
  · unfold hSlot
    iexists sent, ents, ql
    iframe Hprod Hq He Hp
    ipureintro; exact hsl))

set_option hygiene false in
/-- The `binConMsgHandling` case of the handler's loop (internal; names of the main proof). -/
local macro "bin_tail" : tactic => `(tactic| (
  have hb : m.ty = tyProposal ∨ m.ty = tyState ∨ m.ty = tyVote ∨ m.ty = tyDecision := by
    rw [← hty, Hif]; decide
  wp_apply (hBin γ cf k γl γc ch c v m X j l hX hcok hlj hb) $$ [Hold Hfrz Hslots Hrc]
    as ⟨Hold, Hfrz, Hslots, #Hmw⟩
  · iframe Hold Hfrz Hslots Hrc
    iframe #
    done
  ihave HI := hLoop_next (cf := cf) γ k γl γc c recv v P hl X j hPhl HPl $$ [Hold Hfrz Hslots Hcons]
  · iframe Hold Hfrz Hslots Hcons Hhl HPw
    unfold procWit
    iexists l, m
    iframe Hlb Hmw
    ipureintro; exact hlj
  wp_for_post
  iframe))

theorem Consensus.MsgHandler.wp_proof_of (hBin : binConMsgHandling.spec (GF := GF))
    (hPush : heapPush.spec (GF := GF)) (hHEM : Slot.HasEnoughMsg.spec (GF := GF))
    (hMajT : Slot.RecvProposalsMajT.spec (GF := GF))
    (hMajV : Slot.RecvProposalsMajV.spec (GF := GF)) :
    Consensus.MsgHandler.spec (GF := GF) := fun γ cf k γl γc ch c => by
  wp_start as ⟨#Hconf, #Hsh, #Hcfg, Hres⟩
  ihave %hcok : ⌜cf.Ok⌝ $$ [Hcfg]
  · unfold cfgIs; icases Hcfg with ⟨-, %h⟩; ipureintro; exact h
  iapply fupd_wp
  imod hLoop_init γ k γl γc ch c $$ Hres with ⟨#Hro, HI⟩
  imodintro
  ihave #Hro' := Hro
  iunfold consRO at Hro'
  icases Hro' with ⟨%ledger, %ql, %wg, #HsvrId, #Hwg, #Hdone, #Hn2h, #Hh2n, #Hn2e, #He2n, #Hql,
    #Hledger, #Hqlock, #Hstat, #Hchans, #HledRO, #Hslinv, #HslCh, #Hkeys⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ [Hpkg]
  · iPkgInit
  wp_apply (lc := 4) wp_with_defer as %defer Hdefer
  iclear Hdefer
  ihave #Hch' := Hchans
  iunfold srvChans at Hch'
  icases Hch' with ⟨#HcDone, -, -, -, #HcH2n, -, #HcN2h, -⟩
  iclear Hlc3 Hlc4
  wp_for
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch.done, γl.done
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ HcDone
    iapply bag_recv_au γl.done ch.done _ _ $$ [$Hlc1 $Hlc2] HcDone
    inext
    iintro %v Hv
    unfold doneP
    iexfalso; iexact Hv
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Msg, inferInstance, inferInstance, inferInstance, inferInstance, ch.n2h, γl.n2h.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · unfold isSpsc; icases HcN2h with ⟨#H, -⟩; iexact H
    iunfold hLoop at HI
    icases HI with ⟨Hold, Hfrz, Hslots, %recv, %P, Hcons, #HP, %HPl, #HPw⟩
    iapply spsc_rcv_au γl.n2h ch.n2h _ _ recv _ $$ HcN2h [$Hlc1 $Hlc2] Hcons
    inext
    iintro %v %ok Hv
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      iexfalso; icases Hv with ⟨H, -⟩; iexact H
    simp only [↓reduceIte]
    icases Hv with ⟨Hv, Hcons⟩
    unfold n2hP
    icases Hv with ⟨%m, %X, %j, %l, %hl, %Hpr, #Hm, #Hlb, #Hok, Hrc, #Hhl⟩
    obtain ⟨hX, hlj, hhlen, hhli, hprev⟩ := Hpr
    simp only [Int.toNat_natCast] at hhlen hhli hprev
    ihave #HP' := HP
    ihave #Hhl' := Hhl
    iunfold hLb at HP' Hhl'
    ihave %hP := mono_list_lb_valid γl.hlog P hl $$ HP' Hhl'
    have hPhl := procs_snoc hP HPl.symm hhlen hhli
    ihave %Hf := msgRep_fields v m $$ Hm
    obtain ⟨hty, hph, hval⟩ := Hf
    wp_auto_lc 2
    wp_if_destruct
    · -- ClientRequest
      have hcr : m.ty = tyClientRequest := by rw [← hty]; assumption
      ihave ⟨%o, %ho, #Hoo⟩ := bmsgOk_cr γ X m hcr $$ Hok
      ihave ⟨%ov, #Hov, #Hor⟩ := cons_msgRep_obj v m o ho.1 $$ Hm
      wp_auto
      wp_apply (wp_QPush hPush γ k γl γc ch c ov o) $$ [Hrc]
      · iframe Hro Hor
        unfold pendOk
        iframe Hoo
        iexists X, j, l
        iframe Hlb Hrc
        ipureintro; exact ⟨ho.2.symm, m, hlj, hcr, ho.1⟩
      ihave HI := hLoop_next (cf := cf) γ k γl γc c recv v P hl X j hPhl HPl $$ [Hold Hfrz Hslots Hcons]
      · iframe Hold Hfrz Hslots Hcons Hhl HPw
        unfold procWit
        iexists l, m
        iframe Hlb
        isplitr
        · ipureintro; exact hlj
        iapply msgWit_none γl γc X m (msgRound_none_of m (by rw [hcr]; decide)
          (by rw [hcr]; decide) (by rw [hcr]; decide))
      wp_for_post
      iframe
    wp_if_destruct
    · -- ProposalRequest
      have hpr : m.ty = tyProposalRequest := by rw [← hty]; assumption
      ihave ⟨%hphX, %b, #Hpreq⟩ := bmsgOk_preq γ X m hpr $$ Hok
      have hmn : msgRound m = none := msgRound_none_of m (by rw [hpr]; decide)
        (by rw [hpr]; decide) (by rw [hpr]; decide)
      ihave ⟨%ps, #Hc⟩ := confRO_val $$ Hconf
      ihave Hc2 := Hc
      iStructNamed Hc2
      wp_auto
      wp_if_destruct
      · close_none
      have hs : v.Value'.toNat < lenLedger := by unfold lenLedger; word
      have hs' : m.value.toNat < lenLedger := by rw [← hval]; exact hs
      wp_apply (wp_IsTermMatched γ k γl γc ch c v.Value' hs) $$ [$Hconf $Hro]
      ihave #HledRO' := HledRO
      iunfold ledgerRO at HledRO'
      icases HledRO' with ⟨#Hsl, %Hlen, #Hslots'⟩
      ihave %Hl := ownSlice_len _ _ _ $$ Hsl
      rw [List.length_map, Hlen] at Hl
      obtain ⟨e, he⟩ : ∃ e, γl.slots[v.Value'.toNat]? = some e :=
        Option.isSome_iff_exists.mp (by simp [Hlen]; exact hs)
      ihave #Hse := (BigSepL.bigSepL_lookup
        (Φ := fun _ e => iprop(isSlot (GF := GF) e.loc e.γ e.q)) he) $$ Hslots'
      ihave #Hpl : isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger $$ []
      · iPkgInit
      unfold lenLedger at hs Hl
      have hmod : v.Value' % W32 10000 = v.Value' := by word
      rw [hmod]
      slice_index_if'
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z v.Value'))) _ _ e.loc (by word)
        $$ [Hsl]
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z v.Value'))).toNat = v.Value'.toNat by word]
        simp [he]
      iintro -
      ihave ⟨Hs, Hback⟩ := hSlots_acc γl γc _ e he $$ Hslots
      iunfold hSlot at Hs
      icases Hs with ⟨%sent, %ents, %ql, Hprod, %hsl, Hq, He, Hp⟩
      iapply fupd_wp
      imod ents_info γ k γl γc _ e he ents $$ [He] with ⟨He, %hinfo, #Hbm⟩
      · iframe He; iexact Hslinv
      imodintro
      wp_apply (mh_HasEnoughMsg hHEM γ k γl γc _ e he (W32 0) (W32 1) (Or.inl rfl)
        (monoListAuthOwn (entName γl γc v.Value'.toNat) (1 : Qp).half ents)
        (fun st => iprop(monoListAuthOwn (entName γl γc v.Value'.toNat) (1 : Qp).half ents ∗
          ⌜st.total 0 1 = (tally ents 0).length⌝))) $$ Hpl Hse Hconf Hslinv He []
        as %st ⟨He, %htot⟩
      · iintro %st Hg He
        ihave ⟨%ht, Hg, He⟩ := mh_slotGhost_tally γ k γl γc _ st ents $$ [Hg He]
        · iframe
        imodintro
        iframe
        ipureintro; exact ht.total (Or.inl rfl)
      wp_if_destruct
      · have hcq : 0 < cf.q ∧ cf.q ≤ cf.n ∧ cf.n ≤ 5 := by
          have := hcok; unfold RCfg.Ok at this; unfold RCfg.q; omega
        have h2 : (tally ents 0).length = cf.q := by
          have := (hinfo.2 0).1; omega
        have hwf0 : ∀ e ∈ ents, msgRound e.2.2.2 = some (v.Value'.toNat, e.1) :=
          fun e he => (hinfo.1 e he).2
        ihave ⟨%hobj, #Hpf, #Hoks⟩ := props_facts γ _ ents hwf0 $$ Hbm
        have hlos : ((tally ents 0).filterMap (fun e => e.2.2.2.obj)).length = cf.q := by
          have h1 := congrArg List.length (propPairs_snd (tally ents 0))
          rw [List.length_map, List.length_map, propPairs_length _ hobj, h2] at h1
          exact h1.symm
        have hne : (tally ents 0).filterMap (fun e => e.2.2.2.obj) ≠ [] := by
          intro h0; rw [h0] at hlos; simp at hlos; omega
        obtain ⟨o, kk, hh0, hmo, hk, hmax⟩ := (props_head (List.Perm.refl _) hne).2
        have hkq : kk ≤ cf.q := by
          rw [hk, ← hlos, ← List.length_map (f := objId)]; exact List.count_le_length
        slice_index_if'
        wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z v.Value'))) _ _ e.loc (by word)
          $$ [Hsl]
        · iframe Hsl; ipureintro
          rw [show (sint.Z (W64 (uint.Z v.Value'))).toNat = v.Value'.toNat by word]
          simp [he]
        iintro -
        wp_apply (mh_RecvProposalsMajT hMajT γ k γl γc _ e he
          (monoListAuthOwn (entName γl γc v.Value'.toNat) (1 : Qp).half ents)
          (fun st => iprop(monoListAuthOwn (entName γl γc v.Value'.toNat) (1 : Qp).half ents ∗
            ⌜(sortProps st.props).head? = some (o, kk)⌝)))
          $$ Hpl Hse Hslinv He [] [] as %st' %n %hn ⟨He, %hq⟩
        · iintro !> %st Hg He
          ihave ⟨%ht, Hg, He⟩ := mh_slotGhost_tally γ k γl γc _ st ents $$ [Hg He]
          · iframe
          iframe
          ipureintro; exact (ht.props_head hne).1
        · iintro %st Hg He
          ihave ⟨%ht, Hg, He⟩ := mh_slotGhost_tally γ k γl γc _ st ents $$ [Hg He]
          · iframe
          imodintro
          iframe He
          isplitl [Hg]
          · iapply mh_slotGhost_sort $$ Hg
          ipureintro; rw [ht.sorted_eq]; exact hh0
        have hnk : n = kk := by rw [hn, hq]; rfl
        subst hnk
        wp_if_destruct
        · have hkm : n ≥ cf.maj := by
            have h3 := Hif
            unfold RCfg.maj at h3 ⊢
            revert h3; word
          wp_apply (wp_genProposalReply hMajV γ k γl γc ch c v.Value' v.Phase' e
            (by unfold lenLedger; exact hs) he ents o hne (by rw [hh0]; rfl)) $$ [$Hconf $Hro $He]
            as %rv Hrv
          iapply fupd_wp
          imod Hrv with ⟨He, #Hrm⟩
          imodintro
          have hSd : Senders cf (propPairs (tally ents 0)) := by
            refine propPairs_senders (fun e' he' => ?_) (hinfo.2 0).2
            exact (hinfo.1 e' (tally_mem' he')).1
          obtain ⟨hW1, hW2, hW3⟩ := sendersOf_spec hSd (objId o)
          ihave #HW : [∗list] X ∈ sendersOf (propPairs (tally ents 0)) (objId o),
              fact γ.rab (.prop X v.Value'.toNat) (.obj (o.proId.toNat, o.proSeq.toNat)) $$ [Hpf]
          · iapply (bigSepL_sub_pers (fun x : Nat × ObjId => fact (GF := GF) γ.rab
              (.prop x.1 v.Value'.toNat) (.obj x.2)) (propPairs (tally ents 0))
              (sendersOf (propPairs (tally ents 0)) (objId o)) (fun X => (X, (o.proId.toNat, o.proSeq.toNat)))
              (fun X hX => hW3 X hX)) $$ Hpf
          ihave #Hpreq' : fact γ.rab (.preq X v.Value'.toNat) (.bit b) $$ []
          · rw [hval]; iexact Hpreq
          ihave #Hoo := (BigSepL.bigSepL_mem (Φ := fun o => objOk (GF := GF) γ cf o) hmo) $$ Hoks
          ihave #Hoo1' := mh_objOk_svrSeq γ o v.Value' $$ Hoo
          wp_apply (wp_bag_send γl.h2n ch.h2n rv (h2nP γ cf)) $$ [$HcH2n]
          · unfold h2nP
            iexists replyMsg v.Phase' v.Value' o, X
            iframe Hrm
            isplitr
            · ipureintro; exact hX
            unfold replyOk
            iexists { o with svrSeq := v.Value' }, sendersOf (propPairs (tally ents 0)) (objId o), b
            simp only [replyMsg]
            iframe Hoo1' Hpreq'
            isplitr
            · ipureintro
              refine ⟨trivial, by rw [hph]; exact hphX, trivial, trivial, hW1.1, hW1.2, ?_⟩
              rw [hW2, propPairs_snd, ← hk]; exact hkm
            · iexact HW
          restore_slot
          close_none
        restore_slot
        close_none

      restore_slot
      close_none
    have hjP : ∀ j' < j, (X, j') ∈ P := by
      intro j' hj'
      have := hprev j' hj'
      rw [hPhl] at this
      simpa [List.take_append_of_le_length, HPl] using this
    iapply fupd_wp
    imod prevWit_of γ γl γc X j l m P (Nat.lt_of_lt_of_le hX (mh_cf_n_le hcok)) hlj hjP $$ [Hsh Hlb HP] with #Hpw
    · iframe #
    imodintro
    wp_if_destruct
    · bin_tail
    wp_if_destruct
    · bin_tail
    wp_if_destruct
    · bin_tail
    wp_if_destruct
    · bin_tail
    iexfalso
    iapply bmsgOk_other γ X m (by rw [← hty]; assumption) (by rw [← hty]; assumption)
      (by rw [← hty]; assumption) (by rw [← hty]; assumption) (by rw [← hty]; assumption)
      (by rw [← hty]; assumption) $$ Hok
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof
end Perennial.rabia.roles.server.layers.consensus
