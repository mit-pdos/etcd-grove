/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/consensus/HandlerSlot.lean`, run `rabia-r1wake-1`.)

The handler's ghost steps on a slot's invariant (the counting, the notifications).
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.consensus.HandlerDefs

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.consensus

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.ledger rabia rabia.internal.queue

set_option linter.unusedSectionVars false

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable {cf : RCfg}

/-- The handler's halves of slot `s`'s ghost state. -/
def hHalves (γl : SrvNames) (γc : ConsNames) (s : Nat) (ents : List Ent) (ql : List (Option Nat))
    (p : Option (Option Nat)) : IProp GF :=
  iprop(monoListAuthOwn (entName γl γc s) (1 : Qp).half ents ∗
    monoListAuthOwn (γc.qlog s) (1 : Qp).half ql ∗ ghostVar (pendName γl γc s) (1 : Qp).half p)

/-- The invariant's ghost state agrees with the handler's halves. -/
theorem gs_agree (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat) (st : SlotSt)
    (ents : List Ent) (ql : List (Option Nat)) (p : Option (Option Nat)) :
    slotGhost (GF := GF) γ cf k γl γc s st ∗ hHalves γl γc s ents ql p ⊢
      ⌜∃ exd dl rl, SlotOk cf s st ents ql p exd dl rl⌝ ∗ slotGhost γ cf k γl γc s st ∗
        hHalves γl γc s ents ql p := by
  unfold slotGhost hHalves
  iintro ⟨⟨%ents', %ql', %p', %exd, %dl, %rl, He, Hq, Hp, Hx, Hd, Hr, Hents, %hok⟩, He', Hq', Hp'⟩
  ihave %he := monoListAuthOwn_agree _ _ _ _ _ $$ He He'
  ihave %hq := monoListAuthOwn_agree _ _ _ _ _ $$ Hq Hq'
  ihave %hp := ghostVar_agree _ _ _ _ _ $$ Hp Hp'
  obtain ⟨-, rfl⟩ := he
  obtain ⟨-, rfl⟩ := hq
  subst hp
  isplitr
  · ipureintro; exact ⟨exd, dl, rl, hok⟩
  isplitl [He Hq Hp Hx Hd Hr Hents]
  · iexists ents', ql', p', exd, dl, rl
    iframe
    ipureintro; exact hok
  iframe

theorem mlHalves_update {A : Type} [Pos.Countable A] (γ' : GName) (l l' : List A)
    (h : l <+: l') :
    monoListAuthOwn (GF := GF) γ' (1 : Qp).half l ∗ monoListAuthOwn γ' (1 : Qp).half l ⊢
      |==> (monoListAuthOwn γ' (1 : Qp).half l' ∗ monoListAuthOwn γ' (1 : Qp).half l' ∗
        monoListLbOwn γ' l') := by
  iintro ⟨H1, H2⟩
  ihave H : monoListAuthOwn (GF := GF) γ' 1 l $$ [H1 H2]
  · have hf := ((monoListAuthOwn_fractional (GF := GF) γ' l).fractional (1 : Qp).half (1 : Qp).half)
    rw [Qp.half_add_half] at hf
    iapply hf.2
    iframe
  imod monoListAuthOwn_update l' h $$ H with ⟨H, #Hlb⟩
  icases mlAuth_halves γ' l' $$ H with ⟨H1, H2⟩
  imodintro
  isplitl [H1]
  · iexact H1
  isplitl [H2]
  · iexact H2
  iexact Hlb

/-- A copy of `roundDone` (inserted if new). -/
theorem frz_mint (γc : ConsNames) (s ρ : Nat) :
    frzRes (GF := GF) γc ⊢ |==> (frzRes γc ∗ roundDone γc s ρ) := by
  unfold frzRes
  iintro ⟨%F, HA, #HF⟩
  cases hF : F.lookup (s, ρ) with
  | some u =>
    ihave #H := (BigSepM.bigSepM_lookup (Φ := fun (k : Nat × Nat) (_ : Unit) =>
      iprop(roundDone (GF := GF) γc k.1 k.2)) hF) $$ HF
    imodintro
    isplitl [HA]
    · iexists F
      iframe HA
      iexact HF
    · iexact H
  | none =>
    imod ghost_map_insert_persist (s, ρ) () hF $$ HA with ⟨HA, #Hn⟩
    imodintro
    isplitl [HA]
    · iexists F.insert (s, ρ) ()
      iframe HA
      iapply (BigSepM.bigSepM_insert (Φ := fun (k : Nat × Nat) (_ : Unit) =>
        iprop(roundDone (GF := GF) γc k.1 k.2)) hF).2
      isplitr
      · unfold roundDone; iexact Hn
      · iexact HF
    · unfold roundDone; iexact Hn

theorem bcast_slot_sub (X k s : Nat) :
    (↑(bcastN X) : CoPset) ⊆ ⊤ \ ↑(slotN k s) := by
  have hd : (↑(ndot rabiaR "bcast") : CoPset) ## ↑(ndot rabiaR "slot") :=
    ndot_ne_disjoint rabiaR (by decide)
  have h1 : (↑(bcastN X) : CoPset) ## ↑(slotN k s) := by
    unfold bcastN slotN
    exact ndot_preserve_disjoint_l _ (ndot_preserve_disjoint_r _ (ndot_preserve_disjoint_r _ hd))
  intro x hx
  exact LawfulSet.mem_diff.mpr ⟨CoPset.mem_full, fun h => h1 x ⟨hx, h⟩⟩

theorem SlotOk.with_dl {s : Nat} {st : SlotSt} {ents : List Ent} {ql : List (Option Nat)}
    {p : Option (Option Nat)} {exd : Bool} {dl rl : List Unit}
    (h : SlotOk cf s st ents ql p exd dl rl) (hd : st.isDone = true) (dl' : List Unit) :
    SlotOk cf s st ents ql p exd dl' rl := by
  unfold SlotOk at *
  obtain ⟨a, b, c, d, e, f, g, _, i⟩ := h
  exact ⟨a, b, c, d, e, f, g, fun _ => hd, i⟩

theorem SlotOk.done_of_dl {s : Nat} {st : SlotSt} {ents : List Ent} {ql : List (Option Nat)}
    {p : Option (Option Nat)} {exd : Bool} {dl rl : List Unit}
    (h : SlotOk cf s st ents ql p exd dl rl) (hd : dl ≠ []) : st.isDone = true := by
  unfold SlotOk at h; exact h.2.2.2.2.2.2.2.1 hd

theorem unit_prefix (dl : List Unit) : [()] <+: dl ++ [()] := by
  cases dl with
  | nil => exact List.prefix_refl _
  | cons a t => exact ⟨t ++ [()], by simp⟩

theorem unit_prefix_ne {dl : List Unit} (h : [()] <+: dl) : dl ≠ [] := by
  rintro rfl; simp at h

/-- `GetIsDone`'s step: when done, the witness `doneW`. -/
theorem gs_isDone (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat) (st : SlotSt) :
    slotGhost (GF := GF) γ cf k γl γc s st ⊢
      |==> (slotGhost γ cf k γl γc s st ∗ (if st.isDone then doneW γl γc s else iprop(True))) := by
  unfold slotGhost
  iintro ⟨%ents, %ql, %p, %exd, %dl, %rl, He, Hq, Hp, Hx, Hd, Hr, Hents, %hok⟩
  cases hdone : st.isDone with
  | false =>
    imodintro
    isplitl
    · iexists ents, ql, p, exd, dl, rl
      iframe
      ipureintro; exact hok
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  | true =>
    imod monoListAuthOwn_update (dl ++ [()]) (List.prefix_append _ _) $$ Hd with ⟨Hd, #Hlb⟩
    imodintro
    isplitl
    · iexists ents, ql, p, exd, dl ++ [()], rl
      iframe
      ipureintro; exact hok.with_dl hdone _
    · simp only [↓reduceIte]
      unfold doneW
      iapply monoListLbOwn_le [()] (unit_prefix dl) $$ Hlb

/-- `doneW` contradicts a slot not done. -/
theorem gs_notDone (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat) (st : SlotSt)
    (h : st.isDone = false) :
    slotGhost (GF := GF) γ cf k γl γc s st ∗ doneW γl γc s ⊢ False := by
  unfold slotGhost doneW
  iintro ⟨⟨%ents, %ql, %p, %exd, %dl, %rl, -, -, -, -, Hd, -, -, %hok⟩, Hw⟩
  ihave %hv := mono_list_auth_lb_valid _ _ _ _ $$ Hd Hw
  have := hok.done_of_dl (unit_prefix_ne hv.2)
  rw [h] at this; cases this

/-- A persistent witness of a sender's message of round `ρ` (counted, or the round notified), as
membership in the halves' lists. -/
theorem wit_pure (γl : SrvNames) (γc : ConsNames) (s ρ Y : Nat) (ents : List Ent)
    (ql : List (Option Nat)) (q1 q2 : Qp) :
    (counted (GF := GF) γl γc s ρ Y ∨ notified γc s ρ) ∗
      monoListAuthOwn (entName γl γc s) q1 ents ∗ monoListAuthOwn (γc.qlog s) q2 ql ⊢
      ⌜(∃ j m, (ρ, Y, j, m) ∈ ents) ∨ some ρ ∈ ql⌝ ∗
      monoListAuthOwn (entName γl γc s) q1 ents ∗ monoListAuthOwn (γc.qlog s) q2 ql := by
  unfold counted notified qLb
  iintro ⟨H, He, Hq⟩
  icases H with (⟨%l, Hl, %hl⟩ | ⟨%l, Hl, %hl⟩)
  · ihave %hv := mono_list_auth_lb_valid _ _ _ _ $$ He Hl
    iframe He Hq
    ipureintro
    obtain ⟨j, m, hm⟩ := hl
    exact Or.inl ⟨j, m, hv.2.subset hm⟩
  · ihave %hv := mono_list_auth_lb_valid _ _ _ _ $$ Hq Hl
    iframe He Hq
    ipureintro
    exact Or.inr (hv.2.subset hl)

instance cons_bcastInv_timeless (γ : Names) (X : Nat) : Timeless (bcastInv (GF := GF) γ X) := by
  unfold bcastInv; infer_instance

/-- The counted messages of a round have distinct senders: a sender's message of round `ρ` is at a
unique index of its broadcast log (`RoundsOrdered`), whose receipt is exclusive. -/
theorem gs_fresh (γ : Names) (γl : SrvNames) (γc : ConsNames) (s : Nat) (ents : List Ent)
    (e : Ent) (E : CoPset) (hE : ↑(bcastN e.2.1) ⊆ E) (hX : e.2.1 < maxS)
    (hm : msgRound e.2.2.2 = some (s, e.1))
    (hwf : ∀ e' ∈ ents, msgRound e'.2.2.2 = some (s, e'.1)) :
    shared (GF := GF) γ ∗ ([∗list] e' ∈ ents, entRes γ cf γl γc s e') ∗ entRes γ cf γl γc s e ⊢
      |={E}=> (⌜e.2.1 ∉ (tally ents e.1).map (fun e => e.2.1)⌝ ∗
        ([∗list] e' ∈ ents, entRes γ cf γl γc s e') ∗ entRes γ cf γl γc s e) := by
  iintro ⟨#Hsh, Hents, He⟩
  by_cases hin : e.2.1 ∈ (tally ents e.1).map (fun e => e.2.1)
  · obtain ⟨e', he', hX'⟩ := List.mem_map.mp hin
    obtain ⟨he'1, he'2⟩ := List.mem_filter.mp he'
    have he'3 : e'.1 = e.1 := of_decide_eq_true he'2
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp he'1
    have hm' := hwf e' he'1
    rcases e with ⟨ρ, X, j, m⟩
    rcases e' with ⟨ρ', X', j', m'⟩
    simp only at hX' he'3 hm hm' hE hX
    subst hX' he'3
    ihave ⟨He', -⟩ := (BigSepL.bigSepL_lookup_acc
      (Φ := fun _ e' => entRes (GF := GF) γ cf γl γc s e') hi).1 $$ Hents
    unfold entRes
    icases He with ⟨⟨%l, #Hl, %hl⟩, -, Hr, -⟩
    icases He' with ⟨⟨%l', #Hl', %hl'⟩, -, Hr', -⟩
    simp only at hl hl'
    unfold shared
    icases Hsh with ⟨-, #Hbc, -, -⟩
    have hr : (List.range maxS)[X']? = some X' := by simp [hX]
    ihave #Hi := (BigSepL.bigSepL_lookup
      (Φ := fun _ X => iprop(inv (bcastN X) (bcastInv (GF := GF) γ X))) hr) $$ Hbc
    imod inv_acc hE $$ Hi with ⟨Hb, -⟩
    imod Hb with Hb
    unfold bcastInv bcastLb
    icases Hb with ⟨%B, HA, -, %hro⟩
    ihave %hv := mono_list_auth_lb_valid _ _ _ _ $$ HA Hl
    ihave %hv' := mono_list_auth_lb_valid _ _ _ _ $$ HA Hl'
    have hB := prefix_getElem? hv.2 hl
    have hB' := prefix_getElem? hv'.2 hl'
    have hjj := hro.2.1 j j' m m' (s, ρ') hB hB' hm hm'
    subst hjj
    unfold rcpt
    ihave %hv2 := ghostMapElem_valid_2 _ _ _ _ _ _ $$ Hr Hr'
    have := DFrac.valid_op_own hv2.1
    simp at this
  · imodintro
    iframe
    ipureintro; exact hin

/-- The persistent witness in a counted message's resources. -/
def entWit (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : Ent) : IProp GF :=
  match e.1 with
  | 0 => iprop(True)
  | ρ + 1 => iprop(counted γl γc s ρ e.2.1 ∨ notified γc s ρ)

instance entWit_persistent (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : Ent) :
    Persistent (entWit (GF := GF) γl γc s e) := by
  unfold entWit; split <;> infer_instance

theorem entRes_wit (γ : Names) (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : Ent) :
    entRes (GF := GF) γ cf γl γc s e ⊢ entRes γ cf γl γc s e ∗ entWit γl γc s e := by
  unfold entRes entWit
  rcases e with ⟨_ | ρ, X, j, m⟩
  · iintro H; iframe H
  · iintro ⟨H1, H2, H3, #H4⟩; iframe H1 H2 H3; iframe H4

theorem ents_wit (γ : Names) (γl : SrvNames) (γc : ConsNames) (s : Nat) (ents : List Ent) :
    ([∗list] e ∈ ents, entRes (GF := GF) γ cf γl γc s e) ⊢
      ([∗list] e ∈ ents, entRes γ cf γl γc s e) ∗ [∗list] e ∈ ents, entWit γl γc s e := by
  refine .trans ?_ BigSepL.bigSepL_sep_eqv.1
  exact BigSepL.bigSepL_mono_of_forall fun {_ e} => entRes_wit γ γl γc s e

/-- The pure witnesses of the counted messages of round `ρ + 1`. -/
theorem wits_pure (γl : SrvNames) (γc : ConsNames) (s ρ : Nat) (ents : List Ent)
    (ql : List (Option Nat)) (q1 q2 : Qp) : ∀ L : List Ent,
    ([∗list] e ∈ L, entWit (GF := GF) γl γc s e) ∗
      monoListAuthOwn (entName γl γc s) q1 ents ∗ monoListAuthOwn (γc.qlog s) q2 ql ⊢
      ⌜∀ e ∈ L, e.1 = ρ + 1 → (∃ j m, (ρ, e.2.1, j, m) ∈ ents) ∨ some ρ ∈ ql⌝ ∗
      monoListAuthOwn (entName γl γc s) q1 ents ∗ monoListAuthOwn (γc.qlog s) q2 ql
  | [] => by
    iintro ⟨-, He, Hq⟩; iframe He Hq; ipureintro; intro e he; simp at he
  | e :: L => by
    iintro ⟨Hs, He, Hq⟩
    icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨Hw, Hs⟩
    ihave ⟨%hL, He, Hq⟩ := wits_pure γl γc s ρ ents ql q1 q2 L $$ [Hs He Hq]
    · iframe
    by_cases h1 : e.1 = ρ + 1
    · rcases e with ⟨ρ', X, j, m⟩
      simp only at h1; subst h1
      unfold entWit
      simp only
      ihave ⟨%h, He, Hq⟩ := wit_pure γl γc s ρ X ents ql _ _ $$ [Hw He Hq]
      · iframe
      iframe He Hq
      ipureintro
      intro e' he' h'
      rcases List.mem_cons.1 he' with rfl | he'
      · exact h
      · exact hL e' he' h'
    · iframe He Hq
      ipureintro
      intro e' he' h'
      rcases List.mem_cons.1 he' with rfl | he'
      · exact absurd h' h1
      · exact hL e' he' h'

theorem gs_prev (γl : SrvNames) (γc : ConsNames) (s : Nat) (ents' : List Ent)
    (ql' : List (Option Nat)) (q1 q2 : Qp) (e : Ent) {st : SlotSt} {exd : Bool} {dl rl : List Unit}
    (hok : SlotOk cf s st ents' ql' none exd dl rl)
    (hnew : e.2.1 ∉ (tally ents' e.1).map (fun e => e.2.1)) :
    ([∗list] e ∈ ents', entWit (GF := GF) γl γc s e) ∗ entWit γl γc s e ∗
      monoListAuthOwn (entName γl γc s) q1 ents' ∗ monoListAuthOwn (γc.qlog s) q2 ql' ⊢
      ⌜(tally (ents' ++ [e]) e.1).length = cf.q → (e.1 = 0 ∨ some (e.1 - 1) ∈ ql')⌝ ∗
      monoListAuthOwn (entName γl γc s) q1 ents' ∗ monoListAuthOwn (γc.qlog s) q2 ql' := by
  iintro ⟨#Hws, #Hwe, Hen, Hq⟩
  rcases e with ⟨_ | ρ', X, j, m⟩
  · iframe Hen Hq; ipureintro; intro _; exact Or.inl rfl
  ihave ⟨%hL, Hen, Hq⟩ := wits_pure γl γc s ρ' ents' ql' _ _ ents' $$ [Hws Hen Hq]
  · iframe Hen Hq; iexact Hws
  unfold entWit
  simp only
  ihave ⟨%h1, Hen, Hq⟩ := wit_pure γl γc s ρ' X ents' ql' _ _ $$ [Hwe Hen Hq]
  · iframe Hen Hq; iexact Hwe
  iframe Hen Hq
  ipureintro
  intro hfull
  right
  simp only [Nat.add_sub_cancel]
  rw [tally_append] at hfull
  simp only [↓reduceIte, List.length_append, List.length_singleton] at hfull
  simp only at hnew
  apply hok.prev_notified (X :: (tally ents' (ρ' + 1)).map (fun e => e.2.1))
  · exact List.nodup_cons.2 ⟨hnew, (hok.2.2.1 (ρ' + 1)).2⟩
  · simp only [List.length_cons, List.length_map]; omega
  · intro Y hY
    rcases List.mem_cons.1 hY with rfl | hY
    · exact h1
    · obtain ⟨eY, heY, rfl⟩ := List.mem_map.1 hY
      obtain ⟨hm, hr⟩ := List.mem_filter.1 heY
      exact hL eY hm (of_decide_eq_true hr)

/-- The handler counts `e` (`PutRecvProposals`/`PutRecvBCMsgs`'s step). -/
theorem gs_count (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat)
    (st st' : SlotSt) (ents : List Ent) (ql : List (Option Nat)) (e : Ent) (E : CoPset)
    (hE : ↑(bcastN e.2.1) ⊆ E) (hX : e.2.1 < cf.n) (hXm : e.2.1 < maxS)
    (hm : msgRound e.2.2.2 = some (s, e.1))
    (hlt : (tally ents e.1).length < cf.q)
    (htally : TallyOk st ents → TallyOk st' (ents ++ [e]))
    (hd : st'.isDone = st.isDone) (hr : st'.hasRecvDec = st.hasRecvDec) :
    shared (GF := GF) γ ∗ slotGhost γ cf k γl γc s st ∗ hHalves γl γc s ents ql none ∗
        entRes γ cf γl γc s e ⊢
      |={E}=> (slotGhost γ cf k γl γc s st' ∗
        hHalves γl γc s (ents ++ [e]) ql
          (if (tally (ents ++ [e]) e.1).length = cf.q then some (some e.1) else none) ∗
        counted γl γc s e.1 e.2.1 ∗
        ⌜(tally (ents ++ [e]) e.1).length = cf.q →
          (e.1 = 0 ∨ some (e.1 - 1) ∈ ql) ∧ some e.1 ∉ ql⌝) := by
  iintro ⟨#Hsh, Hg, Hh, He⟩
  unfold slotGhost hHalves
  icases Hg with ⟨%ents', %ql', %p', %exd, %dl, %rl, Hen, Hq, Hp, Hx, Hd, Hr, Hents, %hok⟩
  icases Hh with ⟨Hen', Hq', Hp'⟩
  ihave %he := monoListAuthOwn_agree _ _ _ _ _ $$ Hen Hen'
  ihave %hq := monoListAuthOwn_agree _ _ _ _ _ $$ Hq Hq'
  ihave %hp := ghostVar_agree _ _ _ _ _ $$ Hp Hp'
  obtain ⟨-, rfl⟩ := he
  obtain ⟨-, rfl⟩ := hq
  subst hp
  have hwf : ∀ e' ∈ ents', msgRound e'.2.2.2 = some (s, e'.1) := fun e' h => (hok.2.1 e' h).2
  imod gs_fresh γ γl γc s ents' e E hE hXm hm hwf $$ [Hsh Hents He] with ⟨%hnew, Hents, He⟩
  · iframe; iexact Hsh
  ihave ⟨Hents, #Hws⟩ := ents_wit γ γl γc s ents' $$ Hents
  ihave ⟨He, #Hwe⟩ := entRes_wit γ γl γc s e $$ He
  have hnot := hok.not_notified hlt
  ihave ⟨%hprev, Hen, Hq⟩ := gs_prev γl γc s ents' ql' _ _ e hok hnew $$ [Hws Hwe Hen Hq]
  · iframe Hen Hq; iframe Hws; iexact Hwe
  have hok' := hok.count e hX hm hlt hnew (htally hok.1) hd hr
  imod mlHalves_update (entName γl γc s) ents' (ents' ++ [e]) (List.prefix_append _ _)
    $$ [Hen Hen'] with ⟨Hen, Hen', #Hlb⟩
  · iframe
  imod ghostVar_update_halves
    (if (tally (ents' ++ [e]) e.1).length = cf.q then some (some e.1) else none) _ _ _ $$ Hp Hp'
    with ⟨Hp, Hp'⟩
  imodintro
  isplitl [Hen Hq Hp Hx Hd Hr Hents He]
  · iexists ents' ++ [e], ql',
      (if (tally (ents' ++ [e]) e.1).length = cf.q then some (some e.1) else none), exd, dl, rl
    iframe Hen Hq Hp Hx Hd Hr
    isplitl [Hents He]
    · iapply BigSepL.bigSepL_snoc.2
      iframe
    · ipureintro; exact hok'
  iframe Hen' Hq' Hp'
  isplitr
  · unfold counted
    iexists ents' ++ [e]
    iframe Hlb
    ipureintro
    exact ⟨e.2.2.1, e.2.2.2, by simp⟩
  · ipureintro
    intro hfull
    exact ⟨hprev hfull, hnot⟩

/-- Opening slot `s`'s invariant at the handler's halves (the contents are timeless). -/
theorem gs_notify (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV)
    (he : γl.slots[s]? = some e) (ents : List Ent) (ql : List (Option Nat)) (ρ : Nat)
    (hprev : ρ = 0 ∨ some (ρ - 1) ∈ ql) (hnot : some ρ ∉ ql) :
    slotsInv (GF := GF) γ cf k γl γc ∗ hHalves γl γc s ents ql (some (some ρ)) ⊢
      |={⊤}=> (hHalves γl γc s ents (ql ++ [some ρ]) none ∗ qLb γc s (ql ++ [some ρ]) ∗
        ⌜ql.filterMap id = List.range ρ⌝) := by
  iintro ⟨#Hinvs, Hh⟩
  unfold slotsInv
  ihave #Hinv := (BigSepL.bigSepL_lookup
    (Φ := fun s e => iprop(inv (slotN k s) (slotInv (GF := GF) γ cf k γl γc s e))) he) $$ Hinvs
  imod inv_acc (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  imod Hi with Hi
  unfold slotInv
  icases Hi with ⟨%st, Hst, #Hd, Hg⟩
  unfold slotGhost hHalves
  icases Hg with ⟨%ents', %ql', %p', %exd, %dl, %rl, Hen, Hq, Hp, Hx, Hdl, Hr, Hents, %hok⟩
  icases Hh with ⟨Hen', Hq', Hp'⟩
  ihave %he1 := monoListAuthOwn_agree _ _ _ _ _ $$ Hen Hen'
  ihave %hq1 := monoListAuthOwn_agree _ _ _ _ _ $$ Hq Hq'
  ihave %hp1 := ghostVar_agree _ _ _ _ _ $$ Hp Hp'
  obtain ⟨-, rfl⟩ := he1
  obtain ⟨-, rfl⟩ := hq1
  subst hp1
  obtain ⟨hok', hfm⟩ := hok.notify hprev hnot
  imod mlHalves_update (γc.qlog s) ql' (ql' ++ [some ρ]) (List.prefix_append _ _)
    $$ [Hq Hq'] with ⟨Hq, Hq', #Hlb⟩
  · iframe
  imod ghostVar_update_halves (none : Option (Option Nat)) _ _ _ $$ Hp Hp' with ⟨Hp, Hp'⟩
  imod Hclose $$ [Hst Hen Hq Hp Hx Hdl Hr Hents] with -
  · inext
    iexists st
    iframe Hst
    isplitr
    · iexact Hd
    iexists ents', ql' ++ [some ρ], none, exd, dl, rl
    iframe
    ipureintro; exact hok'
  imodintro
  iframe Hen' Hq' Hp'
  unfold qLb
  iframe Hlb
  ipureintro; exact hfm

/-- The decision's notification (none sent yet): opening slot `s`'s invariant. -/
theorem gs_decsend (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV)
    (he : γl.slots[s]? = some e) (ents : List Ent) (ql : List (Option Nat))
    (hnot : none ∉ ql) :
    slotsInv (GF := GF) γ cf k γl γc ∗ hHalves γl γc s ents ql none ⊢
      |={⊤}=> (hHalves γl γc s ents (ql ++ [none]) (some none) ∗ qLb γc s (ql ++ [none])) := by
  iintro ⟨#Hinvs, Hh⟩
  unfold slotsInv
  ihave #Hinv := (BigSepL.bigSepL_lookup
    (Φ := fun s e => iprop(inv (slotN k s) (slotInv (GF := GF) γ cf k γl γc s e))) he) $$ Hinvs
  imod inv_acc (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  imod Hi with Hi
  unfold slotInv
  icases Hi with ⟨%st, Hst, #Hd, Hg⟩
  unfold slotGhost hHalves
  icases Hg with ⟨%ents', %ql', %p', %exd, %dl, %rl, Hen, Hq, Hp, Hx, Hdl, Hr, Hents, %hok⟩
  icases Hh with ⟨Hen', Hq', Hp'⟩
  ihave %he1 := monoListAuthOwn_agree _ _ _ _ _ $$ Hen Hen'
  ihave %hq1 := monoListAuthOwn_agree _ _ _ _ _ $$ Hq Hq'
  ihave %hp1 := ghostVar_agree _ _ _ _ _ $$ Hp Hp'
  obtain ⟨-, rfl⟩ := he1
  obtain ⟨-, rfl⟩ := hq1
  subst hp1
  have hrd : st.hasRecvDec = false := by
    have h := hok.2.2.2.2.2.1
    cases hst : st.hasRecvDec
    · rfl
    · rw [hst] at h; exact absurd (h.1 rfl).1 hnot
  obtain ⟨-, hok'⟩ := hok.dec_send hrd
  imod mlHalves_update (γc.qlog s) ql' (ql' ++ [none]) (List.prefix_append _ _)
    $$ [Hq Hq'] with ⟨Hq, Hq', #Hlb⟩
  · iframe
  imod ghostVar_update_halves (some none : Option (Option Nat)) _ _ _ $$ Hp Hp' with ⟨Hp, Hp'⟩
  imod Hclose $$ [Hst Hen Hq Hp Hx Hdl Hr Hents] with -
  · inext
    iexists st
    iframe Hst
    isplitr
    · iexact Hd
    iexists ents', ql' ++ [none], some none, exd, dl, rl
    iframe
    ipureintro; exact hok'
  imodintro
  iframe Hen' Hq' Hp'
  unfold qLb
  iexact Hlb

/-- `SetHasRecvDec`'s step: the decision's notification no longer pending. -/
theorem gs_decset (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat) (st : SlotSt)
    (ents : List Ent) (ql : List (Option Nat)) (hin : none ∈ ql) :
    slotGhost (GF := GF) γ cf k γl γc s st ∗ hHalves γl γc s ents ql (some none) ⊢
      |==> (slotGhost γ cf k γl γc s { st with hasRecvDec := true } ∗
        hHalves γl γc s ents ql none) := by
  unfold slotGhost hHalves
  iintro ⟨⟨%ents', %ql', %p', %exd, %dl, %rl, Hen, Hq, Hp, Hx, Hdl, Hr, Hents, %hok⟩,
    Hen', Hq', Hp'⟩
  ihave %he1 := monoListAuthOwn_agree _ _ _ _ _ $$ Hen Hen'
  ihave %hq1 := monoListAuthOwn_agree _ _ _ _ _ $$ Hq Hq'
  ihave %hp1 := ghostVar_agree _ _ _ _ _ $$ Hp Hp'
  obtain ⟨-, rfl⟩ := he1
  obtain ⟨-, rfl⟩ := hq1
  subst hp1
  imod ghostVar_update_halves (none : Option (Option Nat)) _ _ _ $$ Hp Hp' with ⟨Hp, Hp'⟩
  imodintro
  isplitl [Hen Hq Hp Hx Hdl Hr Hents]
  · iexists ents', ql', none, exd, dl, rl
    iframe
    ipureintro; exact hok.dec_set hin
  iframe

end ghost

end Perennial.rabia.roles.server.layers.consensus
