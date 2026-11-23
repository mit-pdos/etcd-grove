/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/consensus/ExecRead.lean`, run `rabia-r1wake-1`.)

The executor's reads of a slot's frozen tallies: a snapshot of the counted messages (a lower bound
of the slot's counted list, with their facts) once a round is notified, and the slot's counts
agreeing with it at any later read.
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.consensus.ExecDefs

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.consensus

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model NetConn Dsv rabia.internal.message
  rabia.internal.config rabia.internal.ledger rabia rabia.internal.queue

set_option linter.unusedSectionVars false

/-! ## Pure -/

theorem tally_prefix {ents0 ents : List Ent} {ρ n : Nat} (hp : ents0 <+: ents)
    (h2 : (tally ents0 ρ).length = n) (hle : (tally ents ρ).length ≤ n) :
    tally ents ρ = tally ents0 ρ := by
  obtain ⟨r, rfl⟩ := hp
  unfold tally at *
  rw [List.filter_append] at hle ⊢
  rw [List.length_append] at hle
  have : (List.filter (fun e => decide (e.1 = ρ)) r).length = 0 := by omega
  rw [List.length_eq_zero_iff] at this
  rw [this, List.append_nil]

theorem tally_mem {ents : List Ent} {ρ : Nat} {e : Ent} (h : e ∈ tally ents ρ) :
    e ∈ ents ∧ e.1 = ρ := by
  unfold tally at h
  simpa using h


theorem msgRound_cases {m : MsgV} {s ρ : Nat} (h : msgRound m = some (s, ρ)) :
    (m.obj.map (·.svrSeq.toNat)).getD 0 = s ∧
    ((m.ty = tyProposal ∧ ρ = 0) ∨ (m.ty = tyState ∧ ρ = 2 * m.phase.toNat) ∨
      (m.ty = tyVote ∧ ρ = 2 * m.phase.toNat + 1)) := by
  unfold msgRound roundOf at h
  by_cases h1 : m.ty = tyProposal
  · simp [h1] at h; exact ⟨h.1, Or.inl ⟨h1, h.2.symm⟩⟩
  simp only [h1, ↓reduceIte] at h
  by_cases h2 : m.ty = tyState
  · simp only [h2, ↓reduceIte, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h.1, Or.inr (Or.inl ⟨h2, h.2.symm⟩)⟩
  simp only [h2, ↓reduceIte] at h
  by_cases h3 : m.ty = tyVote
  · simp only [h3, ↓reduceIte, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h.1, Or.inr (Or.inr ⟨h3, h.2.symm⟩)⟩
  simp [h3] at h

theorem ty_ne : tyProposal ≠ tyState ∧ tyProposal ≠ tyVote ∧ tyState ≠ tyVote ∧
    tyClientRequest ≠ tyProposal ∧ tyClientRequest ≠ tyState ∧ tyClientRequest ≠ tyVote := by
  decide

theorem notified_le {ql : List (Option Nat)} {ρ ρ' : Nat}
    (h : ql.filterMap id = List.range (ql.filterMap id).length) (hle : ρ ≤ ρ')
    (hin : some ρ' ∈ ql) : some ρ ∈ ql := by
  have h1 : ρ' ∈ ql.filterMap id := List.mem_filterMap.2 ⟨some ρ', hin, rfl⟩
  rw [h, List.mem_range] at h1
  have h2 : ρ ∈ ql.filterMap id := by rw [h, List.mem_range]; omega
  obtain ⟨a, ha, he⟩ := List.mem_filterMap.1 h2
  simp at he; subst he; exact ha


/-- The sorted tallies of a frozen round 0 are those of its proposals (the order is total on
distinct ids). -/
theorem TallyOk.sort_eq {st : SlotSt} {ents : List Ent} (h : TallyOk st ents) :
    sortProps st.props = sortProps (groupProps ((tally ents 0).filterMap (fun e => e.2.2.2.obj))) := by
  have hg := groupOk_groupProps ((tally ents 0).filterMap (fun e => e.2.2.2.obj))
  have hd' : distinctIds st.props := distinctIds_perm hg.1 h.2.1.symm
  apply eq_of_perm_of_pairwise_asymm tallyLt (fun a b h1 h2 => tallyLt_asymm a b h1 h2)
  · exact ((List.mergeSort_perm _ _).trans h.2.1).trans (List.mergeSort_perm _ _).symm
  · exact sortProps_pairwise _ hd'
  · exact sortProps_pairwise _ hg.1

/-- The head of the sorted tallies of the proposals `os`. -/
def propHead (os : List ObjV) : Option (ObjV × Nat) := (sortProps (groupProps os)).head?

theorem propHead_spec {os : List ObjV} (hne : os ≠ []) :
    ∃ o k, propHead os = some (o, k) ∧ o ∈ os ∧ k = (os.map objId).count (objId o) ∧
      ∀ id, (os.map objId).count id ≤ k :=
  (props_head (List.Perm.refl _) hne).2

section ghost'
end ghost'

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable {cf : RCfg}
variable [package_sem : rabia.roles.server.layers.consensus.Assumptions]

theorem mono_auth_lb {A : Type} [Pos.Countable A] (γ : GName) (q : Qp) (l : List A) :
    monoListAuthOwn (GF := GF) γ q l ⊢ monoListAuthOwn γ q l ∗ monoListLbOwn γ l := by
  unfold monoListAuthOwn monoListLbOwn
  rw [← (own_op γ _ _).to_eq]
  exact (congrArg (own γ) (MonoList.auth_lb_op _ _)).to_bi.1

theorem entRes_bmsg (γ : Names) (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : Ent) :
    entRes (GF := GF) γ cf γl γc s e ⊢ entRes γ cf γl γc s e ∗ bmsgOk γ cf e.2.1 e.2.2.2 := by
  unfold entRes
  iintro ⟨H1, #H2, H3⟩
  iframe H1 H3 H2

/-- Once round `ρ` of slot `s` is notified (in a queue log lower bound): a lower bound of the
counted messages with round `ρ` full, their well-formedness and facts. -/
theorem slot_snapshot (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat)
    (e : SlotV) (he : γl.slots[s]? = some e) (ql : List (Option Nat)) (ρ : Nat)
    (hρ : some ρ ∈ ql) (E : CoPset) (hE : ↑(slotN k s) ⊆ E) :
    slotsInv (GF := GF) γ cf k γl γc ∗ qLb γc s ql ⊢
      |={E}=> ∃ ents : List Ent, monoListLbOwn (entName γl γc s) ents ∗
        ⌜(tally ents ρ).length = cf.q ∧ ((tally ents ρ).map (fun e => e.2.1)).Nodup ∧
          ∀ e ∈ ents, e.2.1 < cf.n ∧ msgRound e.2.2.2 = some (s, e.1)⌝ ∗
        [∗list] e ∈ ents, bmsgOk γ cf e.2.1 e.2.2.2 := by
  iintro ⟨#Hinvs, #Hq⟩
  ihave #Hinv := slotsInv_lookup γ k γl γc s e he $$ Hinvs
  imod inv_acc hE $$ Hinv with ⟨Hi, Hclose⟩
  imod Hi with Hi
  unfold slotInv
  icases Hi with ⟨%st, Hst, #Hd, Hg⟩
  unfold slotGhost
  icases Hg with ⟨%ents, %ql', %pend, %exd, %dl, %rl, He, Hql, Hp, Hx, Hdl, Hrl, Hents, %hok⟩
  unfold qLb
  ihave %hv := mono_list_auth_lb_valid _ _ _ _ $$ Hql Hq
  ihave ⟨He, #Hlb⟩ := mono_auth_lb _ _ _ $$ He
  ihave Hents2 := BigSepL.bigSepL_mono_of_forall
    (Φ := fun _ e => entRes (GF := GF) γ cf γl γc s e)
    (Ψ := fun _ e => iprop(entRes (GF := GF) γ cf γl γc s e ∗ bmsgOk γ cf e.2.1 e.2.2.2))
    (fun {_ e} => entRes_bmsg γ γl γc s e) $$ Hents
  ihave ⟨Hents, #Hb⟩ := BigSepL.bigSepL_sep_eqv.1 $$ Hents2
  have hok' := hok
  obtain ⟨_, hwf, hle, _, hiff, _⟩ := hok'
  have h2 : (tally ents ρ).length = cf.q := (hiff ρ).1 (Or.inl (hv.2.subset hρ))
  imod Hclose $$ [Hst Hd He Hql Hp Hx Hdl Hrl Hents] with -
  · inext
    iexists st
    iframe Hst Hd
    iexists ents, ql', pend, exd, dl, rl
    iframe
    ipureintro; exact hok
  imodintro
  iexists ents
  iframe Hlb Hb
  ipureintro
  exact ⟨h2, (hle ρ).2, hwf⟩

/-- Once a round `ρ' ≥ ρ` of slot `s` is notified (in a queue log lower bound): a lower bound of the
counted messages with round `ρ` full, their well-formedness and facts. -/
theorem slot_snapshot_le (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat)
    (e : SlotV) (he : γl.slots[s]? = some e) (ql : List (Option Nat)) (ρ : Nat)
    (hρ : ∃ ρ', ρ ≤ ρ' ∧ some ρ' ∈ ql) (E : CoPset) (hE : ↑(slotN k s) ⊆ E) :
    slotsInv (GF := GF) γ cf k γl γc ∗ qLb γc s ql ⊢
      |={E}=> ∃ ents : List Ent, monoListLbOwn (entName γl γc s) ents ∗
        ⌜(tally ents ρ).length = cf.q ∧ ((tally ents ρ).map (fun e => e.2.1)).Nodup ∧
          ∀ e ∈ ents, e.2.1 < cf.n ∧ msgRound e.2.2.2 = some (s, e.1)⌝ ∗
        [∗list] e ∈ ents, bmsgOk γ cf e.2.1 e.2.2.2 := by
  iintro ⟨#Hinvs, #Hq⟩
  ihave #Hinv := slotsInv_lookup γ k γl γc s e he $$ Hinvs
  imod inv_acc hE $$ Hinv with ⟨Hi, Hclose⟩
  imod Hi with Hi
  unfold slotInv
  icases Hi with ⟨%st, Hst, #Hd, Hg⟩
  unfold slotGhost
  icases Hg with ⟨%ents, %ql', %pend, %exd, %dl, %rl, He, Hql, Hp, Hx, Hdl, Hrl, Hents, %hok⟩
  unfold qLb
  ihave %hv := mono_list_auth_lb_valid _ _ _ _ $$ Hql Hq
  ihave ⟨He, #Hlb⟩ := mono_auth_lb _ _ _ $$ He
  ihave Hents2 := BigSepL.bigSepL_mono_of_forall
    (Φ := fun _ e => entRes (GF := GF) γ cf γl γc s e)
    (Ψ := fun _ e => iprop(entRes (GF := GF) γ cf γl γc s e ∗ bmsgOk γ cf e.2.1 e.2.2.2))
    (fun {_ e} => entRes_bmsg γ γl γc s e) $$ Hents
  ihave ⟨Hents, #Hb⟩ := BigSepL.bigSepL_sep_eqv.1 $$ Hents2
  have hok' := hok
  obtain ⟨_, hwf, hle, _, hiff, _⟩ := hok'
  obtain ⟨ρ', hle', hρ'⟩ := hρ
  have h2 : (tally ents ρ).length = cf.q :=
    (hiff ρ).1 (Or.inl (notified_le hok.2.2.2.1 hle' (hv.2.subset hρ')))
  imod Hclose $$ [Hst Hd He Hql Hp Hx Hdl Hrl Hents] with -
  · inext
    iexists st
    iframe Hst Hd
    iexists ents, ql', pend, exd, dl, rl
    iframe
    ipureintro; exact hok
  imodintro
  iexists ents
  iframe Hlb Hb
  ipureintro
  exact ⟨h2, (hle ρ).2, hwf⟩

/-- At any later state: the slot's counts are those of the snapshot's round `ρ`. -/
theorem slotGhost_tally (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat)
    (st : SlotSt) (ents0 : List Ent) (ρ : Nat) (h2 : (tally ents0 ρ).length = cf.q) :
    slotGhost (GF := GF) γ cf k γl γc s st ∗ monoListLbOwn (entName γl γc s) ents0 ⊢
      slotGhost γ cf k γl γc s st ∗ ⌜∃ ents, TallyOk st ents ∧ tally ents ρ = tally ents0 ρ⌝ := by
  unfold slotGhost
  iintro ⟨⟨%ents, %ql', %pend, %exd, %dl, %rl, He, Hql, Hp, Hx, Hdl, Hrl, Hents, %hok⟩, #Hlb⟩
  ihave %hv := mono_list_auth_lb_valid _ _ _ _ $$ He Hlb
  isplitl
  · iexists ents, ql', pend, exd, dl, rl
    iframe
    ipureintro; exact hok
  · ipureintro
    exact ⟨ents, hok.1, tally_prefix hv.2 h2 (hok.2.2.1 ρ).1⟩

/-- A counted state of phase `p ≥ 1` (round `2p`): its fact. -/
theorem bmsgOk_st (γ : Names) (X : Nat) (m : MsgV) (s p : Nat) (hp : 1 ≤ p)
    (h : msgRound m = some (s, 2 * p)) :
    bmsgOk (GF := GF) γ cf X m ⊢ fact γ.rab (.st X s p) (.bit m.value.toNat) := by
  obtain ⟨hs, hc⟩ := msgRound_cases h
  have hT := ty_ne
  rcases hc with ⟨ht, hρ⟩ | ⟨ht, hρ⟩ | ⟨ht, hρ⟩
  · omega
  · unfold bmsgOk
    rw [if_neg (by rw [ht]; exact hT.2.2.2.2.1.symm), if_neg (by rw [ht]; exact hT.1.symm),
      if_pos ht]
    iintro ⟨%o, %ho, H⟩
    rw [ho.1] at hs
    simp only [Option.map_some, Option.getD_some] at hs
    have : m.phase.toNat = p := by omega
    rw [hs, this]; iexact H
  · omega

/-- A counted vote of phase `p` (round `2p + 1`): its fact. -/
theorem bmsgOk_vt (γ : Names) (X : Nat) (m : MsgV) (s p : Nat)
    (h : msgRound m = some (s, 2 * p + 1)) :
    bmsgOk (GF := GF) γ cf X m ⊢ fact γ.rab (.vt X s p) (.bit m.value.toNat) := by
  obtain ⟨hs, hc⟩ := msgRound_cases h
  have hT := ty_ne
  rcases hc with ⟨ht, hρ⟩ | ⟨ht, hρ⟩ | ⟨ht, hρ⟩
  · omega
  · omega
  · unfold bmsgOk
    rw [if_neg (by rw [ht]; exact hT.2.2.2.2.2.symm), if_neg (by rw [ht]; exact hT.2.1.symm),
      if_neg (by rw [ht]; exact hT.2.2.1.symm), if_pos ht]
    iintro ⟨%o, %ho, H⟩
    rw [ho.1] at hs
    simp only [Option.map_some, Option.getD_some] at hs
    have : m.phase.toNat = p := by omega
    rw [hs, this]; iexact H

/-- A counted proposal (round 0): its object, facts. -/
theorem bmsgOk_prop (γ : Names) (X : Nat) (m : MsgV) (s : Nat)
    (h : msgRound m = some (s, 0)) :
    bmsgOk (GF := GF) γ cf X m ⊢ ∃ o, ⌜m.obj = some o ∧ o.svrSeq.toNat = s⌝ ∗ objOk γ cf o ∗
      fact γ.rab (.prop X s) (.obj (objId o)) := by
  obtain ⟨hs, hc⟩ := msgRound_cases h
  have hT := ty_ne
  rcases hc with ⟨ht, hρ⟩ | ⟨ht, hρ⟩ | ⟨ht, hρ⟩
  · unfold bmsgOk
    rw [if_neg (by rw [ht]; exact hT.2.2.2.1.symm), if_pos ht]
    iintro ⟨%o, %ho, #H1, #H2⟩
    rw [ho.1] at hs
    simp only [Option.map_some, Option.getD_some] at hs
    subst hs
    iexists o
    unfold objId
    iframe H1 H2
    ipureintro; exact ⟨ho.1, rfl⟩
  · unfold bmsgOk
    rw [if_neg (by rw [ht]; exact hT.2.2.2.2.1.symm), if_neg (by rw [ht]; exact hT.1.symm),
      if_pos ht]
    iintro ⟨%o, %ho, -⟩
    exfalso; omega
  · omega


/-- Persistent elements give the elements of a list they cover. -/
theorem bigSepL_pers_sub {A B : Type} (Φ : A → IProp GF) [∀ a, Persistent (Φ a)] (L : List A)
    (L' : List B) (Ψ : B → IProp GF) (h : ∀ x ∈ L', ∃ a ∈ L, (Φ a ⊢ Ψ x)) :
    ([∗list] a ∈ L, Φ a) ⊢ [∗list] x ∈ L', Ψ x := by
  have key : (iprop(□ [∗list] a ∈ L, Φ a) : IProp GF) ⊢ [∗list] x ∈ L', Ψ x :=
    BigSepL.bigSepL_intro (Φ := fun _ x => Ψ x) (fun k x hx => by
      obtain ⟨a, ha, hΦ⟩ := h x (List.mem_of_getElem? hx)
      exact intuitionistically_elim.trans ((BigSepL.bigSepL_mem (Φ := Φ) ha).trans hΦ))
  iintro #H
  iapply key
  iexact H

/-- A pure property of every element, from persistent elements. -/
theorem bigSepL_pure_of {A : Type} (Φ : A → IProp GF) (P : A → Prop) (h : ∀ a, Φ a ⊢ ⌜P a⌝) :
    ∀ L : List A, ([∗list] a ∈ L, Φ a) ⊢ ⌜∀ a ∈ L, P a⌝
  | [] => by iintro -; ipureintro; simp
  | a :: L => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Ha, H⟩
    ihave %h1 := h a $$ Ha
    ihave %h2 := bigSepL_pure_of Φ P h L $$ H
    ipureintro
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1
    · exact h2 x hx

/-- The facts of a frozen round of states (`r = 1`, `p ≥ 1`) or votes (`r = 2`). -/
theorem bits_facts (γ : Names) (s p r : Nat) (hr : (r = 1 ∧ 1 ≤ p) ∨ r = 2) (ents : List Ent)
    (hwf : ∀ e ∈ ents, msgRound e.2.2.2 = some (s, e.1)) :
    ([∗list] e ∈ ents, bmsgOk (GF := GF) γ cf e.2.1 e.2.2.2) ⊢
      [∗list] kv ∈ bitFacts s p r (bitPairs (tally ents (2 * p + r - 1))), fact γ.rab kv.1 kv.2 := by
  apply bigSepL_pers_sub (fun e : Ent => bmsgOk (GF := GF) γ cf e.2.1 e.2.2.2)
  intro x hx
  unfold bitFacts bitPairs at hx
  rw [List.map_map] at hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  obtain ⟨he1, he2⟩ := tally_mem he
  refine ⟨e, he1, ?_⟩
  have hm := hwf e he1
  rw [he2] at hm
  rcases hr with ⟨rfl, hp⟩ | rfl
  · simp only [Function.comp, ↓reduceIte]
    have h21 : 2 * p + 1 - 1 = 2 * p := by omega
    rw [h21] at hm
    exact bmsgOk_st γ e.2.1 e.2.2.2 s p hp hm
  · simp only [Function.comp, show ¬ (2 = 1) from by decide, ↓reduceIte]
    have h21 : 2 * p + 2 - 1 = 2 * p + 1 := by omega
    rw [h21] at hm
    exact bmsgOk_vt γ e.2.1 e.2.2.2 s p hm

/-- The facts of a frozen round of proposals: each carries an object, with its facts. -/
theorem props_facts0 (γ : Names) (s : Nat) (ents : List Ent)
    (hwf : ∀ e ∈ ents, msgRound e.2.2.2 = some (s, e.1)) :
    ([∗list] e ∈ ents, bmsgOk (GF := GF) γ cf e.2.1 e.2.2.2) ⊢
      ⌜∀ e ∈ tally ents 0, e.2.2.2.obj ≠ none⌝ ∗
      ([∗list] kv ∈ propFacts s (propPairs (tally ents 0)), fact γ.rab kv.1 kv.2) ∗
      [∗list] o ∈ (tally ents 0).filterMap (fun e => e.2.2.2.obj),
        objOk γ cf o ∗ ⌜o.svrSeq.toNat = s⌝ := by
  iintro #H
  isplitr
  · ihave #H' := bigSepL_pers_sub (fun e : Ent => bmsgOk (GF := GF) γ cf e.2.1 e.2.2.2) ents
      (tally ents 0) (fun e => iprop(⌜e.2.2.2.obj ≠ none⌝)) (fun e he => by
        obtain ⟨he1, he2⟩ := tally_mem he
        refine ⟨e, he1, ?_⟩
        have hm := hwf e he1; rw [he2] at hm
        iintro H1
        ihave ⟨%o, %ho, -⟩ := bmsgOk_prop γ e.2.1 e.2.2.2 s hm $$ H1
        ipureintro; rw [ho.1]; simp) $$ H
    iapply bigSepL_pure_of (fun e : Ent => iprop(⌜e.2.2.2.obj ≠ none⌝ : IProp GF))
      (fun e => e.2.2.2.obj ≠ none) (fun a => by iintro %h; ipureintro; exact h) $$ H'
  isplitr
  · iapply bigSepL_pers_sub (fun e : Ent => bmsgOk (GF := GF) γ cf e.2.1 e.2.2.2) ents _ _ _ $$ H
    intro x hx
    unfold propFacts at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨e, he, o, ho, rfl⟩ := propPairs_mem hy
    obtain ⟨he1, he2⟩ := tally_mem he
    refine ⟨e, he1, ?_⟩
    have hm := hwf e he1; rw [he2] at hm
    iintro H1
    ihave ⟨%o', %ho', -, #Hf⟩ := bmsgOk_prop γ e.2.1 e.2.2.2 s hm $$ H1
    rw [ho] at ho'
    obtain ⟨h1, -⟩ := ho'
    cases h1
    iexact Hf
  · iapply bigSepL_pers_sub (fun e : Ent => bmsgOk (GF := GF) γ cf e.2.1 e.2.2.2) ents _ _ _ $$ H
    intro o ho
    obtain ⟨e, he, ho⟩ := List.mem_filterMap.1 ho
    obtain ⟨he1, he2⟩ := tally_mem he
    refine ⟨e, he1, ?_⟩
    have hm := hwf e he1; rw [he2] at hm
    iintro H1
    ihave ⟨%o', %ho', #Hok, -⟩ := bmsgOk_prop γ e.2.1 e.2.2.2 s hm $$ H1
    rw [ho] at ho'
    obtain ⟨h1, h2⟩ := ho'
    cases h1
    iframe Hok
    ipureintro; exact h2

end ghost

end Perennial.rabia.roles.server.layers.consensus
