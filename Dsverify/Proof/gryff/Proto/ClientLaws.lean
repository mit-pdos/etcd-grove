/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto/ClientLaws.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The laws of Gryff's invariant that the client node's adapter uses (cross-package: the adapter
registers an operation, the replicas commit it, the adapter claims its commit).

* `opAU γ i Q`: the client's atomic update for input `i` with commit postcondition `Q` (the
  shape of `opAwpMaybe`'s, at `↑clientN`).
* `opReg γ id i` (persistent): operation `id = (cid, req)` with input `i` is registered (what a
  request's bytes carry, Gryff's client protocol).
* `opPending γ id i Q` (exclusive): the client's handle on its registered operation.
* `opDone γ id o` (persistent): operation `id` is linearized with output `o` (what a reply's bytes
  carry).
* `turnTok γ cid req` (exclusive): Gryff client `cid`'s next request is `req` (one operation in
  flight per client id: write tags `(ts, cid, 0)` are unique to their write).

`op_begin` registers an operation (its atomic update deposited in the invariant, its receipt's
predicate saved); `op_end` claims its commit from a reply's `opDone` (under a later: the receipt
lives in the invariant) and gives the client id's turn back for the next request; `op_place` is
in `WireLaws.lean`, is the coordinator's: it fixes an operation's place from its prophecy (D2);
`opDone_intro_*` witness a linearized operation's output (what a reply carries).
-/
module

public import Dsverify.Proof.gryff.Proto.Inv
public import Dsverify.Proof.gryff.Proto.InvSteps
public import Dsverify.Proof.gryff.Proto2.InvDefs
public import Dsverify.Proof.gryff.Proto2P.Facts
public import Dsverify.Proof.gryff.Lab.ClientSpec
public import Dsverify.Proof.gryff.Lab.ModelsCas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode proto dsverify_lab.harness

section
variable [GooseExts] {GF : BundledGFunctors} [AllG GF] [InvGS_gen .hasLC GF]

/-- Operation `id` with input `i` is registered (persistent): its registration's element. -/
@[irreducible] def opReg (γ : ProtoNames) (id : OpId) (i : RegInput w64) : IProp GF :=
  iprop(∃ n : OpInfo, ghostMapElem γ.ops id DFrac.discard n ∗ ⌜n.input = i⌝)
/-- The client's handle on its registered operation (exclusive): its registration, its saved
commit postcondition, its claim token, and its id's turn element marked pending. -/
@[irreducible] def opPending (γ : ProtoNames) (id : OpId) (i : RegInput w64)
    (Q : w64 → w64 → RegOutput w64 → IProp GF) : IProp GF :=
  iprop(∃ n : OpInfo, ghostMapElem γ.ops id DFrac.discard n ∗ ⌜n.input = i⌝ ∗ savedQ n.rcpt Q ∗
    token n.claim ∗ ghostMapElem γ.turns id.1 (DFrac.own 1) (id.2 + 1, true))
/-- Operation `id` is linearized with output `o` (persistent): a lower bound of `lin` (whose
operations are distinct) records it; and (stage 2) a lower bound of the real history has a reply
to it (`op_end` needs it: the client id's next request is handled after that reply, `WB`). -/
@[irreducible] def opDone (γ : ProtoNames) (id : OpId) (o : RegOutput w64) : IProp GF :=
  iprop((∃ L : List (OpId × RegOutput w64), monoListLbOwn γ.lin L ∗
    ⌜(id, o) ∈ L ∧ (L.map Prod.fst).Nodup⌝) ∗
    ∃ l : List pure.Label, histLb γ l ∗ ⌜repliedIn l id⌝)
/-- Operation `id`'s place is fixed: `p` at frontier `freg` (persistent): the places map records
`p`, or `none` when `p` is not a valid place (`placeRec`). -/
@[irreducible] def opPlaced (γ : ProtoNames) (id : OpId) (p : Option PTag) (freg : PTag) :
    IProp GF :=
  iprop(∃ (n : OpInfo) (q : Option PTag), ghostMapElem γ.ops id DFrac.discard n ∗
    ghostMapElem γ.places id DFrac.discard (Placement.placed q freg) ∗ ⌜placeRec n.input id freg p q⌝)
/-- Gryff client `cid` may register requests `req` and above (exclusive); its last request is not
pending (the turn map's value `(req, false)`; a pending request's `opPending` holds the element
at `(req + 1, true)`, H-U4-4). -/
def turnTok (γ : ProtoNames) (cid req : Int) : IProp GF :=
  ghostMapElem γ.turns cid (DFrac.own 1) (req, false)

theorem opReg_persistent (γ : ProtoNames) (id : OpId) (i : RegInput w64) :
    Persistent (opReg (GF := GF) γ id i) := by
  unfold opReg; infer_instance
theorem opDone_persistent (γ : ProtoNames) (id : OpId) (o : RegOutput w64) :
    Persistent (opDone (GF := GF) γ id o) := by
  unfold opDone; infer_instance
theorem opPlaced_persistent (γ : ProtoNames) (id : OpId) (p : Option PTag) (f : PTag) :
    Persistent (opPlaced (GF := GF) γ id p f) := by
  unfold opPlaced; infer_instance

private theorem nodup_map_inj {α β : Type} (f : α → β) :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: l, h, a, b, ha, hb, e => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 ha with ha1 | ha1
    · rcases List.mem_cons.1 hb with hb1 | hb1
      · rw [ha1, hb1]
      · subst ha1; exact absurd (e ▸ List.mem_map_of_mem hb1) h.1
    · rcases List.mem_cons.1 hb with hb1 | hb1
      · subst hb1; exact absurd (e.symm ▸ List.mem_map_of_mem ha1) h.1
      · exact nodup_map_inj f h.2 ha1 hb1 e

private instance : Inhabited (RegOutput w64) := ⟨.done⟩
private instance : Inhabited (IProp GF) := ⟨iprop(True)⟩

theorem savedQ_agree (γq : GName) (Q1 Q2 : w64 → w64 → RegOutput w64 → IProp GF)
    (a b : w64) (c : RegOutput w64) :
    ⊢ savedQ (GF := GF) γq Q1 -∗ savedQ γq Q2 -∗ ▷ (Q1 a b c ≡ Q2 a b c) := by
  unfold savedQ
  iintro H1 H2
  iapply (saved_pred_agree γq _ _ (fun x : w64 × w64 × RegOutput w64 => Q1 x.1 x.2.1 x.2.2)
    (fun x : w64 × w64 × RegOutput w64 => Q2 x.1 x.2.1 x.2.2) (a, b, c)) $$ H1 H2

private theorem eq_rewrite_wand {P Q : IProp GF} : ⊢ (P ≡ Q) -∗ Q -∗ P := by
  iintro #H HQ
  ihave #Hiff := internalEq_iff P Q $$ H
  icases Hiff with ⟨-, H2⟩
  iapply H2
  iexact HQ

/-! ## The operation budget (D14) -/

theorem budget_split (γ : ProtoNames) (a b : Nat) :
    budget (GF := GF) γ (a + b) ⊢ budget γ a ∗ budget γ b := by
  unfold budget
  iintro ⟨%us, %hl, H⟩
  rw [← List.take_append_drop a us]
  icases BigSepL.bigSepL_append.1 $$ H with ⟨H1, H2⟩
  isplitl [H1]
  · iexists us.take a
    iframe H1
    ipureintro; simp [hl]
  · iexists us.drop a
    iframe H2
    ipureintro; simp [hl]

theorem budget_weaken (γ : ProtoNames) (a b : Nat) (h : b ≤ a) :
    budget (GF := GF) γ a ⊢ budget γ b := by
  iintro H
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  icases budget_split γ b c $$ H with ⟨H, -⟩
  iexact H

theorem budget_zero (γ : ProtoNames) : ⊢ budget (GF := GF) γ 0 := by
  unfold budget
  iexists []
  isplitr
  · ipureintro; rfl
  iapply BigSepL.bigSepL_nil.2; iempintro

/-- Register operation `(cid, req)`: its atomic update goes into the invariant, and it spends one
budget unit (D14: the invariant bounds the registrations by the units given out). Stage 2:
`gryffInv2`; the statement is stage 1's otherwise. -/
theorem op_begin (γ : ProtoNames) (cid r req : Int) (i : RegInput w64)
    (Q : w64 → w64 → RegOutput w64 → IProp GF) (E : CoPset) (hE : ↑gryffN ⊆ E)
    (hr : r ≤ req) :
    gryffInv2 γ ∗ turnTok γ cid r ∗ opAU γ i Q ∗ budget γ 1 ⊢
      |={E}=> opPending γ (cid, req) i Q ∗ opReg γ (cid, req) i := by
  unfold opPending opReg turnTok budget
  iintro ⟨#Hinv, Hturn, HAU, ⟨%us, %hl, Hus⟩⟩
  obtain ⟨u, rfl⟩ := List.length_eq_one_iff.1 hl
  icases Hus with ⟨Hu, -⟩
  imod saved_pred_alloc (fun x : w64 × w64 × RegOutput w64 => Q x.1 x.2.1 x.2.2) DFrac.discard
    DFrac.valid_discard with ⟨%γr, #HQ0⟩
  ihave #HQ : savedQ (GF := GF) γr Q $$ [HQ0]
  · unfold savedQ; iexact HQ0
  imod token_alloc (GF := GF) with ⟨%γc, Htok⟩
  let n : OpInfo := ⟨i, γr, γr, γc⟩
  unfold gryffInv2
  iinv Hinv with Hi Hclose
  all_goals try exact hE
  unfold gryffInv2Body
  icases Hi with ⟨%S, Hreg, Ht0, Ht1, Ht2, Hhist, HP, HNP, Hids, HB, Hlin, Hops, Hturns,
    Hconns, Hplacers, HcR, Hcur, Hrx, Hreqs, >%Hf, Hres⟩
  imod Hops; imod Hturns; imod HB
  ihave %ht := ghost_map_lookup $$ Hturns Hturn
  ihave %hu := ghost_map_lookup $$ HB Hu
  obtain ⟨hfresh, hnl, hf'⟩ := p2.facts_op_begin Hf hr ht hu n
  imod ghost_map_insert_persist (cid, req) n hfresh $$ Hops with ⟨Hops, #Hn⟩
  imod ghost_map_update ((req + 1, true) : Int × Bool) $$ Hturns Hturn with ⟨Hturns, Hturn⟩
  imod ghost_map_delete $$ HB Hu with HB
  imod Hclose $$ [Hreg Ht0 Ht1 Ht2 Hhist HP HNP Hids HB Hlin Hops Hturns Hconns Hplacers HcR
    Hcur Hrx Hreqs Hres HAU] with -
  · inext
    iexists { S with info := S.info.insert (cid, req) n, turns := S.turns.insert cid (req + 1, true), B := S.B.delete u }
    iframe Hreg Ht0 Ht1 Ht2 Hhist HP HNP Hids HB Hlin Hops Hturns Hconns Hplacers HcR Hcur Hrx Hreqs
    isplitr
    · ipureintro; exact hf'
    iapply (BigSepM.bigSepM_insert (show get? S.info (cid, req) = none from hfresh)).2
    iframe Hres
    unfold opRes
    ileft
    isplitr
    · ipureintro; exact hnl
    iexists Q
    have e : (infoMeta n).rcpt = γr := rfl
    have e' : (infoMeta n).input = i := rfl
    rw [e, e']
    iframe HQ
    inext
    iexact HAU
  imodintro
  isplitl [Htok Hturn]
  · iexists n
    iframe Hn HQ Htok Hturn
    ipureintro; rfl
  · iexists n
    iframe Hn
    ipureintro; rfl

/-- Claim a linearized operation's commit, from a reply's witness; the client id's turn passes
to the next request (stage 2: `gryffInv2`; the statement is stage 1's otherwise). -/
theorem op_end (γ : ProtoNames) (cid req : Int) (i : RegInput w64) (o : RegOutput w64)
    (Q : w64 → w64 → RegOutput w64 → IProp GF) (E : CoPset) (hE : ↑gryffN ⊆ E) :
    gryffInv2 γ ∗ opPending γ (cid, req) i Q ∗ opDone γ (cid, req) o ⊢
      |={E}=> ▷ ▷ (∃ σ σ', Q σ σ' o) ∗ turnTok γ cid (req + 1) := by
  unfold opPending opDone turnTok histLb
  iintro ⟨#Hinv, ⟨%n, #Hn, %hn, #HQ, Htok, Hturn⟩, ⟨⟨%L, #HL, %hL⟩, ⟨%l, #Hl, %hrep⟩⟩⟩
  unfold gryffInv2
  iinv Hinv with Hi Hclose
  all_goals try exact hE
  unfold gryffInv2Body
  icases Hi with ⟨%S, Hreg, Ht0, Ht1, Ht2, Hhist, HP, HNP, Hids, HB, Hlin, Hops, Hturns,
    Hconns, Hplacers, HcR, Hcur, Hrx, Hreqs, >%Hf, Hres⟩
  imod Hops; imod Hlin; imod Hturns; imod Hhist
  ihave %hni := ghost_map_lookup $$ Hops Hn
  ihave %ht := ghost_map_lookup $$ Hturns Hturn
  ihave %hLl := mono_list_auth_lb_valid γ.lin 1 S.linL L $$ Hlin HL
  ihave %hll := mono_list_auth_lb_valid γ.s2.hist 1 S.l1 l $$ Hhist Hl
  have hin : ((cid, req), o) ∈ S.linL := hLl.2.subset hL.1
  have hrep' : repliedIn S.l1 (cid, req) := p2.repliedIn_prefix hll.2 hrep
  icases (BI.later_mono (BigSepM.bigSepM_delete
    (show get? S.info (cid, req) = some n from hni)).1) $$ Hres with ⟨Hm, Hrest⟩
  unfold opRes
  have e1 : (infoMeta n).rcpt = n.rcpt := rfl
  have e2 : (infoMeta n).claim = n.claim := rfl
  rw [e1, e2]
  icases Hm with (⟨>%hnot, -⟩ | ⟨%o', %Q', %σ1, %σ2, >%ho', HQ', Hr⟩)
  · exact absurd hin (hnot o)
  have heo : o' = o := by
    have := nodup_map_inj Prod.fst Hf.linNodup ho' hin rfl
    simp only [Prod.mk.injEq, true_and] at this; exact this
  subst heo
  icases BI.later_or.1 $$ Hr with (Hr | Hr)
  · imod ghost_map_update ((req + 1, false) : Int × Bool) $$ Hturns Hturn with ⟨Hturns, Hturn⟩
    have hf' := p2.facts_op_end Hf ht hrep'
    imod Hclose $$ [Hreg Ht0 Ht1 Ht2 Hhist HP HNP Hids HB Hlin Hops Hturns Hconns Hplacers HcR
      Hcur Hrx Hreqs Hrest Htok] with -
    · inext
      iexists { S with turns := S.turns.insert cid (req + 1, false) }
      iframe Hreg Ht0 Ht1 Ht2 Hhist HP HNP Hids HB Hlin Hops Hturns Hconns Hplacers HcR Hcur Hrx Hreqs
      isplitr
      · ipureintro; exact hf'
      iapply (BigSepM.bigSepM_delete (show get? S.info (cid, req) = some n from hni)).2
      iframe Hrest
      iright
      iexists o', Q, σ1, σ2
      rw [e1, e2]
      isplitr
      · ipureintro; exact hin
      isplitr
      · iexact HQ
      iright
      iexact Htok
    imodintro
    iframe Hturn
    inext
    ihave Heq := savedQ_agree n.rcpt Q Q' σ1 σ2 o' $$ HQ HQ'
    inext
    iexists σ1, σ2
    iapply eq_rewrite_wand $$ Heq Hr
  · imod Hr
    iexfalso
    iapply token_exclusive $$ Htok Hr

/-- A reply's witness is unique (an operation has one output). -/
theorem opDone_agree (γ : ProtoNames) (id : OpId) (o1 o2 : RegOutput w64) :
    opDone (GF := GF) γ id o1 ∗ opDone γ id o2 ⊢ ⌜o1 = o2⌝ := by
  unfold opDone
  iintro ⟨⟨⟨%L1, H1, %h1⟩, -⟩, ⟨⟨%L2, H2, %h2⟩, -⟩⟩
  ihave %hp := mono_list_lb_valid $$ H1 H2
  ipureintro
  -- both records are in the longer list, whose operations are distinct
  have key : ∀ {A B : List (OpId × RegOutput w64)}, A <+: B → (id, o1) ∈ A ∨ (id, o1) ∈ B →
      (id, o2) ∈ A ∨ (id, o2) ∈ B → (B.map Prod.fst).Nodup → o1 = o2 := by
    intro A B hAB ha hb hn
    have ha' : (id, o1) ∈ B := ha.elim (fun h => hAB.subset h) (fun h => h)
    have hb' : (id, o2) ∈ B := hb.elim (fun h => hAB.subset h) (fun h => h)
    have := nodup_map_inj Prod.fst hn ha' hb' rfl
    simp only [Prod.mk.injEq, true_and] at this
    exact this
  rcases hp with hp | hp
  · exact key hp (Or.inl h1.1) (Or.inr h2.1) h2.2
  · exact key hp (Or.inr h1.1) (Or.inl h2.1) h1.2

end

end Perennial.gryff
