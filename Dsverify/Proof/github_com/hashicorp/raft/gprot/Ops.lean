/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/gprot/Ops.lean (241f27e).
-/
/-
`gprot` extension E1 (linearizability support): clients' operation tokens.

A client (hr3) that submits a command with data `d` holds `opTok γ d n`, created from its authority
`opsAuth γ M` for a datum it never used (`d ∉ M`) together with a snapshot of length `n` of the
committed log taken when the operation was called (`M` records `d ↦ n`). The leader that appends
the command to its log (`leaderAppendCmd_upd`) takes the token into the invariant. So:
* a client still holding `opTok γ d n` knows no committed entry is its command
  (`cmd_not_committed`);
* every committed command's data is in `M`, with its call snapshot's length below its index
  (`cmd_committed_ops`): it was appended after its operation was called;
* a command is committed at one index at most (`cmd_unique`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Laws

@[expose] public section

set_option linter.unusedVariables false
set_option linter.deprecated false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft
namespace gprot

open proto

section ops
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]
variable (γ : GNames)

/-! ### Internals -/

theorem lookup_ins {V : Type} [Pos.Countable V] (O : GMap (List w8) V) (k k' : List w8) (v : V) :
    (O.insert k v).lookup k' = if k = k' then some v else O.lookup k' := rfl

/-- Two commands of a list whose command data are distinct, with the same data, are one. -/
theorem nodup_filter_idx (es : List Entry) :
    ∀ (j1 j2 : Nat) (a b : Entry),
      ((es.filter (fun e => decide (e.kind = kCommand))).map Entry.data).Nodup →
      es[j1]? = some a → es[j2]? = some b → a.kind = kCommand → b.kind = kCommand →
      a.data = b.data → j1 = j2 := by
  induction es with
  | nil => intro j1 j2 a b _ h1; simp at h1
  | cons x xs ih =>
    intro j1 j2 a b hnd h1 h2 ha hb hab
    by_cases hx : x.kind = kCommand
    · have hf : (x :: xs).filter (fun e => decide (e.kind = kCommand)) =
          x :: xs.filter (fun e => decide (e.kind = kCommand)) := by simp [hx]
      rw [hf, List.map_cons, List.nodup_cons] at hnd
      have hmem : ∀ (j : Nat) (c : Entry), xs[j]? = some c → c.kind = kCommand →
          c.data ∈ (xs.filter (fun e => decide (e.kind = kCommand))).map Entry.data := by
        intro j c hc hck
        exact List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨List.mem_of_getElem? hc, by simp [hck]⟩, rfl⟩
      cases j1 with
      | zero =>
        cases j2 with
        | zero => rfl
        | succ j2 =>
          simp at h1; subst h1
          exact absurd (hab ▸ hmem j2 b h2 hb) hnd.1
      | succ j1 =>
        cases j2 with
        | zero =>
          simp at h2; subst h2
          exact absurd (hab.symm ▸ hmem j1 a h1 ha) hnd.1
        | succ j2 => exact congrArg (· + 1) (ih j1 j2 a b hnd.2 h1 h2 ha hb hab)
    · have hf : (x :: xs).filter (fun e => decide (e.kind = kCommand)) =
          xs.filter (fun e => decide (e.kind = kCommand)) := by simp [hx]
      rw [hf] at hnd
      cases j1 with
      | zero => simp at h1; subst h1; exact absurd ha hx
      | succ j1 =>
        cases j2 with
        | zero => simp at h2; subst h2; exact absurd hb hx
        | succ j2 => exact congrArg (· + 1) (ih j1 j2 a b hnd h1 h2 ha hb hab)

theorem opTok_eq (d : List w8) (n : Nat) :
    opTok (GF := GF) γ d n ⊣⊢ d ↪[γ.ops] n ∗ ∃ L : RLog, CLb γ L ∗ ⌜L.length = n⌝ := by
  unfold opTok; exact .rfl

theorem CLb_eq (L : RLog) : CLb (GF := GF) γ L ⊣⊢ monoListLbOwn γ.C L := by
  unfold CLb; exact .rfl

/-- The invariant's tokens exclude a client's token. -/
theorem ops_excl (O : GMap (List w8) Nat) (d : List w8) (n : Nat) :
    ([∗map] d ↦ n ∈ O, d ↪[γ.ops] n) ∗ d ↪[γ.ops] n ⊢
      ([∗map] d ↦ n ∈ O, d ↪[γ.ops] n) ∗ d ↪[γ.ops] n ∗ ⌜O.lookup d = none⌝ := by
  cases hd : O.lookup d with
  | none => iintro ⟨H, Hf⟩; iframe; ipureintro; rfl
  | some n' =>
    iintro ⟨H, Hf⟩
    ihave ⟨Hf2, Hcl⟩ := (BigSepM.bigSepM_lookup_acc (Φ := fun d n => (d ↪[γ.ops] n : IProp GF))
      (m := O) (i := d) (x := n') hd).1 $$ H
    ihave %hne := ghostMapElem_ne γ.ops d d (DFrac.own 1) n n' $$ Hf Hf2
    exact absurd rfl hne

/-- The invariant's token of data `d`, when there is one. -/
theorem ops_get (O : GMap (List w8) Nat) (d : List w8) (n : Nat) (hd : O.lookup d = some n) :
    ([∗map] d ↦ n ∈ O, d ↪[γ.ops] n) ⊢
      d ↪[γ.ops] n ∗ (d ↪[γ.ops] n -∗ [∗map] d ↦ n ∈ O, d ↪[γ.ops] n) :=
  (BigSepM.bigSepM_lookup_acc (Φ := fun d n => (d ↪[γ.ops] n : IProp GF)) (m := O) hd).1

/-- Taking clients' tokens into the invariant's map. -/
theorem absorb (C : RLog) (cs : List Entry) :
    ∀ O : GMap (List w8) Nat,
    monoListAuthOwn γ.C 1 C ∗ ([∗map] d ↦ n ∈ O, d ↪[γ.ops] n) ∗
      ([∗list] e ∈ cs, ∃ n, opTok (GF := GF) γ e.data n) ⊢
    ∃ O' : GMap (List w8) Nat, monoListAuthOwn γ.C 1 C ∗ ([∗map] d ↦ n ∈ O', d ↪[γ.ops] n) ∗
      ⌜(∀ d n, O.lookup d = some n → O'.lookup d = some n) ∧
        (∀ d n, O'.lookup d = some n → O.lookup d = some n ∨
          (O.lookup d = none ∧ (∃ e ∈ cs, e.data = d) ∧ n ≤ C.length)) ∧
        (∀ e ∈ cs, O.lookup e.data = none ∧ O'.lookup e.data ≠ none) ∧
        (cs.map Entry.data).Nodup⌝ := by
  induction cs with
  | nil =>
    intro O
    iintro ⟨HC, HO, -⟩
    iexists O; iframe; ipureintro
    refine ⟨fun _ _ h => h, fun _ _ h => Or.inl h, fun e he => by simp at he, List.nodup_nil⟩
  | cons e cs ih =>
    intro O
    iintro ⟨HC, HO, Hl⟩
    ihave ⟨⟨%n, Ht⟩, Hl⟩ := BigSepL.bigSepL_cons.1 $$ Hl
    ihave ⟨Hf, %L, #HL, %hLn⟩ := (opTok_eq γ e.data n).1 $$ Ht
    ihave #HL := (CLb_eq γ L).1 $$ HL
    ihave %hpre := mono_list_auth_lb_valid γ.C 1 C L $$ HC HL
    have hn : n ≤ C.length := by rw [← hLn]; exact hpre.2.length_le
    ihave ⟨HO, Hf, %hfresh⟩ := ops_excl γ O e.data n $$ [HO Hf]
    · iframe
    ihave HO1 := (BigSepM.bigSepM_insert (Φ := fun d n => (d ↪[γ.ops] n : IProp GF))
      (m := O) (i := e.data) (x := n) hfresh).2 $$ [Hf HO]
    · iframe
    ihave ⟨%O', HC, HO', %h⟩ := ih (O.insert e.data n) $$ [HC HO1 Hl]
    · iframe
    obtain ⟨h1, h2, h3, h4⟩ := h
    iexists O'; iframe; ipureintro
    have hO1 : ∀ d m, O.lookup d = some m → (O.insert e.data n).lookup d = some m := by
      intro d m hd; rw [lookup_ins]; split
      · subst_vars; rw [hfresh] at hd; cases hd
      · exact hd
    refine ⟨fun d m hd => h1 _ _ (hO1 d m hd), fun d m hd => ?_, fun e' he' => ?_, ?_⟩
    · rcases h2 d m hd with h | ⟨hn1, ⟨e', he', hd'⟩, hm⟩
      · rw [lookup_ins] at h
        split at h
        · subst_vars; cases h
          right; exact ⟨hfresh, ⟨e, List.mem_cons_self, rfl⟩, hn⟩
        · left; exact h
      · rw [lookup_ins] at hn1
        split at hn1
        · cases hn1
        · right; exact ⟨hn1, ⟨e', List.mem_cons_of_mem _ he', hd'⟩, hm⟩
    · rcases List.mem_cons.mp he' with rfl | he'
      · refine ⟨hfresh, ?_⟩
        have := h1 e'.data n (by rw [lookup_ins, if_pos rfl])
        rw [this]; simp
      · have := (h3 e' he').1
        rw [lookup_ins] at this
        split at this
        · cases this
        · exact ⟨this, (h3 e' he').2⟩
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, h4⟩
      obtain ⟨e', he', hd'⟩ := List.mem_map.mp hm
      have := (h3 e' he').1
      rw [lookup_ins, hd', if_pos rfl] at this
      cases this

/-- Open the operation tokens and the committed log of the history, to re-close it at `σ'` (a
leader append: only the leader logs change). -/
theorem HistG_cmd (σ σ' : PState) (hP : PInv σ) (hGr : Grows σ σ')
    (hl : σ'.leader = σ.leader) (hl0 : σ'.len0 = σ.len0) (hc : σ'.cand = σ.cand)
    (hv : σ'.votes = σ.votes) (ha : σ'.acked = σ.acked) (hcm : σ'.commits = σ.commits)
    (hC : σ'.C = σ.C) (ks : List (Nat × Nat)) (oLl : ∀ p, p ∉ ks → llogF σ' p = llogF σ p)
    (hpub : σ'.pubs = σ.pubs := by rfl) :
    HistG (GF := GF) γ σ ⊢ ∃ O : GMap (List w8) Nat, ⌜OpsOK σ O⌝ ∗
      ([∗map] d ↦ n ∈ O, d ↪[γ.ops] n) ∗ monoListAuthOwn γ.C 1 σ.C ∗
      (∀ O' : GMap (List w8) Nat, ⌜OpsOK σ' O'⌝ -∗ ([∗map] d ↦ n ∈ O', d ↪[γ.ops] n) -∗
        monoListAuthOwn γ.C 1 σ.C -∗ |==> HistG γ σ') := by
  unfold HistG OpsG
  iintro ⟨Hl, Hll, Hl0, Hc, Hv, Ha, Hcm, Hvs, ⟨%O, %hO, HO⟩, HC, Hp, Hpm, Hs⟩
  iexists O
  isplitr; · ipureintro; exact hO
  isplitl [HO]; · iexact HO
  isplitl [HC]; · iexact HC
  iintro %O' %hO' HO' HC
  ihave Hp := GMapOf_congr γ.pubs (pubsF σ) (pubsF σ') (fun p => (pubsF_congr hpub p).symm) $$ Hp
  ihave Hpm := PubMaxG_grow γ σ σ' hGr hpub (fun c T h => by rw [hc] at h; exact h) $$ Hpm
  ihave Hs := SnapG_grow γ σ σ' hP hGr $$ Hs
  imod GMapOf_grow γ.llog ks (llogF σ) (llogF σ') (llogF_sub hP hGr) oLl $$ Hll with Hll
  ihave Hl := GMapOf_congr γ.leader σ.leader σ'.leader (fun T => by rw [hl]) $$ Hl
  ihave Hl0 := GMapOf_congr γ.len0 (len0F σ) (len0F σ') (fun T => by unfold len0F; rw [hl, hl0])
    $$ Hl0
  ihave Hc := GMapOf_congr γ.cand (candF σ) (candF σ') (fun p => by unfold candF; rw [hc]) $$ Hc
  ihave Hv := GMapOf_congr γ.votes (votesF σ) (votesF σ') (fun p => by unfold votesF; rw [hv])
    $$ Hv
  ihave Ha := GMapOf_congr γ.acks (acksF σ) (acksF σ') (fun p => (acksF_congr ha p).symm) $$ Ha
  ihave Hcm := GMapOf_congr γ.commits (commitsF σ) (commitsF σ')
    (fun p => (commitsF_congr hcm p).symm) $$ Hcm
  ihave Hvs := GMapOf_congr γ.srvSet (srvsF σ) (srvsF σ')
    (fun i => by unfold srvsF; rw [hGr.1]) $$ Hvs
  rw [hC]
  imodintro
  iframe
  ipureintro; exact hO'

theorem H_CIdx_list (σ : PState) (ks : List (Nat × Entry)) :
    HistG (GF := GF) γ σ ∗ ([∗list] ke ∈ ks, CIdx γ ke.1 ke.2) ⊢
      HistG γ σ ∗ ⌜∀ ke ∈ ks, ent σ.C ke.1 = some ke.2⌝ := by
  induction ks with
  | nil => iintro ⟨H, -⟩; iframe; ipureintro; intro ke h; simp at h
  | cons a ks ih =>
    iintro ⟨H, Hl⟩
    ihave ⟨#Hf, Hfs⟩ := BigSepL.bigSepL_cons.1 $$ Hl
    ihave ⟨H, %h0⟩ := H_C_lookup γ σ a.1 a.2 $$ [H]
    · isplitl [H]; iexact H; iexact Hf
    ihave ⟨H, %hs⟩ := ih $$ [H Hfs]
    · isplitl [H]; iexact H; iexact Hfs
    iframe; ipureintro
    intro ke hke
    rcases List.mem_cons.mp hke with h | h
    · subst h; exact h0
    · exact hs ke h

theorem H_CLb_list (σ : PState) (Ls : List RLog) :
    HistG (GF := GF) γ σ ∗ ([∗list] L ∈ Ls, CLb γ L) ⊢ HistG γ σ ∗ ⌜∀ L ∈ Ls, L <+: σ.C⌝ := by
  induction Ls with
  | nil => iintro ⟨H, -⟩; iframe; ipureintro; intro L h; simp at h
  | cons a Ls ih =>
    iintro ⟨H, Hl⟩
    ihave ⟨#Hf, Hfs⟩ := BigSepL.bigSepL_cons.1 $$ Hl
    ihave ⟨H, %hs⟩ := ih $$ [H Hfs]
    · isplitl [H]; iexact H; iexact Hfs
    unfold HistG CLb
    icases H with ⟨H0, H1, H2, H3, H4, H5, H6, H7, HO, HC, Hr⟩
    ihave %h0 := mono_list_auth_lb_valid γ.C 1 σ.C a $$ HC Hf
    iframe; ipureintro
    intro L hL
    rcases List.mem_cons.mp hL with h | h
    · subst h; exact h0.2
    · exact hs L h

/-- The operation tokens of the opened invariant. -/
theorem H_ops (σ : PState) :
    HistG (GF := GF) γ σ ⊢ ∃ O : GMap (List w8) Nat, ⌜OpsOK σ O⌝ ∗
      ([∗map] d ↦ n ∈ O, d ↪[γ.ops] n) ∗ (([∗map] d ↦ n ∈ O, d ↪[γ.ops] n) -∗ HistG γ σ) := by
  unfold HistG OpsG
  iintro ⟨Hl, Hll, Hl0, Hc, Hv, Ha, Hcm, Hvs, ⟨%O, %hO, HO⟩, HC⟩
  iexists O
  isplitr; · ipureintro; exact hO
  isplitl [HO]; · iexact HO
  iintro HO
  iframe
  ipureintro; exact hO

/-- The token facts after a leader append whose commands' tokens were taken in (`absorb`). -/
theorem OpsOK_append (σ : PState) (i : SID) (es : RLog) (hP : PInv σ)
    (hpre : leaderAppendPre σ i es) (O O' : GMap (List w8) Nat) (hO : OpsOK σ O)
    (h1 : ∀ d n, O.lookup d = some n → O'.lookup d = some n)
    (h2 : ∀ d n, O'.lookup d = some n → O.lookup d = some n ∨
      (O.lookup d = none ∧ (∃ e ∈ es.filter (fun e => decide (e.kind = kCommand)), e.data = d) ∧
        n ≤ σ.C.length))
    (h3 : ∀ e ∈ es.filter (fun e => decide (e.kind = kCommand)),
      O.lookup e.data = none ∧ O'.lookup e.data ≠ none)
    (h4 : ((es.filter (fun e => decide (e.kind = kCommand))).map Entry.data).Nodup) :
    OpsOK (leaderAppend σ i es) O' := by
  have hcls : ∀ T k e, ent ((leaderAppend σ i es).llog T) k = some e →
      ent (σ.llog T) k = some e ∨
      (∃ j, k = (σ.llog (σ.term i)).length + 1 + j ∧ es[j]? = some e) := by
    intro T k e he
    rw [la_llog hP hpre] at he
    split at he
    · rename_i hT
      subst hT
      by_cases hk : k ≤ (σ.llog (σ.term i)).length
      · left; rw [proto.ent_append_left _ _ _ hk] at he; exact he
      · right
        refine ⟨k - (σ.llog (σ.term i)).length - 1, by omega, ?_⟩
        rw [show k = (σ.llog (σ.term i)).length + 1 + (k - (σ.llog (σ.term i)).length - 1) by omega,
          gprot.ent_append_right] at he
        exact he
    · left; exact he
  have hcs : ∀ e ∈ es, e.kind = kCommand → e ∈ es.filter (fun e => decide (e.kind = kCommand)) :=
    fun e he hk => List.mem_filter.mpr ⟨he, by simp [hk]⟩
  have hsome : ∀ d, O.lookup d ≠ none → O'.lookup d ≠ none := by
    intro d hd
    cases h : O.lookup d with
    | none => exact absurd h hd
    | some n => rw [h1 d n h]; simp
  refine ⟨fun T k e he hk => ?_, fun T1 k1 e1 T2 k2 e2 he1 he2 hk1 hk2 hd => ?_,
    fun d n y hn ⟨T, e, he, hk, hd⟩ => ?_⟩
  · rcases hcls T k e he with h | ⟨j, _, hj⟩
    · exact hsome _ (hO.1 T k e h hk)
    · exact (h3 e (hcs e (List.mem_of_getElem? hj) hk)).2
  · rcases hcls _ _ _ he1 with o1 | ⟨j1, hk1', hj1⟩ <;> rcases hcls _ _ _ he2 with o2 | ⟨j2, hk2', hj2⟩
    · exact hO.2.1 _ _ _ _ _ _ o1 o2 hk1 hk2 hd
    · exact absurd ((h3 e2 (hcs e2 (List.mem_of_getElem? hj2) hk2)).1) (hd ▸ hO.1 _ _ _ o1 hk1)
    · exact absurd ((h3 e1 (hcs e1 (List.mem_of_getElem? hj1) hk1)).1) (hd.symm ▸ hO.1 _ _ _ o2 hk2)
    · rw [hk1', hk2', nodup_filter_idx es j1 j2 e1 e2 h4 hj1 hj2 hk1 hk2 hd]
  · show n < y ∨ ∃ e', ent σ.C y = some e' ∧ ¬ (e'.kind = kCommand ∧ e'.data = d)
    rcases h2 d n hn with hold | ⟨hnone, _, hnC⟩
    · rcases hcls T y e he with o | ⟨j, _, hj⟩
      · exact hO.2.2 d n y hold ⟨T, e, o, hk, hd⟩
      · have := (h3 e (hcs e (List.mem_of_getElem? hj) hk)).1
        rw [hd, hold] at this; cases this
    · rcases hcls T y e he with o | ⟨j, hy, hj⟩
      · exact absurd hnone (hd ▸ hO.1 _ _ _ o hk)
      · by_cases hyC : σ.C.length < y
        · left; omega
        · obtain ⟨e', he'⟩ := proto.ent_isSome σ.C y (by omega) (by omega)
          right
          refine ⟨e', he', fun ⟨hk', hd'⟩ => ?_⟩
          have := hO.1 _ _ _ (C_llog σ y e' hP he') hk'
          rw [hd'] at this; exact this hnone

theorem opTok_new (M : GMap (List w8) Nat) (d : List w8) (L : RLog) (hd : M.lookup d = none) :
    opsAuth (GF := GF) γ M ∗ CLb γ L ⊢
      |==> (opsAuth γ (M.insert d L.length) ∗ opTok γ d L.length) := by
  unfold opsAuth
  iintro ⟨Ha, #HL⟩
  imod ghost_map_insert d L.length hd $$ Ha with ⟨Ha, Hf⟩
  imodintro
  isplitl [Ha]; · iexact Ha
  iapply (opTok_eq γ d L.length).2
  isplitl [Hf]; · iexact Hf
  iexists L
  isplitr; · iexact HL
  ipureintro; rfl

/-- **leaderAppend with commands**: as `leaderAppend_upd` (which it replaces in `dispatchLogs`),
for entries that are commands, no-ops or (stage 2) barriers, each command's token going into the
invariant (a barrier has none). -/
theorem leaderAppendCmd_upd (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) (es : RLog)
    (hes : ∀ e ∈ es, e.term = s.term ∧ (e.kind = kCommand ∨ e.kind = kNoop ∨ e.kind = kBarrier)) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ logCouple γ i s.log ∗ leaderIs γ s.term i ∗
      receipt es.length ∗
      ([∗list] e ∈ es.filter (fun e => decide (e.kind = kCommand)), ∃ n, opTok γ e.data n) ⊢
      |={E}=>
      srvOwn γ i { s with log := s.log ++ es } ∗ logCouple γ i (s.log ++ es) ∗
      ([∗list] k ↦ e ∈ es, llogIdx γ s.term (s.log.length + 1 + k) e) := by
  apply Inv_upd γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr, Hcc⟩, Ho, Hlc, #Hl, Hrs, Htoks⟩
  ihave ⟨Hh, %hl⟩ := H_leader_lookup γ σ s.term i $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_open γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  have hP := hg.1
  have hpreA : leaderAppendPre σ i es := ⟨hi', hl, hes⟩
  obtain ⟨hP', hGr⟩ := leaderAppend_inv σ i es hP hpreA
  have hLL : (σ.srv i).log = σ.llog (σ.srv i).term := leader_log σ i hP hi' hl
  have hlen : (σ.srv i).log.length ≤ σ.maxI := log_le_maxI σ i hP hi'
  have oLl : ∀ p, p ∉ (List.range es.length).map
      (fun k => (σ.term i, (σ.log i).length + 1 + k)) →
      llogF (leaderAppend σ i es) p = llogF σ p := by
    intro ⟨T, k⟩ hp
    unfold llogF; simp only [leaderAppend, updT]
    split
    · rename_i hT
      subst hT
      have hLL' : σ.log i = σ.llog (σ.term i) := hLL
      rw [← hLL']
      by_cases hk : k ≤ (σ.log i).length
      · exact ent_append_left _ _ _ hk
      · have hk2 : (σ.log i).length + es.length < k := by
          apply Nat.lt_of_not_le
          intro hk2
          apply hp
          rw [List.mem_map]
          exact ⟨k - (σ.log i).length - 1, List.mem_range.mpr (by omega), by
            simp only [Prod.mk.injEq, true_and]; omega⟩
        rw [ent_none_of_gt _ _ (by simp; omega), ent_none_of_gt _ _ (by omega)]
    · rfl
  have hnew : ∀ (j : Nat) (e : Entry), es[j]? = some e →
      ent ((leaderAppend σ i es).llog (σ.srv i).term) ((σ.srv i).log.length + 1 + j) = some e := by
    intro j e hj
    show ent (updT σ.llog (σ.term i) (σ.log i ++ es) (σ.term i)) ((σ.log i).length + 1 + j) = some e
    simp only [updT, if_true]
    rw [ent_append_right]; exact hj
  have hrc : (leaderAppend σ i es).maxT + (leaderAppend σ i es).maxI ≤
      σ.maxT + σ.maxI + es.length := by
    simp only [leaderAppend, PState.log]; omega
  ihave ⟨Ht, Hd, Hsv, Hlg, Hc⟩ := (srvG_eq γ i (σ.srv i)).1 $$ Hi
  unfold logCouple
  icases Hlc with ⟨Hlc, #Hv⟩
  imod ghostVar_update_halves ((σ.srv i).log ++ es) (γ.slog i) _ _ $$ Hlg Hlc with ⟨Hlg, Hlc⟩
  imod srvOwn_update γ i (σ.srv i) (σ.srv i) { σ.srv i with log := (σ.srv i).log ++ es }
    $$ [Ho Hsv] with ⟨Ho, Hsv⟩
  · iframe
  ihave Hi := (srvG_eq γ i { σ.srv i with log := (σ.srv i).log ++ es }).2 $$ [Ht Hd Hsv Hlg Hc]
  · iframe
  ihave Hs := Hcl $$ %{ σ.srv i with log := (σ.srv i).log ++ es } Hi
  ihave ⟨%O, %hO, HO, HC, Hclose⟩ := HistG_cmd γ σ (leaderAppend σ i es) hP hGr rfl rfl rfl rfl
    rfl rfl rfl ((List.range es.length).map (fun k => (σ.term i, (σ.log i).length + 1 + k))) oLl
    $$ Hh
  ihave ⟨%O', HC, HO', %hab⟩ := absorb γ σ.C (es.filter (fun e => decide (e.kind = kCommand))) O
    $$ [HC HO Htoks]
  · iframe
  obtain ⟨h1, h2, h3, h4⟩ := hab
  imod Hclose $$ %O' [] HO' HC with Hh
  · ipureintro; exact OpsOK_append σ i es hP hpreA O O' hO h1 h2 h3 h4
  ihave ⟨Hh, #Hents⟩ := H_llog_get_list γ (leaderAppend σ i es) (σ.srv i).term es
    (fun k => (σ.srv i).log.length + 1 + k) hnew $$ Hh
  ihave Hr := (receipt_add (GF := GF) (σ.maxT + σ.maxI) es.length).2 $$ [Hr Hrs]
  · iframe
  imodintro
  isplitl [Hh Hs Hr Hcc]
  · iapply InvInner_close γ (leaderAppend σ i es)
      (upd σ.srv i { σ.srv i with log := (σ.srv i).log ++ es }) (σ.maxT + σ.maxI + es.length) rfl
      hrc (GInv_step hg hP' hGr (leaderAppend_kinds σ i es hP hpreA hg.2.2.2.2.1))
    iframe
    iapply CcfgG_congr γ σ (leaderAppend σ i es) rfl rfl rfl $$ Hcc
  isplitl [Ho]; · iexact Ho
  isplitl [Hlc]; · iframe; iexact Hv
  iexact Hents

theorem cmd_not_committed (E : CoPset) (hE : ↑gprotN ⊆ E) (d : List w8) (n k : Nat) (e : Entry) :
    Inv (GF := GF) γ ∗ opTok γ d n ∗ CIdx γ k e ⊢ |={E}=>
      opTok γ d n ∗ ⌜¬ (e.kind = kCommand ∧ e.data = d)⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Ht, #Hc⟩
  ihave ⟨Hh, %hC⟩ := H_C_lookup γ σ k e $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hc
  by_cases hcd : e.kind = kCommand ∧ e.data = d
  · have hl := C_llog σ k e hg.1 hC
    ihave ⟨%O, %hO, HO, Hcl⟩ := H_ops γ σ $$ Hh
    have hne := hO.1 _ _ _ hl hcd.1
    rw [hcd.2] at hne
    ihave ⟨Hf, %L, #HL, %hLn⟩ := (opTok_eq γ d n).1 $$ Ht
    ihave ⟨HO, Hf, %hfr⟩ := ops_excl γ O d n $$ [HO Hf]
    · iframe
    exact absurd hfr hne
  · isplitl [Hh Hs Hr]
    · iframe; ipureintro; exact hg
    iframe; ipureintro; exact hcd

theorem cmd_committed_ops (E : CoPset) (hE : ↑gprotN ⊆ E) (M : GMap (List w8) Nat) (k : Nat)
    (e : Entry) :
    Inv (GF := GF) γ ∗ opsAuth γ M ∗ CIdx γ k e ⊢ |={E}=>
      opsAuth γ M ∗ ⌜e.kind = kCommand → ∃ n, M.lookup e.data = some n ∧ n < k⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, Ha, #Hc⟩
  ihave ⟨Hh, %hC⟩ := H_C_lookup γ σ k e $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hc
  ihave ⟨%O, %hO, HO, Hcl⟩ := H_ops γ σ $$ Hh
  by_cases hk : e.kind = kCommand
  · have hl := C_llog σ k e hg.1 hC
    have hne := hO.1 _ _ _ hl hk
    obtain ⟨n, hn⟩ : ∃ n, O.lookup e.data = some n := by
      cases h : O.lookup e.data with
      | none => exact absurd h hne
      | some n => exact ⟨n, rfl⟩
    have hlt : n < k := by
      rcases hO.2.2 e.data n k hn ⟨e.term, e, hl, hk, rfl⟩ with h | ⟨e', h1, h2⟩
      · exact h
      · rw [hC] at h1; cases h1; exact absurd ⟨hk, rfl⟩ h2
    ihave ⟨Hf, Hcl2⟩ := ops_get γ O e.data n hn $$ HO
    unfold opsAuth
    ihave %hM := ghost_map_lookup (γ := γ.ops) $$ Ha Hf
    ihave HO := Hcl2 $$ Hf
    ihave Hh := Hcl $$ HO
    isplitl [Hh Hs Hr]
    · iframe; ipureintro; exact hg
    iframe; ipureintro; intro _; exact ⟨n, hM, hlt⟩
  · ihave Hh := Hcl $$ HO
    isplitl [Hh Hs Hr]
    · iframe; ipureintro; exact hg
    iframe; ipureintro; intro h; exact absurd h hk

theorem cmd_unique (E : CoPset) (hE : ↑gprotN ⊆ E) (k1 k2 : Nat) (e1 e2 : Entry) :
    Inv (GF := GF) γ ∗ CIdx γ k1 e1 ∗ CIdx γ k2 e2 ⊢ |={E}=>
      ⌜e1.kind = kCommand → e2.kind = kCommand → e1.data = e2.data → k1 = k2⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, #H1, #H2⟩
  ihave ⟨Hh, %hC1⟩ := H_C_lookup γ σ k1 e1 $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact H1
  ihave ⟨Hh, %hC2⟩ := H_C_lookup γ σ k2 e2 $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact H2
  ihave ⟨%O, %hO, HO, Hcl⟩ := H_ops γ σ $$ Hh
  ihave Hh := Hcl $$ HO
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  ipureintro
  intro hk1 hk2 hd
  exact hO.2.1 _ _ _ _ _ _ (C_llog σ k1 e1 hg.1 hC1) (C_llog σ k2 e2 hg.1 hC2) hk1 hk2 hd

/-- A snapshot of the committed log covering given index facts and earlier snapshots. -/
theorem CLb_cover (E : CoPset) (hE : ↑gprotN ⊆ E) (ks : List (Nat × Entry)) (Ls : List RLog) :
    Inv (GF := GF) γ ∗ ([∗list] ke ∈ ks, CIdx γ ke.1 ke.2) ∗ ([∗list] L ∈ Ls, CLb γ L) ⊢ |={E}=>
      ∃ L, CLb γ L ∗ ⌜(∀ ke ∈ ks, ent L ke.1 = some ke.2) ∧ ∀ L' ∈ Ls, L' <+: L⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, #Hks, #HLs⟩
  ihave ⟨Hh, %hks⟩ := H_CIdx_list γ σ ks $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hks
  ihave ⟨Hh, %hLs⟩ := H_CLb_list γ σ Ls $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact HLs
  ihave ⟨Hh, #HC⟩ := H_C_lb γ σ $$ Hh
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  iexists σ.C
  isplitr; · iexact HC
  ipureintro; exact ⟨hks, hLs⟩

end ops

end gprot
end github_com.hashicorp.raft

end Perennial
