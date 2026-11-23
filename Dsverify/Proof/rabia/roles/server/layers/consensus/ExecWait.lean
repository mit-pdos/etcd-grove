/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/consensus/ExecWait.lean`, run `rabia-r1wake-1`.)

The proof of the executor's `wait` (`wp_wait`'s statement): the notifications of a slot come in
round order (`slotQPx`), so in sync mode the received round is the executor's; after a decision is
received by the handler (`hasRecvDec`, the flag `rdW`) the round notifications are skipped until the
decision's; the decision path records `mydec` (`Ghost.decideSlot`) and runs `epilogue`.
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.consensus.ExecLaws

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.consensus

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.ledger rabia rabia.internal.queue

set_option linter.unusedSectionVars false

/-- Discharge the bounds check of an `IndexRef`. -/
local macro "slice_index_if" : tactic =>
  `(tactic| (rw [ite_eq_left_of_eq_true _ _ (eq_true (by constructor <;> word))]))

set_option hygiene false in
/-- `wait`'s `return true`: the round received in sync mode. -/
local macro "wait_ret_true" : tactic =>
  `(tactic| (wp_for_post
             iapply HΦ
             simp only [↓reduceIte]
             icases Hmp with ⟨%mpv, Hmpf, #Hmpo⟩
             ihave Hpriv := Hpcl $$ %x.pv.phase %x.pv.round %mpv [Hph Hrnd Hmpf HRr]
             · (try rw [hp0]); (try rw [hr1]); (try rw [hr2])
               iframe Hph Hrnd Hmpf HRr; iexact Hmpo
             have hpveq : ({ x.pv with phase := x.pv.phase, round := x.pv.round } : PrivSt) = x.pv := rfl
             rw [hpveq]
             iexists { x with recv := recv ++ [v], ql := ql' }
             iframe
             isplitr
             · isplitr
               · ipureintro; exact ht
               isplitr
               · ipureintro; exact he
               isplitr
               · ipureintro; exact hmy
               isplitr
               · iexact Hql'
               ipureintro
               refine ⟨by simp [hrl, hql'.1], ?_, trivial⟩
               show ql'.filterMap id = List.range (ql'.filterMap id).length
               rw [hfm', List.length_range]
             ipureintro
             refine ⟨rfl, rfl, rfl, rfl, ?_, hnone'⟩
             show (ql'.filterMap id).length = _
             rw [hfm', List.length_range, hρe]))

set_option hygiene false in
/-- `c.Ledger[slot]` (slot `σ.t`): the bounds check and the load. -/
local macro "ledger_idx" : tactic =>
  `(tactic| (slice_index_if
             wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 (σ.t : Int))))) _ _ e.loc
               (by word) $$ [Hsl]
             · iframe Hsl; ipureintro
               rw [show (sint.Z (W64 (uint.Z (W32 (σ.t : Int))))).toNat = σ.t by word]
               simp [he]
             iintro -))

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable {cf : RCfg}

instance ex_isRabia_persistent (γ : RabiaNames) : Persistent (isRabia (GF := GF) γ) := by
  unfold isRabia; infer_instance

instance ex_histFacts_persistent (γ : Names) (k : Nat) (H : List (ObjV × DVal)) :
    Persistent (histFacts (GF := GF) γ k H) := by
  unfold histFacts; infer_instance

theorem facts1_intro (γ : RabiaNames) (k1 : FKey) (v1 : FVal) :
    ⊢ fact (GF := GF) γ k1 v1 -∗ [∗list] kv ∈ [(k1, v1)], fact γ kv.1 kv.2 := by
  iintro H1
  isplitl [H1]
  · iexact H1
  · iempintro

theorem facts3_intro (γ : RabiaNames) (k1 k2 k3 : FKey) (v1 v2 v3 : FVal) :
    ⊢ fact (GF := GF) γ k1 v1 -∗ fact γ k2 v2 -∗ fact γ k3 v3 -∗
      [∗list] kv ∈ [(k1, v1), (k2, v2), (k3, v3)], fact γ kv.1 kv.2 := by
  iintro H1 H2 H3
  isplitl [H1]
  · iexact H1
  isplitl [H2]
  · iexact H2
  isplitl [H3]
  · iexact H3
  · iempintro

theorem facts2_intro (γ : RabiaNames) (k1 k2 : FKey) (v1 v2 : FVal) :
    ⊢ fact (GF := GF) γ k1 v1 -∗ fact γ k2 v2 -∗
      [∗list] kv ∈ [(k1, v1), (k2, v2)], fact γ kv.1 kv.2 := by
  iintro H1 H2
  isplitl [H1]
  · iexact H1
  isplitl [H2]
  · iexact H2
  · iempintro

theorem keys_rabia_disj (k : Nat) : (↑(srvKeysN k) : CoPset) ## ↑rabiaN := by
  have hd : (↑(ndot rabiaR "keys") : CoPset) ## ↑(ndot rabiaR "inv") :=
    ndot_ne_disjoint rabiaR (by decide)
  unfold srvKeysN rabiaN
  exact ndot_preserve_disjoint_l _ hd

theorem keys_client_disj (k : Nat) :
    (↑(srvKeysN k) : CoPset) ## cliE := by
  have h : cliE ## ↑(srvKeysN k) := cliE_disj_of_sub (by
    unfold srvKeysN rabiaE
    exact fun x hx => nclose_subseteq _ _ x (nclose_subseteq _ _ x hx))
  exact fun x hx => h x ⟨hx.2, hx.1⟩

theorem client_rabia_disj : cliE ## ↑rabiaN := cliE_rabiaN

theorem sub_diff_of_disj {A B : CoPset} (h : A ## B) : A ⊆ ⊤ \ B := by
  intro x hx
  exact LawfulSet.mem_diff.mpr ⟨CoPset.mem_full, fun h' => h x ⟨hx, h'⟩⟩

theorem disj_symm' {A B : CoPset} (h : A ## B) : B ## A := fun x hx => h x ⟨hx.2, hx.1⟩

theorem keysEx_notObj {t : Nat} {cur Ke : List FKey} (h : KeysEx t cur Ke) :
    ∀ key ∈ Ke, key.isObj = false := by
  intro key hk
  obtain ⟨s, hs, -⟩ := h.1 key hk
  cases key <;> simp_all [FKey.slotOf, model.FKey.isObj]

/-- Recording my decision `d` of slot `t` (from the slot's recorded decision): `mydec k t`, among
my keys. -/
theorem dec_record (γ : Names) (k : Nat) (hk : k < cf.n) (γl : SrvNames) (t : Nat)
    (H : List (ObjV × DVal)) (hH : H.length = t) (cur Ke : List FKey) (hKe : KeysEx t cur Ke)
    (d : DVal) :
    isRabia (GF := GF) γ.rab ∗ cfgIs γ.rab cf ∗ isSrvKeys γ k γl ∗ £ 1 ∗ keysPart γl false Ke ∗
      histFacts γ k H ∗ fact γ.rab (.dec t) (.dval d) ⊢
    |={⊤}=> ∃ Ke' cur', keysPart γl false Ke' ∗ ⌜KeysEx t cur' Ke' ∧ FKey.mydec k t ∈ Ke'⌝ ∗
      fact γ.rab (.mydec k t) (.dval d) := by
  iintro ⟨#Hrab, #Hcfg, #Hks, Hlc, HKe, #Hh, #Hdec⟩
  ihave #Hcf : fact γ.rab FKey.cfg (FVal.cfgv cf) $$ [Hcfg]
  · unfold cfgIs; icases Hcfg with ⟨#H, -⟩; iexact H
  have hobj := keysEx_notObj hKe
  imod srvKeys_acc γ k γl false ⊤ (fun _ _ => CoPset.mem_full) Ke $$ [HKe] with
    ⟨%K, %Ko, HK, ⟨%hperm, %hKo⟩, Hcl⟩
  · iframe HKe; iexact Hks
  have hmyobj : (FKey.mydec k t).isObj = false := rfl
  by_cases hin : FKey.mydec k t ∈ Ke
  · have hinK : FKey.mydec k t ∈ K := hperm.symm.subset (List.mem_append_left _ hin)
    imod fact_of_mine γ.rab (⊤ \ ↑(srvKeysN k)) (sub_diff_of_disj (disj_symm' (keys_rabia_disj k)))
      (.srv k) K (.mydec k t) rfl hinK $$ [HK] with ⟨HK, %v, #Hmy⟩
    · iframe HK; iexact Hrab
    imod Hcl $$ %K %Ke [HK] with HKe
    · iframe HK; ipureintro; exact ⟨hperm, hobj⟩
    ihave #HS := facts3_intro γ.rab (FKey.mydec k t) (FKey.dec t) FKey.cfg v (FVal.dval d)
      (FVal.cfgv cf) $$ Hmy Hdec Hcf
    imod facts_valid γ.rab ⊤ (fun _ _ => CoPset.mem_full)
      [(FKey.mydec k t, v), (FKey.dec t, FVal.dval d), (FKey.cfg, FVal.cfgv cf)] $$ [] with %hv
    · isplitr
      · iexact Hrab
      · iexact HS
    obtain ⟨M, hM0, hS⟩ := hv
    have h1 := hS (FKey.mydec k t, v) (by simp)
    have h2 := hS (FKey.dec t, FVal.dval d) (by simp)
    have hc : CfgOf M cf := hS (FKey.cfg, FVal.cfgv cf) (by simp)
    obtain ⟨hok, hM⟩ := hM0.at hc
    have hj := hM.1 _ _ h1
    cases v with
    | dval d' =>
      have he : d' = d := by
        simp only [Justified] at hj
        have hd' : Decided cf M t d' := by
          rcases hj.2 with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        exact agree M hok hM t d' d hd' (Or.inr (Or.inl h2))
      subst he
      imodintro
      iexists Ke, cur
      iframe HKe Hmy
      ipureintro; exact ⟨hKe, hin⟩
    | _ => simp [Justified] at hj
  · have hnK : FKey.mydec k t ∉ K := by
      intro h
      rcases List.mem_append.mp (hperm.subset h) with h | h
      · exact hin h
      · have := hKo _ h; simp [model.FKey.isObj] at this
    have hE : (↑rabiaN : CoPset) ⊆ ⊤ \ ↑(srvKeysN k) :=
      sub_diff_of_disj (disj_symm' (keys_rabia_disj k))
    have hcE : cliE ⊆ ⊤ \ ↑(srvKeysN k) :=
      sub_diff_of_disj (disj_symm' (keys_client_disj k))
    cases t with
    | zero =>
      ihave #HS := facts1_intro γ.rab (FKey.dec 0) (FVal.dval d) $$ Hdec
      imod decideSlot γ.rab (⊤ \ ↑(srvKeysN k)) hE client_rabia_disj hcE cf k 0 d K
        [(FKey.dec 0, FVal.dval d)] hk hnK (Or.inl rfl)
        (fun M _ _ hS => Or.inr (hS (FKey.dec 0, FVal.dval d) (by simp))) $$ [Hlc HK] with ⟨HK, #Hmy, -⟩
      · iframe Hlc HK Hcfg
        isplitr
        · iexact Hrab
        · iexact HS
      imod Hcl $$ %(FKey.mydec k 0 :: K) %(FKey.mydec k 0 :: Ke) [HK] with HKe
      · iframe HK; ipureintro
        refine ⟨List.Perm.cons _ hperm, ?_⟩
        intro key hkey
        rcases List.mem_cons.mp hkey with h | h
        · subst h; rfl
        · exact hobj key h
      imodintro
      iexists FKey.mydec k 0 :: Ke, FKey.mydec k 0 :: cur
      iframe HKe Hmy
      ipureintro
      refine ⟨⟨?_, ?_⟩, List.mem_cons_self⟩
      · intro key hkey
        rcases List.mem_cons.mp hkey with h | h
        · subst h; exact ⟨0, rfl, Or.inr ⟨rfl, List.mem_cons_self⟩⟩
        · obtain ⟨s, hs, h'⟩ := hKe.1 key h
          exact ⟨s, hs, h'.imp id (fun ⟨a, b⟩ => ⟨a, List.mem_cons_of_mem _ b⟩)⟩
      · intro key hkey
        rcases List.mem_cons.mp hkey with h | h
        · subst h; rfl
        · exact hKe.2 key h
    | succ t =>
      obtain ⟨xp, hxp⟩ : ∃ xp, H[t]? = some xp := by
        cases h : H[t]? with
        | none => simp [List.getElem?_eq_none_iff] at h; omega
        | some xp => exact ⟨xp, rfl⟩
      unfold histFacts
      ihave #Hprev := (BigSepL.bigSepL_lookup (Φ := fun i (x : ObjV × DVal) =>
        iprop(fact (GF := GF) γ.rab (.prop k i) (.obj (objId x.1)) ∗
          fact γ.rab (.mydec k i) (.dval x.2))) hxp) $$ Hh
      icases Hprev with ⟨-, #Hprev⟩
      ihave #HS := facts2_intro γ.rab (FKey.dec (t + 1)) (FKey.mydec k t) (FVal.dval d)
        (FVal.dval xp.2) $$ Hdec Hprev
      imod decideSlot γ.rab (⊤ \ ↑(srvKeysN k)) hE client_rabia_disj hcE cf k (t + 1) d K
        [(FKey.dec (t + 1), FVal.dval d), (FKey.mydec k t, FVal.dval xp.2)] hk hnK
        (Or.inr ⟨xp.2, by simp⟩)
        (fun M _ _ hS => Or.inr (hS (FKey.dec (t + 1), FVal.dval d) (by simp))) $$ [Hlc HK] with ⟨HK, #Hmy, -⟩
      · iframe Hlc HK Hcfg
        isplitr
        · iexact Hrab
        · iexact HS
      imod Hcl $$ %(FKey.mydec k (t + 1) :: K) %(FKey.mydec k (t + 1) :: Ke) [HK] with HKe
      · iframe HK; ipureintro
        refine ⟨List.Perm.cons _ hperm, ?_⟩
        intro key hkey
        rcases List.mem_cons.mp hkey with h | h
        · subst h; rfl
        · exact hobj key h
      imodintro
      iexists FKey.mydec k (t + 1) :: Ke, FKey.mydec k (t + 1) :: cur
      iframe HKe Hmy
      ipureintro
      refine ⟨⟨?_, ?_⟩, List.mem_cons_self⟩
      · intro key hkey
        rcases List.mem_cons.mp hkey with h | h
        · subst h; exact ⟨t + 1, rfl, Or.inr ⟨rfl, List.mem_cons_self⟩⟩
        · obtain ⟨s, hs, h'⟩ := hKe.1 key h
          exact ⟨s, hs, h'.imp id (fun ⟨a, b⟩ => ⟨a, List.mem_cons_of_mem _ b⟩)⟩
      · intro key hkey
        rcases List.mem_cons.mp hkey with h | h
        · subst h; rfl
        · exact hKe.2 key h

end ghost

/-! ## Pure lemmas of `wait` -/

/-- A round notification at the executor's round has the executor's phase and the round's type. -/
theorem wait_ok (m : MsgV) (pv : PrivSt) (hr : pv.round = 1 ∨ pv.round = 2)
    (hround : roundOf m = some (exRound pv))
    (hwf : (m.ty = tyProposal → m.phase = 0) ∧ (m.ty = tyState → 1 ≤ m.phase.toNat)) :
    m.phase = pv.phase ∧ (pv.round = 1 → pv.phase = 0 → m.ty = tyProposal) ∧
    (pv.round = 1 → pv.phase ≠ 0 → m.ty = tyState) ∧ (pv.round = 2 → m.ty = tyVote) := by
  have hrn : pv.round.toNat = 1 ∨ pv.round.toNat = 2 := by
    rcases hr with h | h <;> rw [h] <;> decide
  have hph : ∀ a b : w32, a = b ↔ a.toNat = b.toNat := fun a b =>
    ⟨fun h => h ▸ rfl, fun h => BitVec.eq_of_toNat_eq h⟩
  have hr1 : pv.round = 1 ↔ pv.round.toNat = 1 := hph _ 1
  have hr2 : pv.round = 2 ↔ pv.round.toNat = 2 := hph _ 2
  have hp0 : pv.phase = 0 ↔ pv.phase.toNat = 0 := hph _ 0
  have hmp0 : m.phase = 0 ↔ m.phase.toNat = 0 := hph _ 0
  simp only [ne_eq, hph m.phase pv.phase, hr1, hr2, hp0]
  unfold roundOf exRound at hround
  by_cases hp : m.ty = tyProposal
  · simp only [hp, ↓reduceIte, Option.some.injEq] at hround
    have h0 := hmp0.mp (hwf.1 hp)
    refine ⟨by omega, fun _ _ => hp, fun _ h => by omega, fun h => by omega⟩
  · by_cases hs : m.ty = tyState
    · simp [hs, tyState, tyProposal] at hround
      have h1 := hwf.2 hs
      refine ⟨by omega, fun _ h => by omega, fun _ _ => hs, fun h => by omega⟩
    · by_cases hv : m.ty = tyVote
      · simp [hp, hs, hv, tyState, tyProposal, tyVote] at hround
        refine ⟨by omega, fun h => by omega, fun h => by omega, fun _ => hv⟩
      · simp [hp, hs, hv] at hround

/-- The consumed notifications grow by the received one. -/
theorem ql_next (ql ql' : List (Option Nat)) (eo : Option Nat) (n : Nat) (hn : ql.length = n)
    (hpre : ql <+: ql' ∨ ql' <+: ql) (hl : ql'.length = n + 1) (he : ql'[n]? = some eo) :
    ql' = ql ++ [eo] ∧ ql'.take n = ql := by
  have hp : ql <+: ql' := by
    rcases hpre with h | h
    · exact h
    · have := h.length_le; omega
  obtain ⟨t, rfl⟩ := hp
  have ht : t.length = 1 := by simp at hl; omega
  match t, ht with
  | [a], _ =>
    simp only [List.getElem?_append_right (by omega : ql.length ≤ n), hn, Nat.sub_self] at he
    simp at he
    subst he
    simp [hn]

theorem filterMap_snoc_range (ql : List (Option Nat)) (ρ : Nat)
    (h : ql.filterMap id = List.range ρ) :
    (ql ++ [some ρ]).filterMap id = List.range (ρ + 1) := by
  simp [List.filterMap_append, h, List.range_succ]

theorem SlotOk.with_rl {s : Nat} {st : SlotSt} {ents : List Ent} {ql : List (Option Nat)}
    {p : Option (Option Nat)} {exd : Bool} {dl rl : List Unit}
    (h : SlotOk cf s st ents ql p exd dl rl) (hd : st.hasRecvDec = true) (rl' : List Unit) :
    SlotOk cf s st ents ql p exd dl rl' := by
  unfold SlotOk at *
  obtain ⟨a, b, c, d, e, f, g, i, _⟩ := h
  exact ⟨a, b, c, d, e, f, g, i, fun _ => hd⟩

theorem SlotOk.rd_of_rl {s : Nat} {st : SlotSt} {ents : List Ent} {ql : List (Option Nat)}
    {p : Option (Option Nat)} {exd : Bool} {dl rl : List Unit}
    (h : SlotOk cf s st ents ql p exd dl rl) (hd : rl ≠ []) : st.hasRecvDec = true := by
  unfold SlotOk at h; exact h.2.2.2.2.2.2.2.2 hd

theorem SlotOk.done_eq {s : Nat} {st : SlotSt} {ents : List Ent} {ql : List (Option Nat)}
    {p : Option (Option Nat)} {exd : Bool} {dl rl : List Unit}
    (h : SlotOk cf s st ents ql p exd dl rl) : st.isDone = exd := by
  unfold SlotOk at h; exact h.2.2.2.2.2.2.1

theorem unit_prefix' (dl : List Unit) : [()] <+: dl ++ [()] := by
  cases dl with
  | nil => exact List.prefix_refl _
  | cons a t => exact ⟨t ++ [()], by simp⟩

section steps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable {cf : RCfg}

/-- `GetHasRecvDec`'s step in `wait`: a `true` mints the flag `rdW`; a `false` excludes it. -/
theorem step_hasRecvDec (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (t : Nat)
    (P : Prop) (E : CoPset) (st : SlotSt) :
    slotGhost (GF := GF) γ cf k γl γc t st -∗ (⌜P⌝ ∨ rdW γl γc t) ={E}=∗
      slotGhost γ cf k γl γc t st ∗ (if st.hasRecvDec then rdW γl γc t else iprop(⌜P⌝)) := by
  iintro Hg HR
  unfold slotGhost
  icases Hg with ⟨%ents, %ql, %pend, %exd, %dl, %rl, Hent, Hq, Hp, Hx, Hdw, Hrd, Hres, %hok⟩
  cases hrd : st.hasRecvDec with
  | true =>
    imod monoListAuthOwn_update_app (γ := rdName γl γc t) [()] $$ Hrd with ⟨Hrd, #Hlb⟩
    imodintro
    simp only [↓reduceIte]
    isplitr [HR]
    · iexists ents, ql, pend, exd, dl, rl ++ [()]
      iframe
      ipureintro; exact hok.with_rl hrd _
    · unfold rdW
      iapply monoListLbOwn_le [()] (unit_prefix' rl) $$ Hlb
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases HR with (%hP | #Hw)
    · imodintro
      isplitl [Hent Hq Hp Hx Hdw Hrd Hres]
      · iexists ents, ql, pend, exd, dl, rl
        iframe
        ipureintro; exact hok
      · ipureintro; exact hP
    · unfold rdW
      ihave %hpre := mono_list_auth_lb_valid (rdName γl γc t) 1 rl [()] $$ Hrd Hw
      have hne : rl ≠ [] := by
        intro h; subst h; have := hpre.2.length_le; simp at this
      have := hok.rd_of_rl hne
      rw [hrd] at this; cases this

/-- `GetIsDone`'s step in `wait`: the executor's half of `exName` says not done. -/
theorem step_isDone (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (t : Nat)
    (E : CoPset) (st : SlotSt) :
    slotGhost (GF := GF) γ cf k γl γc t st -∗ ghostVar (exName γl γc t) (1 : Qp).half false ={E}=∗
      slotGhost γ cf k γl γc t st ∗ (ghostVar (exName γl γc t) (1 : Qp).half false ∗ ⌜st.isDone = false⌝) := by
  iintro Hg Hx'
  unfold slotGhost
  icases Hg with ⟨%ents, %ql, %pend, %exd, %dl, %rl, Hent, Hq, Hp, Hx, Hdw, Hrd, Hres, %hok⟩
  ihave %hag := ghostVar_agree (A := Bool) (exName γl γc t) exd (1 : Qp).half false (1 : Qp).half
    $$ Hx Hx'
  imodintro
  isplitl [Hent Hq Hp Hx Hdw Hrd Hres]
  · iexists ents, ql, pend, exd, dl, rl
    iframe
    ipureintro; exact hok
  isplitl [Hx']
  · iexact Hx'
  · ipureintro
    rw [hok.done_eq]
    exact hag

theorem qLb_valid (γc : ConsNames) (s : Nat) (l1 l2 : List (Option Nat)) :
    ⊢ qLb (GF := GF) γc s l1 -∗ qLb γc s l2 -∗ ⌜l1 <+: l2 ∨ l2 <+: l1⌝ := by
  unfold qLb; iintro H1 H2; iapply mono_list_lb_valid $$ H1 H2

end steps

section ro
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable {cf : RCfg}

theorem exRun_ro (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc)
    (σ : ExSt) (x : ExSlot) :
    exRun (GF := GF) γ cf k γl γc ch c σ x ⊢ consRO γ cf k γl γc ch c ∗ exRun γ cf k γl γc ch c σ x := by
  iintro H
  unfold exRun exCommon
  icases H with ⟨⟨#Hro, H1⟩, H2⟩
  iframe Hro
  iframe

end ro

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable {cf : RCfg}
variable [package_sem : rabia.roles.server.layers.consensus.Assumptions] [π : NetProtoGS]

theorem ex_GetIsDone_t (hGID : Slot.GetIsDone.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    (R : IProp GF) (Q : SlotSt → IProp GF) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗
        isSlot e.loc e.γ e.q -∗ slotsInv γ cf k γl γc -∗ R -∗
        (∀ st, slotGhost γ cf k γl γc s st -∗ R ={⊤ \ ↑(slotN k s)}=∗
          slotGhost γ cf k γl γc s st ∗ Q st) -∗
        (∀ st, Q st -∗ Φ #st.isDone) -∗
      WP (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"GetIsDone")) (Val #())) {{ Φ }} := by
  iintro %Φ #Hp #Hs #Hi HR Hstep HΦ
  iapply wp_GetIsDone_inv hGID γ k γl γc s e he R Q
  iframe
  repeat (first | iexact Hp | iexact Hs | iexact Hi | isplitr)

theorem ex_GetHasRecvDec_t (hspec : Slot.GetHasRecvDec.spec (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e)
    (R : IProp GF) (Q : SlotSt → IProp GF) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger -∗
        isSlot e.loc e.γ e.q -∗ slotsInv γ cf k γl γc -∗ R -∗
        (∀ st, slotGhost γ cf k γl γc s st -∗ R ={⊤ \ ↑(slotN k s)}=∗
          slotGhost γ cf k γl γc s (st) ∗ Q st) -∗
        (∀ st, Q st -∗ Φ #st.hasRecvDec) -∗
      WP (App (Val (e.loc @!! go.GoType.PointerType Slot.ty @!! go!"GetHasRecvDec")) (Val #())) {{ Φ }} := by
  iintro %Φ #Hp #Hs #Hi HR Hstep HΦ
  iapply wp_GetHasRecvDec_inv hspec γ k γl γc s e he R Q
  iframe
  repeat (first | iexact Hp | iexact Hs | iexact Hi | isplitr)

set_option maxHeartbeats 3200000 in
theorem wp_wait_proof (D : ExDeps (GF := GF)) (γ : Names) (k : Nat) (γl : SrvNames)
    (γc : ConsNames) (ch : SrvChans) (c : Loc)
    (hk : k < cf.n)
    (hEpi : ∀ (σ : ExSt) (x : ExSlot) (d : DVal) (o : ObjV) (v : ConsensusObj),
      FKey.mydec k σ.t ∈ σ.Ke →
      {{ exPre (GF := GF) γ cf ∗ exRun γ cf k γl γc ch c σ x ∗ decidedW γ cf k σ.t d o v ∗
        fact γ.rab (.prop k σ.t) (.obj (objId x.o)) }}
        (App (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"epilogue"))
          (Val #(W32 σ.t))) (Val #v))
      {{ RET #(); ∃ σ', exIdle γ cf k γl γc ch c σ' ∗ ⌜σ'.t = σ.t + 1⌝ }})
    (σ : ExSt) (x : ExSlot)
    (hr : x.pv.round = 1 ∨ x.pv.round = 2) (hρ : x.ρs = exRound x.pv + 1)
    (hn : (x.ql.filterMap id).length = exRound x.pv) (hnone : none ∉ x.ql) :
    {{ exPre (GF := GF) γ cf ∗ exRun γ cf k γl γc ch c σ x ∗
        fact γ.rab (.prop k σ.t) (.obj (objId x.o)) }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"wait")) (Val #(W32 σ.t)))
    {{ (b : Bool), RET #b;
        if b then ∃ x', exRun γ cf k γl γc ch c σ x' ∗
          ⌜x'.pv = x.pv ∧ x'.ρs = x.ρs ∧ x'.cur = x.cur ∧ x'.o = x.o ∧
            (x'.ql.filterMap id).length = exRound x.pv + 1 ∧ none ∉ x'.ql⌝
        else ∃ σ', exIdle γ cf k γl γc ch c σ' ∗ ⌜σ'.t = σ.t + 1⌝ }} := by
  wp_start as ⟨⟨#Hpkg, #Hconf, #Hsh, #Hcfg⟩, Hrun, #Hprop⟩
  ihave ⟨#Hro, Hrun⟩ := exRun_ro $$ Hrun
  unfold exRun
  icases Hrun with ⟨Hcom, Hcoin, Hseq, %ht, Hsr⟩
  unfold exSlotRes
  icases Hsr with ⟨%e, %he, Hpriv, %hmy, Hpend, Hcons, #Hql, %hq, Hex⟩
  have hs : (W32 (σ.t : Int)).toNat < lenLedger := by unfold lenLedger at *; word
  wp_auto
  wp_apply (wp_PanicTermNotMatched γ k γl γc ch c (W32 (σ.t : Int)) hs) $$ [$Hconf $Hro]
  ihave ⟨%ps, #HConf⟩ := confRO_val $$ Hconf
  ihave Hro2 := Hro
  unfold consRO
  icases Hro2 with ⟨%ledger, %qlk, %wg, #Hsid, #Hwg, #Hdone, #Hn2h, #Hh2n, #Hn2e, #He2n, #Hqlk,
    #Hledger, #Hqm, #Hsm, #Hchans, #HlRO, #Hsinv, #Hschans, #Hkeys⟩
  ihave Hc2 := HConf
  iStructNamed Hc2
  unfold ledgerRO
  icases HlRO with ⟨#Hsl, %Hlen, #Hslots⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  rw [List.length_map, Hlen] at Hl
  ihave #Hse := (BigSepL.bigSepL_lookup
    (Φ := fun _ e => iprop(isSlot (GF := GF) e.loc e.γ e.q)) he) $$ Hslots
  ihave ⟨#Hq, #Ht⟩ := isSlot_queue e.loc e.γ e.q $$ Hse
  ihave #Hsc := (BigSepL.bigSepL_lookup
    (Φ := fun s e => iprop(slotChan (GF := GF) γ cf γc s e)) he) $$ Hschans
  unfold lenLedger at ht Hl hs
  have hmod : W32 (σ.t : Int) % W32 10000 = W32 (σ.t : Int) := by word
  wp_auto
  rw [hmod]
  ihave #Hpl : isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger $$ []
  · iPkgInit
  ihave ⟨Hph, Hrnd, Hmp, %Rr, HRr, Hpcl⟩ := (slotPriv_fields e.loc x.pv).1 $$ Hpriv
  ihave HI : (∃ (recv : List Msg) (ql : List (Option Nat)),
      "Hcons" ∷ spscConsumer (γc.queue σ.t) recv ∗ "#Hql" ∷ qLb γc σ.t ql ∗
      "%Hq" ∷ ⌜recv.length = ql.length ∧ ql.filterMap id = List.range (ql.filterMap id).length ∧
        none ∉ ql⌝ ∗
      "Hmode" ∷ (⌜recv = x.recv ∧ ql = x.ql⌝ ∨ rdW γl γc σ.t)) $$ [Hcons]
  · iexists x.recv, x.ql
    iframe Hcons Hql
    isplitr
    · ipureintro; exact ⟨hq.1, hq.2.1, hnone⟩
    · ileft; ipureintro; exact ⟨rfl, rfl⟩
  wp_for HI
  slice_index_if
  wp_apply (lc := 4) wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 (σ.t : Int))))) _ _ e.loc
    (by word) $$ [Hsl] with Hsl2
  · iframe Hsl; ipureintro
    rw [show (sint.Z (W64 (uint.Z (W32 (σ.t : Int))))).toNat = σ.t by word]
    simp [he]
  unfold srvChans
  icases Hchans with ⟨#Hbdone, -⟩
  unfold slotChan
  ihave #Hqch : isChan e.q (γc.queue σ.t).chanName Msg $$ [Hsc]
  · unfold isSpsc; icases Hsc with ⟨$, -⟩
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `Done`: nothing is sent on it
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch.done, γl.done
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbdone
    iapply bag_recv_au γl.done ch.done _ _ $$ [$Hlc1 $Hlc2] Hbdone
    inext
    iintro %u HP
    unfold doneP
    icases HP with %hf
    exact hf.elim
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- the slot's queue
    simp only [chan.blockingClausePre]
    iexists Msg, inferInstance, inferInstance, inferInstance, inferInstance, e.q, (γc.queue σ.t).chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact Hqch
    iapply spsc_rcv_au (γc.queue σ.t) e.q _ _ recv _ $$ Hsc [$Hlc1 $Hlc2] Hcons
    inext
    iintro %v %ok Hv
    cases ok with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hv with ⟨Hf, -⟩; icases Hf with %hf; exact hf.elim
    | true =>
    simp only [↓reduceIte]
    icases Hv with ⟨HQ, Hcons⟩
    unfold slotQPx slotQP
    icases HQ with ⟨⟨%m, %ql', %eo, #Hm, #Hql', %hql', He⟩, %hwf⟩
    ihave %hmf := msgRep_fields v m $$ Hm
    rcases eo with _ | ρ
    · icases He with ⟨%o, %d, ⟨%hty6, %hobj, %hsv, %hnone⟩, #Hdec, #Hdo⟩
      have hv6 : v.Type' = W32 6 := hmf.1.trans hty6
      have h3 : decide (v.Type' = W32 3) = false := by rw [hv6]; simp
      have h2 : decide (v.Type' = W32 2) = false := by rw [hv6]; simp
      have h1 : decide (v.Type' = W32 1) = false := by rw [hv6]; simp
      have h6 : decide (v.Type' = W32 6) = true := by rw [hv6]; simp
      wp_auto
      repeat (first | (simp only [h1, h2, h3, h6]) | (wp_auto))
      ledger_idx
      wp_pures
      wp_apply_core ex_GetIsDone_t D.getIsDone γ k γl γc σ.t e he
        (ghostVar (exName γl γc σ.t) (1 : Qp).half false)
        (fun st => iprop(ghostVar (exName γl γc σ.t) (1 : Qp).half false ∗ ⌜st.isDone = false⌝))
        $$ Hpl Hse Hsinv Hex
      · iintro %st Hg HR
        iapply step_isDone $$ Hg HR
      iintro %st ⟨Hex, %hnd⟩
      rw [hnd]
      wp_auto
      ihave ⟨%ov, #Hov, #Hovr⟩ := cons_msgRep_obj v m o hobj $$ Hm
      wp_auto
      -- the received decision's slot
      have hrl : recv.length = ql.length := Hq.1
      simp only [Int.toNat_natCast] at hql' hnone
      ihave %hpre := qLb_valid γc σ.t ql ql' $$ Hql Hql'
      obtain ⟨hql'eq, htake⟩ := ql_next ql ql' none recv.length hrl.symm hpre hql'.1 hql'.2
      -- record my decision
      iunfold exCommon at Hcom
      icases Hcom with ⟨#Hro', Hfields, #Hhist, Hmt, %hHlen, #Hpf, HKe, %hKeys, Hexa, Hprod, %hlog,
        Hfresh⟩
      ihave ⟨#Hrab, -⟩ : isRabia γ.rab ∗ True $$ [Hsh]
      · unfold shared; icases Hsh with ⟨#Hr, -⟩; iframe Hr
      imod dec_record γ k hk γl σ.t σ.H hHlen x.cur σ.Ke hKeys d $$ [Hlc3 HKe] with
        ⟨%Ke', %cur', HKe, ⟨%hKe', %hmyin⟩, #Hmy⟩
      · iframe Hlc3 HKe
        repeat (first | iexact Hrab | iexact Hcfg | iexact Hkeys | iexact Hhist | iexact Hdec | isplitr)
      have hfm' : ql'.filterMap id = ql.filterMap id := by rw [hql'eq]; simp
      icases Hmp with ⟨%mpv, Hmpf, #Hmpo⟩
      ihave Hpriv := Hpcl $$ %x.pv.phase %x.pv.round %mpv [Hph Hrnd Hmpf HRr]
      · iframe Hph Hrnd Hmpf HRr; iexact Hmpo
      have hpveq : ({ x.pv with phase := x.pv.phase, round := x.pv.round } : PrivSt) = x.pv := rfl
      rw [hpveq]
      wp_apply (hEpi { σ with Ke := Ke' } { x with recv := recv ++ [v], ql := ql', cur := cur' } d o ov
        hmyin) $$ [Hcoin Hseq Hfields Hmt Hexa Hprod Hfresh HKe Hpriv Hpend Hcons Hex] as
        ⟨%σ'', Hidle, %ht''⟩
      · isplitr
        · isplitr
          · iexact Hpkg
          isplitr
          · iexact Hconf
          isplitr
          · iexact Hsh
          · iexact Hcfg
        isplitl
        · unfold exRun exCommon exSlotRes
          iframe
          repeat (first | (iexact Hro') | (iexact Hhist) | (iexact Hpf) | (iexact Hql') | (ipureintro; first | exact hHlen | exact hKe' | exact hlog | exact ht | exact he | exact hmy) | (iexists e) | (isplitr))
          -- (`exSlotRes` no longer asks `none ∉ x.ql`: `wait` takes it as a premise instead.)
          all_goals (ipureintro; first | (simp [hrl, hql'.1]; done) | (show ql'.filterMap id = _; rw [hfm']; try exact Hq.2.1) | (refine ⟨?_, trivial⟩; show ql'.filterMap id = _; rw [hfm']; try exact Hq.2.1) | trivial)
        · isplitr
          · unfold decidedW
            isplitr
            · iexact Hmy
            isplitr
            · iexact Hdec
            isplitr
            · iexact Hdo
            · iexact Hovr
          · iexact Hprop
      wp_for_post
      iapply HΦ
      simp only [Bool.false_eq_true, ↓reduceIte]
      iexists σ''
      iframe Hidle
      ipureintro; exact ht''
    icases He with ⟨⟨%hrnd, %hrange⟩, #Hrdone⟩
    have hty3 : m.ty = tyProposal ∨ m.ty = tyState ∨ m.ty = tyVote := by
      unfold roundOf at hrnd
      by_cases h1 : m.ty = tyProposal
      · exact Or.inl h1
      by_cases h2 : m.ty = tyState
      · exact Or.inr (Or.inl h2)
      by_cases h3 : m.ty = tyVote
      · exact Or.inr (Or.inr h3)
      simp [h1, h2, h3] at hrnd
    have htv : v.Type' = W32 1 ∨ v.Type' = W32 2 ∨ v.Type' = W32 3 := by
      rw [hmf.1]; rcases hty3 with h | h | h <;> rw [h] <;> simp [tyProposal, tyState, tyVote]
    -- the received round's facts
    have hrl : recv.length = ql.length := Hq.1
    simp only [Int.toNat_natCast] at hql' hrange
    ihave %hpre := qLb_valid γc σ.t ql ql' $$ Hql Hql'
    obtain ⟨hql'eq, htake⟩ := ql_next ql ql' (some ρ) recv.length hrl.symm hpre hql'.1 hql'.2
    rw [htake] at hrange
    have hfm' : ql'.filterMap id = List.range (ρ + 1) := by
      rw [hql'eq]; exact filterMap_snoc_range ql ρ hrange
    have hnone' : none ∉ ql' := by
      rw [hql'eq]; simp only [List.mem_append, List.mem_singleton, reduceCtorEq, _root_.or_false]
      exact Hq.2.2
    wp_auto
    wp_if_destruct
    rotate_left
    wp_if_destruct
    rotate_left
    wp_if_destruct
    rotate_left
    · exfalso; rcases htv with h | h | h <;> simp only [h] at * <;> contradiction
    all_goals (
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 (σ.t : Int))))) _ _ e.loc
        (by word) $$ [Hsl] with Hsl3
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 (σ.t : Int))))).toNat = σ.t by word]
        simp [he]
      wp_apply_core ex_GetHasRecvDec_t D.getHasRecvDec γ k γl γc σ.t e he
        iprop(⌜recv = x.recv ∧ ql = x.ql⌝ ∨ rdW γl γc σ.t)
        (fun st => if st.hasRecvDec then rdW γl γc σ.t else iprop(⌜recv = x.recv ∧ ql = x.ql⌝))
        $$ Hpl Hse Hsinv Hmode
      · iintro %st Hg HR
        iapply step_hasRecvDec $$ Hg HR
      iintro %st Hw
      cases hrd : st.hasRecvDec with
      | true =>
        simp only [↓reduceIte]
        wp_auto
        wp_for_post
        iframe
        iexists recv ++ [v], ql'
        iframe Hcons Hql'
        isplitr
        · ipureintro
          refine ⟨by simp [hrl, hql'.1], ?_, hnone'⟩
          rw [hfm', List.length_range]
        · iright; iexact Hw
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        icases Hw with ⟨%hrx, %hqx⟩
        have hρe : ρ = exRound x.pv := by
          rw [hqx] at hrange
          have := congrArg List.length hrange
          rw [List.length_range] at this
          omega
        have hwfm : (m.ty = tyProposal → m.phase = 0) ∧ (m.ty = tyState → 1 ≤ m.phase.toNat) := by
          obtain ⟨h1, h2⟩ := hwf
          rw [hmf.1, hmf.2.1] at h1 h2
          exact ⟨h1, h2⟩
        obtain ⟨hph, hk1, hk2, hk3⟩ := wait_ok m x.pv hr (hρe ▸ hrnd) hwfm
        wp_auto
        ledger_idx
        wp_pures
        wp_load
        have hvph : v.Phase' = x.pv.phase := hmf.2.1.trans hph
        simp only [hvph]
        wp_auto
        have hvt : v.Type' = m.ty := hmf.1
        rcases hr with hr1 | hr2
        · by_cases hp0 : x.pv.phase = 0
          · have hty' := hk1 hr1 hp0
            ledger_idx
            wp_pures
            wp_load
            simp only [hr1]
            wp_auto
            ledger_idx
            wp_pures
            wp_load
            simp only [hp0]
            wp_auto
            simp only [hvt, hty', tyProposal]
            wp_auto
            ledger_idx; wp_pures; wp_load; (try simp only [hr1]); wp_auto
            ledger_idx; wp_pures; wp_load; (try simp only [hp0]); wp_auto
            ledger_idx; wp_pures; wp_load; (try simp only [hr1]); wp_auto
            wait_ret_true
          · have hty' := hk2 hr1 hp0
            have hp0' : decide (x.pv.phase = W32 0) = false :=
              decide_eq_false (fun h => hp0 (by rw [h]; rfl))
            repeat (first | (ledger_idx) | (wp_load) | (simp only [hr1, hp0', hvt, hty', tyState, decide_false, decide_true]) | (wp_auto))
            wait_ret_true
        · have hty' := hk3 hr2
          repeat (first | (ledger_idx) | (wp_load) | (simp only [hr2, hvt, hty', tyVote, decide_false, decide_true]) | (wp_auto))
          wait_ret_true)
    done
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end Perennial.rabia.roles.server.layers.consensus
