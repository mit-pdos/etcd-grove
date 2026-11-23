/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/consensus/ExecFind.lean`, run `rabia-r1wake-1`.)

The executor's AfterWaits' helpers: the frame of a slot's run, recording my decision
(`decideSlot` from a `decJust`), `toNet` of a message without a round, the proposal request's key;
the frozen quorums of a notified round with their facts (`quorum_bits`, `quorum_props`).
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.consensus.ExecQuorum
public import Dsverify.Proof.rabia.roles.server.layers.consensus.ExecBefore

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.consensus

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model NetConn Dsv rabia.internal.message
  rabia.internal.config rabia.internal.ledger rabia rabia.internal.queue

set_option linter.unusedSectionVars false


/-! ## Pure helpers -/

theorem PrivSt.my_setMy (pv : PrivSt) (p r : Nat) (x : w32) (hr : r = 1 ∨ r = 2) :
    (pv.setMy p r x).my p r = x := by
  unfold PrivSt.setMy PrivSt.my
  simp only
  rw [List.getElem?_modify]
  have : p < (pv.myBC ++ List.replicate (p + 1 - pv.myBC.length) (0, 0)).length := by
    simp; omega
  rw [List.getElem?_eq_getElem this]
  simp only [↓reduceIte, Option.map_some]
  rcases hr with rfl | rfl <;> simp

theorem PrivSt.setMy_phase (pv : PrivSt) (p r : Nat) (x : w32) :
    (pv.setMy p r x).phase = pv.phase := rfl
theorem PrivSt.setMy_round (pv : PrivSt) (p r : Nat) (x : w32) :
    (pv.setMy p r x).round = pv.round := rfl
theorem PrivSt.setMy_myProp (pv : PrivSt) (p r : Nat) (x : w32) :
    (pv.setMy p r x).myProp = pv.myProp := rfl
theorem PrivSt.my_with (pv : PrivSt) (ph rd : w32) (p r : Nat) :
    ({ phase := ph, round := rd, myProp := pv.myProp, myBC := pv.myBC } : PrivSt).my p r =
      pv.my p r := rfl

theorem PrivSt.setMy_len (pv : PrivSt) (p r : Nat) (x : w32) :
    p < (pv.setMy p r x).myBC.length ∧ pv.myBC.length ≤ (pv.setMy p r x).myBC.length := by
  unfold PrivSt.setMy
  simp only [List.length_modify, List.length_append, List.length_replicate]
  omega

theorem af_keys_rabia_disj (k : Nat) : (↑(srvKeysN k) : CoPset) ## ↑rabiaN := by
  have hd : (↑(ndot rabiaR "keys") : CoPset) ## ↑(ndot rabiaR "inv") :=
    ndot_ne_disjoint rabiaR (by decide)
  unfold srvKeysN rabiaN
  exact ndot_preserve_disjoint_l _ hd

theorem af_keys_client_disj (k : Nat) :
    (↑(srvKeysN k) : CoPset) ## cliE := by
  have h : cliE ## ↑(srvKeysN k) := cliE_disj_of_sub (by
    unfold srvKeysN rabiaE
    exact (nclose_subseteq _ _).trans (nclose_subseteq _ _))
  exact fun x hx => h x ⟨hx.2, hx.1⟩

theorem af_client_rabia_disj : cliE ## ↑rabiaN := cliE_rabiaN

theorem af_sub_diff {A B : CoPset} (h : A ## B) : A ⊆ ⊤ \ B := by
  intro x hx
  exact LawfulSet.mem_diff.mpr ⟨CoPset.mem_full, fun h' => h x ⟨hx, h'⟩⟩

theorem af_disj_symm {A B : CoPset} (h : A ## B) : B ## A := fun x hx => h x ⟨hx.2, hx.1⟩

theorem af_keysEx_mydec {t k : Nat} {cur Ke : List FKey} (h : KeysEx t cur Ke)
    (hmd : FKey.mydec k t ∉ cur) : FKey.mydec k t ∉ Ke := by
  intro hin
  obtain ⟨s, hs, hor⟩ := h.1 _ hin
  simp only [FKey.slotOf, Option.some.injEq] at hs
  subst hs
  rcases hor with h1 | ⟨_, h2⟩
  · omega
  · exact hmd h2

theorem af_keysEx_cons {t : Nat} {cur Ke : List FKey} (h : KeysEx t cur Ke) (key : FKey)
    (hs : key.slotOf = some t) : KeysEx t (key :: cur) (key :: Ke) := by
  refine ⟨fun k' hk' => ?_, fun k' hk' => ?_⟩
  · rcases List.mem_cons.1 hk' with rfl | hk'
    · exact ⟨t, hs, Or.inr ⟨rfl, List.mem_cons_self⟩⟩
    · obtain ⟨s', hs', hor⟩ := h.1 _ hk'
      refine ⟨s', hs', ?_⟩
      rcases hor with h1 | ⟨h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, List.mem_cons_of_mem _ h2⟩
  · rcases List.mem_cons.1 hk' with rfl | hk'
    · exact hs
    · exact h.2 _ hk'

theorem af_keysEx_notObj {t : Nat} {cur Ke : List FKey} (h : KeysEx t cur Ke) :
    ∀ key ∈ Ke, key.isObj = false := by
  intro key hk
  obtain ⟨s, hs, -⟩ := h.1 key hk
  cases key <;> simp_all [FKey.slotOf, model.FKey.isObj]

theorem af_exLog_snoc_none {L : List MsgV} {t ρ : Nat} {m : MsgV} (hok : ExLogOk L)
    (hpos : ExLogPos L t ρ) (hm : msgRound m = none) (hty : m.ty ≠ tyClientRequest) :
    ExLogOk (L ++ [m]) ∧ ExLogPos (L ++ [m]) t ρ := by
  have hget : ∀ (i : Nat) (x : MsgV), (L ++ [m])[i]? = some x →
      (i < L.length ∧ L[i]? = some x) ∨ (i = L.length ∧ x = m) := by
    intro i x h
    by_cases hi : i < L.length
    · left; rw [List.getElem?_append_left hi] at h; exact ⟨hi, h⟩
    · right
      rw [List.getElem?_append_right (by omega)] at h
      cases hk : i - L.length with
      | zero => rw [hk] at h; simp at h; exact ⟨by omega, h.symm⟩
      | succ n => rw [hk] at h; simp at h
  have hleft : ∀ (i : Nat) (x : MsgV), L[i]? = some x → (L ++ [m])[i]? = some x := by
    intro i x h
    have hi : i < L.length := (List.getElem?_eq_some_iff.mp h).1
    rw [List.getElem?_append_left hi]; exact h
  obtain ⟨⟨h1, h2, h3⟩, hcr⟩ := hok
  obtain ⟨p1, p2⟩ := hpos
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro i x sl r hx hr
    rcases hget i x hx with ⟨hi, hx⟩ | ⟨rfl, rfl⟩
    · obtain ⟨j, hj, y, hy, hyr⟩ := h1 i x sl r hx hr
      exact ⟨j, hj, y, hleft j y hy, hyr⟩
    · rw [hm] at hr; cases hr
  · intro i j x y sr hx hy hxr hyr
    rcases hget i x hx with ⟨hi, hx'⟩ | ⟨hi, hx'⟩ <;> rcases hget j y hy with ⟨hj, hy'⟩ | ⟨hj, hy'⟩
    · exact h2 i j x y sr hx' hy' hxr hyr
    · subst hy'; rw [hm] at hyr; cases hyr
    · subst hx'; rw [hm] at hxr; cases hxr
    · omega
  · intro i j x y o o' hx hy hxt hyt _ _ _
    rcases hget i x hx with ⟨hi, hx⟩ | ⟨rfl, rfl⟩
    · rcases hget j y hy with ⟨hj, hy⟩ | ⟨rfl, rfl⟩
      · exact h3 i j x y o o' hx hy hxt hyt ‹_› ‹_› ‹_›
      · exact absurd hyt hty
    · exact absurd hxt hty
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hcr x hx
    · simp at hx; subst hx; exact hty
  · intro x hx sl r hr
    rcases List.mem_append.mp hx with hx | hx
    · exact p1 x hx sl r hr
    · simp at hx; subst hx; rw [hm] at hr; cases hr
  · intro r hr
    obtain ⟨y, hy, hyr⟩ := p2 r hr
    exact ⟨y, List.mem_append_left _ hy, hyr⟩

section reads
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable {cf : RCfg}
variable [package_sem : rabia.roles.server.layers.consensus.Assumptions]

/-- The configuration's fact and its validity. -/
theorem cfgIs_fact (γ : Names) :
    cfgIs (GF := GF) γ.rab cf ⊢ fact γ.rab (cfgFact cf).1 (cfgFact cf).2 ∗ ⌜cf.Ok⌝ := by
  unfold cfgIs cfgFact; iintro ⟨#H, %h⟩; iframe H; ipureintro; exact h

theorem cf_bounds (hc : cf.Ok) : 1 ≤ cf.f ∧ cf.n ≤ 5 ∧ 2 ≤ cf.q ∧ cf.q ≤ cf.n ∧ cf.maj ≤ 3 ∧
    cf.mpf ≤ 5 ∧ cf.fp1 ≤ 3 ∧ cf.maj ≤ cf.q := by
  unfold RCfg.Ok at hc; unfold RCfg.q RCfg.maj RCfg.mpf RCfg.fp1; omega

theorem consRO_slot (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans)
    (c : Loc) (s : Nat) (e : SlotV) (he : γl.slots[s]? = some e) :
    consRO (GF := GF) γ cf k γl γc ch c ⊢ slotsInv γ cf k γl γc ∗ isSlot e.loc e.γ e.q ∗
      ∃ ledger : GoSlice, structFieldRef Consensus go!"Ledger" c ↦□ ledger ∗
        ledger ↦*□ γl.slots.map (·.loc) ∗ ⌜γl.slots.length = lenLedger⌝ := by
  unfold consRO
  iintro ⟨%ledger, %qlk, %wg, #HId, #HWg, #HDone, #Hn2h, #Hh2n, #Hn2e, #He2n, #HQL, #HL,
    #HQm, #HSm, #HCh, #HLro, #HSI, #HSC, #HK⟩
  unfold ledgerRO
  icases HLro with ⟨#Hsl, %Hlen, #Hslots0⟩
  ihave #Hse := (BigSepL.bigSepL_lookup
    (Φ := fun _ e => iprop(isSlot (GF := GF) e.loc e.γ e.q)) he) $$ Hslots0
  iframe HSI Hse
  iexists ledger
  iframe HL Hsl
  ipureintro; exact Hlen

theorem consRO_done (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans)
    (c : Loc) :
    consRO (GF := GF) γ cf k γl γc ch c ⊢ structFieldRef Consensus go!"Done" c ↦□ ch.done ∗
      isChanBag (V := Unit) γl.done ch.done doneP := by
  unfold consRO
  iintro ⟨%ledger, %qlk, %wg, #HId, #HWg, #HDone, #Hn2h, #Hh2n, #Hn2e, #He2n, #HQL, #HL,
    #HQm, #HSm, #HCh, #HLro, #HSI, #HSC, #HK⟩
  unfold srvChans
  icases HCh with ⟨#Hd, -⟩
  iframe HDone Hd

/-- `exRun` without the slot's private part. -/
def exRunFrame (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc)
    (σ : ExSt) (x : ExSlot) : IProp GF :=
  iprop(exCommon γ cf k γl γc ch c σ x.cur x.ρs (σ.t + 1) ∗ exCoinOk c ∗
    structFieldRef Consensus go!"SvrSeq" c ↦ (W64 (σ.t : Int) : w64) ∗ ⌜σ.t < lenLedger⌝ ∗
    pendOk γ cf γl x.o ∗ spscConsumer (γc.queue σ.t) x.recv ∗ qLb γc σ.t x.ql ∗
    ⌜x.recv.length = x.ql.length ∧ x.ql.filterMap id = List.range (x.ql.filterMap id).length ∧
      True⌝ ∗
    ghostVar (exName γl γc σ.t) (1 : Qp).half false)

theorem exRun_split (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans)
    (c : Loc) (σ : ExSt) (x : ExSlot) :
    exRun (GF := GF) γ cf k γl γc ch c σ x ⊢ ∃ e, ⌜γl.slots[σ.t]? = some e ∧ σ.t < lenLedger ∧
      x.pv.myProp = x.o⌝ ∗ slotPriv e.loc x.pv ∗ consRO γ cf k γl γc ch c ∗ qLb γc σ.t x.ql ∗
      exRunFrame γ cf k γl γc ch c σ x := by
  unfold exRun exSlotRes exRunFrame
  iintro ⟨Hcom, Hcoin, Hseq, %ht, ⟨%e, %he, Hpriv, %hmy, Hpo, Hcons, #Hql, %hq, Hx⟩⟩
  ihave #Hro : consRO γ cf k γl γc ch c $$ [Hcom]
  · unfold exCommon; icases Hcom with ⟨#Hro, -⟩; iexact Hro
  iexists e
  isplitr
  · ipureintro; exact ⟨he, ht, hmy⟩
  iframe Hpriv Hro Hql Hcom Hcoin Hseq Hpo Hcons Hx
  ipureintro; exact ⟨ht, hq⟩

theorem exRun_join (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans)
    (c : Loc) (σ : ExSt) (x : ExSlot) (e : SlotV) (pv' : PrivSt)
    (he : γl.slots[σ.t]? = some e) (hmy : pv'.myProp = x.o) :
    exRunFrame (GF := GF) γ cf k γl γc ch c σ x ∗ slotPriv e.loc pv' ⊢
      exRun γ cf k γl γc ch c σ { x with pv := pv' } := by
  unfold exRun exSlotRes exRunFrame
  iintro ⟨⟨Hcom, Hcoin, Hseq, %ht, Hpo, Hcons, #Hql, %hq, Hx⟩, Hpriv⟩
  iframe Hcom Hcoin Hseq
  isplitr
  · ipureintro; exact ht
  iexists e
  iframe Hpriv Hpo Hcons Hql Hx
  ipureintro; exact ⟨he, hmy, hq⟩

/-- (A missing law of `message`: unfolds `objRep`.) Setting the slot number of a represented object. -/
theorem objRep_svrSeq (v : ConsensusObj) (o : ObjV) (s : w32) :
    objRep (GF := GF) v o ⊢ objRep { v with SvrSeq' := s } { o with svrSeq := s } := by
  unfold objRep
  iintro ⟨%h, H1, H2, H3⟩
  iframe H1 H2 H3
  ipureintro; exact ⟨h.1, h.2.1, rfl, h.2.2.2⟩

theorem objOk_svrSeq (γ : Names) (o : ObjV) (s : w32) :
    objOk (GF := GF) γ cf o ⊢ objOk γ cf { o with svrSeq := s } := by
  unfold objOk; iintro H; iexact H

instance af_isRabia_persistent (γ : RabiaNames) : Persistent (isRabia (GF := GF) γ) := by
  unfold isRabia; infer_instance

instance af_histFacts_persistent (γ : Names) (k : Nat) (H : List (ObjV × DVal)) :
    Persistent (histFacts (GF := GF) γ k H) := by
  unfold histFacts; infer_instance

/-- Deciding slot `t` from my own evidence: `mydec k t` and `dec t` recorded. -/
theorem dec_commit (γ : Names) (k : Nat) (hk : k < cf.n) (γl : SrvNames) (t : Nat)
    (H : List (ObjV × DVal)) (hH : H.length = t) (cur Ke : List FKey) (hKe : KeysEx t cur Ke)
    (hmd : FKey.mydec k t ∉ cur) (d : DVal) :
    isRabia (GF := GF) γ.rab ∗ cfgIs γ.rab cf ∗ isSrvKeys γ k γl ∗ £ 1 ∗ keysPart γl false Ke ∗
      histFacts γ k H ∗ decJust γ cf t d ⊢
    |={⊤}=> keysPart γl false (FKey.mydec k t :: Ke) ∗
      ⌜KeysEx t (FKey.mydec k t :: cur) (FKey.mydec k t :: Ke)⌝ ∗
      fact γ.rab (.mydec k t) (.dval d) ∗ fact γ.rab (.dec t) (.dval d) := by
  iintro ⟨#Hrab, #Hcfg, #Hks, Hlc, HKe, #Hh, #Hj⟩
  unfold decJust
  icases Hj with ⟨%S, #HS, %hJ⟩
  have hobj := af_keysEx_notObj hKe
  have hnKe := af_keysEx_mydec hKe hmd
  -- the previous slot's decision fact
  ihave ⟨%S2, #HS2, %hS2⟩ : ∃ S2 : List (FKey × FVal), ([∗list] kv ∈ S2, fact γ.rab kv.1 kv.2) ∗
      ⌜t = 0 ∨ ∃ d', (FKey.mydec k (t - 1), FVal.dval d') ∈ S2⌝ $$ []
  · cases t with
    | zero =>
      iexists []
      isplitr
      · iapply BigSepL.bigSepL_nil.2; itrivial
      · ipureintro; left; rfl
    | succ t' =>
      obtain ⟨xh, hxh⟩ : ∃ xh, H[t']? = some xh :=
        Option.isSome_iff_exists.mp (by simp [hH])
      unfold histFacts
      ihave ⟨-, #Hmy⟩ := (BigSepL.bigSepL_lookup
        (Φ := fun i (x : ObjV × DVal) => iprop(fact (GF := GF) γ.rab (.prop k i) (.obj (objId x.1)) ∗
          fact γ.rab (.mydec k i) (.dval x.2))) hxh) $$ Hh
      iexists [(FKey.mydec k t', FVal.dval xh.2)]
      isplitr
      · iapply BigSepL.bigSepL_cons.2
        iframe Hmy
        iapply BigSepL.bigSepL_nil.2; itrivial
      · ipureintro; right; exact ⟨xh.2, by simp⟩
  imod srvKeys_acc γ k γl false ⊤ (fun _ _ => CoPset.mem_full) Ke $$ [HKe] with
    ⟨%K, %Ko, HK, ⟨%hperm, %hKo⟩, Hcl⟩
  · iframe HKe; iexact Hks
  have hnK : FKey.mydec k t ∉ K := by
    intro hin
    rcases List.mem_append.1 (hperm.subset hin) with h | h
    · exact hnKe h
    · have := hKo _ h; simp [model.FKey.isObj] at this
  ihave #HSS : [∗list] kv ∈ S ++ S2, fact γ.rab kv.1 kv.2 $$ []
  · iapply BigSepL.bigSepL_append.2
    iframe HS HS2
  imod decideSlot γ.rab (⊤ \ ↑(srvKeysN k)) (af_sub_diff (af_disj_symm (af_keys_rabia_disj k)))
    af_client_rabia_disj (af_sub_diff (af_disj_symm (af_keys_client_disj k))) cf k t d K (S ++ S2) hk hnK
    (by
      rcases hS2 with h | ⟨d', hd'⟩
      · exact Or.inl h
      · exact Or.inr ⟨d', List.mem_append_right _ hd'⟩)
    (fun M hc hM hSM => Or.inl (hJ M hc hM (fun kv hkv => hSM kv (List.mem_append_left _ hkv))))
    $$ [HK Hlc] with ⟨HK, #Hmy, #Hdec⟩
  · iframe HK Hlc HSS Hcfg; iexact Hrab
  imod Hcl $$ %(FKey.mydec k t :: K) %(FKey.mydec k t :: Ke) [HK] with HKe
  · iframe HK
    ipureintro
    refine ⟨List.Perm.cons _ hperm, fun key hk => ?_⟩
    rcases List.mem_cons.1 hk with rfl | hk
    · rfl
    · exact hobj _ hk
  imodintro
  iframe HKe Hmy Hdec
  ipureintro
  exact af_keysEx_cons hKe _ rfl

/-- `toNet` of a decision message of slot `t`: `E_k` grows by it. -/
theorem wp_toNet_dec (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans)
    (c : Loc) (σ : ExSt) (x : ExSlot) (w : Msg) (o : ObjV) (d : DVal)
    (ho : o.svrSeq.toNat = σ.t) (ht : σ.t < lenLedger) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.consensus ∗
        exRunFrame γ cf k γl γc ch c σ x ∗ msgRep w (decMsg o σ.t) ∗
        fact γ.rab (.dec σ.t) (.dval d) ∗ decObjOk γ cf σ.t d o }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"toNet")) (Val #w))
    {{ RET #(); ∃ (L : List MsgV) (sent : List Msg),
        exRunFrame γ cf k γl γc ch c { σ with L := L, sent := sent } x }} := by
  iintro %Φ ⟨#Hpk, Hfr, #Hw, #Hdec, #Hdo⟩ HΦ
  unfold exRunFrame exCommon
  icases Hfr with ⟨⟨#Hro, Hf, #Hh, Hm, %hH, #Hpf, Hk, %hK, Hex, Hsp, %hlog, Hfs⟩, Hrest⟩
  have hoeq : { o with svrSeq := W32 σ.t } = o := by
    cases o; simp only [ObjV.mk.injEq, and_true, true_and]
    unfold lenLedger at ht; simp only at ho; word
  have hmr : msgRound (decMsg o σ.t) = none := by
    simp [msgRound, roundOf, decMsg, tyDecision, tyProposal, tyState, tyVote]
  have hty : (decMsg o σ.t).ty ≠ tyClientRequest := by
    simp [decMsg, tyDecision, tyClientRequest]
  obtain ⟨hlen, hok, hpos⟩ := hlog
  have hnew := af_exLog_snoc_none hok hpos hmr hty
  unfold exAuth
  imod monoListAuthOwn_update (σ.L ++ [decMsg o σ.t]) (List.prefix_append _ _) $$ Hex
    with ⟨Hex, #Hlb⟩
  wp_apply wp_toNet γ k γl γc ch c w σ.sent $$ [$Hpk $Hro $Hsp]
  · unfold e2nP
    iexists decMsg o σ.t, σ.L ++ [decMsg o σ.t]
    iframe Hw
    isplitr
    · unfold bmsgOk
      have h0 : (decMsg o σ.t).ty = tyDecision := rfl
      rw [h0]
      simp only [show tyDecision ≠ tyClientRequest by decide, show tyDecision ≠ tyProposal by decide,
        show tyDecision ≠ tyState by decide, show tyDecision ≠ tyVote by decide,
        show tyDecision ≠ tyProposalRequest by decide, ↓reduceIte]
      iexists o, d
      isplitr
      · ipureintro; unfold decMsg; rw [hoeq]
      rw [ho]
      iframe Hdec Hdo
    isplitr
    · unfold exLb; iexact Hlb
    · ipureintro
      refine ⟨?_, hnew.1⟩
      rw [hlen]; simp
  iintro Hsp
  iapply HΦ
  iexists σ.L ++ [decMsg o σ.t], σ.sent ++ [w]
  iframe Hro Hf Hh Hm Hpf Hk Hrest Hfs Hsp
  iframe Hex
  ipureintro
  exact ⟨hH, hK, by simp [hlen], hnew.1, hnew.2⟩

/-- My decision of slot `t` recorded in the frame (keys). -/
theorem frame_dec_commit (γ : Names) (k : Nat) (hk : k < cf.n) (γl : SrvNames) (γc : ConsNames)
    (ch : SrvChans) (c : Loc) (σ : ExSt) (x : ExSlot) (hmd : FKey.mydec k σ.t ∉ x.cur) (d : DVal) :
    shared (GF := GF) γ ∗ cfgIs γ.rab cf ∗ exRunFrame γ cf k γl γc ch c σ x ∗ £ 1 ∗
      decJust γ cf σ.t d ⊢
      |={⊤}=> exRunFrame γ cf k γl γc ch c { σ with Ke := FKey.mydec k σ.t :: σ.Ke }
          { x with cur := FKey.mydec k σ.t :: x.cur } ∗
        fact γ.rab (.mydec k σ.t) (.dval d) ∗ fact γ.rab (.dec σ.t) (.dval d) := by
  iintro ⟨#Hsh, #Hcfg, Hfr, Hlc, #Hj⟩
  unfold exRunFrame exCommon
  icases Hfr with ⟨⟨#Hro, Hf, #Hh, Hm, %hH, #Hpf, Hk, %hK, Hex, Hsp, %hlog, Hfs⟩, Hrest⟩
  ihave #Hks : isSrvKeys γ k γl $$ [Hro]
  · unfold consRO
    iintro
    icases Hro with ⟨%a, %b, %d', -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HK⟩
    iexact HK
  ihave #Hrab : isRabia γ.rab $$ [Hsh]
  · unfold shared; icases Hsh with ⟨#H, -⟩; iexact H
  imod dec_commit γ k hk γl σ.t σ.H hH x.cur σ.Ke hK hmd d $$ [Hlc Hk] with ⟨Hk, %hK', #Hmy, #Hdec⟩
  · iframe Hrab Hcfg Hks Hlc Hk Hh Hj
  imodintro
  iframe Hmy Hdec Hro Hf Hh Hm Hpf Hk Hex Hsp Hfs Hrest
  ipureintro
  exact ⟨hH, hK', hlog⟩

theorem decObjOk_svrSeq (γ : Names) (t : Nat) (d : DVal) (o : ObjV) :
    decObjOk (GF := GF) γ cf t d o ⊢ ⌜o.svrSeq.toNat = t⌝ := by
  unfold decObjOk; cases d with
  | null => iintro %h; ipureintro; exact h.2.1
  | obj id => iintro ⟨%h, -⟩; ipureintro; exact h.2

theorem frame_coin (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc)
    (σ : ExSt) (x : ExSlot) :
    exRunFrame (GF := GF) γ cf k γl γc ch c σ x ⊢ coinOk c ∗ (coinOk c -∗ exRunFrame γ cf k γl γc ch c σ x) := by
  unfold exRunFrame
  iintro ⟨Hcom, Hcoin, Hrest⟩
  isplitl [Hcoin]
  · unfold exCoinOk coinOk; iexact Hcoin
  · iintro Hc; iframe Hcom Hrest; unfold exCoinOk coinOk; iexact Hc

/-- `toNet` of a message without a round (a request or a decision): `E_k` grows by it. -/
theorem wp_toNet_none (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans)
    (c : Loc) (σ : ExSt) (x : ExSlot) (w : Msg) (m : MsgV) (hmr : msgRound m = none)
    (hty : m.ty ≠ tyClientRequest) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.consensus ∗
        exRunFrame γ cf k γl γc ch c σ x ∗ msgRep w m ∗ bmsgOk γ cf k m }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"toNet")) (Val #w))
    {{ RET #(); ∃ (L : List MsgV) (sent : List Msg),
        exRunFrame γ cf k γl γc ch c { σ with L := L, sent := sent } x }} := by
  iintro %Φ ⟨#Hpk, Hfr, #Hw, #Hok⟩ HΦ
  unfold exRunFrame exCommon
  icases Hfr with ⟨⟨#Hro, Hf, #Hh, Hm, %hH, #Hpf, Hk, %hK, Hex, Hsp, %hlog, Hfs⟩, Hrest⟩
  obtain ⟨hlen, hok, hpos⟩ := hlog
  have hnew := af_exLog_snoc_none hok hpos hmr hty
  unfold exAuth
  imod monoListAuthOwn_update (σ.L ++ [m]) (List.prefix_append _ _) $$ Hex
    with ⟨Hex, #Hlb⟩
  wp_apply wp_toNet γ k γl γc ch c w σ.sent $$ [$Hpk $Hro $Hsp]
  · unfold e2nP
    iexists m, σ.L ++ [m]
    iframe Hw Hok
    isplitr
    · unfold exLb; iexact Hlb
    · ipureintro
      refine ⟨?_, hnew.1⟩
      rw [hlen]; simp
  iintro Hsp
  iapply HΦ
  iexists σ.L ++ [m], σ.sent ++ [w]
  iframe Hro Hf Hh Hm Hpf Hk Hrest Hfs Hsp
  iframe Hex
  ipureintro
  exact ⟨hH, hK, by simp [hlen], hnew.1, hnew.2⟩

/-- My proposal request of slot `t` recorded (the key `preq k t`). -/
theorem frame_insert_preq (γ : Names) (k : Nat) (hk : k < cf.n) (γl : SrvNames) (γc : ConsNames)
    (ch : SrvChans) (c : Loc) (σ : ExSt) (x : ExSlot) (hq : FKey.preq k σ.t ∉ x.cur) :
    shared (GF := GF) γ ∗ cfgIs γ.rab cf ∗ exRunFrame γ cf k γl γc ch c σ x ⊢
      |={⊤}=> exRunFrame γ cf k γl γc ch c { σ with Ke := FKey.preq k σ.t :: σ.Ke }
          { x with cur := FKey.preq k σ.t :: x.cur } ∗
        fact γ.rab (.preq k σ.t) (.bit 0) := by
  iintro ⟨#Hsh, #Hcfg, Hfr⟩
  unfold cfgIs
  icases Hcfg with ⟨#Hcf, -⟩
  unfold exRunFrame exCommon
  icases Hfr with ⟨⟨#Hro, Hf, #Hh, Hm, %hH, #Hpf, Hk, %hK, Hex, Hsp, %hlog, Hfs⟩, Hrest⟩
  ihave #Hks : isSrvKeys γ k γl $$ [Hro]
  · unfold consRO
    icases Hro with ⟨%a, %b, %d', -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HK⟩
    iexact HK
  ihave #Hj : factJust γ (.preq k σ.t) (.bit 0) $$ []
  · unfold factJust
    iexists [cfgFact cf]
    isplitr
    · iapply BigSepL.bigSepL_cons.2
      isplitr
      · unfold cfgFact; iexact Hcf
      · iapply BigSepL.bigSepL_nil.2; itrivial
    · ipureintro
      intro M hM hS hfree
      apply Valid.insert M (cfgOf_of hS) hM _ _ hfree
      · simp only [Justified]; exact hk
      · exact ⟨by simp, fun id X r => ⟨by simp, by simp⟩⟩
      · intro X' s' p' b' h; cases h
      · intro X' s' p' b' h; cases h
      · intro s' h; cases h
      · intro X' s' h; cases h
  imod insertMine γ k γl σ.t x.cur σ.Ke (.preq k σ.t) (.bit 0) rfl hq rfl
    (fun r id X s => ⟨by simp, by simp, by simp, by simp, by simp⟩) hK $$ [Hk] with ⟨Hk, %hK', #Hpq⟩
  · iframe Hsh Hks Hk Hj
  imodintro
  iframe Hpq Hro Hf Hh Hm Hpf Hk Hex Hsp Hfs Hrest
  ipureintro
  exact ⟨hH, hK', hlog⟩

/-- A recorded proposal request of mine is of a slot `≤ t`. -/
theorem frame_preq_le (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames)
    (ch : SrvChans) (c : Loc) (σ : ExSt) (x : ExSlot) (v b : Nat) :
    shared (GF := GF) γ ∗ exRunFrame γ cf k γl γc ch c σ x ∗ fact γ.rab (.preq k v) (.bit b) ⊢
      |={⊤}=> exRunFrame γ cf k γl γc ch c σ x ∗ ⌜v ≤ σ.t⌝ := by
  iintro ⟨#Hsh, Hfr, #Hpq⟩
  unfold exRunFrame exCommon
  icases Hfr with ⟨⟨#Hro, Hf, #Hh, Hm, %hH, #Hpf, Hk, %hK, Hex, Hsp, %hlog, Hfs⟩, Hrest⟩
  ihave #Hks : isSrvKeys γ k γl $$ [Hro]
  · unfold consRO
    icases Hro with ⟨%a, %b', %d', -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HK⟩
    iexact HK
  ihave #Hrab : isRabia γ.rab $$ [Hsh]
  · unfold shared; icases Hsh with ⟨#H, -⟩; iexact H
  imod srvKeys_acc γ k γl false ⊤ (fun _ _ => CoPset.mem_full) σ.Ke $$ [Hk] with
    ⟨%K, %Ko, HK, ⟨%hperm, %hKo⟩, Hcl⟩
  · iframe Hk; iexact Hks
  imod fact_mine γ.rab (⊤ \ ↑(srvKeysN k)) (af_sub_diff (af_disj_symm (af_keys_rabia_disj k)))
    (.srv k) K (.preq k v) (.bit b) $$ [HK] with ⟨HK, %hmine⟩
  · iframe HK Hpq; iexact Hrab
  have hin : FKey.preq k v ∈ K := hmine rfl
  have hle : v ≤ σ.t := by
    rcases List.mem_append.1 (hperm.subset hin) with h | h
    · obtain ⟨s, hs, hor⟩ := hK.1 _ h
      simp only [FKey.slotOf, Option.some.injEq] at hs
      subst hs; omega
    · have := hKo _ h; simp [model.FKey.isObj] at this
  imod Hcl $$ %K %σ.Ke [HK] with Hk
  · iframe HK; ipureintro; exact ⟨hperm, af_keysEx_notObj hK⟩
  imodintro
  iframe Hro Hf Hh Hm Hpf Hk Hex Hsp Hfs Hrest
  ipureintro
  exact ⟨⟨hH, hK, hlog⟩, hle⟩


/-- A notified round of states (`r = 1`, `p ≥ 1`) or votes (`r = 2`) of slot `s`: its frozen
quorum, the senders' values with their facts. -/
theorem quorum_bits (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV)
    (he : γl.slots[s]? = some e) (ql : List (Option Nat)) (p r ρ : Nat)
    (hr : (r = 1 ∧ 1 ≤ p) ∨ r = 2) (hρe : ρ = 2 * p + r - 1) (hρ : some ρ ∈ ql) :
    slotsInv (GF := GF) γ cf k γl γc ∗ qLb γc s ql ⊢
      |={⊤}=> ∃ ents0 : List Ent, monoListLbOwn (entName γl γc s) ents0 ∗
        ⌜(tally ents0 ρ).length = cf.q ∧ Senders cf (bitPairs (tally ents0 ρ)) ∧
          (bitPairs (tally ents0 ρ)).length = cf.q⌝ ∗
        [∗list] kv ∈ bitFacts s p r (bitPairs (tally ents0 ρ)), fact γ.rab kv.1 kv.2 := by
  subst hρe
  iintro ⟨#Hsi, #Hq⟩
  imod slot_snapshot γ k γl γc s e he ql _ hρ ⊤ (by simp) $$ [Hsi Hq] with
    ⟨%ents0, #Hlb, %h0, #Hb⟩
  · iframe Hsi Hq
  ihave #HF := bits_facts γ s p r hr ents0 (fun e he => (h0.2.2 e he).2) $$ Hb
  imodintro
  iexists ents0
  iframe Hlb HF
  ipureintro
  exact ⟨h0.1, bitPairs_senders (fun e he => (h0.2.2 e (tally_mem he).1).1) h0.2.1,
    by rw [bitPairs_length, h0.1]⟩

/-- Once a round of slot `s` is notified: the frozen quorum of its proposals (round 0), the
senders' objects with their facts. -/
theorem quorum_props (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (s : Nat) (e : SlotV)
    (he : γl.slots[s]? = some e) (ql : List (Option Nat)) (hρ : ∃ ρ', 0 ≤ ρ' ∧ some ρ' ∈ ql) :
    slotsInv (GF := GF) γ cf k γl γc ∗ qLb γc s ql ⊢
      |={⊤}=> ∃ ents0 : List Ent, monoListLbOwn (entName γl γc s) ents0 ∗
        ⌜(tally ents0 0).length = cf.q ∧ Senders cf (propPairs (tally ents0 0)) ∧
          (propPairs (tally ents0 0)).length = cf.q ∧
          (propPairs (tally ents0 0)).map Prod.snd = (objsOf (tally ents0 0)).map objId⌝ ∗
        ([∗list] kv ∈ propFacts s (propPairs (tally ents0 0)), fact γ.rab kv.1 kv.2) ∗
        [∗list] o ∈ objsOf (tally ents0 0), objOk γ cf o ∗ ⌜o.svrSeq.toNat = s⌝ := by
  iintro ⟨#Hsi, #Hq⟩
  imod slot_snapshot_le γ k γl γc s e he ql 0 hρ ⊤ (by simp) $$ [Hsi Hq] with
    ⟨%ents0, #Hlb, %h0, #Hb⟩
  · iframe Hsi Hq
  ihave ⟨%hobj, #HF, #Ho⟩ := props_facts0 γ s ents0 (fun e he => (h0.2.2 e he).2) $$ Hb
  imodintro
  iexists ents0
  iframe Hlb HF Ho
  ipureintro
  exact ⟨h0.1, propPairs_senders (fun e he => (h0.2.2 e (tally_mem he).1).1) h0.2.1,
    by rw [propPairs_length _ hobj, h0.1], propPairs_snd _⟩

/-- The objects of a frozen round 0 are not none (`q > 0`). -/
theorem objsOf_ne {T : List Ent} (hc : cf.Ok) (hl : (propPairs T).length = cf.q)
    (hs : (propPairs T).map Prod.snd = (objsOf T).map objId) : objsOf T ≠ [] := by
  intro h
  rw [h] at hs
  have := congrArg List.length hs
  simp only [List.length_map, List.map_nil, List.length_nil] at this
  have := (cf_bounds hc).2.2.1
  omega

end reads

end Perennial.rabia.roles.server.layers.consensus

namespace Perennial.rabia.roles.server.layers.consensus

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model NetConn Dsv rabia.internal.message
  rabia.internal.config rabia.internal.ledger rabia rabia.internal.queue

section find
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable {cf : RCfg}
variable [package_sem : rabia.roles.server.layers.consensus.Assumptions]

local macro "slice_index_if" : tactic =>
  `(tactic| (rw [ite_eq_left_of_eq_true _ _ (eq_true (by constructor <;> word))]))

theorem wp_requestProposalAndWait_strong (D : ExDeps (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc) (hk : k < cf.n)
    (σ : ExSt) (x : ExSlot) (hq : FKey.preq k σ.t ∉ x.cur) :
    {{ exPre (GF := GF) γ cf ∗ exRun γ cf k γl γc ch c σ x }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"requestProposalAndWait"))
        (Val #(W32 σ.t)))
    {{ (v : ConsensusObj), RET #v; ∃ σ' x' o, exRun γ cf k γl γc ch c σ' x' ∗
        ⌜ExStep σ x σ' x' ∧ x'.pv = x.pv ∧ x'.ρs = x.ρs ∧ o.svrSeq.toNat = σ.t ∧
          x'.cur = FKey.preq k σ.t :: x.cur⌝ ∗
        objRep v o ∗ objOk γ cf o ∗ majPropW γ cf σ.t (objId o) }} := by
  wp_start as ⟨#Hpre, Hrun⟩
  ihave ⟨#Hpk, #Hconf, #Hsh, #Hcfg⟩ := Hpre
  ihave ⟨%e, %hee, Hpriv, #Hro, #Hql, Hfr⟩ := exRun_split γ k γl γc ch c σ x $$ Hrun
  obtain ⟨he, ht, hmy⟩ := hee
  ihave ⟨-, %hcf⟩ := cfgIs_fact γ $$ Hcfg
  have hb := cf_bounds hcf
  ihave #Hro2 := Hro
  unfold consRO
  icases Hro2 with ⟨%ledger, %qlk, %wg, #HId, #HWg, #HDone, #Hn2h, #Hh2n, #Hn2e, #He2n, #HQL, #HL,
    #HQm, #HSm, #HCh, #HLro, #HSI, #HSC, #HK⟩
  wp_auto
  imod frame_insert_preq γ k hk γl γc ch c σ x hq $$ [Hsh Hcfg Hfr] with ⟨Hfr, #Hpq⟩
  · iframe Hsh Hcfg Hfr
  have htk : (W32 k : w32).toNat = k := by word
  have htt : (W32 σ.t : w32).toNat = σ.t := by unfold lenLedger at ht; word
  let mq : MsgV := { ty := tyProposalRequest, phase := W32 k, value := W32 σ.t, obj := none }
  ihave #Hmq : msgRep { Type' := W32 4, Phase' := W32 k, Value' := W32 σ.t, Obj' := null } mq $$ []
  · iapply cons_msgRep_intro _ mq ⟨rfl, rfl, rfl⟩
    ipureintro; rfl
  wp_apply (wp_toNet_none γ k γl γc ch c _ _ _ mq
    (by simp [mq, msgRound, roundOf, tyProposalRequest, tyProposal, tyState, tyVote])
    (by simp [mq, tyProposalRequest, tyClientRequest])) $$ [$Hpk $Hfr $Hmq]
    as ⟨%L2, %sent2, Hfr⟩
  · unfold bmsgOk
    simp only [mq, show tyProposalRequest ≠ tyClientRequest by decide,
      show tyProposalRequest ≠ tyProposal by decide, show tyProposalRequest ≠ tyState by decide,
      show tyProposalRequest ≠ tyVote by decide, ↓reduceIte]
    isplitr
    · ipureintro; exact ⟨htk, trivial⟩
    · iexists 0; rw [htt]; iexact Hpq
  unfold srvChans
  icases HCh with ⟨-, -, -, -, -, -, -, #Hbn2e⟩
  ihave HI : ("Hfr" ∷ exRunFrame γ cf k γl γc ch c
      { ({ σ with Ke := FKey.preq k σ.t :: σ.Ke } : ExSt) with L := L2, sent := sent2 }
      { x with cur := FKey.preq k σ.t :: x.cur } ∗ "Hpriv" ∷ slotPriv e.loc x.pv) $$ [Hfr Hpriv]
  · iframe Hfr Hpriv
  wp_for HI
  wp_apply wp_bag_receive γl.n2e ch.n2e (n2eP γ cf k) $$ [Hbn2e] as %v Hn
  · iexact Hbn2e
  unfold n2eP replyOk
  icases Hn with ⟨%mm, #Hmm, ⟨%o, %W, %b, %hr, #Hoo, #HW, #Hpq'⟩⟩
  ihave %hmf := msgRep_fields v mm $$ Hmm
  obtain ⟨hty, hph', hob, hsv, hnd, hlt', hlen⟩ := hr
  rw [show v.Type' = W32 5 by rw [hmf.1, hty]; rfl]
  rw [decide_eq_true rfl]
  wp_auto
  rw [hmf.2.2]
  by_cases hlt : mm.value.toNat < σ.t
  · rw [decide_eq_true (by word)]
    wp_auto
    wp_for_post
    iframe
    isplitl [Hfr]
    · iexact Hfr
    · iexact Hpriv
  · rw [decide_eq_false (by word)]
    ihave ⟨%ov, #Hov, #Hor⟩ := cons_msgRep_obj v mm o hob $$ Hmm
    imod frame_preq_le γ k γl γc ch c
      ({ ({ σ with Ke := FKey.preq k σ.t :: σ.Ke } : ExSt) with L := L2, sent := sent2 })
      { x with cur := FKey.preq k σ.t :: x.cur } mm.value.toNat b $$ [Hsh Hfr Hpq'] with ⟨Hfr, %hle⟩
    · iframe Hsh Hpq'; iexact Hfr
    have heq : mm.value.toNat = σ.t := by simp only at hle; omega
    wp_auto
    wp_for_post
    iapply HΦ
    iexists _, { x with cur := FKey.preq k σ.t :: x.cur, pv := x.pv }, o
    isplitl [Hfr Hpriv]
    · iapply exRun_join γ k γl γc ch c
        ({ ({ σ with Ke := FKey.preq k σ.t :: σ.Ke } : ExSt) with L := L2, sent := sent2 })
        { x with cur := FKey.preq k σ.t :: x.cur } e x.pv he hmy $$ [Hfr Hpriv]
      iframe Hpriv; iexact Hfr
    isplitr
    · ipureintro
      refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, ?_, rfl⟩
      rw [hsv]; exact heq
    iframe Hor Hoo
    unfold majPropW objId
    iexists W
    isplitr
    · ipureintro; exact ⟨⟨hnd, hlt'⟩, hlen⟩
    rw [← heq]
    iexact HW

theorem wp_requestProposalAndWait_proof (D : ExDeps (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc) (hk : k < cf.n)
    (σ : ExSt) (x : ExSlot) (hq : FKey.preq k σ.t ∉ x.cur) :
    {{ exPre (GF := GF) γ cf ∗ exRun γ cf k γl γc ch c σ x }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"requestProposalAndWait"))
        (Val #(W32 σ.t)))
    {{ (v : ConsensusObj), RET #v; ∃ σ' x' o, exRun γ cf k γl γc ch c σ' x' ∗
        ⌜ExStep σ x σ' x' ∧ x'.pv = x.pv ∧ x'.ρs = x.ρs ∧ o.svrSeq.toNat = σ.t⌝ ∗
        objRep v o ∗ objOk γ cf o ∗ majPropW γ cf σ.t (objId o) }} := by
  iintro %Φ Hpre HΦ
  iapply wp_requestProposalAndWait_strong D γ k γl γc ch c hk σ x hq $$ Hpre
  inext
  iintro %v ⟨%σ', %x', %o, Hrun, %h, Hrest⟩
  iapply HΦ
  iexists σ', x', o
  iframe Hrun Hrest
  ipureintro; exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩


/-- The specification `findReturnValue` needs of `requestProposalAndWait`. -/
abbrev rpwSpec (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans)
    (c : Loc) : Prop :=
  ∀ (σ : ExSt) (x : ExSlot), FKey.preq k σ.t ∉ x.cur →
    {{ exPre (GF := GF) γ cf ∗ exRun γ cf k γl γc ch c σ x }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"requestProposalAndWait"))
        (Val #(W32 σ.t)))
    {{ (v : ConsensusObj), RET #v; ∃ σ' x' o, exRun γ cf k γl γc ch c σ' x' ∗
        ⌜ExStep σ x σ' x' ∧ x'.pv = x.pv ∧ x'.ρs = x.ρs ∧ o.svrSeq.toNat = σ.t ∧
          x'.cur = FKey.preq k σ.t :: x.cur⌝ ∗
        objRep v o ∗ objOk γ cf o ∗ majPropW γ cf σ.t (objId o) }}

/-- `findReturnValue(t, pse, rod)` after a frozen round `2 pse + rod - 1` whose values' majority is
`b`, with the evidence that a decision meaning `b` is justified (`bitEvW`): the decision object and
its justification. -/
theorem wp_findReturnValue_strong (D : ExDeps (GF := GF)) (γ : Names) (k : Nat)
    (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc)
    (hRPW : rpwSpec (GF := GF) γ cf k γl γc ch c)
    (σ : ExSt) (x : ExSlot) (pse rod : w32) (hrod : rod = 1 ∨ rod = 2)
    (hpr : (rod.toNat = 1 ∧ 1 ≤ pse.toNat) ∨ rod.toNat = 2) (vs : List Nat)
    (hq : FKey.preq k σ.t ∉ x.cur) :
    {{ exPre (GF := GF) γ cf ∗ exRun γ cf k γl γc ch c σ x ∗
        notified γc σ.t (2 * pse.toNat + rod.toNat - 1) ∗
        frozenVals cf γl γc σ.t (2 * pse.toNat + rod.toNat - 1) vs ∗ bitEvW γ cf σ.t (majV vs) }}
      (App (App (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"findReturnValue"))
        (Val #(W32 σ.t))) (Val #pse)) (Val #rod))
    {{ (v : ConsensusObj), RET #v; ∃ σ' x' d o, exRun γ cf k γl γc ch c σ' x' ∗
        ⌜ExStep σ x σ' x' ∧ x'.pv = x.pv ∧ (x'.cur = x.cur ∨ x'.cur = FKey.preq k σ.t :: x.cur) ∧
          x'.ρs = x.ρs⌝ ∗
        objRep v o ∗ decObjOk γ cf σ.t d o ∗ decJust γ cf σ.t d }} := by
  wp_start as ⟨#Hpre, Hrun, #Hnot, #Hfz, #Hev⟩
  ihave ⟨#Hpk, #Hconf, #Hsh, #Hcfg⟩ := Hpre
  ihave ⟨-, %hcf⟩ := cfgIs_fact γ $$ Hcfg
  have hcb := cf_bounds hcf
  unfold notified frozenVals
  icases Hnot with ⟨%qln, #Hqn, %hqn⟩
  icases Hfz with ⟨%entsV, #HlbV, ⟨%hV, %hVl⟩⟩
  unfold bitEvW
  icases Hev with ⟨%Sb, #HSb, %hSb⟩
  ihave ⟨%e, %hee, Hpriv, #Hro, #Hql, Hfr⟩ := exRun_split γ k γl γc ch c σ x $$ Hrun
  obtain ⟨he, ht, hmy⟩ := hee
  ihave ⟨#Hsi, #Hse, %ledger, #HL, #Hsl, %Hlen⟩ := consRO_slot γ k γl γc ch c σ.t e he $$ Hro
  ihave ⟨%ps, #Hc⟩ := confRO_val $$ Hconf
  ihave Hc2 := Hc
  iStructNamed Hc2
  ihave #Hpl : isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.ledger $$ []
  · iPkgInit
  have hts : (W32 σ.t).toNat = σ.t := by unfold lenLedger at ht; word
  have hs : (W32 σ.t).toNat < lenLedger := by rw [hts]; exact ht
  wp_auto
  wp_apply wp_PanicTermNotMatched γ k γl γc ch c (W32 σ.t) hs $$ [$Hconf $Hro]
  try wp_auto
  have hmod : W32 σ.t % W32 10000 = W32 σ.t := by unfold lenLedger at ht; word
  rw [hmod]
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  rw [List.length_map, Hlen] at Hl
  unfold lenLedger at Hl ht
  slice_index_if
  wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
    word) $$ [Hsl] with Hsl2
  · iframe Hsl; ipureintro
    rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
    simp [he]
  wp_apply_core wp_bcMajV_frozen D.bcMajV γ k γl γc σ.t e he pse rod hrod hpr _ rfl entsV hVl
    $$ Hpl Hse Hsi HlbV
  rw [show valsOf (tally entsV (2 * pse.toNat + rod.toNat - 1)) = vs from hV]
  have hb1 := majV_le1 vs
  wp_auto
  rcases (show majV vs = 0 ∨ majV vs = 1 by omega) with hb0 | hb0
  · rw [hb0, decide_eq_false (by decide)]
    wp_auto
    iapply HΦ
    iexists σ, { x with pv := x.pv }, DVal.null,
      ({ proId := 0, proSeq := 0, svrSeq := W32 σ.t, isNull := true, cliIds := [], cliSeqs := [],
         commands := [] } : ObjV)
    isplitl [Hfr Hpriv]
    · iapply exRun_join γ k γl γc ch c σ x e x.pv he hmy $$ [Hfr Hpriv]
      iframe Hfr; iexact Hpriv
    isplitr
    · ipureintro; exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, Or.inl rfl, rfl⟩
    isplitr
    · unfold objRep
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
      isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSlice_nil
      · iapply ownSlice_nil
    isplitr
    · unfold decObjOk
      ipureintro
      exact ⟨rfl, by unfold lenLedger at hs; exact hts, rfl⟩
    · unfold decJust
      iexists Sb
      iframe HSb
      ipureintro
      intro M hc hM hS
      have := hSb M hc hM hS .null
      rw [hb0] at this
      exact this bitDec_null
  · rw [hb0, decide_eq_true (by decide)]
    imod quorum_props γ k γl γc σ.t e he qln ⟨_, Nat.zero_le _, hqn⟩ $$ [Hsi Hqn] with
      ⟨%ents0, #Hlb, ⟨%h0, %hS0, %hl0, %hsnd⟩, #HF0, #Hos⟩
    · iframe Hsi Hqn
    have hne := objsOf_ne hcf hl0 hsnd
    obtain ⟨o, kk, hhead, hom, hkk, hmax⟩ := propHead_spec hne
    wp_auto
    slice_index_if
    wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
      word) $$ [Hsl] with Hsl2
    · iframe Hsl; ipureintro
      rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
      simp [he]
    wp_apply_core wp_propMajT_frozen D.majT γ k γl γc σ.t e he ents0 h0 hne $$ Hpl Hse Hsi Hlb
    rw [hhead]
    simp only [Option.map_some, Option.getD_some]
    have hkq : kk ≤ cf.q := by
      have := List.count_le_length (a := objId o) (l := (objsOf (tally ents0 0)).map objId)
      rw [List.length_map] at this
      have h2 : (objsOf (tally ents0 0)).length = cf.q := by
        rw [← hl0, ← List.length_map (f := Prod.snd), hsnd, List.length_map]
      omega
    wp_auto
    by_cases hmaj : kk ≥ cf.maj
    · rw [decide_eq_true (by word)]
      wp_auto
      slice_index_if
      wp_apply wp_load_slice_index ledger (sint.Z (W64 (uint.Z (W32 σ.t)))) _ _ e.loc (by
        word) $$ [Hsl] with Hsl2
      · iframe Hsl; ipureintro
        rw [show (sint.Z (W64 (uint.Z (W32 σ.t)))).toNat = σ.t by word]
        simp [he]
      wp_apply_core wp_propMajV_frozen D.majV γ k γl γc σ.t e he ents0 h0 hne
        $$ Hpl Hse Hsi Hlb
      rw [hhead]
      simp only [Option.map_some, Option.get!_some]
      iintro %v #Hv
      wp_auto
      ihave ⟨#Hoo, -⟩ := (BigSepL.bigSepL_mem
        (Φ := fun o : ObjV => iprop(objOk (GF := GF) γ cf o ∗ ⌜o.svrSeq.toNat = σ.t⌝)) hom) $$ Hos
      iapply HΦ
      iexists σ, { x with pv := x.pv }, DVal.obj (objId o), { o with svrSeq := W32 σ.t }
      isplitl [Hfr Hpriv]
      · iapply exRun_join γ k γl γc ch c σ x e x.pv he hmy $$ [Hfr Hpriv]
        iframe Hfr; iexact Hpriv
      isplitr
      · ipureintro; exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, Or.inl rfl, rfl⟩
      isplitr
      · iapply objRep_svrSeq v o (W32 σ.t) $$ Hv
      isplitr
      · unfold decObjOk
        isplitr
        · ipureintro; exact ⟨rfl, hts⟩
        · iapply objOk_svrSeq γ o (W32 σ.t) $$ Hoo
      · unfold decJust
        iexists Sb ++ propFacts σ.t (propPairs (tally ents0 0))
        isplitr
        · iapply BigSepL.bigSepL_append.2
          iframe HSb HF0
        · ipureintro
          intro M hc hM hS
          have hb := hSb M hc hM (fun kv hkv => hS kv (List.mem_append_left _ hkv))
            (.obj (objId o))
          rw [hb0] at hb
          apply hb
          apply bitDec_obj
          apply majProp_of hS0
            (propFacts_mem (fun kv hkv => hS kv (List.mem_append_right _ hkv)))
          rw [hsnd, ← hkk]; exact hmaj
    · rw [decide_eq_false (by word)]
      wp_auto
      ihave Hrun := exRun_join γ k γl γc ch c σ x e x.pv he hmy $$ [Hfr Hpriv]
      · iframe Hfr; iexact Hpriv
      wp_apply (hRPW σ { x with pv := x.pv } hq) $$ [$Hrun]
        as %v ⟨%σ', %x', %o', Hrun, %hst, #Hor, #Hook, #Hmp⟩
      · unfold exPre; iframe Hconf Hsh Hcfg
      unfold majPropW
      icases Hmp with ⟨%W, %hW, #HW⟩
      try wp_auto
      iapply HΦ
      iexists σ', x', DVal.obj (objId o'), o'
      iframe Hrun Hor
      isplitr
      · ipureintro; exact ⟨hst.1, hst.2.1, Or.inr hst.2.2.2.2, hst.2.2.1⟩
      isplitr
      · unfold decObjOk
        isplitr
        · ipureintro; exact ⟨rfl, hst.2.2.2.1⟩
        · iexact Hook
      · unfold decJust
        iexists Sb ++ W.map (fun X => (FKey.prop X σ.t, FVal.obj (objId o')))
        isplitr
        · iapply BigSepL.bigSepL_append.2
          iframe HSb
          rw [BigSepL.bigSepL_map]
          iexact HW
        · ipureintro
          intro M hc hM hS
          have hb := hSb M hc hM (fun kv hkv => hS kv (List.mem_append_left _ hkv))
            (.obj (objId o'))
          rw [hb0] at hb
          apply hb
          apply bitDec_obj
          refine ⟨W, hW.1, hW.2, fun X hX => ?_⟩
          exact hS _ (List.mem_append_right _
            (List.mem_map_of_mem (f := fun X => (FKey.prop X σ.t, FVal.obj (objId o'))) hX))

end find

end Perennial.rabia.roles.server.layers.consensus
