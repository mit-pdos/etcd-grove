module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Specs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Common
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Store
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.Log
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.CommitM
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Node.StoreLemmas

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace NodeP

/-- A response entry: (key, version, value). -/
abbrev PEnt := GoString × w64 × GoString

/-- One item appended to a response map. -/
def respStep (r : GMap GoString (List (GoString × w64))) (e : PEnt) :
    GMap GoString (List (GoString × w64)) :=
  <[e.1 := (r !! e.1).getD [] ++ [(e.2.2, e.2.1)]]> r

/-- The response map of a list of entries (`makePropagateResponse`). -/
def respOf (es : List PEnt) : GMap GoString (List (GoString × w64)) := es.foldl respStep ∅

theorem respOf_take_succ (es : List PEnt) (j : Nat) (e : PEnt) (h : es[j]? = some e) :
    respOf (es.take (j + 1)) = respStep (respOf (es.take j)) e := by
  unfold respOf
  rw [List.take_add_one, h]
  simp [List.foldl_append]

theorem respStep_lookup (r : GMap GoString (List (GoString × w64))) (e : PEnt) (k : GoString) :
    respStep r e !! k = if e.1 = k then some ((r !! e.1).getD [] ++ [(e.2.2, e.2.1)]) else r !! k := by
  unfold respStep; simp

theorem mem_fold_respStep (es : List PEnt) (r : GMap GoString (List (GoString × w64)))
    (k : GoString) (x : GoString) (v : w64) :
    (x, v) ∈ ((es.foldl respStep r) !! k).getD [] ↔ (x, v) ∈ (r !! k).getD [] ∨ (k, v, x) ∈ es := by
  induction es generalizing r with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons, ih, respStep_lookup, List.mem_cons]
    by_cases hk : e.1 = k
    · subst hk
      obtain ⟨k0, v0, x0⟩ := e
      simp only [↓reduceIte, Option.getD_some, List.mem_append, List.mem_singleton, Prod.mk.injEq,
        true_and, or_assoc, and_comm]
    · simp only [hk, ↓reduceIte]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl h
        · exact absurd (by rw [← h]) hk
        · exact Or.inr h

/-- Membership in the response: exactly the entries, by key. -/
theorem mem_respOf (es : List PEnt) (k : GoString) (x : GoString) (v : w64) :
    (x, v) ∈ ((respOf es) !! k).getD [] ↔ (k, v, x) ∈ es := by
  unfold respOf
  rw [mem_fold_respStep]
  simp

theorem isSome_fold_respStep (es : List PEnt) (r : GMap GoString (List (GoString × w64)))
    (k : GoString) :
    ((es.foldl respStep r) !! k).isSome ↔ (r !! k).isSome ∨ ∃ e ∈ es, e.1 = k := by
  induction es generalizing r with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons, ih, respStep_lookup, List.mem_cons]
    by_cases hk : e.1 = k
    · simp only [hk, ↓reduceIte, Option.isSome_some, true_or, true_iff]
      exact Or.inr ⟨e, Or.inl rfl, hk⟩
    · simp only [hk, ↓reduceIte]
      constructor
      · rintro (h | ⟨e', he', hk'⟩)
        · exact Or.inl h
        · exact Or.inr ⟨e', Or.inr he', hk'⟩
      · rintro (h | ⟨e', rfl | he', hk'⟩)
        · exact Or.inl h
        · exact absurd hk' hk
        · exact Or.inr ⟨e', he', hk'⟩

theorem respOf_isSome (es : List PEnt) (k : GoString) :
    ((respOf es) !! k).isSome ↔ ∃ e ∈ es, e.1 = k := by
  unfold respOf
  rw [isSome_fold_respStep]
  simp

section prop
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogHyp GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

instance itemPtr_persistent (p : Loc) (k : GoString) (v : w64) (x : GoString) :
    Persistent (itemPtr (hG := hG) p k v x) := by
  unfold itemPtr; infer_instance

/-- A response map's slice for key `k`, with its capacity (the loop's form of `respPtr`'s). -/
def respSl (resp : GMap GoString (List (GoString × w64))) (k : GoString) (sl : GoSlice) :
    IProp GF :=
  iprop(∃ vvs : List transport.ValueVersion, sl ↦* vvs ∗
    ownSliceCap transport.ValueVersion sl (DFrac.own 1) ∗
    ⌜vvs.map (·.Version') = ((resp !! k).getD []).map Prod.snd⌝ ∗
    [∗list] i ↦ vv ∈ vvs, ∃ x, ⌜(((resp !! k).getD [])[i]?).map Prod.fst = some x⌝ ∗
      vv.Value' ↦*□ x)

/-- The response map's entry for `e`'s key, and the way back after appending `e`. -/
theorem resp_step_acc (m : GMap GoString GoSlice) (r : GMap GoString (List (GoString × w64)))
    (e : PEnt) (Hdom : ∀ k, (m !! k).isSome ↔ (r !! k).isSome) :
    ([∗map] k ↦ s ∈ m, respSl (GF := GF) r k s) ⊢
      respSl r e.1 ((m !! e.1).getD slice.nil) ∗
      (∀ s', respSl (respStep r e) e.1 s' -∗
        [∗map] k ↦ s ∈ <[e.1 := s']> m, respSl (respStep r e) k s) := by
  have hrest : ∀ (m' : GMap GoString GoSlice), (∀ k, (m' !! k).isSome → k ≠ e.1) →
      ([∗map] k ↦ s ∈ m', respSl (GF := GF) r k s) ⊢
        [∗map] k ↦ s ∈ m', respSl (GF := GF) (respStep r e) k s := by
    intro m' hm'
    apply BI.BigSepM.bigSepM_mono
    intro k s hs
    have hk : k ≠ e.1 := hm' k (by
      show (m' !! k).isSome
      rw [show m' !! k = some s from hs]; rfl)
    unfold respSl
    rw [respStep_lookup, if_neg (Ne.symm hk)]
  cases hk : m !! e.1 with
  | some s0 =>
    simp only [Option.getD_some]
    refine (BI.BigSepM.bigSepM_delete (Φ := fun k s => respSl (GF := GF) r k s) hk).1.trans ?_
    iintro ⟨H0, Hrest⟩
    iframe H0
    iintro %s' Hs'
    iapply (BI.BigSepM.bigSepM_insert_delete (Φ := fun k s => respSl (GF := GF) (respStep r e) k s)).2
    iframe Hs'
    iapply hrest $$ Hrest
    intro k hks heq
    subst heq
    show False
    have : (GMap.delete e.1 m !! e.1).isSome := hks
    rw [GMap.lookup_delete] at this
    exact absurd this (by simp)
  | none =>
    have hr : r !! e.1 = none := by
      have := Hdom e.1
      rw [hk] at this
      cases h : r !! e.1 with
      | none => rfl
      | some _ => rw [h] at this; simp at this
    simp only [Option.getD_none]
    iintro Hm
    isplitr
    · unfold respSl
      iexists []
      isplitr; · iapply ownSlice_nil
      isplitr; · iapply ownSliceCap_nil
      isplitr; · ipureintro; simp [hr]
      iapply BI.BigSepL.bigSepL_nil_intro (P := iprop(True))
      itrivial
    iintro %s' Hs'
    iapply (BI.BigSepM.bigSepM_insert (Φ := fun k s => respSl (GF := GF) (respStep r e) k s) hk).2
    iframe Hs'
    iapply hrest $$ Hm
    intro k hks heq
    subst heq
    rw [hk] at hks
    exact absurd hks (by simp)

theorem wp_makePropagateResponse (sl : GoSlice) (ps : List Loc) (es : List PEnt) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node ∗ sl ↦* ps ∗
        ⌜ps.length = es.length⌝ ∗
        [∗list] i ↦ p ∈ ps, ∃ e : PEnt, ⌜es[i]? = some e⌝ ∗ itemPtr p e.1 e.2.1 e.2.2 }}
      (App (Val (@! node.makePropagateResponse)) (Val #sl))
    {{ (rp : Loc), RET #rp; respPtr rp (respOf es) }} := by
  wp_start as ⟨Hsl, %Hlen, #Hps⟩
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoSlice)) as %mp Hmp
  ihave %Hsllen := ownSlice_len $$ Hsl
  ihave IH : iprop(∃ (j : w64) (m : GMap GoString GoSlice) (it : Loc),
      "i" ∷ i_ptr ↦ j ∗ "item" ∷ item_ptr ↦ it ∗ "Hmp" ∷ mp ↦$ m ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (es.length : Int)⌝ ∗
      "%Hdom" ∷ ⌜∀ k, (m !! k).isSome ↔ ((respOf (es.take (sint.nat j))) !! k).isSome⌝ ∗
      "Hm" ∷ [∗map] k ↦ s ∈ m, respSl (respOf (es.take (sint.nat j))) k s) $$ [i item Hmp]
  · iexists W64 0, ∅, (zero_val Loc : Loc)
    iframe
    isplitr
    · ipureintro; exact ⟨by word, by word⟩
    isplitr
    · ipureintro; intro k
      have h0 : sint.nat (W64 0) = 0 := by word
      rw [h0]; simp [respOf]
    iapply BI.BigSepM.bigSepM_empty_intro (P := iprop(True))
    itrivial
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z sl.len := Hif
    simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len from ⟨Hj.1, Hlt⟩, _root_.and_self, ↓reduceIte]
    have Hjn : (sint.Z j).toNat < ps.length := by word
    obtain ⟨p, Hp⟩ : ∃ p, ps[(sint.Z j).toNat]? = some p := ⟨_, List.getElem?_eq_getElem Hjn⟩
    obtain ⟨e, He⟩ : ∃ e, es[(sint.Z j).toNat]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hjn)⟩
    wp_apply wp_load_slice_index sl (sint.Z j) ps (DFrac.own 1) p Hj.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hp
    ihave #Hpe := BI.BigSepL.bigSepL_lookup (Φ := fun i p => iprop(∃ e : PEnt, ⌜es[i]? = some e⌝ ∗
      itemPtr (hG := hG) p e.1 e.2.1 e.2.2)) Hp $$ Hps
    icases Hpe with ⟨%e', %He', #Hip⟩
    rw [He] at He'
    cases He'
    unfold itemPtr
    icases Hip with ⟨#Hk, #Hv, %vsl, #Hvsl, #Hx⟩
    ihave ⟨Hk0, Hback⟩ := resp_step_acc m (respOf (es.take (sint.nat j))) e Hdom $$ Hm
    wp_auto
    wp_apply wp_map_lookup1 $$ Hmp with Hmp
    unfold respSl
    icases Hk0 with ⟨%vvs, Hs0, Hcap0, %Hver, Hvals⟩
    rw [show (zero_val GoSlice) = slice.nil from rfl]
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hs0 $Hcap0 $Hsl1] as %s' ⟨Hs', Hcap', -⟩
    wp_apply wp_mapInsert $$ Hmp with Hmp
    wp_for_post
    have hsucc : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have He' : es[sint.nat j]? = some e := He
    have hstep := respOf_take_succ es (sint.nat j) e He'
    iframe
    iexists (j + W64 1), (<[e.1 := s']> m), p
    rw [hsucc, hstep]
    iframe
    isplitr
    · ipureintro
      have := Hsllen.1; rw [Hlen] at this
      constructor <;> word
    isplitr
    · ipureintro
      intro k
      rw [GMap.lookup_insert_eq_iff, respStep_lookup]
      by_cases hk : e.1 = k
      · simp [hk]
      · simp only [hk, ↓reduceIte]; exact Hdom k
    iapply Hback
    iexists (vvs ++ [{ Value' := vsl, Version' := e.2.1 }])
    iframe Hs' Hcap'
    have hlen : vvs.length = ((respOf (es.take (sint.nat j)) !! e.1).getD []).length := by
      have := congrArg List.length Hver; simpa using this
    rw [respStep_lookup, if_pos rfl]
    simp only [Option.getD_some]
    isplitr
    · ipureintro; simp [Hver]
    iapply (BI.BigSepL.bigSepL_append (Φ := fun i (vv : transport.ValueVersion) => iprop(∃ x, ⌜Option.map Prod.fst
      (((respOf (es.take (sint.nat j)) !! e.1).getD [] ++ [(e.2.2, e.2.1)])[i]?) = some x⌝ ∗
      vv.Value' ↦*□ x))).2
    isplitl [Hvals]
    · iapply BI.BigSepL.bigSepL_mono ?_ $$ Hvals
      intro i vv hi
      iintro ⟨%x, %hx, Hx⟩
      iexists x
      iframe Hx
      ipureintro
      have hi' : i < vvs.length := (List.getElem?_eq_some_iff.mp hi).1
      rw [List.getElem?_append_left (by omega)]
      exact hx
    · iapply (BI.BigSepL.bigSepL_singleton (Φ := fun i (vv : transport.ValueVersion) => iprop(∃ x, ⌜Option.map Prod.fst
        (((respOf (es.take (sint.nat j)) !! e.1).getD [] ++ [(e.2.2, e.2.1)])[i + vvs.length]?) =
          some x⌝ ∗ vv.Value' ↦*□ x))).2
      iexists e.2.2
      iframe Hx
      ipureintro
      rw [List.getElem?_append_right (by omega)]
      simp [hlen]
  · have hjl : sint.nat j = es.length := by
      have := Hsllen.1; rw [Hlen] at this; word
    rw [hjl, List.take_length] at Hdom ⊢
    iapply HΦ
    unfold respPtr
    iexists mp, m
    iframe
    isplitr
    · ipureintro; exact Hdom
    iapply BI.BigSepM.bigSepM_mono ?_ $$ Hm
    intro k s _
    unfold respSl
    iintro ⟨%vvs, Hs, -, %H1, H2⟩
    iexists vvs
    iframe
    ipureintro; exact H1

/-- Facts of a response's entries from facts of the entries. -/
theorem resp_facts (es : List PEnt) (Ψ : GoString → w64 → GoString → IProp GF)
    [∀ k v x, Persistent (Ψ k v x)] :
    (□ ∀ k v x, ⌜(k, v, x) ∈ es⌝ → Ψ k v x) ⊢
      [∗map] k ↦ vvs ∈ respOf es, [∗list] e ∈ vvs, Ψ k e.2 e.1 := by
  apply BI.BigSepM.bigSepM_intro
  intro k vvs hk
  apply BI.BigSepL.bigSepL_intro
  intro i e he
  have hmem : (e.1, e.2) ∈ ((respOf es) !! k).getD [] := by
    rw [show (respOf es) !! k = some vvs from hk]
    exact List.mem_of_getElem? he
  have := (mem_respOf es k e.1 e.2).1 hmem
  iintro #H
  iapply H
  ipureintro; exact this

theorem wp_FwdPropagate (HL : Laws (GF := GF)) (cfg : Cfg GF) (n : Loc) (a : GoString)
    (ptr : Loc) (dq : DFrac) (req : GMap GoString w64) (Φ : val → IProp GF) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node -∗
      isNode cfg n a -∗ reqPtr ptr dq req -∗
      ▷ (∀ (rp : Loc) (err : GoInterface), reqPtr ptr dq req -∗
          (⌜err = interface.nil⌝ ∗ (∃ resp, respPtr rp resp ∗ respItems cfg.γ resp) ∨ errNE err) -∗
          Φ (PairV #rp #err)) -∗
      WP (App (Val #(methods (go.GoType.PointerType node.Node.ty) go!"FwdPropagate" #n)) (Val #ptr))
        {{ Φ }} := by
  iintro #Hpkg #Hn Hreq HΦ
  unfold isNode isNodeDef nodeFields
  icases Hn with ⟨#Hctx, %Ha, -, %st, %γs, %nbM, %latM, %f, %lg, %ch, #Hst, #Hstore, #Htr, #Hfac,
    #Haddr, #Hpub, #Hcdra, #Hlog, #Hch, %Hch, #Hnb, #Hlat, #Hmu, #Hinv⟩
  ihave #Hstore' := Hstore
  iunfold isStore at Hstore'
  icases Hstore' with ⟨%e, %he, -⟩
  subst he
  unfold reqPtr
  icases Hreq with ⟨%mp, Hptr, Hmp⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply (wp_store_AllNewerDirty cfg a γs e mp req dq) $$ [$Hstore $Hinv $Hmp]
  iintro %sl %S0 Hmp Hsl #Hf
  wp_auto
  unfold itemsIn
  icases Hsl with ⟨%ps, %es, Hsl, %Hes, #Hps⟩
  wp_apply (wp_makePropagateResponse sl ps (es.map fun e => (e.1, e.2.1, e.2.2.1))) $$ [$Hsl]
  · isplitr
    · ipureintro; simp [Hes.1]
    iapply BI.BigSepL.bigSepL_mono ?_ $$ Hps
    intro i p _
    iintro ⟨%e', %he', #Hp⟩
    iexists (e'.1, e'.2.1, e'.2.2.1)
    iframe Hp
    ipureintro; simp [he']
  iintro %rp Hrp
  wp_auto
  iapply HΦ $$ [Hptr Hmp]
  · iexists mp; iframe
  ileft
  isplitr
  · ipureintro; rfl
  iexists _
  iframe Hrp
  unfold respItems
  iapply resp_facts _ (fun k v x => valsElem cfg.γ v k x)
  iintro !> %k %v %x %hmem
  simp only [List.mem_map] at hmem
  obtain ⟨e', he', heq⟩ := hmem
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  have h1 := (Hes.2 e' he').1
  ihave #Hfe := itemFacts_lookup cfg.γ S0 _ ((StoreS.mem_items S0 e'.1 _).1 h1) $$ Hf
  unfold itemFact
  icases Hfe with ⟨#Hv, -⟩
  iexact Hv

theorem wp_BackPropagate (HL : Laws (GF := GF)) (cfg : Cfg GF) (n : Loc) (a : GoString)
    (ptr : Loc) (dq : DFrac) (req : GMap GoString w64) (L : CLog) (Φ : val → IProp GF) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.despreston.go_craq.node -∗
      isNode cfg n a -∗ reqPtr ptr dq req -∗ covers cfg.γ a L -∗
      ▷ (∀ (rp : Loc) (err : GoInterface), reqPtr ptr dq req -∗
          (⌜err = interface.nil⌝ ∗ (∃ resp, respPtr rp resp ∗ respItems cfg.γ resp ∗
              respCommitted cfg.γ resp ∗ ⌜respCovers req resp L⌝) ∨ errNE err) -∗
          Φ (PairV #rp #err)) -∗
      WP (App (Val #(methods (go.GoType.PointerType node.Node.ty) go!"BackPropagate" #n)) (Val #ptr))
        {{ Φ }} := by
  iintro #Hpkg #Hn Hreq #Hcov HΦ
  unfold isNode isNodeDef nodeFields
  icases Hn with ⟨#Hctx, %Ha, -, %st, %γs, %nbM, %latM, %f, %lg, %ch, #Hst, #Hstore, #Htr, #Hfac,
    #Haddr, #Hpub, #Hcdra, #Hlog, #Hch, %Hch, #Hnb, #Hlat, #Hmu, #Hinv⟩
  ihave #Hstore' := Hstore
  iunfold isStore at Hstore'
  icases Hstore' with ⟨%e, %he, -⟩
  subst he
  unfold reqPtr
  icases Hreq with ⟨%mp, Hptr, Hmp⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply (wp_store_AllNewerCommitted HL cfg a γs e mp req dq L) $$ [$Hstore $Hinv $Hmp $Hcov]
  iintro %sl %S0 Hmp Hsl #Hf %Hbound
  wp_auto
  unfold newestIn
  icases Hsl with ⟨%ps, %es, Hsl, %Hes, #Hps⟩
  wp_apply (wp_makePropagateResponse sl ps es) $$ [$Hsl]
  · isplitr
    · ipureintro; exact Hes.1
    iexact Hps
  iintro %rp Hrp
  wp_auto
  iapply HΦ $$ [Hptr Hmp]
  · iexists mp; iframe
  ileft
  isplitr
  · ipureintro; rfl
  iexists _
  iframe Hrp
  have hfact : ∀ k v x, (k, v, x) ∈ es → (k, v, x, true) ∈ S0 := by
    intro k v x h
    exact (StoreS.mem_items S0 k _).1 (Hes.2.2.1 _ h).1
  isplitr
  · unfold respItems
    iapply resp_facts _ (fun k v x => valsElem cfg.γ v k x)
    iintro !> %k %v %x %hmem
    ihave #Hfe := itemFacts_lookup cfg.γ S0 _ (hfact k v x hmem) $$ Hf
    unfold itemFact
    icases Hfe with ⟨#Hv, -⟩
    iexact Hv
  isplitr
  · unfold respCommitted
    iapply resp_facts _ (fun k v _ => cvLb cfg.γ k v)
    iintro !> %k %v %x %hmem
    ihave #Hfe := itemFacts_lookup cfg.γ S0 _ (hfact k v x hmem) $$ Hf
    unfold itemFact
    icases Hfe with ⟨-, #Hc⟩
    simp only [↓reduceIte]
    iexact Hc
  ipureintro
  intro k hk
  obtain ⟨e', he', hek⟩ := Hes.2.2.2 k (by have := Hbound k; omega)
  refine ⟨e'.2.2, e'.2.1, ?_, ?_⟩
  · apply (mem_respOf es k _ _).2
    rw [← hek]; exact he'
  · rw [(Hes.2.2.1 e' he').2, hek]; exact Hbound k

end prop

end NodeP

end github_com.despreston.go_craq

end Perennial
