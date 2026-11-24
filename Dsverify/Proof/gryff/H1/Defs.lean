/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/Defs.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1: shared definitions and the frozen specs it calls, restated in a section with one
`HeapGS` (hub request H2-R0 / H1-R1: the frozen sections also bind an unrelated
`GooseGlobalGS`, at which their WPs are stated).
-/
module

public import Dsverify.Proof.gryff.H1.Tag
public import Dsverify.GeneratedProof.gryff.examples.gryffnet
public import Dsverify.Proof.gryff.Lib.SortHyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB RecoveryInstance Proposal ReadOp WriteOp OngoingOp
  Msg Ev Ext Out Cmd Deps AMap StepRes)

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem amap_put_get {n : Nat} {V : Type} (m : model.AMap n V) (k k' : BitVec n) (v : V) :
    (m.put k v).get? k' = if k' = k then some v else m.get? k' := by
  unfold model.AMap.get?
  induction m with
  | nil =>
    simp only [model.AMap.put, List.lookup]
    by_cases h : k' = k
    · subst h; simp
    · have : (k' == k) = false := by simpa using h
      simp [this, h]
  | cons e t ih =>
    obtain ⟨a, b⟩ := e
    simp only [model.AMap.put]
    by_cases hka : k = a
    · subst hka
      simp only [↓reduceIte, List.lookup]
      by_cases h : k' = k
      · subst h; simp
      · have : (k' == k) = false := by simpa using h
        simp [this, h]
    · simp only [hka, ↓reduceIte]
      split
      · simp only [List.lookup]
        by_cases h : k' = k
        · subst h; simp
        · have : (k' == k) = false := by simpa using h
          simp only [this, h, ↓reduceIte]
      · simp only [List.lookup]
        rw [ih]
        by_cases h : k' = a
        · subst h
          have : k' ≠ k := fun h' => hka h'.symm
          simp [this]
        · have : (k' == a) = false := by simpa using h
          simp only [this]

theorem amap_del_get {n : Nat} {V : Type} (m : model.AMap n V) (k k' : BitVec n) :
    (m.del k).get? k' = if k' = k then none else m.get? k' := by
  unfold model.AMap.del model.AMap.get?
  induction m with
  | nil => simp [List.lookup]
  | cons e t ih =>
    obtain ⟨a, b⟩ := e
    by_cases hak : a = k
    · subst hak
      simp only [List.filter, bne_self_eq_false]
      rw [ih]
      by_cases h : k' = a
      · simp [h]
      · have h2 : (k' == a) = false := by simpa using h
        simp only [h, ite_false]; simp only [List.lookup, h2]
    · have h1 : (a != k) = true := by simpa using hak
      simp only [List.filter, h1, List.lookup]
      by_cases h : k' = a
      · subst h; simp [hak]
      · have h2 : (k' == a) = false := by simpa using h
        simp only [h2]; exact ih

theorem amap_del_get_self {n : Nat} {V : Type} (m : model.AMap n V) (k : BitVec n) :
    (m.del k).get? k = none := by
  rw [amap_del_get]; simp

theorem amap_del_get_ne {n : Nat} {V : Type} (m : model.AMap n V) (k k' : BitVec n) (h : k' ≠ k) :
    (m.del k).get? k' = m.get? k' := by
  rw [amap_del_get]; simp [h]


set_option hygiene false in
/-- Build a `[]interface{}` literal (`Printf`'s arguments) and forget it. -/
macro "wp_lit_drop" : tactic => `(tactic| (
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.InterfaceType [])))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.any) _ _
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %_sl ⟨-, -⟩
  wp_pures))

set_option hygiene false in
/-- A `Printf` call through an interface whose `Printf` spec is `H` (`specT True ...`). -/
macro "wp_printf " H:ident : tactic => `(tactic| (
  wp_lit_drop
  try (wp_load; wp_pures; wp_load)
  wp_apply $H:ident $$ %_ %_ as %_ ⟨%_, -⟩))

set_option hygiene false in
/-- A `Printf` call without arguments (`nil` slice). -/
macro "wp_printf0 " H:ident : tactic => `(tactic| (
  try (wp_load; wp_pures; wp_load)
  wp_apply $H:ident $$ %_ %_ as %_ ⟨%_, -⟩))

/-- A `stats` key's kind (`statsIntKey key` or `key ∈ statsMapKeys`) for a literal key. -/
macro "stats_key" : tactic => `(tactic| first
  | (left; simp only [statsIntKeys]; decide)
  | (simp only [statsMapKeys]; decide))

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF]
variable [sortA : SortSliceHyp GF]
variable [strconvA : strconv.Assumptions] -- N-5

/-! ## `stats` (the frozen specs, unproved: `statsOk` is a sealed slot and the frozen specs admit
any key, while `Max` / `Add` / `IncrementStrInt` type-assert the key's entry: H1-R5) -/
theorem StatsMap.Max.wp' (st : Loc) (key : GoString) (v : w64) (hk : statsIntKey key) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.stats ∗ statsOk st }}
      (App (App (Val (st @!! go.GoType.PointerType src.stats.StatsMap.ty @!! go!"Max"))
        (Val #key)) (Val #v))
    {{ (n : w64), RET #n; True }} :=
  StatsMap.Max.wp st key v hk

theorem StatsMap.Increment.wp' (st : Loc) (key : GoString) (hk : statsIntKey key) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.stats ∗ statsOk st }}
      (App (Val (st @!! go.GoType.PointerType src.stats.StatsMap.ty @!! go!"Increment"))
        (Val #key))
    {{ (n : w64), RET #n; True }} :=
  StatsMap.Increment.wp st key hk

theorem StatsMap.IncrementStrInt.wp' (st : Loc) (key : GoString) (idx : w64)
    (hk : key ∈ statsMapKeys) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.stats ∗ statsOk st }}
      (App (App (Val (st @!! go.GoType.PointerType src.stats.StatsMap.ty @!! go!"IncrementStrInt"))
        (Val #key)) (Val #idx))
    {{ (n : w64), RET #n; True }} :=
  StatsMap.IncrementStrInt.wp st key idx hk

/-! ## The participant's parts -/

/-- The participant's fixed fields (persistent). -/
def partiFix (pa : Loc) (ip : GoInterface) (k : Fin 3) (smR owR : Loc) : IProp GF :=
  iprop(pa.[src.gryffcommon.GryffParticipant, go!"id"] ↦□ rid32 k ∗
    pa.[src.gryffcommon.GryffParticipant, go!"iparti"] ↦□ ip ∗
    pa.[src.gryffcommon.GryffParticipant, go!"noConflicts"] ↦□ false ∗
    pa.[src.gryffcommon.GryffParticipant, go!"storeTag"] ↦□ smR ∗
    pa.[src.gryffcommon.GryffParticipant, go!"OngoingWrites"] ↦□ owR)

instance partiFix_persistent (pa : Loc) (ip : GoInterface) (k : Fin 3) (smR owR : Loc) :
    Persistent (partiFix (GF := GF) pa ip k smR owR) := by
  unfold partiFix; infer_instance

theorem partiFix_open (pa : Loc) (ip : GoInterface) (k : Fin 3) (smR owR : Loc) :
    partiFix (GF := GF) pa ip k smR owR ⊣⊢
      pa.[src.gryffcommon.GryffParticipant, go!"id"] ↦□ rid32 k ∗
      pa.[src.gryffcommon.GryffParticipant, go!"iparti"] ↦□ ip ∗
      pa.[src.gryffcommon.GryffParticipant, go!"noConflicts"] ↦□ false ∗
      pa.[src.gryffcommon.GryffParticipant, go!"storeTag"] ↦□ smR ∗
      pa.[src.gryffcommon.GryffParticipant, go!"OngoingWrites"] ↦□ owR := .rfl

/-- The store's tag map (`storeTag`) at tag `tag`. -/
def storeRep (sm : GMap w64 Loc) (tag : model.Tag) : IProp GF :=
  iprop(⌜∀ kk, kk ≠ W64 0 → sm.lookup kk = none⌝ ∗
    (match sm.lookup (W64 0) with
     | none => iprop(⌜tag = model.tag0⌝)
     | some md => iprop(∃ (tp : Loc) (gt : src.gryffproto.Tag),
        md ↦ (src.gryffcommon.StoreMetadata.mk tp) ∗ tp ↦□ gt ∗ ⌜tagOf gt = tag⌝)))

/-- A metadata struct `md` obtained from `GetStoreMetadata` stays readable: it is the store's
entry, or a private fresh one. -/
def mdAlive (sm : GMap w64 Loc) (md : Loc) : IProp GF :=
  iprop(⌜sm.lookup (W64 0) = some md⌝ ∨ ∃ (tp : Loc) (gt : src.gryffproto.Tag),
    md ↦ (src.gryffcommon.StoreMetadata.mk tp) ∗ tp ↦□ gt)

theorem mdAlive_mono (sm sm' : GMap w64 Loc) (md : Loc)
    (h : ∀ x, sm.lookup (W64 0) = some x → sm'.lookup (W64 0) = some x) :
    mdAlive (GF := GF) sm md ⊢ mdAlive sm' md := by
  unfold mdAlive
  iintro (%H | H)
  · ileft; ipureintro; exact h _ H
  · iright; iexact H

theorem mdAlive_read (sm : GMap w64 Loc) (md : Loc) (t : model.Tag) :
    storeRep (GF := GF) sm t ∗ mdAlive sm md ⊢ ∃ (tp : Loc) (gt : src.gryffproto.Tag),
      md ↦ (src.gryffcommon.StoreMetadata.mk tp) ∗ tp ↦□ gt ∗
      (md ↦ (src.gryffcommon.StoreMetadata.mk tp) -∗ storeRep sm t ∗ mdAlive sm md) := by
  unfold mdAlive storeRep
  iintro ⟨⟨%H0, Hm⟩, (%H | ⟨%tp, %gt, Hmd, #Htp⟩)⟩
  · rw [H]
    icases Hm with ⟨%tp, %gt, Hmd, #Htp, %Htag⟩
    iexists tp, gt
    iframe Hmd Htp
    iintro Hmd
    isplitl [Hmd]
    · isplitl []
      · ipureintro; exact H0
      iexists tp, gt
      iframe Hmd Htp
      ipureintro; exact Htag
    ileft; ipureintro; rfl
  · iexists tp, gt
    iframe Hmd Htp
    iintro Hmd
    isplitl [Hm]
    · isplitl []
      · ipureintro; exact H0
      iexact Hm
    iright; iexists tp, gt
    iframe Hmd Htp

/-- The ongoing writes (`OngoingWrites`) at `ong`. -/
def owRep (ow : GMap w32 Loc) (ong : AMap 32 w32) : IProp GF :=
  iprop(⌜∀ c, (ow.lookup c).isSome = (ong.get? c).isSome⌝ ∗
    [∗map] c ↦ op ∈ ow, ∃ (r : w32) (g : src.gryffcommon.OngoingWriteOp)
        (wm : src.gryffproto.Write1Proxied), ⌜ong.get? c = some r⌝ ∗ op ↦ g ∗
      g.Write1Proxied' ↦ wm ∗
      ⌜g.SentWrite1Reply' = true ∧ g.FastOverwite' = false ∧ wm.RequestId' = r ∧
        wm.ClientId' = c ∧ wm.K' = W64 0⌝)

/-- One entry of the ongoing writes. -/
def owEnt (ong : AMap 32 w32) (c : w32) (op : Loc) : IProp GF :=
  iprop(∃ (r : w32) (g : src.gryffcommon.OngoingWriteOp)
        (wm : src.gryffproto.Write1Proxied), ⌜ong.get? c = some r⌝ ∗ op ↦ g ∗
      g.Write1Proxied' ↦ wm ∗
      ⌜g.SentWrite1Reply' = true ∧ g.FastOverwite' = false ∧ wm.RequestId' = r ∧
        wm.ClientId' = c ∧ wm.K' = W64 0⌝)

/-- The ongoing writes' entries. -/
def owEntries (ow : GMap w32 Loc) (ong : AMap 32 w32) : IProp GF :=
  iprop([∗map] c ↦ op ∈ ow, owEnt ong c op)

theorem owEntries_del (ow : GMap w32 Loc) (ong : AMap 32 w32) (c : w32) :
    owEntries (GF := GF) ow ong ⊢ owEntries (GMap.delete c ow) (ong.del c) := by
  unfold owEntries owEnt
  cases hc : ow !! c with
  | none =>
    rw [GMap.delete_notin _ _ hc]
    refine BigSepM.bigSepM_mono (fun {k v} hk => ?_)
    have hne : k ≠ c := by
      intro he; subst he; change ow !! k = some v at hk; rw [hc] at hk; cases hk
    iintro ⟨%r, %g, %wm, %Hr, H⟩
    iexists r, g, wm
    iframe H
    ipureintro; rw [amap_del_get_ne _ _ _ hne]; exact Hr
  | some x =>
    refine (BigSepM.bigSepM_delete (M := GMap w32) (i := c) (x := x) hc).1.trans ?_
    refine BI.sep_elim_right.trans ?_
    refine BigSepM.bigSepM_mono (fun {k v} hk => ?_)
    have hne : k ≠ c := by
      intro he; subst he
      change (GMap.delete k ow) !! k = some v at hk; rw [GMap.lookup_delete] at hk; cases hk
    iintro ⟨%r, %g, %wm, %Hr, H⟩
    iexists r, g, wm
    iframe H
    ipureintro; rw [amap_del_get_ne _ _ _ hne]; exact Hr

/-- One ongoing write (client `c`, request `r`) at `op`. -/
def owE (c r : w32) (op : Loc) : IProp GF :=
  iprop(∃ (g : src.gryffcommon.OngoingWriteOp) (wm : src.gryffproto.Write1Proxied), op ↦ g ∗
    g.Write1Proxied' ↦ wm ∗
    ⌜g.SentWrite1Reply' = true ∧ g.FastOverwite' = false ∧ wm.RequestId' = r ∧
      wm.ClientId' = c ∧ wm.K' = W64 0⌝)

/-- Take client `c`'s entry out. -/
theorem owEntries_take (ow : GMap w32 Loc) (ong : AMap 32 w32) (c : w32) :
    owEntries ow ong ⊢ owEntries (GMap.delete c ow) ong ∗
      (match ow !! c with
       | none => iprop(True)
       | some op => iprop(∃ r, ⌜ong.get? c = some r⌝ ∗ owE (GF := GF) c r op)) := by
  unfold owEntries owEnt
  cases hc : ow !! c with
  | none =>
    rw [GMap.delete_notin _ _ hc]
    iintro H; iframe H
  | some x =>
    refine (BigSepM.bigSepM_delete (M := GMap w32) (i := c) (x := x) hc).1.trans ?_
    unfold owE
    iintro ⟨⟨%r, %g, %wm, %Hr, H⟩, Hrest⟩
    iframe Hrest
    iexists r
    isplitl []
    · ipureintro; exact Hr
    iexists g, wm; iexact H

/-- Put client `c`'s entry (request `r`) back. -/
theorem owEntries_put (ow : GMap w32 Loc) (ong : AMap 32 w32) (c r : w32) (op : Loc) :
    owEntries (GMap.delete c ow) ong ∗ owE (GF := GF) c r op ⊢
      owEntries (<[c := op]> ow) (ong.put c r) := by
  unfold owEntries
  have Hm : ([∗map] c' ↦ op' ∈ GMap.delete c ow, owEnt (GF := GF) ong c' op') ⊢
      ([∗map] c' ↦ op' ∈ GMap.delete c ow, owEnt (ong.put c r) c' op') :=
    BigSepM.bigSepM_mono (M := GMap w32) (fun {k v} hk => by
      have hne : k ≠ c := by
        intro he; subst he
        change (GMap.delete k ow) !! k = some v at hk; rw [GMap.lookup_delete] at hk; cases hk
      unfold owEnt
      iintro ⟨%r', %g, %wm, %Hr, H⟩
      iexists r', g, wm
      iframe H
      ipureintro; rw [amap_put_get]; simp [hne, Hr])
  iintro ⟨Hrest, H⟩
  iapply (BigSepM.bigSepM_insert_delete (M := GMap w32) (m := ow) (i := c) (x := op)
    (Φ := fun c' op' => owEnt (ong.put c r) c' op')).2
  isplitl [H]
  · unfold owE owEnt
    icases H with ⟨%g, %wm, H⟩
    iexists r, g, wm
    iframe H
    ipureintro; rw [amap_put_get]; simp
  iapply Hm $$ Hrest

theorem owEntries_congr (ow : GMap w32 Loc) (ong ong' : AMap 32 w32)
    (h : ∀ c, ong.get? c = ong'.get? c) : owEntries (GF := GF) ow ong ⊢ owEntries ow ong' := by
  unfold owEntries owEnt
  refine BigSepM.bigSepM_mono (fun {k v} _ => ?_)
  iintro ⟨%r, %g, %wm, %Hr, H⟩
  iexists r, g, wm
  iframe H
  ipureintro; rw [← h]; exact Hr

/-- Put back an entry taken by `owEntries_take` (unchanged). -/
theorem owEntries_restore (ow : GMap w32 Loc) (ong : AMap 32 w32) (c r : w32) (op : Loc)
    (hc : ow !! c = some op) (hr : ong.get? c = some r) :
    owEntries (GMap.delete c ow) ong ∗ owE (GF := GF) c r op ⊢ owEntries ow ong := by
  refine (owEntries_put ow ong c r op).trans ?_
  rw [GMap.insert_id _ _ _ hc]
  refine owEntries_congr _ _ _ (fun c' => ?_)
  rw [amap_put_get]
  by_cases h : c' = c
  · subst h; simp [hr]
  · simp [h]

theorem owRep_eq (ow : GMap w32 Loc) (ong : AMap 32 w32) :
    owRep (GF := GF) ow ong = iprop(⌜∀ c, (ow.lookup c).isSome = (ong.get? c).isSome⌝ ∗ owEntries ow ong) :=
  rfl

theorem owRep_del (ow : GMap w32 Loc) (ong : AMap 32 w32) (c : w32) :
    owRep (GF := GF) ow ong ⊢ owRep (GMap.delete c ow) (ong.del c) := by
  rw [owRep_eq, owRep_eq]
  iintro ⟨%Hdom, Hws⟩
  isplitl []
  · ipureintro; intro c'
    by_cases h : c' = c
    · subst h; rw [GMap.lookup_delete, amap_del_get_self]; rfl
    · rw [GMap.lookup_delete_ne _ (Ne.symm h), amap_del_get_ne _ _ _ h]; exact Hdom c'
  iapply owEntries_del $$ Hws

theorem partiOwn_open (pa : Loc) (ip : GoInterface) (k : Fin 3) (tag : model.Tag)
    (ong : AMap 32 w32) :
    partiOwn (GF := GF) pa ip k tag ong ⊣⊢ ∃ (smR owR : Loc) (sm : GMap w64 Loc) (ow : GMap w32 Loc),
      partiFix pa ip k smR owR ∗ smR ↦$ sm ∗ owR ↦$ ow ∗ storeRep sm tag ∗ owRep ow ong := by
  unfold partiOwn partiFix storeRep owRep
  constructor
  · iintro ⟨%smR, %owR, %sm, %ow, #H1, #H2, #H3, #H4, #H5, Hsm, How, %H6, Hm, %H7, Hws⟩
    iexists smR, owR, sm, ow
    iframe H1 H2 H3 H4 H5 Hsm How Hm Hws
    ipureintro; exact ⟨H6, H7⟩
  · iintro ⟨%smR, %owR, %sm, %ow, ⟨#H1, #H2, #H3, #H4, #H5⟩, Hsm, How, ⟨%H6, Hm⟩, %H7, Hws⟩
    iexists smR, owR, sm, ow
    iframe H1 H2 H3 H4 H5 Hsm How Hm Hws
    ipureintro; exact ⟨H6, H7⟩

/-- A `StoreMetadata` struct as its one field, with the way back. -/
theorem storeMeta_acc (md tp : Loc) :
    (md ↦ (src.gryffcommon.StoreMetadata.mk tp) : IProp GF) ⊢
      md.[src.gryffcommon.StoreMetadata, go!"Tag"] ↦ tp ∗
      (∀ tp' : Loc, md.[src.gryffcommon.StoreMetadata, go!"Tag"] ↦ tp' -∗
        md ↦ (src.gryffcommon.StoreMetadata.mk tp')) := by
  iintro H
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ H
  iStructNamed H
  iframe Tag
  iintro %tp' H'
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe H'

instance (priority := high) ipartiOk_persistent' (ip : GoInterface) (V : w64 → IProp GF) :
    Persistent (ipartiOk ip V) := by
  unfold ipartiOk specT; infer_instance

/-- `ipartiOk`'s parts. -/
theorem ipartiOk_open (ip : GoInterface) (V : w64 → IProp GF) :
    ipartiOk ip V ⊣⊢
    (∀ v : w64, specT iprop(V v) (App (icall src.gryffcommon.IGryffParticipant.ty go!"GetCurrentValue" ip) (Val #(W64 0))) (fun ret => iprop(⌜ret = #v⌝ ∗ V v))) ∗
    (∀ (v : w64) (v' : w64), specT iprop(V v) (App (App (icall src.gryffcommon.IGryffParticipant.ty go!"SetCurrentValue" ip)
        (Val #(W64 0))) (Val #v')) (fun ret => iprop(⌜ret = #()⌝ ∗ V v'))) ∗
    (∀ (f : GoString) (a : GoSlice), specT iprop(True) (App (App (icall src.gryffcommon.IGryffParticipant.ty go!"Printf" ip) (Val #f)) (Val #a)) (fun ret => iprop(⌜ret = #()⌝ ∗ True))) ∗
    specT iprop(True) (App (icall src.gryffcommon.IGryffParticipant.ty go!"GetStats" ip) (Val #())) (fun ret => iprop(∃ st : Loc, ⌜ret = #st⌝ ∗ statsOk st)) ∗
    (∀ (c : w32) (w : Loc), specT iprop(False) (App (App (icall src.gryffcommon.IGryffParticipant.ty go!"HandleWrite1Overwrite" ip)
        (Val #c)) (Val #w)) (fun ret => iprop(⌜ret = #()⌝ ∗ True))) ∗
    (∀ w : Loc, specT iprop(False) (App (icall src.gryffcommon.IGryffParticipant.ty go!"SendWrite1Timeout" ip) (Val #w)) (fun ret => iprop(⌜ret = #()⌝ ∗ True))) := by
  unfold ipartiOk; exact .rfl

end

end Perennial.gryff.replica2
