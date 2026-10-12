/-
The watchable store's lock invariant is fractional (`watchStoreInv_fractional`), as
`sync.init_RWMutex` needs (unit 3b's `newWatchableStore`): every part splits by fractions and two
parts agree on their witnesses. The watcher group's interval tree is fractional through the
tree's pending contract (`adt.ownIvt_split.spec`, a hypothesis until unit 4). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore
public import Spec.go_etcd_io.etcd.pkg.v3.adt.ownIvt_split

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ## Generic -/

include sem in
theorem loc_injW : ∀ v1 v2 : Loc, (#v1 : val) = #v2 → v1 = v2 :=
  fun _ _ h => go.intoVal_inj h

/-- An existential of fractional predicates whose witnesses agree is fractional. -/
theorem wFractional_exists {X : Type} (Φ : X → Qp → IProp GF) (hfrac : ∀ x, Fractional (Φ x))
    (hagree : ∀ x y q1 q2, Φ x q1 ∗ Φ y q2 ⊢ ⌜x = y⌝) :
    Fractional (fun q => iprop(∃ x, Φ x q)) where
  fractional p q := by
    constructor
    · iintro ⟨%x, H⟩
      icases ((hfrac x).fractional p q).1 $$ H with ⟨H1, H2⟩
      isplitl [H1]
      · iexists x; iexact H1
      · iexists x; iexact H2
    · refine (sep_exists_right.1).trans (exists_elim fun x => ?_)
      refine (sep_exists_left.1).trans (exists_elim fun y => ?_)
      refine (and_intro (hagree x y p q) .rfl).trans (pure_elim_left fun h => ?_)
      subst h
      exact ((hfrac x).fractional p q).2.trans (exists_intro (Ψ := fun x => Φ x (p + q)) x)

theorem wFractional_equiv {Φ Ψ : Qp → IProp GF} (h : ∀ q, Φ q ⊣⊢ Ψ q) (hΨ : Fractional Ψ) :
    Fractional Φ where
  fractional p q :=
    (h (p + q)).trans ((hΨ.fractional p q).trans (sep_congr (h p).symm (h q).symm))

theorem wFractional_sep {Φ Ψ : Qp → IProp GF} (hΦ : Fractional Φ) (hΨ : Fractional Ψ) :
    Fractional (fun q => iprop(Φ q ∗ Ψ q)) := by
  haveI := hΦ; haveI := hΨ; infer_instance

theorem wFractional_persistent (P : IProp GF) [Persistent P] : Fractional (fun _ : Qp => P) where
  fractional _ _ := ⟨persistent_sep_dup.1, sep_elim_left⟩

theorem wFractional_pure (φ : Prop) : Fractional (fun _ : Qp => (iprop(⌜φ⌝) : IProp GF)) :=
  wFractional_persistent _

theorem wFractional_bigSepM {K V : Type} [DecidableEq K] (m : GMap K V)
    (Φ : K → V → Qp → IProp GF) (h : ∀ k v, Fractional (Φ k v)) :
    Fractional (fun q => iprop([∗map] k ↦ v ∈ m, Φ k v q)) where
  fractional p q :=
    ⟨(BigSepM.bigSepM_mono fun _ => ((h _ _).fractional p q).1).trans
        (BiEntails.of_eq BigSepM.bigSepM_sep_eq).1,
      (BiEntails.of_eq BigSepM.bigSepM_sep_eq).2.trans
        (BigSepM.bigSepM_mono fun _ => ((h _ _).fractional p q).2)⟩

theorem wFractional_bigSepL {A : Type} (l : List A) (Φ : A → Qp → IProp GF)
    (h : ∀ a, Fractional (Φ a)) :
    Fractional (fun q => iprop([∗list] a ∈ l, Φ a q)) where
  fractional p q :=
    ⟨(BigSepL.bigSepL_mono fun _ => ((h _).fractional p q).1).trans BigSepL.bigSepL_sep_eqv.1,
      BigSepL.bigSepL_sep_eqv.2.trans (BigSepL.bigSepL_mono fun _ => ((h _).fractional p q).2)⟩

theorem wFractional_typed {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (l : Loc) (v : V) :
    Fractional (fun q => typedPointsto (GF := GF) l v (DFrac.own q)) :=
  fractional_of_dfractional (fun dq => typedPointsto l v dq)

theorem wFractional_half {Φ : Qp → IProp GF} (h : Fractional Φ) :
    Fractional (fun q => Φ q.half) where
  fractional p q := by rw [qp_half_add]; exact h.fractional p.half q.half

/-! ## Maps -/

theorem ownMap_fractionalW {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]
    (mref : Loc) (m : GMap K V) :
    Fractional (fun q : Qp => (ownMap (GF := GF) mref (DFrac.own q) m : IProp GF)) where
  fractional p q := by
    rw [ownMap_unseal]
    have hh := fun mv => (heapPointsto_fractional mref mv).fractional p q
    constructor
    · iintro H
      unfold ownMapDef
      iNamed H
      icases (hh mv).1 $$ Hown with ⟨H1, H2⟩
      isplitl [H1]
      · iexists mv, mp; simp only [named]; iframe H1; ipureintro; exact ⟨His_map, Hagree, Hdom, Hdefault⟩
      · iexists mv, mp; simp only [named]; iframe H2; ipureintro; exact ⟨His_map, Hagree, Hdom, Hdefault⟩
    · iintro ⟨H1, H2⟩
      unfold ownMapDef
      iNamedSuffix H1 "1"
      iNamedSuffix H2 "2"
      icombine Hown1 Hown2 gives % ⟨_, Hmv⟩
      subst Hmv
      iexists mv, mp
      simp only [named]
      isplitl [Hown1 Hown2]
      · iapply (hh mv).2; iframe
      ipureintro; exact ⟨His_map2, Hagree2, Hdom2, Hdefault2⟩

/-- Two parts of a map points-to agree on the map (for values whose Go values are injective). -/
theorem ownMap_agreeW {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]
    (hinj : ∀ v1 v2 : V, (#v1 : val) = #v2 → v1 = v2) (mref : Loc) (dq1 dq2 : DFrac)
    (m1 m2 : GMap K V) :
    (ownMap (GF := GF) mref dq1 m1 : IProp GF) ∗ ownMap mref dq2 m2 ⊢ ⌜m1 = m2⌝ := by
  rw [ownMap_unseal]
  unfold ownMapDef
  iintro ⟨H1, H2⟩
  iNamedSuffix H1 "1"
  iNamedSuffix H2 "2"
  icombine Hown1 Hown2 gives % ⟨_, Hmv⟩
  subst Hmv
  ipureintro
  apply GMap.ext
  intro k
  have e1 := Hagree1 k
  have e2 := Hagree2 k
  rw [← go.mapLookup_pure _ _ _ His_map1, go.mapLookup_pure _ _ _ His_map2] at e1
  rw [e1] at e2
  cases h1 : m1 !! k <;> cases h2 : m2 !! k <;> rw [h1, h2] at e2 <;> simp at e2
  all_goals first | rfl | rw [hinj _ _ e2]

theorem unit_inj : ∀ v1 v2 : Unit, (#v1 : val) = #v2 → v1 = v2 := fun _ _ _ => rfl


include sem in
theorem mkOk_watcherSet_inj {a b : GoMap}
    (h : (interface.mkOk watcherSet.ty #a : GoInterface) = interface.mkOk watcherSet.ty #b) :
    a = b := by
  unfold interface.mkOk at h
  simp only [GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at h
  exact go.intoVal_inj h

/-! ## The watcher group -/

variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem ownWatcherSet_fractional (m : GoMap) (S : GMap Loc Unit) :
    Fractional (fun q => ownWatcherSet (GF := GF) m S q) := by
  unfold ownWatcherSet; exact ownMapFrac' m S
where ownMapFrac' (m : GoMap) (S : GMap Loc Unit) :=
  ownMap_fractionalW (GF := GF) (K := Loc) (V := Unit) m S

theorem ownKeyMap_fractional (km : GoMap) (KM : GMap GoString GoMap) (W : GMap Loc WatchRange) :
    Fractional (fun q => ownKeyMap (GF := GF) km KM W q) := by
  unfold ownKeyMap
  refine wFractional_sep (ownMap_fractionalW km KM) (wFractional_sep (wFractional_pure _) ?_)
  exact wFractional_bigSepM KM _ (fun k m => ownWatcherSet_fractional m _)

theorem rangeSet_fractional (W : GMap Loc WatchRange) (z : adt.Entry) :
    Fractional (fun q => rangeSet (GF := GF) W z q) := by
  unfold rangeSet
  refine wFractional_exists (fun m q => iprop(⌜z.2 = interface.mkOk watcherSet.ty #m⌝ ∗
    ownWatcherSet m (ivlMembers W z.1) q)) (fun m => wFractional_sep (wFractional_pure _)
      (ownWatcherSet_fractional m _)) ?_
  intro x y q1 q2
  iintro ⟨⟨%h1, -⟩, ⟨%h2, -⟩⟩
  ipureintro
  exact mkOk_watcherSet_inj (sem := sem) (h1.symm.trans h2)

/-- The group's body at its witnesses. -/
def groupBody (wg : Loc) (W : GMap Loc WatchRange)
    (x : Loc × Loc × Loc × GMap GoString GoMap × List adt.Entry) (q : Qp) : IProp GF :=
  iprop(typedPointsto wg
      ({ keyWatchers' := x.1,
         ranges' := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.adt.intervalTree.ty) #x.2.2.1,
         watchers' := x.2.1 } : watcherGroup) (DFrac.own q) ∗
    ownWatcherSet x.2.1 (domSet W) q ∗
    ([∗map] w ↦ r ∈ W, ∃ fcs, watcherFixed w r fcs) ∗
    ownKeyMap x.1 x.2.2.2.1 W q ∗ adt.ownIvt (GF := GF) (hG := hG) (sem := sem) x.2.2.1 x.2.2.2.2 q ∗ ⌜RangesOk W x.2.2.2.2⌝ ∗
    [∗list] z ∈ x.2.2.2.2, rangeSet W z q)

theorem ownWatcherGroup_body (wg : Loc) (W : GMap Loc WatchRange) (q : Qp) :
    ownWatcherGroup (GF := GF) wg W q ⊣⊢ iprop(∃ x, groupBody wg W x q) := by
  constructor
  · iintro H
    unfold ownWatcherGroup
    icases H with ⟨%km, %ws, %t, %KM, %L, H⟩
    iNamed H
    iexists (km, ws, t, KM, L)
    unfold groupBody
    iframe
    iframe #
    ipureintro; exact HL
  · iintro ⟨%x, H⟩
    unfold groupBody
    icases H with ⟨Hwg, Hws, #Hfixed, Hkm, Hivt, %HL, Hranges⟩
    unfold ownWatcherGroup
    iexists x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2
    simp only [named]
    iframe
    iframe #
    ipureintro; exact HL

/-- **The group is fractional**, through the tree's pending fractionality. -/
theorem ownWatcherGroup_fractional (hsplit : adt.ownIvt_split.spec (GF := GF) (hG := hG))
    (wg : Loc) (W : GMap Loc WatchRange) : Fractional (fun q => ownWatcherGroup (GF := GF) wg W q) := by
  refine wFractional_equiv (ownWatcherGroup_body wg W) (wFractional_exists _ (fun x => ?_) ?_)
  · unfold groupBody
    refine wFractional_sep (wFractional_typed _ _) (wFractional_sep (ownWatcherSet_fractional _ _)
      (wFractional_sep (wFractional_persistent _) (wFractional_sep (ownKeyMap_fractional _ _ _)
        (wFractional_sep ⟨fun p q => hsplit.1 _ _ p q⟩ (wFractional_sep (wFractional_pure _)
          (wFractional_bigSepL _ _ (fun z => rangeSet_fractional W z)))))))
  · rintro ⟨a, b, c, d, e⟩ ⟨a', b', c', d', e'⟩ q1 q2
    unfold groupBody
    iintro ⟨⟨Hwg1, -, -, Hkm1, Hivt1, -⟩, ⟨Hwg2, -, -, Hkm2, Hivt2, -⟩⟩
    icombine Hwg1 Hwg2 gives %Heq
    simp only [watcherGroup.mk.injEq] at Heq
    obtain ⟨h1, h3, h2⟩ := Heq
    have h3' := mkOk_loc_inj _ h3
    subst h1 h2 h3'
    unfold ownKeyMap
    icases Hkm1 with ⟨Hkm1, -⟩
    icases Hkm2 with ⟨Hkm2, -⟩
    ihave %hKM := ownMap_agreeW (K := GoString) (V := GoMap) (loc_injW (sem := sem)) a _ _ _ _ $$ [Hkm1 Hkm2]
    · iframe
    ihave %hL := hsplit.2 _ _ _ _ _ $$ [Hivt1 Hivt2]
    · iframe
    ipureintro
    simp_all

/-! ## Batches and states -/

theorem watcherOwn_fractional (w : Loc) (st : WatcherSt) :
    Fractional (fun q => watcherOwn (GF := GF) w st q) := by
  unfold watcherOwn
  exact wFractional_sep (wFractional_typed _ _) (wFractional_sep (wFractional_typed _ _)
    (wFractional_sep (wFractional_typed _ _) (wFractional_sep (wFractional_typed _ _)
      (wFractional_typed _ _))))

theorem ownEventBatch_fractional (eb : Loc) (B : EventBatch) :
    Fractional (fun q => ownEventBatch (GF := GF) eb B q) := by
  have heq : ∀ q, ownEventBatch (GF := GF) eb B q ⊣⊢ iprop(∃ x : GoSlice × List Loc,
      typedPointsto eb ({ evs' := x.1, revs' := B.revs, moreRev' := B.moreRev } : eventBatch)
        (DFrac.own q) ∗
      ownSlice x.1 x.2 (DFrac.own q) ∗ ownSliceCap Loc x.1 (DFrac.own q) ∗
      ⌜x.2.length = B.evs.length⌝ ∗ [∗list] y ∈ x.2.zip B.evs, evIs y.1 y.2) := by
    intro q
    unfold ownEventBatch
    constructor
    · iintro ⟨%s, %ps, H⟩; iexists (s, ps); iexact H
    · iintro ⟨%x, H⟩; iexists x.1, x.2; iexact H
  refine wFractional_equiv heq (wFractional_exists _ (fun x => ?_) ?_)
  · exact wFractional_sep (wFractional_typed _ _) (wFractional_sep
      (fractional_of_dfractional (fun dq => ownSlice x.1 x.2 dq)) (wFractional_sep
        (fractional_of_dfractional (fun dq => ownSliceCap Loc x.1 dq))
        (wFractional_sep (wFractional_pure _) (wFractional_persistent _))))
  · rintro ⟨s1, ps1⟩ ⟨s2, ps2⟩ q1 q2
    iintro ⟨⟨H1, Hs1, -⟩, ⟨H2, Hs2, -⟩⟩
    icombine H1 H2 gives %Heq
    simp only [eventBatch.mk.injEq] at Heq
    obtain ⟨rfl, -⟩ := Heq
    ihave %Hps := ownSlice_agree _ _ _ _ _ $$ Hs1 Hs2
    ipureintro; simp only at Hps; rw [Hps]

theorem ownWatcherBatch_fractional (wb : GoMap) (Bm : GMap Loc EventBatch) :
    Fractional (fun q => ownWatcherBatch (GF := GF) wb Bm q) := by
  unfold ownWatcherBatch
  refine wFractional_exists _ (fun PB => ?_) ?_
  · exact wFractional_sep (ownMap_fractionalW _ _) (wFractional_sep (wFractional_pure _)
      (wFractional_bigSepM PB _ (fun _ p => wFractional_sep (wFractional_pure _)
        (ownEventBatch_fractional p.1 p.2))))
  · intro PB1 PB2 q1 q2
    iintro ⟨⟨Hm1, %Hb1, -⟩, ⟨Hm2, %Hb2, -⟩⟩
    ihave %Hf := ownMap_agreeW (K := Loc) (V := Loc) (loc_injW (sem := sem)) wb _ _ _ _ $$ [Hm1 Hm2]
    · iframe
    ipureintro
    apply GMap.ext
    intro k
    have h1 := congrArg (· !! k) Hf
    have h2 := congrArg (· !! k) (Hb1.symm.trans Hb2)
    simp only [GMap.lookup_fmap] at h1 h2
    cases e1 : PB1 !! k <;> cases e2 : PB2 !! k <;> rw [e1, e2] at h1 h2 <;> simp at h1 h2
    all_goals first | rfl | (rename_i a b; obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; simp_all)

/-! ## The lock invariant -/

theorem wFractional_ite (c : Prop) [Decidable c] {Φ Ψ : Qp → IProp GF} (h1 : Fractional Φ)
    (h2 : Fractional Ψ) : Fractional (fun q => if c then Φ q else Ψ q) := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact h1
  · simp only [hc, ↓reduceIte]; exact h2

theorem memberRes_fractional (γ : WsNames) (σ : WsState) (w : Loc) (st : WatcherSt) :
    Fractional (fun q => memberRes (GF := GF) γ q σ w st) := by
  have heq : ∀ q, memberRes (GF := GF) γ q σ w st ⊣⊢ iprop(∃ x : WatcherNames × WatchRange × GoSlice,
      ⌜σ.M !! w = some x.1⌝ ∗ watcherMeta γ w x.1 ∗ watcherFixed w x.2.1 x.2.2 ∗
      if σ.live w then
        watcherChan γ w x.1 st.ch ∗ filtersOk x.2.2 ∗ ⌜sint.Z x.2.1.startRev ≤ (x.1.lo : Int)⌝ ∗
        ∃ y : List EvM × Nat, ⌜σ.E !! w = some (y.1, y.2)⌝ ∗
          monoListAuthOwn x.1.evs q.half y.1 ∗ dghostVar x.1.live (DFrac.own q.half) true ∗
          popFacts γ σ w x.2.1 x.1.lo st y.1 y.2
      else cancelled x.1) := by
    intro q
    unfold memberRes
    constructor
    · iintro ⟨%γw, %r, %fcs, H⟩
      iexists (γw, r, fcs)
      icases H with ⟨%h, #Hm, #Hf, H⟩
      isplitr
      · ipureintro; exact h
      iframe Hm Hf
      by_cases hl : σ.live w
      · simp only [hl, ↓reduceIte]
        icases H with ⟨#Hc, #Ho, %hs, %evsw, %d, H⟩
        iframe Hc Ho
        isplitr
        · ipureintro; exact hs
        iexists (evsw, d)
        iexact H
      · simp only [hl, ↓reduceIte]; iexact H
    · iintro ⟨%x, H⟩
      iexists x.1, x.2.1, x.2.2
      icases H with ⟨%h, #Hm, #Hf, H⟩
      isplitr
      · ipureintro; exact h
      iframe Hm Hf
      by_cases hl : σ.live w
      · simp only [hl, ↓reduceIte]
        icases H with ⟨#Hc, #Ho, %hs, %y, H⟩
        iframe Hc Ho
        isplitr
        · ipureintro; exact hs
        iexists y.1, y.2
        iexact H
      · simp only [hl, ↓reduceIte]; iexact H
  refine wFractional_equiv heq (wFractional_exists _ (fun x => ?_) ?_)
  · refine wFractional_sep (wFractional_pure _) (wFractional_sep (wFractional_persistent _)
      (wFractional_sep (wFractional_persistent _) (wFractional_ite _ ?_ (wFractional_persistent _))))
    refine wFractional_sep (wFractional_persistent _) (wFractional_sep (wFractional_persistent _)
      (wFractional_sep (wFractional_pure _) (wFractional_exists _ (fun y => ?_) ?_)))
    · exact wFractional_sep (wFractional_pure _) (wFractional_sep
        (wFractional_half (monoListAuthOwn_fractional _ _))
        (wFractional_sep (wFractional_half (dghostVar_fractional _ _)) (wFractional_persistent _)))
    · intro y1 y2 q1 q2
      iintro ⟨⟨%h1, -⟩, ⟨%h2, -⟩⟩
      ipureintro
      rw [h1] at h2
      obtain ⟨a, b⟩ := y1; obtain ⟨c, d⟩ := y2
      simp_all
  · rintro ⟨γ1, r1, f1⟩ ⟨γ2, r2, f2⟩ q1 q2
    iintro ⟨⟨%h1, -, #Hf1, -⟩, ⟨%h2, -, #Hf2, -⟩⟩
    ihave %Hag := watcherFixed_agree w r1 r2 f1 f2 $$ [$Hf1 $Hf2]
    ipureintro
    rw [h1] at h2
    obtain ⟨rfl, rfl⟩ := Hag
    simp_all

theorem watchStoreBody_fractional (hsplit : adt.ownIvt_split.spec (GF := GF) (hG := hG))
    (s : Loc) (γ : WsNames) (σ : WsState) :
    Fractional (fun q => watchStoreBody (GF := GF) s γ q σ) := by
  unfold watchStoreBody
  simp only [named]
  exact wFractional_sep (ghostVar_fractional _ _) (wFractional_sep
    (wFractional_half (ghostVar_fractional _ _)) (wFractional_sep (wFractional_persistent _)
    (wFractional_sep (ownWatcherGroup_fractional hsplit _ _) (wFractional_sep
    (ownWatcherGroup_fractional hsplit _ _) (wFractional_sep (wFractional_typed _ _)
    (wFractional_sep (fractional_of_dfractional (fun dq => ownSlice σ.vs σ.vbs dq))
    (wFractional_sep (fractional_of_dfractional (fun dq => ownSliceCap GoMap σ.vs dq))
    (wFractional_sep (wFractional_pure _) (wFractional_sep
      (wFractional_bigSepL _ _ (fun x => ownWatcherBatch_fractional x.1 x.2)) (wFractional_sep
      (wFractional_bigSepM _ _ (fun w st => watcherOwn_fractional w st)) (wFractional_sep
      (wFractional_bigSepM _ _ (fun w st => wFractional_half (watcherOwn_fractional w st)))
      (wFractional_sep (ghostMapAuth_fractional _ _) (wFractional_sep (wFractional_persistent _)
      (wFractional_sep (wFractional_bigSepM _ _ (fun w st => memberRes_fractional γ σ w st))
      (wFractional_sep (wFractional_persistent _) (wFractional_pure _))))))))))))))))

/-- **The lock invariant is fractional** (through the tree's pending fractionality): two parts
agree on the state through `γ.wst`. -/
theorem watchStoreInv_fractional (hsplit : adt.ownIvt_split.spec (GF := GF) (hG := hG))
    (s : Loc) (γ : WsNames) : Fractional (watchStoreInv (GF := GF) s γ) := by
  unfold watchStoreInv
  refine wFractional_exists _ (fun σ => watchStoreBody_fractional hsplit s γ σ) ?_
  intro σ1 σ2 q1 q2
  unfold watchStoreBody
  iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
  ihave %H := ghostVar_valid_2 γ.wst _ _ _ _ $$ H1 H2
  ipureintro; exact H.2

end proof

end mvcc
end EtcdGrove
end Perennial
