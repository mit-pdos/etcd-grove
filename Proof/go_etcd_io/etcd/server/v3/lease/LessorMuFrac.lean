/-
**`le.mu`'s resource is fractional** (prove-ps2-newlessor3, 2026-11-21): `lessorMu lp γl` is a
`Fractional` family, what `sync.init_RWMutex` takes to make `le.mu`'s reader slots (`newLessor`). The
split direction is the pieces' fractions; the combine direction needs every existential of the two
shares to agree: the fields' and maps' values (their points-to agree), the live set (`leaseFrag`'s
element), the names (the ghost map's authority, `lessorGhost`; the pins), the history (its
authority), the checkpoint heap's items (its slice and its items' read-only ids). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.NotifCell

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lease

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease

section frac
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem pt_frac {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) (q1 q2 : Qp) :
    (l ↦{DFrac.own (q1 + q2)} v : IProp GF) ⊣⊢ l ↦{DFrac.own q1} v ∗ l ↦{DFrac.own q2} v :=
  (typedPointsto_dfractional (GF := GF) l v).dfractional (DFrac.own q1) (DFrac.own q2)

theorem pt_frac_half {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) (q1 q2 : Qp) :
    (l ↦{DFrac.own (q1 + q2).half} v : IProp GF) ⊣⊢
      l ↦{DFrac.own q1.half} v ∗ l ↦{DFrac.own q2.half} v := by
  rw [Qp_half_add]; exact pt_frac l v _ _

theorem map_frac {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]
    (m : Loc) (A : GMap K V) (q1 q2 : Qp) :
    (ownMap (GF := GF) m (DFrac.own (q1 + q2)) A : IProp GF) ⊣⊢
      ownMap m (DFrac.own q1) A ∗ ownMap m (DFrac.own q2) A :=
  (ownMap_fractional (GF := GF) m A).fractional q1 q2

theorem map_frac_half {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]
    (m : Loc) (A : GMap K V) (q1 q2 : Qp) :
    (ownMap (GF := GF) m (DFrac.own (q1 + q2).half) A : IProp GF) ⊣⊢
      ownMap m (DFrac.own q1.half) A ∗ ownMap m (DFrac.own q2.half) A := by
  rw [Qp_half_add]; exact map_frac m A _ _

theorem keep_pure {P : IProp GF} {φ : Prop} (h : P ⊢ ⌜φ⌝) : P ⊢ ⌜φ⌝ ∗ P :=
  (and_intro h .rfl).trans persistent_and_sep_mp

theorem ownMap_agree_k {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]
    [go.IntoValInj V] (m : Loc) (dq1 dq2 : DFrac) (A B : GMap K V) :
    ownMap (GF := GF) m dq1 A ∗ ownMap m dq2 B ⊢ ⌜A = B⌝ ∗ ownMap m dq1 A ∗ ownMap m dq2 B :=
  keep_pure (ownMap_agree m dq1 dq2 A B)

theorem ghostMapAuth_agree_k {K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V]
    (γ : GName) (q1 q2 : Qp) (A B : GMap K V) :
    ghostMapAuth (GF := GF) γ q1 A ∗ ghostMapAuth γ q2 B ⊢
      ⌜A = B⌝ ∗ ghostMapAuth γ q1 A ∗ ghostMapAuth γ q2 B :=
  keep_pure (by iintro ⟨H1, H2⟩; iapply ghostMapAuth_agree γ q1 q2 A B $$ H1 H2)

theorem monoListAuthOwn_agree_k {A : Type} [Pos.Countable A] (γ : GName) (q1 q2 : Qp) (l1 l2 : List A) :
    monoListAuthOwn (GF := GF) γ q1 l1 ∗ monoListAuthOwn γ q2 l2 ⊢
      ⌜l1 = l2⌝ ∗ monoListAuthOwn γ q1 l1 ∗ monoListAuthOwn γ q2 l2 :=
  keep_pure (by
    iintro ⟨H1, H2⟩
    ihave %H := monoListAuthOwn_agree γ q1 q2 l1 l2 $$ H1 H2
    ipureintro; exact H.2)

/-- A queue item's share. -/
instance lwtAt_fractional (p : Loc) (id k : w64) : Fractional (fun q => lwtAt (GF := GF) p id k q) where
  fractional q1 q2 := by
    unfold lwtAt
    refine ⟨?_, ?_⟩
    · iintro ⟨#Hid, ⟨%t, Ht⟩, Hk⟩
      icases (pt_frac _ t q1 q2).1 $$ Ht with ⟨Ht1, Ht2⟩
      icases (pt_frac _ k q1 q2).1 $$ Hk with ⟨Hk1, Hk2⟩
      isplitl [Ht1 Hk1]
      · iframe Hid Hk1; iexists t; iexact Ht1
      · iframe Hid Hk2; iexists t; iexact Ht2
    · iintro ⟨⟨#Hid, ⟨%t1, Ht1⟩, Hk1⟩, ⟨-, ⟨%t2, Ht2⟩, Hk2⟩⟩
      icombine Ht1 Ht2 gives %He
      subst He
      iframe Hid
      isplitl [Ht1 Ht2]
      · iexists t1; iapply (pt_frac _ t1 q1 q2).2; iframe
      iapply (pt_frac _ k q1 q2).2; iframe

/-- A queue's share, at its items. -/
instance queueAt_fractional (s : GoSlice) (xs : List (Loc × w64)) :
    Fractional (fun q => queueAt (GF := GF) s xs q) where
  fractional q1 q2 := by
    unfold queueAt
    have hc := (ownSliceCap_dfractional (GF := GF) (V := Loc) s).dfractional (DFrac.own q1) (DFrac.own q2)
    rw [DFrac.op_own] at hc
    have hs := (ownSlice_fractional (GF := GF) s (xs.map Prod.fst)).fractional q1 q2
    have hl := (fractional_bigSepL (PROP := IProp GF) (l := xs)
      (Ψ := fun k x q => lwtAt (GF := GF) x.1 x.2 (W64 k) q)).fractional q1 q2
    refine ⟨?_, ?_⟩
    · iintro ⟨Hs, Hc, Hl⟩
      icases hs.1 $$ Hs with ⟨Hs1, Hs2⟩
      icases hc.1 $$ Hc with ⟨Hc1, Hc2⟩
      icases hl.1 $$ Hl with ⟨Hl1, Hl2⟩
      isplitl [Hs1 Hc1 Hl1]
      · iframe
      · iframe
    · iintro ⟨⟨Hs1, Hc1, Hl1⟩, ⟨Hs2, Hc2, Hl2⟩⟩
      isplitl [Hs1 Hs2]
      · iapply hs.2; iframe
      isplitl [Hc1 Hc2]
      · iapply hc.2; iframe
      iapply hl.2; iframe

/-- A queue's items' read-only ids. -/
theorem lwts_ids (xs : List (Loc × w64)) (q : Qp) :
    ([∗list] k ↦ x ∈ xs, lwtAt (GF := GF) x.1 x.2 (W64 k) q) ⊢
      ([∗list] k ↦ x ∈ xs, lwtAt (GF := GF) x.1 x.2 (W64 k) q) ∗
        [∗list] x ∈ xs, lwF go!"id" x.1 ↦□ x.2 := by
  refine (BigSepL.bigSepL_mono_of_forall (Ψ := fun k x =>
    iprop(lwtAt (GF := GF) x.1 x.2 (W64 k) q ∗ lwF go!"id" x.1 ↦□ x.2)) ?_).trans
    BigSepL.bigSepL_sep_eqv.1
  intro k x
  iintro H
  (try iunfold lwtAt at H)
  icases H with ⟨#Hid, Ht, Hk⟩
  (try iunfold lwtAt)
  iframe Hid Ht Hk

/-- Two lists of items at the same pointers, each item's id read-only, are equal. -/
theorem ids_agree (xs ys : List (Loc × w64)) (h : xs.map Prod.fst = ys.map Prod.fst) :
    ([∗list] x ∈ xs, (lwF go!"id" x.1 ↦□ x.2 : IProp GF)) ∗
      ([∗list] x ∈ ys, (lwF go!"id" x.1 ↦□ x.2 : IProp GF)) ⊢ ⌜xs = ys⌝ := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => iintro -; ipureintro; rfl
    | cons y ys => simp at h
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      iintro ⟨H1, H2⟩
      icases BigSepL.bigSepL_cons.1 $$ H1 with ⟨Hx, H1⟩
      icases BigSepL.bigSepL_cons.1 $$ H2 with ⟨Hy, H2⟩
      rw [h1]
      icombine Hx Hy gives %Hid
      ihave %Hr := ih ys h2 $$ [$H1 $H2]
      ipureintro
      rw [Hr, show x = y from Prod.ext h1 Hid]

/-- Two shares of a queue at the same slice agree on its items. -/
theorem queueAt_agree (s : GoSlice) (xs ys : List (Loc × w64)) (q1 q2 : Qp) :
    queueAt (GF := GF) s xs q1 ∗ queueAt s ys q2 ⊢ ⌜xs = ys⌝ ∗ queueAt s xs q1 ∗ queueAt s ys q2 := by
  unfold queueAt
  iintro ⟨⟨Hs1, Hc1, Hl1⟩, ⟨Hs2, Hc2, Hl2⟩⟩
  icombine Hs1 Hs2 gives %Hf
  icases lwts_ids xs q1 $$ Hl1 with ⟨Hl1, Hi1⟩
  icases lwts_ids ys q2 $$ Hl2 with ⟨Hl2, Hi2⟩
  ihave %Hxy := ids_agree xs ys Hf $$ [$Hi1 $Hi2]
  iframe
  ipureintro; exact Hxy

/-- A lease's state under `le.mu`. -/
instance leaseMeta_fractional (id : w64) (l : Loc) : Fractional (fun q => leaseMeta (GF := GF) id l q) where
  fractional q1 q2 := by
    unfold leaseMeta
    refine ⟨?_, ?_⟩
    · iintro ⟨#Hid, #Ht, #Hc, ⟨%r, Hr⟩, ⟨%e, He⟩, #Hg⟩
      icases (pt_frac _ r q1 q2).1 $$ Hr with ⟨Hr1, Hr2⟩
      icases (pt_frac_half _ e q1 q2).1 $$ He with ⟨He1, He2⟩
      isplitl [Hr1 He1]
      · iframe Hid Ht Hc Hg; isplitl [Hr1]; · iexists r; iexact Hr1
        iexists e; iexact He1
      · iframe Hid Ht Hc Hg; isplitl [Hr2]; · iexists r; iexact Hr2
        iexists e; iexact He2
    · iintro ⟨⟨#Hid, #Ht, #Hc, ⟨%r1, Hr1⟩, ⟨%e1, He1⟩, #Hg⟩, ⟨-, -, -, ⟨%r2, Hr2⟩, ⟨%e2, He2⟩, -⟩⟩
      icombine Hr1 Hr2 gives %Hr
      icombine He1 He2 gives %He
      subst Hr He
      iframe Hid Ht Hc Hg
      isplitl [Hr1 Hr2]
      · iexists r1; iapply (pt_frac _ r1 q1 q2).2; iframe
      iexists e1; iapply (pt_frac_half _ e1 q1 q2).2; iframe

/-- `le.mu`'s share of the expiry notifier's cell. -/
instance notifShare_fractional (lp : Loc) (γl : GName) : Fractional (fun q => notifShare (GF := GF) lp γl q) where
  fractional q1 q2 := by
    unfold notifShare
    refine ⟨?_, ?_⟩
    · iintro ⟨%γr, #Hp, Hx, #Hi⟩
      icases (ghostVar_split _ () q1 q2) $$ Hx with ⟨Hx1, Hx2⟩
      isplitl [Hx1]
      · iexists γr; iframe Hp Hx1 Hi
      · iexists γr; iframe Hp Hx2 Hi
    · iintro ⟨⟨%γr, #Hp, Hx1, #Hi⟩, ⟨%γr', #Hp', Hx2, -⟩⟩
      ihave %Hγ := lessorPinR_agree γl γr γr' $$ [$Hp $Hp']
      subst Hγ
      iexists γr
      iframe Hp Hi
      iapply ((ghostVar_fractional (GF := GF) _ ()).fractional q1 q2).2
      iframe

/-- `le.mu`'s share of `demotec`'s variable. -/
instance demoteTie_fractional (γl : GName) (dc : GoChan) : Fractional (fun q => demoteTie (GF := GF) γl q dc) where
  fractional q1 q2 := by
    unfold demoteTie
    refine ⟨?_, ?_⟩
    · iintro ⟨%γr, #Hp, Hx, #Hi⟩
      icases ((ghostVar_half_fractional (GF := GF) _ dc).fractional q1 q2).1 $$ Hx with ⟨Hx1, Hx2⟩
      isplitl [Hx1]
      · iexists γr; iframe Hp Hx1 Hi
      · iexists γr; iframe Hp Hx2 Hi
    · iintro ⟨⟨%γr, #Hp, Hx1, #Hi⟩, ⟨%γr', #Hp', Hx2, -⟩⟩
      ihave %Hγ := lessorPinR_agree γl γr γr' $$ [$Hp $Hp']
      subst Hγ
      iexists γr
      iframe Hp Hi
      iapply ((ghostVar_half_fractional (GF := GF) _ dc).fractional q1 q2).2
      iframe

/-- The lessor's apply-side fields. -/
instance lessorExtra_fractional (lp : Loc) (γl : GName) (M : GMap w64 Loc) :
    Fractional (fun q => lessorExtra (GF := GF) lp γl M q) where
  fractional q1 q2 := by
    unfold lessorExtra
    have hm := (fractional_bigSepM (PROP := IProp GF) (m := M)
      (Ψ := fun id l q => leaseMeta (GF := GF) id l q)).fractional q1 q2
    refine ⟨?_, ?_⟩
    · iintro ⟨%dc, %np, %h, %hx, %b, Hdc, Hnp, Hns, Hh, Hq, Hcp, Hm, Hb, Hdt, #Hs⟩
      icases (pt_frac _ dc q1 q2).1 $$ Hdc with ⟨Hdc1, Hdc2⟩
      icases (pt_frac_half _ np q1 q2).1 $$ Hnp with ⟨Hnp1, Hnp2⟩
      icases ((notifShare_fractional lp γl).fractional q1 q2).1 $$ Hns with ⟨Hns1, Hns2⟩
      icases (pt_frac _ h q1 q2).1 $$ Hh with ⟨Hh1, Hh2⟩
      icases ((queueAt_fractional h hx).fractional q1 q2).1 $$ Hq with ⟨Hq1, Hq2⟩
      icases (pt_frac _ func.nil q1 q2).1 $$ Hcp with ⟨Hcp1, Hcp2⟩
      icases hm.1 $$ Hm with ⟨Hm1, Hm2⟩
      icases (pt_frac_half _ b q1 q2).1 $$ Hb with ⟨Hb1, Hb2⟩
      icases ((demoteTie_fractional γl dc).fractional q1 q2).1 $$ Hdt with ⟨Hdt1, Hdt2⟩
      isplitl [Hdc1 Hnp1 Hns1 Hh1 Hq1 Hcp1 Hm1 Hb1 Hdt1]
      · iexists dc, np, h, hx, b; iframe; iframe #
      · iexists dc, np, h, hx, b; iframe; iframe #
    · iintro ⟨⟨%dc, %np, %h, %hx, %b, Hdc, Hnp, Hns, Hh, Hq, Hcp, Hm, Hb, Hdt, #Hs⟩,
        ⟨%dc', %np', %h', %hx', %b', Hdc', Hnp', Hns', Hh', Hq', Hcp', Hm', Hb', Hdt', -⟩⟩
      icombine Hdc Hdc' gives %E1
      icombine Hnp Hnp' gives %E2
      icombine Hh Hh' gives %E3
      icombine Hb Hb' gives %E4
      subst E1 E2 E3 E4
      icases queueAt_agree h hx hx' q1 q2 $$ [$Hq $Hq'] with ⟨%E5, Hq, Hq'⟩
      subst E5
      iexists dc, np, h, hx, b
      iframe Hs
      isplitl [Hdc Hdc']
      · iapply (pt_frac _ dc q1 q2).2; iframe
      isplitl [Hnp Hnp']
      · iapply (pt_frac_half _ np q1 q2).2; iframe
      isplitl [Hns Hns']
      · iapply ((notifShare_fractional lp γl).fractional q1 q2).2; iframe
      isplitl [Hh Hh']
      · iapply (pt_frac _ h q1 q2).2; iframe
      isplitl [Hq Hq']
      · iapply ((queueAt_fractional h hx).fractional q1 q2).2; iframe
      isplitl [Hcp Hcp']
      · iapply (pt_frac _ func.nil q1 q2).2; iframe
      isplitl [Hm Hm']
      · iapply hm.2; iframe
      isplitl [Hb Hb']
      · iapply (pt_frac_half _ b q1 q2).2; iframe
      iapply ((demoteTie_fractional γl dc).fractional q1 q2).2; iframe

/-- The lessor's ghost map's contents name its names. -/
theorem lessorGhost_inj (lp lp' : Loc) (a b a' b' : GName) (r r' : LessorRdNames) (L L' : List w64)
    (h : lessorGhost lp a b r L = lessorGhost lp' a' b' r' L') : lp = lp' ∧ a = a' ∧ b = b' ∧ r = r' := by
  have h1 := congrArg (fun m => GMap.lookup m false) h
  unfold lessorGhost at h1
  simp [GMap.lookup_insert_eq_iff] at h1
  obtain ⟨h1, h2, h3, h4⟩ := h1
  exact ⟨h1, h2, h3, h4⟩

/-- The lessor's share of its ghost maps' authority. -/
instance lessorAuth_fractional (γl : GName) (lp : Loc) (L : List w64) (M : GMap w64 Loc) :
    Fractional (fun q => lessorAuth (GF := GF) γl q lp L M) where
  fractional q1 q2 := by
    unfold lessorAuth
    refine ⟨?_, ?_⟩
    · iintro ⟨%a, %b, %r, Ha, Hc, #Hg⟩
      icases ((ghostMapAuth_fractional (GF := GF) γl _).fractional q1 q2).1 $$ Ha with ⟨Ha1, Ha2⟩
      icases ((ghostMapAuth_fractional (GF := GF) b M).fractional q1 q2).1 $$ Hc with ⟨Hc1, Hc2⟩
      isplitl [Ha1 Hc1]
      · iexists a, b, r; iframe; iframe #
      · iexists a, b, r; iframe; iframe #
    · iintro ⟨⟨%a, %b, %r, Ha, Hc, #Hg⟩, ⟨%a', %b', %r', Ha', Hc', -⟩⟩
      ihave %E := ghostMapAuth_agree _ _ _ _ _ $$ Ha Ha'
      obtain ⟨-, E1, E2, E3⟩ := lessorGhost_inj _ _ _ _ _ _ _ _ _ _ E
      subst E1 E2 E3
      iexists a, b, r
      iframe Hg
      isplitl [Ha Ha']
      · iapply ((ghostMapAuth_fractional (GF := GF) γl _).fractional q1 q2).2; iframe
      iapply ((ghostMapAuth_fractional (GF := GF) b M).fractional q1 q2).2; iframe

/-- **`le.mu`'s resource is fractional**: what `init_RWMutex` takes. -/
instance lessorMu_fractional (lp : Loc) (γl : GName) : Fractional (lessorMu (GF := GF) lp γl) where
  fractional q1 q2 := by
    unfold lessorMu
    have hfr : ∀ L : List w64, leaseFrag (GF := GF) γl (q1 + q2).half L ⊣⊢
        leaseFrag γl q1.half L ∗ leaseFrag γl q2.half L := fun L => by
      unfold leaseFrag; rw [Qp_half_add]
      exact (ghostMapElem_fractional (GF := GF) true γl (Sum.inr L : LessorGV)).fractional q1.half q2.half
    have hhl : ∀ (γ : GName) (hs : List LSnap), (monoListAuthOwn γ (q1 + q2).half.half hs : IProp GF) ⊣⊢
        monoListAuthOwn γ q1.half.half hs ∗ monoListAuthOwn γ q2.half.half hs := fun γ hs => by
      rw [Qp_half_add, Qp_half_add]
      exact (monoListAuthOwn_fractional (GF := GF) γ hs).fractional _ _
    refine ⟨?_, ?_⟩
    · iintro ⟨%lm, %im, %M, %I, %rd, %L, Hlm, HM, Him, HI, Hrd, Ha, Hg, %HL, #Hsz, #Hls, Hx,
        ⟨%γr, %hs, #Hp, Hh, %Hhs⟩⟩
      icases (pt_frac _ lm q1 q2).1 $$ Hlm with ⟨Hlm1, Hlm2⟩
      icases (map_frac lm M q1 q2).1 $$ HM with ⟨HM1, HM2⟩
      icases (pt_frac_half _ im q1 q2).1 $$ Him with ⟨Him1, Him2⟩
      icases (map_frac_half im I q1 q2).1 $$ HI with ⟨HI1, HI2⟩
      icases (pt_frac_half _ rd q1 q2).1 $$ Hrd with ⟨Hrd1, Hrd2⟩
      icases ((lessorAuth_fractional γl lp L M).fractional q1 q2).1 $$ Ha with ⟨Ha1, Ha2⟩
      icases (hfr L).1 $$ Hg with ⟨Hg1, Hg2⟩
      icases ((lessorExtra_fractional lp γl M).fractional q1 q2).1 $$ Hx with ⟨Hx1, Hx2⟩
      icases (hhl γr.1 hs).1 $$ Hh with ⟨Hh1, Hh2⟩
      isplitl [Hlm1 HM1 Him1 HI1 Hrd1 Ha1 Hg1 Hx1 Hh1]
      · iexists lm, im, M, I, rd, L; iframe; iframe #
        all_goals first
          | (isplitr; · ipureintro; exact HL)
          | skip
        all_goals first
          | (iexists γr, hs; iframe; iframe #; ipureintro; exact Hhs)
          | (ipureintro; exact Hhs)
          | (ipureintro; exact HL)
      · iexists lm, im, M, I, rd, L; iframe; iframe #
        all_goals first
          | (isplitr; · ipureintro; exact HL)
          | skip
        all_goals first
          | (iexists γr, hs; iframe; iframe #; ipureintro; exact Hhs)
          | (ipureintro; exact Hhs)
          | (ipureintro; exact HL)
    · iintro ⟨⟨%lm, %im, %M, %I, %rd, %L, Hlm, HM, Him, HI, Hrd, Ha, Hg, %HL, #Hsz, #Hls, Hx,
          ⟨%γr, %hs, #Hp, Hh, %Hhs⟩⟩,
        ⟨%lm', %im', %M', %I', %rd', %L', Hlm', HM', Him', HI', Hrd', Ha', Hg', -, -, -, Hx',
          ⟨%γr', %hs', #Hp', Hh', -⟩⟩⟩
      icombine Hlm Hlm' gives %E1
      subst E1
      icases ownMap_agree_k lm _ _ M M' $$ [$HM $HM'] with ⟨%E2, HM, HM'⟩
      subst E2
      icombine Him Him' gives %E3
      subst E3
      icases ownMap_agree_k im _ _ I I' $$ [$HI $HI'] with ⟨%E4, HI, HI'⟩
      subst E4
      icombine Hrd Hrd' gives %E5
      subst E5
      iunfold leaseFrag at Hg Hg'
      icombine Hg Hg' gives %E6
      obtain ⟨-, E6⟩ := E6
      cases E6
      ihave %E7 := lessorPinR_agree γl γr γr' $$ [$Hp $Hp']
      subst E7
      icases monoListAuthOwn_agree_k γr.1 _ _ hs hs' $$ [$Hh $Hh'] with ⟨%E8, Hh, Hh'⟩
      subst E8
      iexists lm, im, M, I, rd, L
      isplitl [Hlm Hlm']
      · iapply (pt_frac _ lm q1 q2).2; iframe
      isplitl [HM HM']
      · iapply (map_frac lm M q1 q2).2; iframe
      isplitl [Him Him']
      · iapply (pt_frac_half _ im q1 q2).2; iframe
      isplitl [HI HI']
      · iapply (map_frac_half im I q1 q2).2; iframe
      isplitl [Hrd Hrd']
      · iapply (pt_frac_half _ rd q1 q2).2; iframe
      isplitl [Ha Ha']
      · iapply ((lessorAuth_fractional γl lp L M).fractional q1 q2).2; iframe
      isplitl [Hg Hg']
      · iapply (hfr L).2; iunfold leaseFrag; iframe
      iframe Hsz Hls
      isplitr
      · ipureintro; exact HL
      isplitl [Hx Hx']
      · iapply ((lessorExtra_fractional lp γl M).fractional q1 q2).2; iframe
      iexists γr, hs
      iframe Hp
      isplitl [Hh Hh']
      · iapply (hhl γr.1 hs).2; iframe
      ipureintro; exact Hhs

end frac

end lease
end EtcdGrove
end Perennial
