/-
The lessor's proofs' lemmas (2026-10-13, unit 8). Lean-first (no Rocq counterpart).

A `LeaseItem` is a safe map key (comparing it with itself does not panic: a struct of a
string).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.LessorHist
public import Perennial.Proof.sync.RWMutexThreads
public import Perennial.Proof.time
public import Perennial.Golang.Theory.Map
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.GhostMap
public import Perennial.IrisLib.BI

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lease

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

instance leaseItem_safeMapKey (k : LeaseItem) : SafeMapKey (GF := GF) LeaseItem.ty k where
  key_ok := trivial
  wp_go_eq_map_key k' _ s E Φ := by
    iintro HΦ
    wp_pures
    rw [show decide (k.Key' = k'.Key') = decide (k = k') by cases k; cases k'; simp]
    iapply HΦ

/-- `(*Time).Before` on a fractional points-to (2026-10-13, unit 9: the queue's `Less` reads the
items' times at the lock's share; Perennial's `Time.wp_ptr_Before` takes the whole). -/
theorem Time.wp_ptr_Before_dq (l : Loc) (t u : _root_.Perennial.time.Time) (dq : DFrac) :
    {{ (l ↦{dq} t : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType _root_.Perennial.time.Time.ty @!! go!"Before"))
        (Val #u))
    {{ (b : Bool), RET #b; l ↦{dq} t }} := by
  wp_start as Hl
  wp_auto
  wp_apply _root_.Perennial.time.Time.wp_Before as %b -
  iapply HΦ $$ Hl

/-- Two halves of a points-to agree and make the whole. -/
theorem ptsto_halves_combine {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v w : V) :
    typedPointsto (GF := GF) l v (DFrac.own (1 : Qp).half) ∗
      typedPointsto (GF := GF) l w (DFrac.own (1 : Qp).half) ⊢
      ⌜v = w⌝ ∗ typedPointsto (GF := GF) l v (DFrac.own 1) := by
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %Heq
  subst Heq
  isplitr
  · ipureintro; rfl
  rw [dfrac_own_half_half 1]
  iapply ((typedPointsto_dfractional (GF := GF) l v).dfractional _ _).2
  iframe

/-- Two halves of a map points-to agree and make the whole (unit T3, L2b: the item map and the
item sets, half the lock's, half the lease owner's). -/
theorem ownMap_halves_combine {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V]
    [go.IntoValInj K] [go.IntoValInj V] (m : Loc) (A B : GMap K V) :
    ownMap (GF := GF) m (DFrac.own (1 : Qp).half) A ∗ ownMap (GF := GF) m (DFrac.own (1 : Qp).half) B ⊢
      ⌜A = B⌝ ∗ ownMap (GF := GF) m (DFrac.own 1) A := by
  iintro ⟨H1, H2⟩
  ihave %Heq := ownMap_agree m _ _ A B $$ [$H1 $H2]
  subst Heq
  isplitr
  · ipureintro; rfl
  have h := (ownMap_fractional (GF := GF) m A).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  iapply h.2
  iframe

/-- A map points-to in two halves. -/
theorem ownMap_halves_split {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V]
    [go.IntoValInj K] (m : Loc) (A : GMap K V) :
    ownMap (GF := GF) m (DFrac.own 1) A ⊢
      ownMap (GF := GF) m (DFrac.own (1 : Qp).half) A ∗ ownMap (GF := GF) m (DFrac.own (1 : Qp).half) A := by
  have h := (ownMap_fractional (GF := GF) m A).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h.1

/-- A points-to in two halves. -/
theorem ptsto_halves_split {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢
      typedPointsto (GF := GF) l v (DFrac.own (1 : Qp).half) ∗
        typedPointsto (GF := GF) l v (DFrac.own (1 : Qp).half) := by
  iintro H
  rw [dfrac_own_half_half 1]
  iapply ((typedPointsto_dfractional (GF := GF) l v).dfractional _ _).1 $$ H

/-- What a lease's `mu` guards is fractional. -/
instance leaseItems_fractional (γl : GName) (l : Loc) : Fractional (leaseItems (GF := GF) γl l) where
  fractional q1 q2 := by
    unfold leaseItems
    rw [Qp_half_add]
    constructor
    · iintro ⟨%sm, %S, %γr, #Hp, Hsm, HS, He⟩
      icases (typedPointsto_frac_add _ _ q1.half q2.half).1 $$ Hsm with ⟨Hs1, Hs2⟩
      icases ((ownMap_fractional (GF := GF) sm S).fractional q1.half q2.half).1 $$ HS with ⟨HS1, HS2⟩
      icases ((ghostMapElem_fractional (GF := GF) l γr.2 S).fractional q1 q2).1 $$ He with ⟨He1, He2⟩
      isplitl [Hs1 HS1 He1]
      · iexists sm, S, γr; iframe; iframe #
      · iexists sm, S, γr; iframe; iframe #
    · iintro ⟨⟨%sm1, %S1, %γr1, #Hp1, Hsm1, HS1, He1⟩, ⟨%sm2, %S2, %γr2, #Hp2, Hsm2, HS2, He2⟩⟩
      ihave %Hr := lessorPinR_agree γl γr1 γr2 $$ [$Hp1 $Hp2]
      subst Hr
      icombine Hsm1 Hsm2 gives %Hsm
      subst Hsm
      ihave %HS := ownMap_agree sm1 _ _ S1 S2 $$ [$HS1 $HS2]
      subst HS
      iexists sm1, S1, γr1
      iframe Hp1
      isplitl [Hsm1 Hsm2]
      · iapply (typedPointsto_frac_add _ _ q1.half q2.half).2; iframe
      isplitl [HS1 HS2]
      · iapply ((ownMap_fractional (GF := GF) sm1 S1).fractional q1.half q2.half).2; iframe
      · iapply ((ghostMapElem_fractional (GF := GF) l γr1.2 S1).fractional q1 q2).2; iframe

/-- What a lease's `expiryMu` guards is fractional. -/
instance leaseExpiry_fractional (l : Loc) : Fractional (leaseExpiry (GF := GF) l) where
  fractional q1 q2 := by
    unfold leaseExpiry
    rw [Qp_half_add]
    constructor
    · iintro ⟨%e, He⟩
      icases (typedPointsto_frac_add _ _ _ _).1 $$ He with ⟨H1, H2⟩
      isplitl [H1]
      · iexists e; iframe
      · iexists e; iframe
    · iintro ⟨⟨%e1, H1⟩, ⟨%e2, H2⟩⟩
      icombine H1 H2 gives %He
      subst He
      iexists e1
      iapply (typedPointsto_frac_add _ _ _ _).2; iframe

theorem lessorGhost_insert (lp : Loc) (γga γcl : GName) (γr : LessorRdNames) (L L' : List w64) :
    (lessorGhost lp γga γcl γr L).insert true (Sum.inr L' : LessorGV) =
      lessorGhost lp γga γcl γr L' := by
  apply GMap.ext
  intro k
  unfold lessorGhost
  cases k <;> simp [GMap.lookup_insert_eq_iff]

/-- **The live set grows by a lease that may be granted** (`leaseGranted`, D19n), with both
halves (the lessor's under `le.mu`, the owner's). -/
theorem lessor_live_grant (γl : GName) (lp : Loc) (L : List w64) (M : GMap w64 Loc) (id : w64) :
    lessorAuth (GF := GF) γl 1 lp L M ∗ leaseFrag γl (1 : Qp).half L ∗
      leaseFrag γl (1 : Qp).half L ∗ leaseGranted γl id ==∗
      lessorAuth γl 1 lp (L ++ [id]) M ∗ leaseFrag γl (1 : Qp).half (L ++ [id]) ∗
        leaseFrag γl (1 : Qp).half (L ++ [id]) := by
  unfold lessorAuth leaseFrag
  iintro ⟨⟨%γga, %γcl, %γr, Ha, Hcl, #Hgr⟩, H1, H2, #Hid⟩
  ihave #Hl : iprop([∗list] x ∈ L ++ [id], leaseGranted (GF := GF) γl x) $$ []
  · iapply BigSepL.bigSepL_snoc.2
    iframe Hgr Hid
  icases ghostMapElem_combine true γl _ _ _ _ $$ H1 H2 with ⟨H, -⟩
  ihave H : ghostMapElem (GF := GF) γl true (DFrac.own 1) (Sum.inr L : LessorGV) $$ [H]
  · rw [dfrac_own_half_half 1]; iexact H
  imod ghost_map_update (Sum.inr (L ++ [id]) : LessorGV) $$ Ha H with ⟨Ha, H⟩
  rw [lessorGhost_insert]
  isplitl [Ha Hcl]
  · iexists γga, γcl, γr
    iframe Ha Hcl
    iframe Hl
  ihave H : ghostMapElem (GF := GF) γl true (DFrac.own ((1 : Qp).half + (1 : Qp).half))
      (Sum.inr (L ++ [id]) : LessorGV) $$ [H]
  · rw [Qp.half_add_half]; iexact H
  iapply ((ghostMapElem_fractional (GF := GF) true γl (Sum.inr (L ++ [id]) : LessorGV)).fractional
    (1 : Qp).half (1 : Qp).half).1 $$ H

/-- A conjunction over a list gives the one over a filter of it. -/
theorem bigSepL_filter (P : w64 → IProp GF) (p : w64 → Bool) :
    ∀ L : List w64, ([∗list] x ∈ L, P x) ⊢ [∗list] x ∈ L.filter p, P x
  | [] => by simp only [List.filter_nil]; exact .rfl
  | x :: L => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hx, H⟩
    ihave H := bigSepL_filter P p L $$ H
    rw [List.filter_cons]
    split
    · iapply BigSepL.bigSepL_cons.2; iframe Hx H
    · iexact H

/-- **The live set loses a lease** (`Revoke`), with both halves (the lessor's under `le.mu`, the
owner's): the live set without `id`. -/
theorem lessor_live_revoke (γl : GName) (lp : Loc) (L : List w64) (M : GMap w64 Loc) (id : w64) :
    lessorAuth (GF := GF) γl 1 lp L M ∗ leaseFrag γl (1 : Qp).half L ∗
      leaseFrag γl (1 : Qp).half L ==∗
      lessorAuth γl 1 lp (L.filter (· != id)) M ∗ leaseFrag γl (1 : Qp).half (L.filter (· != id)) ∗
        leaseFrag γl (1 : Qp).half (L.filter (· != id)) := by
  unfold lessorAuth leaseFrag
  iintro ⟨⟨%γga, %γcl, %γr, Ha, Hcl, #Hgr⟩, H1, H2⟩
  ihave #Hl := bigSepL_filter (fun x => leaseGranted (GF := GF) γl x) (· != id) L $$ Hgr
  icases ghostMapElem_combine true γl _ _ _ _ $$ H1 H2 with ⟨H, -⟩
  ihave H : ghostMapElem (GF := GF) γl true (DFrac.own 1) (Sum.inr L : LessorGV) $$ [H]
  · rw [dfrac_own_half_half 1]; iexact H
  imod ghost_map_update (Sum.inr (L.filter (· != id)) : LessorGV) $$ Ha H with ⟨Ha, H⟩
  rw [lessorGhost_insert]
  isplitl [Ha Hcl]
  · iexists γga, γcl, γr
    iframe Ha Hcl
    iframe Hl
  ihave H : ghostMapElem (GF := GF) γl true (DFrac.own ((1 : Qp).half + (1 : Qp).half))
      (Sum.inr (L.filter (· != id)) : LessorGV) $$ [H]
  · rw [Qp.half_add_half]; iexact H
  iapply ((ghostMapElem_fractional (GF := GF) true γl
    (Sum.inr (L.filter (· != id)) : LessorGV)).fractional (1 : Qp).half (1 : Qp).half).1 $$ H

/-- The lessor's authority names the pin's closers' map. -/
theorem lessorAuth_pin (γl : GName) (q : Qp) (lp lp' : Loc) (L : List w64) (M : GMap w64 Loc)
    (γga γcl : GName) :
    lessorAuth (GF := GF) γl q lp L M ∗ lessorPinG γl lp' γga γcl ⊢
      ⌜lp = lp'⌝ ∗ ghostMapAuth γcl q M ∗
        (∀ M' : GMap w64 Loc, ghostMapAuth γcl q M' -∗ lessorAuth γl q lp L M') := by
  unfold lessorAuth lessorPinG lessorPinAll
  iintro ⟨⟨%γa, %γc, %γr, Ha, Hcl, #Hgr⟩, %γr', #Hp⟩
  ihave %Hl := ghost_map_lookup $$ Ha Hp
  have hl : (lessorGhost lp γa γc γr L).lookup false = some (Sum.inl (lp, γa, γc, γr)) := by
    unfold lessorGhost; simp [GMap.lookup_insert_eq_iff]
  rw [hl] at Hl
  cases Hl
  iframe Hcl
  isplitr
  · ipureintro; rfl
  iintro %M' Hcl
  iexists γga, γcl, γr
  iframe Ha Hcl Hgr

/-! ### The history's steps (Part B, 2026-10-31)

The owner appends to the lessor's history under `le.mu`'s write lock: with its half
(`leaseClosers`), the lock's quarter (`lessorMu` at fraction 1) and the invariant's quarter
(`lessorRdInv`, opened for the step). -/

/-- The history's whole authority: the owner's half, the lock's quarter, the invariant's. -/
theorem hist_full (γ : GName) (hs : List LSnap) :
    monoListAuthOwn (GF := GF) γ 1 hs ⊣⊢
      monoListAuthOwn γ (1 : Qp).half hs ∗ monoListAuthOwn γ (1 : Qp).half.half hs ∗
        monoListAuthOwn γ Qp.quarter hs := by
  have h1 := (monoListAuthOwn_fractional (GF := GF) γ hs).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h1
  have h2 := (monoListAuthOwn_fractional (GF := GF) γ hs).fractional (1 : Qp).half.half Qp.quarter
  have hq : (1 : Qp).half.half + Qp.quarter = (1 : Qp).half :=
    Subtype.ext (by simp only [Qp.val_add, Qp.val_half, Qp.quarter]; grind)
  rw [hq] at h2
  constructor
  · iintro H
    icases h1.1 $$ H with ⟨Ho, H⟩
    icases h2.1 $$ H with ⟨Hl, Ha⟩
    iframe
  · iintro ⟨Ho, Hl, Ha⟩
    iapply h1.2
    iframe Ho
    iapply h2.2
    iframe

/-- **A reader under `le.mu` sees the history's last snapshot** (`Lookup`): the lock's share of
the history has it, at an index no earlier than the reader's lower bound. -/
theorem lockHist_at (γl : GName) (γr : LessorRdNames) (q : Qp) (hs : List LSnap) (σ : LSnap)
    (m : Nat) (hlast : hs.getLast? = some σ) :
    lessorLb (GF := GF) γl m ∗ lessorPinR γl γr ∗ monoListAuthOwn γr.1 q hs ⊢
      monoListAuthOwn γr.1 q hs ∗ ⌜m ≤ hs.length - 1⌝ ∗ lessorAt γl (hs.length - 1) σ := by
  unfold lessorLb lessorAt
  iintro ⟨⟨%γr', %hs', #Hpr', #Hlb, %Hm⟩, #Hpr, Ha⟩
  ihave %Hr := lessorPinR_agree γl γr γr' $$ [$Hpr $Hpr']
  subst Hr
  ihave %Hpre := mono_list_auth_lb_valid γr.1 q hs hs' $$ Ha Hlb
  ihave #Hlb' := monoListLbOwn_get γr.1 q hs $$ Ha
  have ⟨hσ, hpos⟩ := getLast?_getElem? hlast
  ihave #Hidx := monoListIdxOwn_get (hs.length - 1) σ hσ $$ Hlb'
  iframe Ha
  isplitr
  · ipureintro
    have := Hpre.2.length_le
    omega
  iexists γr; iframe Hpr Hidx

/-- **The owner appends a snapshot** (`Revoke`, the item sets unchanged). -/
theorem hist_append (γl : GName) (γr : LessorRdNames) (hs : List LSnap)
    (Sm : GMap Loc (GMap LeaseItem Unit)) (σ' : LSnap) (E : CoPset) (hE : ↑lessorRdN ⊆ E)
    (hstep : setsOk hs Sm → histOk hs → setsOk (hs ++ [σ']) Sm ∧ histOk (hs ++ [σ'])) :
    lessorRdInv (GF := GF) γl ∗ lessorPinR γl γr ∗ monoListAuthOwn γr.1 (1 : Qp).half hs ∗
      monoListAuthOwn γr.1 (1 : Qp).half.half hs ∗ ghostMapAuth γr.2 (1 : Qp).half Sm ⊢
    |={E}=> monoListAuthOwn γr.1 (1 : Qp).half (hs ++ [σ']) ∗
      monoListAuthOwn γr.1 (1 : Qp).half.half (hs ++ [σ']) ∗ ghostMapAuth γr.2 (1 : Qp).half Sm := by
  unfold lessorRdInv
  iintro ⟨⟨%γr1, #Hp1, #Hinv⟩, #Hp, Ho, Hl, HSo⟩
  ihave %H1 := lessorPinR_agree γl γr γr1 $$ [$Hp $Hp1]
  subst H1
  iinv Hinv with Hb Hclose
  iunfold lessorRdBody at Hb
  icases Hb with ⟨%hs0, %Sm0, >Ha, >HS, >%Hok, #>Hids⟩
  ihave %Hh := monoListAuthOwn_agree γr.1 _ _ hs hs0 $$ Ho Ha
  obtain ⟨-, rfl⟩ := Hh
  ihave %HSm := ghostMapAuth_agree γr.2 _ _ Sm Sm0 $$ HSo HS
  subst HSm
  ihave Hfull := (hist_full γr.1 hs).2 $$ [$Ho $Hl $Ha]
  imod monoListAuthOwn_update_app [σ'] $$ Hfull with ⟨Hfull, -⟩
  icases (hist_full γr.1 _).1 $$ Hfull with ⟨Ho, Hl, Ha⟩
  imod Hclose $$ [Ha HS] with -
  · inext; iunfold lessorRdBody; iexists hs ++ [σ'], Sm; iframe Ha HS Hids
    ipureintro; exact hstep Hok.1 Hok.2
  imodintro
  iframe

/-- **The owner appends a snapshot and changes the lease `l`'s item set** (`Attach`,
`Detach`: under `l.mu`'s write lock too, whose element of the item sets' map it holds whole). -/
theorem hist_append_set (γl : GName) (γr : LessorRdNames) (hs : List LSnap)
    (Sm : GMap Loc (GMap LeaseItem Unit)) (σ' : LSnap) (l : Loc) (S S' : GMap LeaseItem Unit)
    (E : CoPset) (hE : ↑lessorRdN ⊆ E)
    (hstep : setsOk hs Sm → histOk hs → Sm.lookup l = some S →
      setsOk (hs ++ [σ']) (Sm.insert l S') ∧ histOk (hs ++ [σ'])) :
    lessorRdInv (GF := GF) γl ∗ lessorPinR γl γr ∗ monoListAuthOwn γr.1 (1 : Qp).half hs ∗
      monoListAuthOwn γr.1 (1 : Qp).half.half hs ∗ ghostMapAuth γr.2 (1 : Qp).half Sm ∗
      ghostMapElem γr.2 l (DFrac.own 1) S ⊢
    |={E}=> monoListAuthOwn γr.1 (1 : Qp).half (hs ++ [σ']) ∗
      monoListAuthOwn γr.1 (1 : Qp).half.half (hs ++ [σ']) ∗
      ghostMapAuth γr.2 (1 : Qp).half (Sm.insert l S') ∗ ghostMapElem γr.2 l (DFrac.own 1) S' := by
  unfold lessorRdInv
  iintro ⟨⟨%γr1, #Hp1, #Hinv⟩, #Hp, Ho, Hl, HSo, He⟩
  ihave %H1 := lessorPinR_agree γl γr γr1 $$ [$Hp $Hp1]
  subst H1
  iinv Hinv with Hb Hclose
  iunfold lessorRdBody at Hb
  icases Hb with ⟨%hs0, %Sm0, >Ha, >HS, >%Hok, #>Hids⟩
  ihave %Hh := monoListAuthOwn_agree γr.1 _ _ hs hs0 $$ Ho Ha
  obtain ⟨-, rfl⟩ := Hh
  ihave %HSm := ghostMapAuth_agree γr.2 _ _ Sm Sm0 $$ HSo HS
  subst HSm
  ihave %HlS := ghost_map_lookup $$ HSo He
  ihave Hfull := (hist_full γr.1 hs).2 $$ [$Ho $Hl $Ha]
  imod monoListAuthOwn_update_app [σ'] $$ Hfull with ⟨Hfull, -⟩
  icases (hist_full γr.1 _).1 $$ Hfull with ⟨Ho, Hl, Ha⟩
  ihave HSf := (ghostMapAuth_halves γr.2 Sm).2 $$ [$HSo $HS]
  imod ghost_map_update S' $$ HSf He with ⟨HSf, He⟩
  icases (ghostMapAuth_halves γr.2 _).1 $$ HSf with ⟨HSo, HS⟩
  imod Hclose $$ [Ha HS] with -
  · inext; iunfold lessorRdBody; iexists hs ++ [σ'], Sm.insert l S'; iframe Ha HS
    isplitr
    · ipureintro; exact hstep Hok.1 Hok.2 HlS
    iapply (BigSepM.bigSepM_insert_exist_elim (Φ := fun l _ => iprop(∃ id : w64, lsF go!"ID" l ↦□ id))
      (x' := S') (show Iris.Std.PartialMap.get? Sm l = some S from HlS) .rfl)
    iexact Hids
  imodintro
  iframe

/-- **`Grant`'s step**: a fresh `*Lease` `l` of `id` (its `ID` owned whole, so not in the item
sets' map, so in no snapshot) is registered with the empty set, its `ID` made read-only, and the
snapshot with `l` in the lease map appended. -/
theorem grant_hist (γl : GName) (γr : LessorRdNames) (hs : List LSnap)
    (Sm : GMap Loc (GMap LeaseItem Unit)) (M : GMap w64 Loc) (I : GMap LeaseItem w64) (id : w64)
    (l : Loc) (E : CoPset) (hE : ↑lessorRdN ⊆ E) (hlast : hs.getLast? = some (M, I))
    (hM : M.lookup id = none) (hI : ∀ it : LeaseItem, I.lookup it ≠ some id) :
    lessorRdInv (GF := GF) γl ∗ lessorPinR γl γr ∗ monoListAuthOwn γr.1 (1 : Qp).half hs ∗
      monoListAuthOwn γr.1 (1 : Qp).half.half hs ∗ ghostMapAuth γr.2 (1 : Qp).half Sm ∗
      lsF go!"ID" l ↦ id ⊢
    |={E}=> monoListAuthOwn γr.1 (1 : Qp).half (hs ++ [(M.insert id l, I)]) ∗
      monoListAuthOwn γr.1 (1 : Qp).half.half (hs ++ [(M.insert id l, I)]) ∗
      ghostMapAuth γr.2 (1 : Qp).half (Sm.insert l (∅ : GMap LeaseItem Unit)) ∗
      ghostMapElem γr.2 l (DFrac.own 1) (∅ : GMap LeaseItem Unit) ∗ lsF go!"ID" l ↦□ id := by
  unfold lessorRdInv
  iintro ⟨⟨%γr1, #Hp1, #Hinv⟩, #Hp, Ho, Hl, HSo, HID⟩
  ihave %H1 := lessorPinR_agree γl γr γr1 $$ [$Hp $Hp1]
  subst H1
  iinv Hinv with Hb Hclose
  iunfold lessorRdBody at Hb
  icases Hb with ⟨%hs0, %Sm0, >Ha, >HS, >%Hok, #>Hids⟩
  ihave %Hh := monoListAuthOwn_agree γr.1 _ _ hs hs0 $$ Ho Ha
  obtain ⟨-, rfl⟩ := Hh
  ihave %HSm := ghostMapAuth_agree γr.2 _ _ Sm Sm0 $$ HSo HS
  subst HSm
  cases Hfresh : Sm.lookup l with
  | some S =>
    ihave ⟨%id', HID'⟩ := BigSepM.bigSepM_lookup Hfresh $$ Hids
    iexfalso
    iapply w64_own_discard_false _ id id' $$ [$HID $HID']
  | none =>
  have hnew : ∀ (k : Nat) (τ : LSnap) (id' : w64), hs[k]? = some τ → τ.1.lookup id' ≠ some l :=
    fun k τ id' hk h => by have := Hok.1.1 k τ id' l hk h; rw [Hfresh] at this; cases this
  ihave Hfull := (hist_full γr.1 hs).2 $$ [$Ho $Hl $Ha]
  imod monoListAuthOwn_update_app [(M.insert id l, I)] $$ Hfull with ⟨Hfull, -⟩
  icases (hist_full γr.1 _).1 $$ Hfull with ⟨Ho, Hl, Ha⟩
  ihave HSf := (ghostMapAuth_halves γr.2 Sm).2 $$ [$HSo $HS]
  imod ghost_map_insert l (∅ : GMap LeaseItem Unit) Hfresh $$ HSf with ⟨HSf, He⟩
  icases (ghostMapAuth_halves γr.2 _).1 $$ HSf with ⟨HSo, HS⟩
  ipersist HID
  imod Hclose $$ [Ha HS] with -
  · inext; iunfold lessorRdBody; iexists hs ++ [(M.insert id l, I)], Sm.insert l ∅; iframe Ha HS
    isplitr
    · ipureintro; exact setsOk_grant hlast Hok.1 Hok.2 hM hI hnew
    iapply (BigSepM.bigSepM_insert (Φ := fun l _ => iprop(∃ id : w64, lsF go!"ID" l ↦□ id))
      (show Iris.Std.PartialMap.get? Sm l = none from Hfresh)).2
    isplitr
    · iexists id; iexact HID
    iexact Hids
  imodintro
  iframe
  iexact HID

/-- **`Grant`'s ghost step, a granted lease joining the lessor and the owner** (unit T3; Part B):
the closers' map gains the lease (with the lessor's map), the owner its element (half in
`leaseOwn`'s closers, half in the revokers, with the right to close its `revokec`) and (L2b) its
half of the lease's item set, empty (no item of the item map is on a lease not yet live); (Part
B) the lease's empty set registered, its `ID` read-only, the snapshot with it appended to the
history (`grant_hist`), and its lock made: one reader slot to the owner (`closerAt`), the others in
the lease's pool under `threadBound GF ≤ 2^30 - 1` (`isLeaseObj`). -/
theorem closers_grant (γl : GName) (lp : Loc) (L : List w64) (M : GMap w64 Loc) (id : w64)
    (l : Loc) (c : GoChan) (I I0 : GMap LeaseItem w64) (sm : Loc) (E : CoPset)
    (hE : ↑lessorRdN ⊆ E) (hl : l ≠ null) (hM : M.lookup id = none)
    (hL : ∀ x : w64, x ∈ L ↔ (M.lookup x).isSome) :
    lessorRdInv (GF := GF) γl ∗ lessorAuth γl 1 lp L M ∗ leaseClosers γl L I0 ∗
        leaseRevokers γl L ∗
        (∃ (γr : LessorRdNames) (hs : List LSnap), lessorPinR γl γr ∗
          monoListAuthOwn γr.1 (1 : Qp).half.half hs ∗ ⌜hs.getLast? = some (M, I)⌝) ∗
        lsF go!"revokec" l ↦□ c ∗ revokeCloser c ∗ lsF go!"itemSet" l ↦ sm ∗
        sm ↦$ (∅ : GMap LeaseItem Unit) ∗
        lsF go!"mu" l ↦ (zero_val _root_.Perennial.sync.RWMutex) ∗ lsF go!"ID" l ↦ id ⊢
      |={E}=> lessorAuth γl 1 lp L (M.insert id l) ∗ leaseClosers γl (L ++ [id]) I0 ∗
        leaseRevokers γl (L ++ [id]) ∗
        (∃ (γr : LessorRdNames) (hs : List LSnap), lessorPinR γl γr ∗
          monoListAuthOwn γr.1 (1 : Qp).half.half hs ∗ ⌜hs.getLast? = some (M.insert id l, I)⌝) ∗
        isLeaseObj γl l ∗ lsF go!"ID" l ↦□ id := by
  iintro ⟨#Hrd, Ha, Hcls, Hrvk, ⟨%γrl, %hsl, #Hprl, Hl, %Hlastl⟩, #Hrc, Hrcl, HiS, Hsm, Hmu0, HID⟩
  iunfold leaseClosers at Hcls
  icases Hcls with ⟨%lp', %γga, %γcl, %C, %im, #Hp, %HC, Him, HI, %HIL, %HIS, Hcs, %γr, %hs, %Sm,
    #Hpr, Ho, %Hlast, HSo⟩
  ihave %Hr := lessorPinR_agree γl γr γrl $$ [$Hpr $Hprl]
  subst Hr
  ihave %Hh := monoListAuthOwn_agree γr.1 _ _ hs hsl $$ Ho Hl
  obtain ⟨-, rfl⟩ := Hh
  rw [Hlast] at Hlastl
  cases Hlastl
  iunfold leaseRevokers at Hrvk
  icases Hrvk with ⟨%lp'', %γga', %γcl', %C', #Hp', %HC', Hrs⟩
  ihave %Hpp := lessorPinG_agree γl lp' lp'' γga γga' γcl γcl' $$ [$Hp $Hp']
  obtain ⟨rfl, rfl, rfl⟩ := Hpp
  icases lessorAuth_pin γl 1 lp lp' L M γga γcl $$ [$Ha $Hp] with ⟨%Hlp, Hcl, Hback⟩
  subst Hlp
  have hnotL : id ∉ L := by
    intro h; have := (hL id).1 h; rw [hM] at this; cases this
  have hC' : C'.lookup id = none := by
    cases h : C'.lookup id with
    | none => rfl
    | some _ => exact absurd ((HC' id).2 (by rw [h]; rfl)) hnotL
  have hI : ∀ it : LeaseItem, I.lookup it ≠ some id := fun it h => hnotL (HIL it id h)
  -- the history: `l` registered, the snapshot with it appended
  imod grant_hist γl γr hs Sm M I id l E hE Hlast hM hI $$ [$Hrd $Hpr $Ho $Hl $HSo $HID]
    with ⟨Ho, Hl, HSo, He, #HID⟩
  -- the lease's lock, its slots: the owner's and the pool's
  icases ptsto_halves_split _ sm $$ HiS with ⟨HiS, HiS'⟩
  icases ownMap_halves_split sm (∅ : GMap LeaseItem Unit) $$ Hsm with ⟨Hsm, Hsm'⟩
  imod (sync.init_RWMutex (leaseItems γl l) (E := E) (lsF go!"mu" l)) $$ [HiS Hsm He] Hmu0
    with HmuRs
  · inext; iunfold leaseItems; iexists sm, ∅, γr; iframe; iframe #
  have hmax : sync.rwmutex.actualMaxReaders.toNat =
      (sync.rwmutex.actualMaxReaders.toNat - 1) + 1 := by
    rw [sync.rwmutex.actualMaxReaders_unseal]; decide
  rw [hmax, List.replicate_succ]
  icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ HmuRs with ⟨HmuR, HmuRest⟩
  icases sync.ownRWMutex_guard _ _ $$ HmuR with ⟨HmuR, #HmuG⟩
  ihave Hpo : iprop(|={E}=> □ (⌜threadBound GF ≤ 2 ^ 30 - 1⌝ → ∃ γp : GName,
      threadPool.isThreadPool leasePoolN γp (sync.ownRWMutex (lsF go!"mu" l) (leaseItems γl l))))
    $$ [HmuRest]
  · by_cases hb : threadBound GF ≤ 2 ^ 30 - 1
    · have hn : threadBound GF ≤ (sync.rwmutex.actualMaxReaders.toNat - 1) + 1 := by
        rw [← hmax, sync.rwmutex.actualMaxReaders_unseal]; simp; omega
      imod threadPool.init leasePoolN (sync.ownRWMutex (lsF go!"mu" l) (leaseItems γl l)) E _ hn
        $$ HmuRest with ⟨%γp, #Hpool⟩
      imodintro
      iintro !> %_
      iexists γp; iexact Hpool
    · imodintro
      iintro !> %h
      iexfalso; ipureintro; exact hb h
  imod Hpo with #Hpo
  ihave #Hlo : isLeaseObj γl l $$ []
  · iunfold isLeaseObj; iframe HmuG Hrd Hpo; ipureintro; exact hl
  -- the closers' map
  imod ghost_map_insert id l hM $$ Hcl with ⟨Hcl, He2⟩
  icases (ghostMapElem_fractional (GF := GF) id γcl l).fractional (1 : Qp).half (1 : Qp).half |>.1
    $$ [He2] with ⟨He2, He2'⟩
  · rw [Qp.half_add_half]; iexact He2
  ihave Ha := Hback $$ %(M.insert id l) Hcl
  have hlast' : (hs ++ [(M.insert id l, I)]).getLast? = some (M.insert id l, I) := by simp
  imodintro
  iframe Ha Hlo HID
  isplitl [Him HI Hcs He2 HiS' Hsm' HmuR Ho HSo]
  · iunfold leaseClosers
    iexists lp, γga, γcl, (M.insert id l), im
    iframe Hp Him HI
    isplitr
    · ipureintro
      intro x
      rw [List.mem_append, List.mem_singleton, HC x]
      by_cases hx : id = x
      · subst hx; simp [GMap.lookup_insert_eq_iff, hM]
      · have : (M.insert id l).lookup x = M.lookup x := GMap.lookup_insert_ne M l hx
        rw [this]
        constructor
        · rintro (h | h)
          · exact h
          · exact absurd h.symm hx
        · intro h; exact Or.inl h
    isplitr
    · ipureintro
      intro it x h
      exact List.mem_append_left _ (HIL it x h)
    isplitr
    · ipureintro; exact HIS
    isplitl [Hcs He2 HiS' Hsm' HmuR]
    · iapply (BigSepM.bigSepM_insert (Φ := fun (i : w64) (x : Loc) =>
        closerAt (GF := GF) γl γcl I i x) hM).2
      iframe Hcs
      iunfold closerAt
      iframe He2 HmuR
      iunfold leaseItemsOwn
      iexists sm, ∅
      iframe HiS' Hsm'
      ipureintro
      intro it
      simp only [GMap.lookup_empty, reduceCtorEq, false_iff]
      exact hI it
    iexists γr, hs ++ [(M.insert id l, I)], Sm.insert l ∅
    iframe Hpr Ho HSo
    ipureintro; exact hlast'
  isplitl [Hrs He2' Hrcl]
  · iunfold leaseRevokers
    iexists lp, γga, γcl, (C'.insert id l)
    iframe Hp
    isplitr
    · ipureintro
      intro x
      rw [List.mem_append, List.mem_singleton, HC' x]
      by_cases hx : id = x
      · subst hx; simp [GMap.lookup_insert_eq_iff, hC']
      · have : (C'.insert id l).lookup x = C'.lookup x := GMap.lookup_insert_ne C' l hx
        rw [this]
        constructor
        · rintro (h | h)
          · exact h
          · exact absurd h.symm hx
        · intro h; exact Or.inl h
    iapply (BigSepM.bigSepM_insert (Φ := fun (i : w64) (x : Loc) =>
      iprop(ghostMapElem (GF := GF) γcl i (DFrac.own (1 : Qp).half) x ∗
        ∃ c : GoChan, lsF go!"revokec" x ↦□ c ∗ revokeCloser c)) hC').2
    iframe Hrs He2'
    iexists c; iframe Hrc Hrcl
  iexists γr, hs ++ [(M.insert id l, I)]
  iframe Hpr Hl
  ipureintro; exact hlast'

/-- **The owner's resource of one live lease, taken out** (unit T3, L2b): its closers' map's
element and its half of the item set, and back with the item map changed from `I` to any `I'`
that attaches the same items to every other lease. -/
theorem closers_items (γl γcl : GName) (C : GMap w64 Loc) (id : w64) (l : Loc)
    (I : GMap LeaseItem w64) (hC : C.lookup id = some l) :
    ([∗map] i ↦ x ∈ C, closerAt (GF := GF) γl γcl I i x) ⊢
      ghostMapElem γcl id (DFrac.own (1 : Qp).half) l ∗ leaseItemsOwn l I id ∗
      ∀ I' : GMap LeaseItem w64,
        ⌜∀ id' : w64, id' ≠ id → ∀ it : LeaseItem, I'.lookup it = some id' ↔ I.lookup it = some id'⌝ -∗
        ghostMapElem γcl id (DFrac.own (1 : Qp).half) l -∗ leaseItemsOwn l I' id -∗
        [∗map] i ↦ x ∈ C, closerAt γl γcl I' i x := by
  iintro H
  icases (BigSepM.bigSepM_delete (Φ := fun i x => closerAt (GF := GF) γl γcl I i x) hC).1 $$ H
    with ⟨Hc, Hrest⟩
  iunfold closerAt at Hc
  icases Hc with ⟨He, Hit, Hslot⟩
  iframe He Hit
  iintro %I' %Hoth He Hit
  iapply (BigSepM.bigSepM_delete (Φ := fun i x => closerAt (GF := GF) γl γcl I' i x) hC).2
  isplitl [He Hit Hslot]
  · iunfold closerAt; iframe
  iapply BigSepM.bigSepM_impl $$ Hrest
  iintro !> %k %v %hk Hc
  have hne : k ≠ id := fun h => (Iris.Std.LawfulPartialMap.get?_delete_some_iff.1 hk).1 h.symm
  iunfold closerAt at Hc
  iunfold closerAt
  icases Hc with ⟨He, Hit, Hslot⟩
  iframe He Hslot
  iunfold leaseItemsOwn at Hit
  iunfold leaseItemsOwn
  icases Hit with ⟨%sm, %S, Hsm, HS, %HSI⟩
  iexists sm, S
  iframe Hsm HS
  ipureintro
  intro it
  rw [HSI it, Hoth k hne it]

theorem insertAll_snoc {K V : Type} [DecidableEq K] (m : GMap K V) (xs : List K) (x : K) (v : V) :
    insertAll m (xs ++ [x]) v = (insertAll m xs v).insert x v := by
  unfold insertAll; rw [List.foldl_append]; rfl

theorem deleteAll_snoc {K V : Type} [DecidableEq K] (m : GMap K V) (xs : List K) (x : K) :
    deleteAll m (xs ++ [x]) = (deleteAll m xs).delete x := by
  unfold deleteAll; rw [List.foldl_append]; rfl

/-- `Attach`'s loop keeps the lease's item set the item map's. -/
theorem itemsFor_attach (I : GMap LeaseItem w64) (id : w64) (S : GMap LeaseItem Unit)
    (xs : List LeaseItem) (h : itemsFor I id S) :
    itemsFor (insertAll I xs id) id (insertAll S xs ()) := by
  intro it
  rw [insertAll_lookup, insertAll_lookup]
  by_cases hi : it ∈ xs <;> simp [hi, h it]

/-- `Attach`'s loop changes no other lease's items (no item of `xs` is on another lease). -/
theorem attach_other (I : GMap LeaseItem w64) (id id' : w64) (xs : List LeaseItem)
    (hxs : ∀ it ∈ xs, I.lookup it = none ∨ I.lookup it = some id) (hne : id' ≠ id)
    (it : LeaseItem) : (insertAll I xs id).lookup it = some id' ↔ I.lookup it = some id' := by
  rw [insertAll_lookup]
  by_cases hi : it ∈ xs
  · simp only [hi, ↓reduceIte, Option.some.injEq]
    constructor
    · intro h; exact absurd h.symm hne
    · intro h
      rcases hxs it hi with h' | h' <;> rw [h'] at h
      · cases h
      · cases h; exact absurd rfl hne
  · simp [hi]

/-- `Detach`'s loop keeps the lease's item set the item map's. -/
theorem itemsFor_detach (I : GMap LeaseItem w64) (id : w64) (S : GMap LeaseItem Unit)
    (xs : List LeaseItem) (h : itemsFor I id S) :
    itemsFor (deleteAll I xs) id (deleteAll S xs) := by
  intro it
  rw [deleteAll_lookup, deleteAll_lookup]
  by_cases hi : it ∈ xs <;> simp [hi, h it]

/-- `Detach`'s loop changes no other lease's items (every item of `xs` is on the lease). -/
theorem detach_other (I : GMap LeaseItem w64) (id id' : w64) (xs : List LeaseItem)
    (hxs : ∀ it ∈ xs, I.lookup it = some id) (hne : id' ≠ id)
    (it : LeaseItem) : (deleteAll I xs).lookup it = some id' ↔ I.lookup it = some id' := by
  rw [deleteAll_lookup]
  by_cases hi : it ∈ xs
  · simp only [hi, ↓reduceIte, reduceCtorEq, false_iff]
    rw [hxs it hi]; intro h; cases h; exact hne rfl
  · simp [hi]

/-- **The owner's whole resource of one live lease, taken out** (unit T3: `Revoke`), and back at
any item map attaching the same items to every other lease. -/
theorem closers_take (γl γcl : GName) (C : GMap w64 Loc) (id : w64) (l : Loc)
    (I : GMap LeaseItem w64) (hC : C.lookup id = some l) :
    ([∗map] i ↦ x ∈ C, closerAt (GF := GF) γl γcl I i x) ⊢
      closerAt γl γcl I id l ∗
      ∀ I' : GMap LeaseItem w64,
        ⌜∀ id' : w64, id' ≠ id → ∀ it : LeaseItem, I'.lookup it = some id' ↔ I.lookup it = some id'⌝ -∗
        closerAt γl γcl I' id l -∗ [∗map] i ↦ x ∈ C, closerAt γl γcl I' i x := by
  iintro H
  icases (BigSepM.bigSepM_delete (Φ := fun i x => closerAt (GF := GF) γl γcl I i x) hC).1 $$ H
    with ⟨Hc, Hrest⟩
  iframe Hc
  iintro %I' %Hoth Hc
  iapply (BigSepM.bigSepM_delete (Φ := fun i x => closerAt (GF := GF) γl γcl I' i x) hC).2
  iframe Hc
  iapply BigSepM.bigSepM_impl $$ Hrest
  iintro !> %k %v %hk Hc
  have hne : k ≠ id := fun h => (Iris.Std.LawfulPartialMap.get?_delete_some_iff.1 hk).1 h.symm
  iunfold closerAt at Hc
  iunfold closerAt
  icases Hc with ⟨He, Hit, Hslot⟩
  iframe He Hslot
  iunfold leaseItemsOwn at Hit
  iunfold leaseItemsOwn
  icases Hit with ⟨%sm, %S, Hsm, HS, %HSI⟩
  iexists sm, S
  iframe Hsm HS
  ipureintro
  intro it
  rw [HSI it, Hoth k hne it]

/-- Two whole points-to of one `int` field contradict. -/
theorem w64Field_excl (a : Loc) (v w : w64) :
    a ↦ v ∗ a ↦ w ⊢ (False : IProp GF) := by
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  iintro ⟨⟨H1, _⟩, ⟨H2, _⟩⟩
  -- an integer's points-to is its bytes: the first byte's points-tos clash
  simp only [typedPointstoDef_w64, natBytes, bytesPointsto]
  icases H1 with ⟨H1, _⟩
  icases H2 with ⟨H2, _⟩
  icombine H1 H2 gives % ⟨Hbad, _⟩
  exfalso
  have : (1 + 1 : Rat) ≤ 1 := Hbad
  grind

/-- Setting a position whose body is `emp` does not change a big separating conjunction. -/
theorem bigSepL_set_emp {A : Type} (C : Nat → A → IProp GF) (l : List A) (i : Nat) (v : A)
    (hi : i < l.length) (hC : ∀ y, C i y = iprop(emp)) :
    ([∗list] k ↦ y ∈ l.set i v, C k y) ⊣⊢ [∗list] k ↦ y ∈ l, C k y := by
  have hv : (l.set i v)[i]? = some v := by simp [hi]
  have hl : l[i]? = some l[i] := List.getElem?_eq_getElem hi
  constructor
  · refine (BigSepL.bigSepL_lookup_acc hv).1.trans ?_
    refine sep_elim_right.trans ((forall_elim l[i]).trans ?_)
    rw [hC, List.set_set, List.set_getElem_self hi]
    exact emp_wand.1
  · refine (BigSepL.bigSepL_lookup_acc hl).1.trans ?_
    refine sep_elim_right.trans ((forall_elim v).trans ?_)
    rw [hC]
    exact emp_wand.1

/-- The swapped list's elements: `b` at `i`, `a` at `j` (`a`, `b` the elements at `i`, `j`). -/
theorem listSwap_eq {A : Type} (xs : List A) (i j : Nat) (a b : A) (ha : xs[i]? = some a)
    (hb : xs[j]? = some b) : listSwap xs i j = (xs.set i b).set j a := by
  unfold listSwap; rw [ha, hb]

end lemmas

section closeLemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`close(c)` by the closer of a lease's `revokec`** (unit T3: `Revoke`'s deferred close): the
channel idle, owned, so the close does not panic. -/
theorem wp_revokec_close {ty : go.GoType} {dir : go.ChanDir}
    [ty ↓u go.ChannelType dir (go.StructType [])] (c : GoChan) :
    {{ revokeCloser (GF := GF) c }} (App (Val #(functions go.close [ty])) (Val #c))
    {{ RET #(); True }} := by
  iintro %Φ Hcl HΦ
  iunfold revokeCloser at Hcl
  icases Hcl with ⟨%γc, #Hch, Hown⟩
  iapply chan.wp_close (ct := ty) (V := Unit) c γc $$ Hch
  iintro _
  unfold closeAu
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists .Idle
  dsimp only
  iframe Hown
  iintro -
  imod Hmask with -
  imodintro
  iapply HΦ
  itrivial

end closeLemmas

end lease
end EtcdGrove
end Perennial
