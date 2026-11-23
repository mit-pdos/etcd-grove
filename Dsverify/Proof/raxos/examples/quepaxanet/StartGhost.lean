/-
The start's ghost state (the lab's `Kit/StartGhost.lean`, re-based on this branch's `Ghost.lean`):
maps built from lists of keys (`mkMap`), the initial resources of every ghost name (`consRes`,
`smrRes`, `ownRes`, `alloc_init`), and the two invariants' initial states (`consInv_init`,
`smrInv_init`).

Changed against the lab: over any bundle `GF` (the kit's specs are); tickets are `Int × Nat × Nat`,
the frames' positions `Nat × Nat` and the read counters keyed by the net extension's connection
numbers (`Nat`); the outputs are `KOut`; the new name `net` (`netTok γ k` for the server machines
`k = 1..5`) is allocated here; the abstract state's other half goes to the pending library
(`ownRes`' `ownState`-half, `pend_alloc`), not to the orchestrator.
-/
module

public import Dsverify.Proof.raxos.examples.quepaxanet.Kit

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

namespace Perennial

namespace raxos.examples.quepaxanet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net BigSepM BigSepL
open raxos raxos.pure

/-! ## Maps from lists of keys -/

/-- The map `k ↦ f k` for the keys `l`. -/
def mkMap {K V : Type} [DecidableEq K] (l : List K) (f : K → V) : GMap K V :=
  l.foldr (fun k m => GMap.insert k (f k) m) ∅

theorem mkMap_lookup {K V : Type} [DecidableEq K] (l : List K) (f : K → V) (k : K) :
    (mkMap l f).lookup k = if k ∈ l then some (f k) else none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show (GMap.insert a (f a) (mkMap l f)).lookup k = _
    unfold GMap.insert
    simp only [ih, List.mem_cons]
    by_cases h : a = k
    · subst h; simp
    · simp [h, Ne.symm h]

theorem bigSepM_mkMap {PROP : Type _} [BI PROP] {K V : Type} [DecidableEq K] (f : K → V)
    (Φ : K → V → PROP) : ∀ l : List K, l.Nodup →
    (([∗map] k ↦ v ∈ mkMap l f, Φ k v) ⊣⊢ [∗list] k ∈ l, Φ k (f k))
  | [], _ => by
    show ([∗map] k ↦ v ∈ (∅ : GMap K V), Φ k v) ⊣⊢ _
    exact bigSepM_empty.trans bigSepL_nil.symm
  | a :: l, h => by
    have hn : a ∉ l := (List.nodup_cons.1 h).1
    have hl := bigSepM_mkMap f Φ l (List.nodup_cons.1 h).2
    show ([∗map] k ↦ v ∈ PartialMap.insert (mkMap l f) a (f a), Φ k v) ⊣⊢ _
    refine (bigSepM_insert ?_).trans ?_
    · show (mkMap l f).lookup a = none
      rw [mkMap_lookup]; simp [hn]
    · exact (sep_congr .rfl hl).trans (bigSepL_cons (Φ := fun _ k => Φ k (f k))).symm

theorem nodup_flatMap' {α β : Type _} (f : α → List β) : ∀ (L : List α), L.Nodup →
    (∀ a ∈ L, (f a).Nodup) → (∀ a ∈ L, ∀ b ∈ L, a ≠ b → ∀ x ∈ f a, x ∉ f b) →
    (L.flatMap f).Nodup
  | [], _, _, _ => by simp
  | a :: L, hL, h1, h2 => by
    rw [List.nodup_cons] at hL
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨h1 a (by simp), nodup_flatMap' f L hL.2 (fun b hb => h1 b (by simp [hb]))
      (fun b hb b' hb' => h2 b (by simp [hb]) b' (by simp [hb'])), ?_⟩
    intro x hx y hy hxy
    subst hxy
    rw [List.mem_flatMap] at hy
    obtain ⟨b, hb, hy⟩ := hy
    exact h2 a (by simp) b (by simp [hb]) (fun h => hL.1 (h ▸ hb)) x hx hy

theorem nodup_serverIds : serverIds.Nodup := by decide

theorem nodup_srvNats : ([1, 2, 3, 4, 5] : List Nat).Nodup := by decide

theorem mem_ticketsOf {c : Nat} {t : Ticket} (h : t ∈ ticketsOf c) : t.2.1 = c := by
  unfold ticketsOf at h
  simp only [List.mem_flatMap, List.mem_map] at h
  obtain ⟨_, _, _, _, rfl⟩ := h
  rfl

/-- The workload's tickets, client by client, are distinct. -/
theorem clientTickets_nodup : ((List.range 6).flatMap ticketsOf).Nodup := by
  refine nodup_flatMap' _ _ List.nodup_range (fun c _ => ?_) ?_
  · unfold ticketsOf
    refine nodup_flatMap' _ _ nodup_serverIds (fun k _ => ?_) ?_
    · exact List.pairwise_map.2 (List.nodup_range.imp (fun h h2 => h (by simpa using h2)))
    · intro a _ b _ hab x hx hy
      simp only [List.mem_map] at hx hy
      obtain ⟨j, _, rfl⟩ := hx
      obtain ⟨j', _, h⟩ := hy
      simp at h; omega
  · intro a _ b _ hab x hx hy
    exact hab ((mem_ticketsOf hx).symm.trans (mem_ticketsOf hy))

/-! ## The initial resources -/

section init
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The recorders' initial slot states (no slot yet). -/
abbrev R0 : GMap Int (GMap Int RecSt) := mkMap serverIds (fun _ => ∅)
/-- The proxies' initial frontiers. -/
abbrev Fr0 : GMap Int Int := mkMap serverIds (fun _ => 1)
/-- The clients' initial request counts. -/
abbrev Cnt0 : GMap Nat Nat := mkMap (List.range 6) (fun _ => 0)
/-- The initial registry: only `"nil"`. -/
abbrev Reg0 : GMap GoString RegEntry := mkMap [go!"nil"] (fun _ => RegEntry.nil)

/-- What `consInv` holds at the start. -/
def consRes (γ : QNames) : IProp GF :=
  iprop(monoListAuthOwn γ.hist 1 ([] : World) ∗
    ghostMapAuth γ.recs 1 R0 ∗ ([∗map] r ↦ m ∈ R0, ghostMapElem γ.recs r (DFrac.own (1 : Qp).half) m) ∗
    ghostMapAuth γ.front 1 Fr0 ∗
    ([∗map] me ↦ n ∈ Fr0, ghostMapElem γ.front me (DFrac.own (1 : Qp).half) n) ∗
    ghostMapAuth γ.inits 1 (∅ : GMap (Int × Int) Unit) ∗
    ghostMapAuth γ.tix 1 (∅ : GMap Ticket (Nat × Nat)) ∗
    ghostMapAuth γ.cred 1 (∅ : GMap Ticket Unit) ∗
    ghostMapAuth γ.rd 1 (∅ : GMap Nat Nat) ∗
    monoListAuthOwn γ.spent 1 ([] : List Ticket))

/-- What `smrInv` holds at the start. -/
def smrRes (γ : QNames) : IProp GF :=
  iprop(monoListAuthOwn γ.exec 1 ([] : List (List GoString)) ∗
    ghostVar γ.puts (1 : Qp).half ([] : List (GoString × GoString)) ∗
    ghostMapAuth γ.reg 1 Reg0 ∗
    ghostMapAuth γ.res 1 (∅ : GMap GoString KOut) ∗
    ghostMapAuth γ.cnt 1 Cnt0 ∗
    ([∗map] c ↦ n ∈ Cnt0, ghostMapElem γ.cnt c (DFrac.own (1 : Qp).half) n))

/-- The machines' parts at the start (and the abstract state's half, for the pending library). -/
def ownRes (γ : QNames) : IProp GF :=
  iprop(confTok γ ∗ ghostVar γ.puts (1 : Qp).half ([] : List (GoString × GoString)) ∗
    ([∗list] c ∈ List.range 6, ghostMapElem γ.cnt c (DFrac.own (1 : Qp).half) (0 : Nat)) ∗
    ([∗list] c ∈ List.range 6, [∗list] t ∈ ticketsOf c, ticketTok γ t) ∗
    ghostMapElem γ.reg go!"nil" .discard RegEntry.nil ∗ spentLb γ 0 ∗
    ([∗list] r ∈ serverIds, recHalf γ r ∅) ∗
    ([∗list] me ∈ serverIds, initFront γ me 1) ∗
    ([∗list] k ∈ ([1, 2, 3, 4, 5] : List Nat), netTok γ k))

theorem halves_mkMap {K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V]
    (g : GName) (f : K → V) (l : List K) (hl : l.Nodup) :
    ([∗map] k ↦ v ∈ mkMap l f, ghostMapElem (GF := GF) g k (DFrac.own 1) v) ⊢
      ([∗map] k ↦ v ∈ mkMap l f, ghostMapElem g k (DFrac.own (1 : Qp).half) v) ∗
      [∗list] k ∈ l, ghostMapElem g k (DFrac.own (1 : Qp).half) (f k) :=
  (bigSepM_mkMap f _ l hl).1.trans <|
    (bigSepL_mono_of_forall (fun {_ k} => (ghostMapElem_halves g k (f k)).1)).trans <|
    bigSepL_sep_eqv.1.trans (sep_mono (bigSepM_mkMap f _ l hl).2 .rfl)

/-- Allocate every ghost name but the gRPC world's (`grpc` is a placeholder here: the world's
registry is allocated over the method specs, which mention the other names, `Start.lean`). -/
theorem alloc_init : ⊢@{IProp GF} |==> ∃ γ : QNames, consRes γ ∗ smrRes γ ∗ ownRes γ := by
  imod ghost_map_alloc_empty (GF := GF) (K := Unit) (V := QConf) with ⟨%gconf, Hconf⟩
  imod mono_list_own_alloc (GF := GF) ([] : World) with ⟨%gh, Hh, -⟩
  imod ghost_map_alloc (GF := GF) R0 with ⟨%gr, Hr, Hrs⟩
  icases halves_mkMap gr _ _ nodup_serverIds $$ Hrs with ⟨Hrs, Hrs'⟩
  imod ghost_map_alloc (GF := GF) Fr0 with ⟨%gf, Hf, Hfs⟩
  icases halves_mkMap gf _ _ nodup_serverIds $$ Hfs with ⟨Hfs, Hfs'⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Int × Int) (V := Unit) with ⟨%gi, Hi⟩
  imod mono_list_own_alloc (GF := GF) ([] : List (List GoString)) with ⟨%ge, He, -⟩
  imod ghostVar_alloc (GF := GF) ([] : List (GoString × GoString)) with ⟨%gp, Hp⟩
  icases (ghostVar_split_half gp 1 _).1 $$ Hp with ⟨Hp, Hp'⟩
  imod ghost_map_alloc (GF := GF) Reg0 with ⟨%greg, Hreg, Hregs⟩
  ihave Hregs := (bigSepM_mkMap _ _ [go!"nil"] (by decide)).1 $$ Hregs
  icases bigSepL_cons.1 $$ Hregs with ⟨Hnil, -⟩
  imod ghostMapElem_persist $$ Hnil with #Hnil
  imod ghost_map_alloc_empty (GF := GF) (K := GoString) (V := KOut) with ⟨%gres, Hres⟩
  imod ghost_map_alloc (GF := GF) Cnt0 with ⟨%gc, Hc, Hcs⟩
  icases halves_mkMap gc _ _ (List.nodup_range) $$ Hcs with ⟨Hcs, Hcs'⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Ticket) (V := Nat × Nat) with ⟨%gtix, Htix⟩
  imod ghost_map_alloc (GF := GF) (mkMap ((List.range 6).flatMap ticketsOf) (fun _ => ()))
    with ⟨%gtick, -, Hticks⟩
  ihave Hticks := (bigSepM_mkMap _ _ _ clientTickets_nodup).1 $$ Hticks
  rw [bigSepL_flatMap]
  imod ghost_map_alloc_empty (GF := GF) (K := Ticket) (V := Unit) with ⟨%gcred, Hcred⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Nat) with ⟨%grd, Hrd⟩
  imod mono_list_own_alloc (GF := GF) ([] : List Ticket) with ⟨%gs, Hs, Hslb⟩
  imod ghost_map_alloc (GF := GF) (mkMap ([1, 2, 3, 4, 5] : List Nat) (fun _ => ()))
    with ⟨%gnet, -, Hnets⟩
  ihave Hnets := (bigSepM_mkMap _ _ _ nodup_srvNats).1 $$ Hnets
  imodintro
  iexists ⟨gconf, gh, gr, gf, gi, ge, gp, greg, gres, gc, gh, gtix, gtick, gcred, grd, gs, gnet⟩
  unfold consRes smrRes ownRes spentLb recHalf initFront ticketTok confTok netTok
  dsimp only
  iframe # ∗
  ipureintro
  simp

theorem consInv_init [NetProtoGS] (γ : QNames) : consRes γ ⊢ consInv (G := Gg) γ := by
  unfold consRes consInv
  iintro ⟨Hh, Hr, Hrs, Hf, Hfs, Hi, Htix, Hcr, Hrd, Hs⟩
  have hR : ∀ r, R0.lookup r = if r ∈ serverIds then some ∅ else none :=
    fun r => mkMap_lookup _ _ r
  have hF : ∀ r, Fr0.lookup r = if r ∈ serverIds then some 1 else none :=
    fun r => mkMap_lookup _ _ r
  iexists [], R0, Fr0, ∅, ∅, ∅, ∅, []
  iframe
  isplitr
  · ileft; ipureintro; rfl
  isplitr
  · ipureintro
    refine ⟨fun r => ?_, fun r m hm i => ?_⟩
    · show (R0.lookup r).isSome = true ↔ _
      rw [hR]; split <;> simp_all
    · change R0.lookup r = some m at hm
      rw [hR] at hm
      split at hm
      · cases hm; rfl
      · cases hm
  isplitr
  · iapply bigSepM_empty.2; iempintro
  isplitr
  · iapply bigSepL_nil.2; iempintro
  isplitr
  · iapply bigSepM_empty.2; iempintro
  isplitr
  · ipureintro
    refine ⟨fun me => ?_, fun me n hn => ?_, fun _ _ h => by simp at h, fun _ _ _ _ h => by simp at h,
      fun _ h => by simp at h, fun _ h => by simp at h, List.nodup_nil, fun _ h => by simp at h⟩
    · show (Fr0.lookup me).isSome = true ↔ _
      rw [hF]; split <;> simp_all
    · change Fr0.lookup me = some n at hn
      rw [hF] at hn
      split at hn
      · cases hn; simp
      · cases hn
  · iapply bigSepL_nil.2; iempintro

theorem smrInv_init (γ : QNames) : smrRes γ ∗ ghostMapElem γ.reg go!"nil" .discard RegEntry.nil ⊢
    smrInv (G := Gg) γ := by
  unfold smrRes smrInv
  iintro ⟨⟨He, Hp, Hreg, Hres, Hc, Hcs⟩, #Hnil⟩
  have hReg : ∀ x, Reg0.lookup x = if x = go!"nil" then some RegEntry.nil else none := by
    intro x; unfold Reg0; rw [mkMap_lookup]; simp
  have hdone : ∀ B, (execLog B []).done = [] := fun _ => rfl
  iexists [], Reg0, ∅, Cnt0
  iframe
  isplitr
  · iapply bigSepL_nil.2; iempintro
  isplitr
  · iapply (bigSepM_mkMap _ _ [go!"nil"] (by decide)).2
    iapply bigSepL_cons.2
    iframe Hnil
    iapply bigSepL_nil.2; iempintro
  isplitr
  · iapply bigSepM_empty.2; iempintro
  isplitr
  · ipureintro
    refine ⟨?_, ?_, fun x e he hn => ?_, fun x he => ?_, fun x c j inp q t he => ?_, fun x => ?_,
      fun x hx => ?_,
      fun x o h => by simp at h⟩
    · intro c n h
      have h' : (Cnt0).lookup c = some n := h
      rw [mkMap_lookup] at h'
      split at h'
      · rename_i hc; simp at hc h'; omega
      · cases h'
    · show Reg0.lookup _ = _
      rw [hReg]; simp
    · change Reg0.lookup x = some e at he
      rw [hReg] at he
      split at he
      · assumption
      · cases he
    · change Reg0.lookup x = some _ at he
      rw [hReg] at he
      split at he <;> cases he
    · change Reg0.lookup x = some _ at he
      rw [hReg] at he
      split at he <;> cases he
    · simp [hdone]
    · simp [hdone] at hx
  · iapply (bigSepM_mkMap _ _ [go!"nil"] (by decide)).2
    iapply bigSepL_cons.2
    isplitl
    · itrivial
    · iapply bigSepL_nil.2; iempintro

end init

end raxos.examples.quepaxanet
end Perennial
