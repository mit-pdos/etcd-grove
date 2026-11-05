/-
**`Recover`'s ghost step** (the lease-expiry plan's S1, 2026-11-04): the leases `initAndRecover`
made join the lessor in place of the old ones. Lean-first (no Rocq counterpart).

Each recovered `*Lease` is registered in the item sets' map with the empty set (as `Grant` registers
a fresh one: `recover_one`, over the list `recover_all`), its locks made; the closers' map is
replaced (the old leases' elements, both halves, deleted; the new ones inserted: `closers_swap`);
the live set set to the records' ids, each meeting the grant guard (`lessor_live_set`); and one
snapshot appended to the history, the recovered leases with no item and their TTLs (`recover_hist`).
In the monotone mode the append keeps `histMono` only when every live id is recovered.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorRecover

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lease

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease

/-! ### The recovered map, pure -/

/-- Two elements of a list whose images are distinct are equal when their images are. -/
theorem nodup_map_inj {α β : Type} (f : α → β) :
    ∀ (xs : List α), (xs.map f).Nodup → ∀ {p q : α}, p ∈ xs → q ∈ xs → f p = f q → p = q
  | [], _, _, _, hp, _, _ => by simp at hp
  | x :: xs, hnd, p, q, hp, hq, he => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 hp with rfl | hp' <;> rcases List.mem_cons.1 hq with rfl | hq'
    · rfl
    · exact absurd (by rw [he]; exact List.mem_map_of_mem hq') hnd.1
    · exact absurd (by rw [← he]; exact List.mem_map_of_mem hp') hnd.1
    · exact nodup_map_inj f xs hnd.2 hp' hq' he

/-- The recovered lease map with a first record, its id not among the others'. -/
theorem recMap_cons (x : (w64 × w64 × w64) × Loc) (xs : List ((w64 × w64 × w64) × Loc))
    (h : x.1.1 ∉ xs.map (·.1.1)) : recMap (x :: xs) = (recMap xs).insert x.1.1 x.2 :=
  foldIns_cons (fun p : (w64 × w64 × w64) × Loc => p.1.1) (fun p => p.2) x xs ∅ h

/-- The recovered lease map's ids are the records'. -/
theorem recMap_isSome (xs : List ((w64 × w64 × w64) × Loc)) (k : w64) :
    ((recMap xs).lookup k).isSome ↔ k ∈ xs.map (·.1.1) := by
  have := foldIns_isSome (fun p : (w64 × w64 × w64) × Loc => p.1.1) (fun p => p.2) k xs ∅
  simp only [GMap.lookup_empty, Option.isSome_none, Bool.false_eq_true, or_false] at this
  exact this

/-- The recovered lease map's entries are the records', the ids distinct. -/
theorem recMap_lookup (xs : List ((w64 × w64 × w64) × Loc)) (k : w64) (l : Loc)
    (hnd : (xs.map (·.1.1)).Nodup) :
    (recMap xs).lookup k = some l ↔ ∃ p ∈ xs, p.1.1 = k ∧ p.2 = l := by
  have := foldIns_lookup (fun p : (w64 × w64 × w64) × Loc => p.1.1) (fun p => p.2) k l xs ∅ hnd
  simp only [GMap.lookup_empty, reduceCtorEq, and_false, or_false] at this
  exact this

/-- The recovered TTLs' ids are the records'. -/
theorem recTTLs_isSome (mt : w64) (recs : List (w64 × w64 × w64)) (k : w64) :
    ((recTTLs mt recs).lookup k).isSome ↔ k ∈ recs.map (·.1) := by
  have := foldIns_isSome (fun x : w64 × w64 × w64 => x.1) (fun x => grantTTL mt x.2.1) k recs ∅
  simp only [GMap.lookup_empty, Option.isSome_none, Bool.false_eq_true, or_false] at this
  exact this

/-- A record's recovered TTL, the ids distinct. -/
theorem recTTLs_lookup (mt : w64) (recs : List (w64 × w64 × w64)) (x : w64 × w64 × w64)
    (hx : x ∈ recs) (hnd : (recs.map (·.1)).Nodup) :
    (recTTLs mt recs).lookup x.1 = some (grantTTL mt x.2.1) :=
  ((foldIns_lookup (fun x : w64 × w64 × w64 => x.1) (fun x => grantTTL mt x.2.1) x.1
    (grantTTL mt x.2.1) recs ∅ hnd).2 (Or.inl ⟨x, hx, rfl, rfl⟩))

/-- The recovered lease map has at most one lease per record. -/
theorem recMap_size (xs : List ((w64 × w64 × w64) × Loc)) : GMap.size (recMap xs) ≤ xs.length := by
  have := foldIns_size (fun p : (w64 × w64 × w64) × Loc => p.1.1) (fun p => p.2) xs ∅
  have h0 : GMap.size (∅ : GMap w64 Loc) = 0 := GMap.map_size_empty
  unfold recMap recMapFrom; omega

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- The recovered snapshot: the recovered lease map, no item, the recovered TTLs. -/
abbrev recSnap (mt : w64) (xs : List ((w64 × w64 × w64) × Loc)) : LSnap :=
  (recMap xs, ∅, recTTLs mt (xs.map Prod.fst))

/-- **`Recover`'s snapshot keeps the item sets' agreement**: its leases are fresh (in no snapshot),
distinct, registered with the empty set, and it has no item. -/
theorem recover_step_ok {hs : List LSnap} {Sm : GMap Loc (GMap LeaseItem Unit)} {τ : LSnap}
    (mt : w64) (xs : List ((w64 × w64 × w64) × Loc)) (hlast : hs.getLast? = some τ)
    (hnd : (xs.map (·.1.1)).Nodup)
    (hreg : ∀ p ∈ xs, Sm.lookup p.2 = some ∅ ∧
      ∀ (k : Nat) (τ : LSnap) (id' : w64), hs[k]? = some τ → τ.1.lookup id' ≠ some p.2)
    (hnd2 : (xs.map (·.2)).Nodup) (hok : setsOk hs Sm) (hh : histOk hs) :
    setsOk (hs ++ [recSnap mt xs]) Sm ∧ histOk (hs ++ [recSnap mt xs]) := by
  have hlk : ∀ (id : w64) (l : Loc), (recSnap mt xs).1.lookup id = some l →
      ∃ p ∈ xs, p.1.1 = id ∧ p.2 = l := fun id l h => (recMap_lookup xs id l hnd).1 h
  refine setsOk_snoc hlast hok hh (fun _ h => h) ?_ ?_ ?_ ?_ (fun l S hS _ => Or.inl hS) ?_
  · intro id l h
    obtain ⟨p, hp, -, rfl⟩ := hlk id l h
    rw [(hreg p hp).1]; rfl
  · intro id l h
    obtain ⟨p, hp, -, rfl⟩ := hlk id l h
    exact Or.inr (hreg p hp).2
  · intro id id' l h h'
    obtain ⟨p, hp, rfl, rfl⟩ := hlk id l h
    obtain ⟨p', hp', rfl, he⟩ := hlk id' p.2 h'
    have : p' = p := nodup_map_inj (·.2) xs hnd2 hp' hp he
    rw [this]
  · intro id l S h hS
    obtain ⟨p, hp, -, rfl⟩ := hlk id l h
    rw [(hreg p hp).1] at hS
    cases hS
    intro it
    simp only [GMap.lookup_empty, reduceCtorEq]
  · intro it id h; simp at h


/-- **Registering a fresh `*Lease`** (in no snapshot, not in the map) with the empty set keeps
the item sets' agreement. -/
theorem setsOk_register {hs : List LSnap} {Sm : GMap Loc (GMap LeaseItem Unit)} {l : Loc}
    (hok : setsOk hs Sm)
    (hnew : ∀ (k : Nat) (τ : LSnap) (id' : w64), hs[k]? = some τ → τ.1.lookup id' ≠ some l) :
    setsOk hs (Sm.insert l ∅) := by
  refine ⟨fun i σ id l' hi hl => ?_, fun l' S hS => ?_⟩
  · rw [GMap.lookup_insert_is_Some]
    by_cases h : l = l'
    · exact Or.inl h
    · exact Or.inr ⟨h, hok.1 i σ id l' hi hl⟩
  · rcases (GMap.lookup_insert_Some _ _ _ _ _).1 hS with ⟨rfl, rfl⟩ | ⟨_, h⟩
    · exact Or.inl ⟨fun i σ id hi => hnew i σ id hi, rfl⟩
    · exact hok.2 l' S h

/-- The recovered lease map's conjunction is the records'. -/
theorem recMap_bigSepM (Φ : w64 → Loc → IProp GF) :
    ∀ (xs : List ((w64 × w64 × w64) × Loc)), (xs.map (·.1.1)).Nodup →
      (([∗map] k ↦ v ∈ recMap xs, Φ k v) ⊣⊢ [∗list] p ∈ xs, Φ p.1.1 p.2)
  | [], _ => by
    have h : recMap ([] : List ((w64 × w64 × w64) × Loc)) = ∅ := rfl
    rw [h]
    exact BigSepM.bigSepM_empty.trans BigSepL.bigSepL_nil.symm
  | x :: xs, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [recMap_cons x xs hnd.1]
    have hn : Iris.Std.PartialMap.get? (recMap xs) x.1.1 = none := by
      show (recMap xs).lookup x.1.1 = none
      cases h : (recMap xs).lookup x.1.1 with
      | none => rfl
      | some _ =>
        have := (recMap_isSome xs x.1.1).1 (by rw [h]; rfl)
        exact absurd this hnd.1
    refine (BigSepM.bigSepM_insert hn).trans ?_
    refine (sep_congr .rfl (recMap_bigSepM Φ xs hnd.2)).trans ?_
    exact (BigSepL.bigSepL_cons (Φ := fun _ (p : (w64 × w64 × w64) × Loc) => Φ p.1.1 p.2)).symm

/-- **What a recovered lease of id `id` at `l` gives the lessor and its owner** (`recover_one`): the
lease (`isLeaseObj`), its state under `le.mu` (`leaseMeta`, at the whole fraction), and the owner's:
its half of the empty item set, a reader slot of its lock, its `revokec` with the right to close it. -/
def recCore (γl : GName) (id : w64) (l : Loc) : IProp GF :=
  iprop(isLeaseObj γl l ∗ leaseMeta id l 1 ∗
    leaseItemsOwn l ∅ id ∗ sync.ownRWMutex (lsF go!"mu" l) (leaseItems γl l) ∗
    (∃ c : GoChan, lsF go!"revokec" l ↦□ c ∗ revokeCloser c))

/-- **A recovered lease, set up**: its read-only `ttl` (the record's, raised to `mt`) and
`recCore`. -/
def recDone (γl : GName) (mt : w64) (x : w64 × w64 × w64) (l : Loc) : IProp GF :=
  iprop(lsF go!"ttl" l ↦□ grantTTL mt x.2.1 ∗ recCore γl x.1 l)

/-- **One recovered lease set up** (as `Grant`'s `grant_hist` and `closers_grant`, without the
append): its `*Lease` (whose `ID` it owns whole, so in no snapshot) registered with the empty set,
its `ID` and `ttl` read-only, its two locks made, their spare slots in the lease's pools. -/
theorem recover_one (γl : GName) (γr : LessorRdNames) (hs : List LSnap)
    (Sm : GMap Loc (GMap LeaseItem Unit)) (mt : w64) (x : w64 × w64 × w64) (l : Loc) (E : CoPset)
    (hE : ↑lessorRdN ⊆ E) :
    lessorRdInv (GF := GF) γl ∗ lessorPinR γl γr ∗ monoListAuthOwn γr.1 (1 : Qp).half hs ∗
      ghostMapAuth γr.2.1 (1 : Qp).half Sm ∗ recLease mt x l ⊢
    |={E}=> ⌜Sm.lookup l = none ∧
        ∀ (k : Nat) (τ : LSnap) (id' : w64), hs[k]? = some τ → τ.1.lookup id' ≠ some l⌝ ∗
      monoListAuthOwn γr.1 (1 : Qp).half hs ∗ ghostMapAuth γr.2.1 (1 : Qp).half (Sm.insert l ∅) ∗
      recDone γl mt x l := by
  iintro ⟨#Hrd, #Hp, Ho, HSo, Hl⟩
  iunfold recLease at Hl
  icases Hl with ⟨%Hlnn, HID, Httl, Hrem, HexMu, Hexp, Hmu0, ⟨%sm, HiS, Hsm⟩, ⟨%c, Hrc, Hrcl⟩⟩
  ipersist Httl
  ipersist Hrc
  -- registered with the empty set, under the readers' invariant
  ihave #Hrd' := Hrd
  iunfold lessorRdInv at Hrd'
  icases Hrd' with ⟨%γr1, #Hp1, #Hinv⟩
  ihave %H1 := lessorPinR_agree γl γr γr1 $$ [$Hp $Hp1]
  subst H1
  iinv Hinv with Hb Hclose
  iunfold lessorRdBody at Hb
  icases Hb with ⟨%hs0, %Sm0, >Ha, >HS, >%Hok, >%Hmono, >HU, #>Htie, #>Hids⟩
  ihave %Hh := monoListAuthOwn_agree γr.1 _ _ hs hs0 $$ Ho Ha
  obtain ⟨-, rfl⟩ := Hh
  ihave %HSm := ghostMapAuth_agree γr.2.1 _ _ Sm Sm0 $$ HSo HS
  subst HSm
  cases Hfresh : Sm.lookup l with
  | some S =>
    ihave ⟨%id', HID'⟩ := BigSepM.bigSepM_lookup Hfresh $$ Hids
    iexfalso
    iapply w64_own_discard_false _ x.1 id' $$ [$HID $HID']
  | none =>
  have hnew : ∀ (k : Nat) (τ : LSnap) (id' : w64), hs[k]? = some τ → τ.1.lookup id' ≠ some l :=
    fun k τ id' hk h => by have := Hok.1.1 k τ id' l hk h; rw [Hfresh] at this; cases this
  ihave HSf := (ghostMapAuth_halves γr.2.1 Sm).2 $$ [$HSo $HS]
  imod ghost_map_insert l (∅ : GMap LeaseItem Unit) Hfresh $$ HSf with ⟨HSf, He⟩
  icases (ghostMapAuth_halves γr.2.1 _).1 $$ HSf with ⟨HSo, HS⟩
  ipersist HID
  imod Hclose $$ [Ha HS HU] with -
  · inext; iunfold lessorRdBody; iexists hs, Sm.insert l ∅
    iframe Ha HS Htie
    isplitr
    · ipureintro; exact ⟨setsOk_register Hok.1 hnew, Hok.2⟩
    isplitr
    · ipureintro; exact Hmono
    isplitl [HU]
    · iexact HU
    iapply (BigSepM.bigSepM_insert (Φ := fun l _ => iprop(∃ id : w64, lsF go!"ID" l ↦□ id))
      (show Iris.Std.PartialMap.get? Sm l = none from Hfresh)).2
    isplitr
    · iexists x.1; iexact HID
    iexact Hids
  -- the expiry lock: its guard half of `expiry`, its spare slots in the lease's other pool
  icases ptsto_halves_split _ _ $$ Hexp with ⟨Hexp, HexpG⟩
  imod (sync.init_RWMutex (leaseExpiry l) (E := E) (lsF go!"expiryMu" l)) $$ [HexpG] HexMu
    with HexRs
  · inext; iunfold leaseExpiry; iexists _; iexact HexpG
  have hmax : sync.rwmutex.actualMaxReaders.toNat =
      (sync.rwmutex.actualMaxReaders.toNat - 1) + 1 := by
    rw [sync.rwmutex.actualMaxReaders_unseal]; decide
  rw [hmax, List.replicate_succ]
  icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ HexRs with ⟨HexR, HexRest⟩
  icases sync.ownRWMutex_guard _ _ $$ HexR with ⟨-, #HexG⟩
  imod slotsPool leaseExpPoolN (sync.ownRWMutex (lsF go!"expiryMu" l) (leaseExpiry l)) E $$ HexRest
    with #Hpe
  -- the lease's lock, its slots: the owner's and the pool's
  icases ptsto_halves_split _ sm $$ HiS with ⟨HiS, HiS'⟩
  icases ownMap_halves_split sm (∅ : GMap LeaseItem Unit) $$ Hsm with ⟨Hsm, Hsm'⟩
  imod (sync.init_RWMutex (leaseItems γl l) (E := E) (lsF go!"mu" l)) $$ [HiS Hsm He] Hmu0
    with HmuRs
  · inext; iunfold leaseItems; iexists sm, ∅, γr; iframe; iframe #
  rw [hmax, List.replicate_succ]
  icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ HmuRs with ⟨HmuR, HmuRest⟩
  icases sync.ownRWMutex_guard _ _ $$ HmuR with ⟨HmuR, #HmuG⟩
  imod slotsPool leasePoolN (sync.ownRWMutex (lsF go!"mu" l) (leaseItems γl l)) E $$ HmuRest
    with #Hpo
  imodintro
  isplitr
  · ipureintro; exact ⟨rfl, hnew⟩
  iframe Ho HSo
  iunfold recDone
  iframe Httl
  iunfold recCore
  iframe HmuR
  isplitr
  · iunfold isLeaseObj; iframe HmuG Hrd HexG Hpo Hpe; ipureintro; exact Hlnn
  isplitl [Hrem Hexp]
  · iunfold leaseMeta
    iframe HID HexG
    isplitr
    · iexists _; iexact Httl
    isplitr
    · iexists c; iexact Hrc
    isplitl [Hrem]
    · iexists _; iexact Hrem
    iexists _; iexact Hexp
  isplitl [HiS' Hsm']
  · iunfold leaseItemsOwn
    iexists sm, ∅
    iframe HiS' Hsm'
    ipureintro
    intro it
    simp only [GMap.lookup_empty, reduceCtorEq]
  iexists c; iframe Hrc Hrcl

/-- **Every recovered lease set up** (`recover_one` over the records): the item sets' map grows by
the recovered `*Lease`s, each fresh (in no snapshot, not in the map before), distinct, with the
empty set. -/
theorem recover_all (γl : GName) (γr : LessorRdNames) (hs : List LSnap) (mt : w64) (E : CoPset)
    (hE : ↑lessorRdN ⊆ E) :
    ∀ (xs : List ((w64 × w64 × w64) × Loc)) (Sm : GMap Loc (GMap LeaseItem Unit)),
    lessorRdInv (GF := GF) γl ∗ lessorPinR γl γr ∗ monoListAuthOwn γr.1 (1 : Qp).half hs ∗
      ghostMapAuth γr.2.1 (1 : Qp).half Sm ∗ ([∗list] p ∈ xs, recLease mt p.1 p.2) ⊢
    |={E}=> ∃ Sm' : GMap Loc (GMap LeaseItem Unit),
      ⌜(∀ l, (Sm.lookup l).isSome → Sm'.lookup l = Sm.lookup l) ∧
        (∀ (l : Loc) (S : GMap LeaseItem Unit), Sm'.lookup l = some S →
          Sm.lookup l = some S ∨ (l ∈ xs.map (·.2) ∧ S = ∅)) ∧
        (∀ p ∈ xs, Sm.lookup p.2 = none ∧ Sm'.lookup p.2 = some ∅ ∧
          ∀ (k : Nat) (τ : LSnap) (id' : w64), hs[k]? = some τ → τ.1.lookup id' ≠ some p.2) ∧
        (xs.map (·.2)).Nodup⌝ ∗
      monoListAuthOwn γr.1 (1 : Qp).half hs ∗ ghostMapAuth γr.2.1 (1 : Qp).half Sm' ∗
      [∗list] p ∈ xs, recDone γl mt p.1 p.2
  | [], Sm => by
    iintro ⟨-, -, Ho, HSo, -⟩
    imodintro
    iexists Sm
    iframe Ho HSo
    isplitr
    · ipureintro
      refine ⟨fun _ _ => rfl, fun _ _ h => Or.inl h, fun _ h => by simp at h, List.nodup_nil⟩
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; itrivial
  | x :: xs, Sm => by
    iintro ⟨#Hrd, #Hp, Ho, HSo, Hl⟩
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ Hl with ⟨Hx, Hl⟩
    imod recover_one γl γr hs Sm mt x.1 x.2 E hE $$ [$Hrd $Hp $Ho $HSo $Hx]
      with ⟨⟨%Hfr, %Hnew⟩, Ho, HSo, Hx⟩
    imod recover_all γl γr hs mt E hE xs (Sm.insert x.2 ∅) $$ [$Hrd $Hp $Ho $HSo $Hl]
      with ⟨%Sm', ⟨%H1, %H2, %H3, %H4⟩, Ho, HSo, Hl⟩
    imodintro
    iexists Sm'
    iframe Ho HSo
    isplitr
    · ipureintro
      have hx2 : Sm'.lookup x.2 = some ∅ := by
        rw [H1 x.2 (by rw [GMap.lookup_insert]; rfl), GMap.lookup_insert]
      refine ⟨fun l hl => ?_, fun l S hS => ?_, fun p hp => ?_, ?_⟩
      · have hne : x.2 ≠ l := fun h => by subst h; rw [Hfr] at hl; cases hl
        rw [H1 l (by rw [GMap.lookup_insert_ne _ _ hne]; exact hl), GMap.lookup_insert_ne _ _ hne]
      · rcases H2 l S hS with h | ⟨h1, h2⟩
        · rcases (GMap.lookup_insert_Some _ _ _ _ _).1 h with ⟨rfl, rfl⟩ | ⟨_, h⟩
          · exact Or.inr ⟨List.mem_cons_self .., rfl⟩
          · exact Or.inl h
        · exact Or.inr ⟨List.mem_cons_of_mem _ h1, h2⟩
      · rcases List.mem_cons.1 hp with rfl | hp
        · exact ⟨Hfr, hx2, Hnew⟩
        · obtain ⟨h1, h2, h3⟩ := H3 p hp
          refine ⟨?_, h2, h3⟩
          have hne : x.2 ≠ p.2 := fun h => by rw [← h, GMap.lookup_insert] at h1; cases h1
          rw [GMap.lookup_insert_ne _ _ hne] at h1; exact h1
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hm => ?_, H4⟩
        obtain ⟨p, hp, hpx⟩ := List.mem_map.1 hm
        have h1 := (H3 p hp).1
        rw [hpx, GMap.lookup_insert] at h1; cases h1
    iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
    iframe Hx Hl

/-- **The owner appends a snapshot whose TTLs are tied** (`Recover`: the snapshot is not derived
from the last one, so its tie is given, `ttlTie σ'`; the item sets unchanged). -/
theorem recover_hist (γl : GName) (γr : LessorRdNames) (hs : List LSnap)
    (Sm : GMap Loc (GMap LeaseItem Unit)) (σ' : LSnap) (E : CoPset) (hE : ↑lessorRdN ⊆ E)
    (hstep : setsOk hs Sm → histOk hs → setsOk (hs ++ [σ']) Sm ∧ histOk (hs ++ [σ']))
    (hmono : γr.2.2.1 = true → histMono hs → histMono (hs ++ [σ'])) (U Un : List w64)
    (hfresh : ∀ id : w64, (σ'.1.lookup id).isSome → id ∉ U)
    (hin : ∀ id : w64, snapHas σ' id → id ∈ Un) :
    lessorRdInv (GF := GF) γl ∗ lessorPinR γl γr ∗ monoListAuthOwn γr.1 (1 : Qp).half hs ∗
      monoListAuthOwn γr.1 (1 : Qp).half.half hs ∗ ghostMapAuth γr.2.1 (1 : Qp).half Sm ∗
      ttlTie σ' ∗ leaseEver γl U ⊢
    |={E}=> monoListAuthOwn γr.1 (1 : Qp).half (hs ++ [σ']) ∗
      monoListAuthOwn γr.1 (1 : Qp).half.half (hs ++ [σ']) ∗ ghostMapAuth γr.2.1 (1 : Qp).half Sm ∗
      leaseEver γl (U ++ Un) := by
  unfold lessorRdInv leaseEver
  iintro ⟨⟨%γr1, #Hp1, #Hinv⟩, #Hp, Ho, Hl, HSo, #Hσ', ⟨%γr2, #Hp2, HUo⟩⟩
  ihave %H1 := lessorPinR_agree γl γr γr1 $$ [$Hp $Hp1]
  subst H1
  ihave %H2 := lessorPinR_agree γl γr γr2 $$ [$Hp $Hp2]
  subst H2
  iinv Hinv with Hb Hclose
  iunfold lessorRdBody at Hb
  icases Hb with ⟨%hs0, %Sm0, >Ha, >HS, >%Hok, >%Hmono, >HU, #>Htie, #>Hids⟩
  icases HU with ⟨%U0, HU, %HUi⟩
  ihave %HUe := dghostVar_agree γr.2.2.2 _ _ _ _ $$ HUo HU
  subst HUe
  imod dghostVar_update_halves (U ++ Un) γr.2.2.2 U U $$ HUo HU with ⟨HUo, HU⟩
  ihave %Hh := monoListAuthOwn_agree γr.1 _ _ hs hs0 $$ Ho Ha
  obtain ⟨-, rfl⟩ := Hh
  ihave %HSm := ghostMapAuth_agree γr.2.1 _ _ Sm Sm0 $$ HSo HS
  subst HSm
  ihave #Htie' := ties_snoc hs σ' $$ [$Htie $Hσ']
  ihave Hfull := (hist_full γr.1 hs).2 $$ [$Ho $Hl $Ha]
  imod monoListAuthOwn_update_app [σ'] $$ Hfull with ⟨Hfull, -⟩
  icases (hist_full γr.1 _).1 $$ Hfull with ⟨Ho, Hl, Ha⟩
  imod Hclose $$ [Ha HS HU] with -
  · inext; iunfold lessorRdBody; iexists hs ++ [σ'], Sm; iframe Ha HS Htie' Hids
    isplitr
    · ipureintro; exact hstep Hok.1 Hok.2
    isplitr
    · ipureintro; exact fun h => hmono h (Hmono h)
    iexists U ++ Un; iframe HU; ipureintro
    refine ⟨?_, histIn_snoc_new (histIn_mono HUi.2 (fun x hx => List.mem_append_left _ hx))
      (fun x hx => List.mem_append_right _ (hin x hx))⟩
    rcases hsl : hs.getLast? with _ | τ
    · rw [List.getLast?_eq_none_iff] at hsl; subst hsl; exact histOnce_single σ'
    · exact histOnce_fresh hsl (fun id h => not_everIn_of_histIn HUi.2 (hfresh id h)) HUi.1
  imodintro
  iframe Ho Hl HSo
  iexists γr; iframe Hp HUo

/-- **The closers' map replaced** (`Recover`): the old leases' elements, both halves, deleted; the
recovered ones', both halves, inserted. -/
theorem closers_swap (γcl : GName) (M M' : GMap w64 Loc) :
    ghostMapAuth (GF := GF) γcl 1 M ∗
      ([∗map] id ↦ l ∈ M, ghostMapElem γcl id (DFrac.own (1 : Qp).half) l) ∗
      ([∗map] id ↦ l ∈ M, ghostMapElem γcl id (DFrac.own (1 : Qp).half) l) ==∗
    ghostMapAuth γcl 1 M' ∗
      ([∗map] id ↦ l ∈ M', ghostMapElem γcl id (DFrac.own (1 : Qp).half) l) ∗
      ([∗map] id ↦ l ∈ M', ghostMapElem γcl id (DFrac.own (1 : Qp).half) l) := by
  iintro ⟨Ha, H1, H2⟩
  ihave H : iprop([∗map] id ↦ l ∈ M, iprop(ghostMapElem (GF := GF) γcl id (DFrac.own (1 : Qp).half) l ∗
      ghostMapElem γcl id (DFrac.own (1 : Qp).half) l)) $$ [H1 H2]
  · rw [BigSepM.bigSepM_sep_eq]; iframe
  ihave H : iprop([∗map] id ↦ l ∈ M, ghostMapElem (GF := GF) γcl id (DFrac.own 1) l) $$ [H]
  · iapply BigSepM.bigSepM_impl $$ H
    iintro !> %k %v %_ H
    iapply (ghostMapElem_halves γcl k v).2 $$ H
  imod ghost_map_delete_big M $$ Ha H with Ha
  have hdisj : GMap.Disjoint M' (M \ M) := by
    intro k _ h2
    rw [gmap_lookup_difference] at h2
    cases h : M.lookup k <;> simp [h] at h2
  imod ghost_map_insert_big M' hdisj $$ Ha with ⟨Ha, H⟩
  have heq : M' ∪ (M \ M) = M' := by
    apply GMap.ext; intro k
    rw [gmap_lookup_union, gmap_lookup_difference]
    cases h : M.lookup k <;> cases M'.lookup k <;> simp
  rw [heq]
  ihave H : iprop([∗map] id ↦ l ∈ M', iprop(ghostMapElem (GF := GF) γcl id (DFrac.own (1 : Qp).half) l ∗
      ghostMapElem γcl id (DFrac.own (1 : Qp).half) l)) $$ [H]
  · iapply BigSepM.bigSepM_impl $$ H
    iintro !> %k %v %_ H
    iapply (ghostMapElem_halves γcl k v).1 $$ H
  ihave ⟨H1, H2⟩ : iprop(([∗map] id ↦ l ∈ M', ghostMapElem (GF := GF) γcl id (DFrac.own (1 : Qp).half) l) ∗
      [∗map] id ↦ l ∈ M', ghostMapElem γcl id (DFrac.own (1 : Qp).half) l) $$ [H]
  · rw [← BigSepM.bigSepM_sep_eq]; iexact H
  imodintro
  iframe

/-- **The live set replaced** (`Recover`), with both halves (the lessor's under `le.mu`, the
owner's), by a set every lease of which may be granted. -/
theorem lessor_live_set (γl : GName) (lp : Loc) (L L' : List w64) (M : GMap w64 Loc) :
    lessorAuth (GF := GF) γl 1 lp L M ∗ leaseFrag γl (1 : Qp).half L ∗
      leaseFrag γl (1 : Qp).half L ∗ □ ([∗list] id ∈ L', leaseGranted γl id) ==∗
      lessorAuth γl 1 lp L' M ∗ leaseFrag γl (1 : Qp).half L' ∗
        leaseFrag γl (1 : Qp).half L' := by
  unfold lessorAuth leaseFrag
  iintro ⟨⟨%γga, %γcl, %γr, Ha, Hcl, -⟩, H1, H2, #Hl⟩
  icases ghostMapElem_combine true γl _ _ _ _ $$ H1 H2 with ⟨H, -⟩
  ihave H : ghostMapElem (GF := GF) γl true (DFrac.own 1) (Sum.inr L : LessorGV) $$ [H]
  · rw [dfrac_own_half_half 1]; iexact H
  imod ghost_map_update (Sum.inr L' : LessorGV) $$ Ha H with ⟨Ha, H⟩
  rw [lessorGhost_insert]
  isplitl [Ha Hcl]
  · iexists γga, γcl, γr
    iframe Ha Hcl
    iframe Hl
  ihave H : ghostMapElem (GF := GF) γl true (DFrac.own ((1 : Qp).half + (1 : Qp).half))
      (Sum.inr L' : LessorGV) $$ [H]
  · rw [Qp.half_add_half]; iexact H
  iapply ((ghostMapElem_fractional (GF := GF) true γl (Sum.inr L' : LessorGV)).fractional
    (1 : Qp).half (1 : Qp).half).1 $$ H

/-- **`Recover`'s ghost step, the recovered leases replacing the lessor's** (the lease-expiry plan's
S1): from the lessor's authority at the live set `L` and lease map `M` (the lock's), both halves of
the live set, the owner's closers (unfolded: its pin, its closers `C`, its half of the history and
of the item sets' map; the old item map's half is the caller's), the lock's share of the history
(at `M`), the revokers, the owner's half of the new, empty item map, the recovered ids' grant
guard and the leases `initAndRecover` made: each recovered lease set up (`recover_all`), the
closers' map replaced (`closers_swap`), the live set the records' ids (`lessor_live_set`), the
recovered snapshot appended (`recover_hist`; in the monotone mode every live id recovered keeps
`histMono`). After: the lessor's authority and its half of the live set at the recovered map,
the owner's resource at the empty item map, the revokers, the lock's share of the history, every
recovered lease's object and state, and the snapshot's index. -/
theorem closers_recover (γl : GName) (lp lp' : Loc) (L : List w64) (M C : GMap w64 Loc)
    (I I0 : GMap LeaseItem w64) (mono : Bool) (mt : w64) (xs : List ((w64 × w64 × w64) × Loc))
    (im : Loc) (γga γcl : GName) (E : CoPset) (hE : ↑lessorRdN ⊆ E)
    (hL : ∀ x : w64, x ∈ L ↔ (M.lookup x).isSome)
    (hnd : (xs.map (·.1.1)).Nodup)
    (hmono : mono = true → ∀ id ∈ L, id ∈ xs.map (·.1.1)) (U : List w64)
    (hfresh : ∀ id ∈ xs.map (·.1.1), id ∉ U) :
    lessorRdInv (GF := GF) γl ∗ lessorModeIs γl mono ∗ leaseEver γl U ∗ lessorAuth γl 1 lp L M ∗
      leaseFrag γl (1 : Qp).half L ∗ leaseFrag γl (1 : Qp).half L ∗
      lessorPinG γl lp' γga γcl ∗ ([∗map] id ↦ l ∈ C, closerAt γl γcl I id l) ∗
      (∃ (γr : LessorRdNames) (hs : List LSnap) (Sm : GMap Loc (GMap LeaseItem Unit)),
        lessorPinR γl γr ∗ monoListAuthOwn γr.1 (1 : Qp).half hs ∗
        ⌜∃ T, hs.getLast? = some (C, I, T)⌝ ∗ ghostMapAuth γr.2.1 (1 : Qp).half Sm) ∗
      (∃ (γr : LessorRdNames) (hs : List LSnap), lessorPinR γl γr ∗
        monoListAuthOwn γr.1 (1 : Qp).half.half hs ∗ ⌜∃ T, hs.getLast? = some (M, I0, T)⌝) ∗
      leaseRevokers γl L ∗
      lF go!"itemMap" lp ↦{DFrac.own (1 : Qp).half} im ∗
      im ↦${DFrac.own (1 : Qp).half} (∅ : GMap LeaseItem w64) ∗
      □ ([∗list] id ∈ xs.map (·.1.1), leaseGranted γl id) ∗
      ([∗list] p ∈ xs, recLease mt p.1 p.2) ⊢
    |={E}=> lessorAuth γl 1 lp (xs.map (·.1.1)) (recMap xs) ∗
      leaseFrag γl (1 : Qp).half (xs.map (·.1.1)) ∗ leaseOwn γl (xs.map (·.1.1)) ∅ ∗
      leaseRevokers γl (xs.map (·.1.1)) ∗
      (∃ (γr : LessorRdNames) (hs : List LSnap), lessorPinR γl γr ∗
        monoListAuthOwn γr.1 (1 : Qp).half.half hs ∗ ⌜∃ T, hs.getLast? = some (recMap xs, ∅, T)⌝) ∗
      ([∗map] _id ↦ l ∈ recMap xs, isLeaseObj γl l) ∗
      ([∗map] id ↦ l ∈ recMap xs, leaseMeta id l 1) ∗ leaseEver γl (U ++ xs.map (·.1.1)) ∗
      ∃ i : Nat, lessorAt γl i (recSnap mt xs) := by
  iintro ⟨#Hrd, #Hmode, HUo, Ha, Hg1, Hg2, #Hp, Hcs, ⟨%γr, %hs, %Sm, #Hpr, Ho, %Hlast, HSo⟩,
    ⟨%γrl, %hsl, #Hprl, Hl, %Hlastl⟩, Hrvk, Him, HI, #Hgr, Hrec⟩
  obtain ⟨T, Hlast⟩ := Hlast
  obtain ⟨T', Hlastl⟩ := Hlastl
  ihave %Hr := lessorPinR_agree γl γr γrl $$ [$Hpr $Hprl]
  subst Hr
  ihave %Hh := monoListAuthOwn_agree γr.1 _ _ hs hsl $$ Ho Hl
  obtain ⟨-, rfl⟩ := Hh
  have hCM : C = M := by
    rw [Hlast] at Hlastl
    simp only [Option.some.injEq, Prod.mk.injEq] at Hlastl
    exact Hlastl.1
  subst hCM
  -- the revokers' closers are the lessor's map
  iunfold leaseRevokers at Hrvk
  icases Hrvk with ⟨%lp'', %γga', %γcl', %C', #Hp', %HC', Hrs⟩
  ihave %Hpp := lessorPinG_agree γl lp' lp'' γga γga' γcl γcl' $$ [$Hp $Hp']
  obtain ⟨rfl, rfl, rfl⟩ := Hpp
  icases lessorAuth_pin γl 1 lp lp' L C γga γcl $$ [$Ha $Hp] with ⟨%Hlp, Hcl, Hback⟩
  subst Hlp
  ihave HcsE : iprop([∗map] id ↦ l ∈ C, ghostMapElem (GF := GF) γcl id
      (DFrac.own (1 : Qp).half) l) $$ [Hcs]
  · iapply BigSepM.bigSepM_impl $$ Hcs
    iintro !> %k %v %_ H
    iunfold closerAt at H
    icases H with ⟨H, -, -⟩
    iexact H
  ihave HrsE : iprop([∗map] id ↦ l ∈ C', ghostMapElem (GF := GF) γcl id
      (DFrac.own (1 : Qp).half) l) $$ [Hrs]
  · iapply BigSepM.bigSepM_impl $$ Hrs
    iintro !> %k %v %_ ⟨H, -⟩
    iexact H
  ihave %Hsub := ghost_map_lookup_big C' $$ Hcl HrsE
  have Hsub' : ∀ k v, C'.lookup k = some v → C.lookup k = some v := Hsub
  have hC' : C' = C := by
    apply GMap.ext; intro k
    cases h : C'.lookup k with
    | some v => exact (Hsub' k v h).symm
    | none =>
      cases h2 : C.lookup k with
      | none => rfl
      | some v =>
        have := (HC' k).1 ((hL k).2 (by rw [h2]; rfl))
        rw [h] at this; cases this
  ihave HrsE : iprop([∗map] id ↦ l ∈ C, ghostMapElem (GF := GF) γcl id
      (DFrac.own (1 : Qp).half) l) $$ [HrsE]
  · rw [← hC']; iexact HrsE
  -- the closers' map and the live set replaced
  imod closers_swap γcl C (recMap xs) $$ [$Hcl $HcsE $HrsE] with ⟨Hcl, Hn1, Hn2⟩
  ihave Ha := Hback $$ %(recMap xs) Hcl
  imod lessor_live_set γl lp L (xs.map (·.1.1)) (recMap xs) $$ [$Ha $Hg1 $Hg2 $Hgr]
    with ⟨Ha, Hg1, Hg2⟩
  -- each recovered lease set up
  imod recover_all γl γr hs mt E hE xs Sm $$ [$Hrd $Hpr $Ho $HSo $Hrec]
    with ⟨%Sm', ⟨%H1, %H2, %H3, %H4⟩, Ho, HSo, Hd⟩
  ihave Hd : iprop([∗list] p ∈ xs, iprop(lsF go!"ttl" p.2 ↦□ grantTTL mt p.1.2.1 ∗
      recCore γl p.1.1 p.2)) $$ [Hd]
  · iunfold recDone at Hd; iexact Hd
  icases (BigSepL.bigSepL_sep_eqv (PROP := IProp GF)).1 $$ Hd with ⟨#Httls, Hd⟩
  -- the recovered snapshot's TTLs are its leases' `ttl` fields
  ihave #Htie : ttlTie (GF := GF) (recSnap mt xs) $$ []
  · iunfold ttlTie
    isplitr
    · ipureintro; intro id
      show ((recTTLs mt (xs.map Prod.fst)).lookup id).isSome ↔ ((recMap xs).lookup id).isSome
      rw [recTTLs_isSome, recMap_isSome, List.map_map]; exact Iff.rfl
    iapply (recMap_bigSepM (fun id l => iprop(∃ t : w64,
      ⌜(recTTLs mt (xs.map Prod.fst)).lookup id = some t⌝ ∗ lsF go!"ttl" l ↦□ t)) xs hnd).2
    iapply (BigSepL.bigSepL_impl (PROP := IProp GF)) $$ Httls
    iintro !> %k %p %hk #Ht
    iexists grantTTL mt p.1.2.1
    iframe Ht
    ipureintro
    exact recTTLs_lookup mt _ p.1 (List.mem_map_of_mem (List.mem_of_getElem? hk))
      (by rw [List.map_map]; exact hnd)
  -- the snapshot appended
  iunfold lessorModeIs at Hmode
  icases Hmode with ⟨%γrm, #Hprm, %Hm⟩
  ihave %Hrm := lessorPinR_agree γl γr γrm $$ [$Hpr $Hprm]
  subst Hrm
  have hsub : γr.2.2.1 = true → ∀ id : w64, ((C, I, T).1.lookup id).isSome →
      ((recSnap mt xs).1.lookup id).isSome := fun hb id h => by
    show ((recMap xs).lookup id).isSome
    rw [recMap_isSome]
    exact hmono (Hm ▸ hb) id ((hL id).2 h)
  imod recover_hist γl γr hs Sm' (recSnap mt xs) E hE
      (recover_step_ok mt xs Hlast hnd (fun p hp => ⟨(H3 p hp).2.1, (H3 p hp).2.2⟩) H4)
      (fun h hm => histMono_snoc Hlast (hsub h) hm) U (xs.map (·.1.1))
      (fun id h => hfresh id ((recMap_isSome xs id).1 h))
      (fun id h => by
        rcases h with h | ⟨it, h⟩
        · exact (recMap_isSome xs id).1 h
        · simp [recSnap, GMap.lookup_empty] at h)
    $$ [$Hrd $Hpr $Ho $Hl $HSo $Htie $HUo] with ⟨Ho, Hl, HSo, HUo⟩
  ihave #Hlb0 := monoListLbOwn_get γr.1 _ _ $$ Ho
  ihave #Hidx0 := monoListIdxOwn_get hs.length (recSnap mt xs) (getElem?_snoc_len hs _) $$ Hlb0
  have hlast' : (hs ++ [recSnap mt xs]).getLast? = some (recMap xs, ∅, recTTLs mt (xs.map Prod.fst)) := by
    simp
  -- the recovered leases' resources, split by owner
  ihave Hd := (recMap_bigSepM (fun id l => recCore (GF := GF) γl id l) xs hnd).2 $$ Hd
  ihave Hall : iprop([∗map] id ↦ l ∈ recMap xs, iprop(recCore (GF := GF) γl id l ∗
      ghostMapElem γcl id (DFrac.own (1 : Qp).half) l ∗
      ghostMapElem γcl id (DFrac.own (1 : Qp).half) l)) $$ [Hd Hn1 Hn2]
  · rw [BigSepM.bigSepM_sep_eq, BigSepM.bigSepM_sep_eq]; iframe
  ihave Hall : iprop([∗map] id ↦ l ∈ recMap xs, iprop(closerAt (GF := GF) γl γcl ∅ id l ∗
      ((ghostMapElem γcl id (DFrac.own (1 : Qp).half) l ∗
        ∃ c : GoChan, lsF go!"revokec" l ↦□ c ∗ revokeCloser c) ∗
      (isLeaseObj γl l ∗ leaseMeta id l 1)))) $$ [Hall]
  · iapply BigSepM.bigSepM_impl $$ Hall
    iintro !> %k %v %_ ⟨Hc, He1, He2⟩
    iunfold recCore at Hc
    icases Hc with ⟨#Hlo, Hm, Hio, Hmu, Hrc⟩
    iunfold closerAt
    iframe
    iexact Hlo
  ihave ⟨Hcls, Hall⟩ : iprop(([∗map] id ↦ l ∈ recMap xs, closerAt (GF := GF) γl γcl ∅ id l) ∗
      [∗map] id ↦ l ∈ recMap xs, iprop((ghostMapElem (GF := GF) γcl id (DFrac.own (1 : Qp).half) l ∗
        ∃ c : GoChan, lsF go!"revokec" l ↦□ c ∗ revokeCloser c) ∗
      (isLeaseObj γl l ∗ leaseMeta id l 1))) $$ [Hall]
  · rw [← BigSepM.bigSepM_sep_eq]; iexact Hall
  ihave ⟨Hrv, Hall⟩ : iprop(([∗map] id ↦ l ∈ recMap xs,
      iprop(ghostMapElem (GF := GF) γcl id (DFrac.own (1 : Qp).half) l ∗
        ∃ c : GoChan, lsF go!"revokec" l ↦□ c ∗ revokeCloser c)) ∗
      [∗map] id ↦ l ∈ recMap xs, iprop(isLeaseObj (GF := GF) γl l ∗ leaseMeta id l 1)) $$ [Hall]
  · rw [← BigSepM.bigSepM_sep_eq]; iexact Hall
  ihave ⟨Hlos, Hmetas⟩ : iprop(([∗map] _id ↦ l ∈ recMap xs, isLeaseObj (GF := GF) γl l) ∗
      [∗map] id ↦ l ∈ recMap xs, leaseMeta (GF := GF) id l 1) $$ [Hall]
  · rw [← BigSepM.bigSepM_sep_eq]; iexact Hall
  imodintro
  iframe Ha Hg1 Hlos Hmetas HUo
  isplitl [Hg2 Hcls Him HI Ho HSo]
  · iunfold leaseOwn; iframe Hg2
    iunfold leaseClosers
    iexists lp, γga, γcl, recMap xs, im
    iframe Hp Him HI Hcls
    isplitr
    · ipureintro; intro x; exact (recMap_isSome xs x).symm
    isplitr
    · ipureintro; intro it x h; simp at h
    isplitr
    · ipureintro; intro it x h; simp at h
    iexists γr, hs ++ [recSnap mt xs], Sm'
    iframe Hpr Ho HSo
    ipureintro; exact ⟨_, hlast'⟩
  isplitl [Hrv]
  · iunfold leaseRevokers
    iexists lp, γga, γcl, recMap xs
    iframe Hp Hrv
    ipureintro; intro x; exact (recMap_isSome xs x).symm
  isplitl [Hl]
  · iexists γr, hs ++ [recSnap mt xs]; iframe Hpr Hl; ipureintro; exact ⟨_, hlast'⟩
  iexists hs.length
  iunfold lessorAt
  iexists γr; iframe Hpr Hidx0

end lemmas

end lease
end EtcdGrove
end Perennial
