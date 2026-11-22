/-
**`newLessor`'s ghost state** (prove-ps2-newlessor5, 2026-11-21): the lessor's readers' model allocated at
the recovered snapshot, index `0` (`NewLessor.spec`'s `lessorAt γl 0 _`), from the leases
`initAndRecover` made. Unlike `Recover` (`closers_recover`), which appends to an existing history and
registers each lease in an existing invariant (`recover_one`), here the item sets' map is built before
the invariant exists (`recs_register`: each lease's `ID` made read-only, which also shows the leases
distinct), the invariant is allocated at the single snapshot (`lessorRdBody_init`), and only then are the
leases' locks made (`recover_locks`: `recover_one`'s second half). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.LessorRecoverLemmas

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

/-- **A lease `initAndRecover` made, registered** (`recLease` with its `ID` and `ttl` read-only). -/
def recLeaseR (mt : w64) (x : w64 × w64 × w64) (l : Loc) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ lsF go!"ID" l ↦□ x.1 ∗ lsF go!"ttl" l ↦□ grantTTL mt x.2.1 ∗
    lsF go!"remainingTTL" l ↦ x.2.2 ∗
    lsF go!"expiryMu" l ↦ (zero_val _root_.Perennial.sync.RWMutex) ∗
    lsF go!"expiry" l ↦ (zero_val _root_.Perennial.time.Time) ∗
    lsF go!"mu" l ↦ (zero_val _root_.Perennial.sync.RWMutex) ∗
    (∃ sm : Loc, lsF go!"itemSet" l ↦ sm ∗ sm ↦$ (∅ : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem Unit)) ∗
    (∃ c : GoChan, lsF go!"revokec" l ↦ c ∗ revokeCloser c))

/-- **The recovered leases registered in a fresh item sets' map** (`γS`, whole; no invariant yet): each
lease's `ID` and `ttl` made read-only, each lease new to the map (its `ID` owned whole is not one of the
map's read-only ones, `w64_own_discard_false`), so the leases are distinct, each with its element at the
empty set. -/
theorem recs_register (γS : GName) (mt : w64) :
    ∀ (xs : List ((w64 × w64 × w64) × Loc)) (Sm : GMap Loc (GMap LeaseItem Unit)),
    ghostMapAuth (GF := GF) γS 1 Sm ∗ ([∗map] l ↦ _S ∈ Sm, ∃ id : w64, lsF go!"ID" l ↦□ id) ∗
      ([∗list] p ∈ xs, recLease mt p.1 p.2) ⊢
    |==> ∃ Sm' : GMap Loc (GMap LeaseItem Unit),
      ⌜(∀ l, (Sm.lookup l).isSome → Sm'.lookup l = Sm.lookup l) ∧
        (∀ (l : Loc) (S : GMap LeaseItem Unit), Sm'.lookup l = some S →
          Sm.lookup l = some S ∨ (l ∈ xs.map (·.2) ∧ S = ∅)) ∧
        (∀ p ∈ xs, Sm.lookup p.2 = none ∧ Sm'.lookup p.2 = some ∅) ∧
        (xs.map (·.2)).Nodup⌝ ∗
      ghostMapAuth γS 1 Sm' ∗ ([∗map] l ↦ _S ∈ Sm', ∃ id : w64, lsF go!"ID" l ↦□ id) ∗
      □ ([∗list] p ∈ xs, lsF go!"ttl" p.2 ↦□ grantTTL mt p.1.2.1) ∗
      [∗list] p ∈ xs, iprop(ghostMapElem γS p.2 (DFrac.own 1) (∅ : GMap LeaseItem Unit) ∗
        recLeaseR mt p.1 p.2)
  | [], Sm => by
    iintro ⟨Ha, Hids, -⟩
    imodintro
    iexists Sm
    iframe Ha Hids
    isplitr
    · ipureintro
      refine ⟨fun _ _ => rfl, fun _ _ h => Or.inl h, fun _ h => by simp at h, List.nodup_nil⟩
    isplitr
    · imodintro; iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; itrivial
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; itrivial
  | x :: xs, Sm => by
    iintro ⟨Ha, #Hids, Hl⟩
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ Hl with ⟨Hx, Hl⟩
    iunfold recLease at Hx
    icases Hx with ⟨%Hlnn, HID, Httl, Hrem, HexMu, Hexp, Hmu0, Hset, Hrc⟩
    cases Hfresh : Sm.lookup x.2 with
    | some S =>
      ihave ⟨%id', HID'⟩ := BigSepM.bigSepM_lookup Hfresh $$ Hids
      iexfalso
      iapply w64_own_discard_false _ x.1.1 id' $$ [$HID $HID']
    | none =>
    imod ghost_map_insert x.2 (∅ : GMap LeaseItem Unit) Hfresh $$ Ha with ⟨Ha, He⟩
    ipersist HID
    ipersist Httl
    ihave #Hids1 : iprop([∗map] l ↦ _S ∈ Sm.insert x.2 (∅ : GMap LeaseItem Unit),
        ∃ id : w64, lsF go!"ID" l ↦□ id) $$ []
    · iapply (BigSepM.bigSepM_insert (Φ := fun l _ => iprop(∃ id : w64, lsF go!"ID" l ↦□ id))
        (show Iris.Std.PartialMap.get? Sm x.2 = none from Hfresh)).2
      isplitr
      · iexists x.1.1; iexact HID
      iexact Hids
    imod recs_register γS mt xs (Sm.insert x.2 ∅) $$ [$Ha $Hids1 $Hl]
      with ⟨%Sm', ⟨%H1, %H2, %H3, %H4⟩, Ha, #Hids2, #Httls, Hl⟩
    imodintro
    iexists Sm'
    iframe Ha Hids2
    isplitr
    · ipureintro
      have hx2 : Sm'.lookup x.2 = some ∅ := by
        rw [H1 x.2 (by rw [GMap.lookup_insert]; rfl), GMap.lookup_insert]
      refine ⟨fun l hl => ?_, fun l S hS => ?_, fun p hp => ?_, ?_⟩
      · have hne : x.2 ≠ l := fun h => by subst h; rw [Hfresh] at hl; cases hl
        rw [H1 l (by rw [GMap.lookup_insert_ne _ _ hne]; exact hl), GMap.lookup_insert_ne _ _ hne]
      · rcases H2 l S hS with h | ⟨h1, h2⟩
        · rcases (GMap.lookup_insert_Some _ _ _ _ _).1 h with ⟨rfl, rfl⟩ | ⟨_, h⟩
          · exact Or.inr ⟨List.mem_cons_self .., rfl⟩
          · exact Or.inl h
        · exact Or.inr ⟨List.mem_cons_of_mem _ h1, h2⟩
      · rcases List.mem_cons.1 hp with rfl | hp
        · exact ⟨Hfresh, hx2⟩
        · obtain ⟨h1, h2⟩ := H3 p hp
          refine ⟨?_, h2⟩
          have hne : x.2 ≠ p.2 := fun h => by rw [← h, GMap.lookup_insert] at h1; cases h1
          rw [GMap.lookup_insert_ne _ _ hne] at h1; exact h1
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hm => ?_, H4⟩
        obtain ⟨p, hp, hpx⟩ := List.mem_map.1 hm
        have h1 := (H3 p hp).1
        rw [hpx, GMap.lookup_insert] at h1; cases h1
    isplitr
    · imodintro
      iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
      iframe Httl Httls
    iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
    iframe Hl He
    iunfold recLeaseR
    iframe; iframe #
    ipureintro; exact Hlnn

/-- **A registered recovered lease's locks made** (`recover_one`'s second half, the lease already in the
item sets' map of the lessor's readers' names `γr` with its element at the empty set): its two locks
made, their spare slots in the lease's pools. -/
theorem recover_locks (γl : GName) (γr : LessorRdNames) (mt : w64) (x : w64 × w64 × w64) (l : Loc)
    (E : CoPset) :
    lessorRdInv (GF := GF) γl ∗ lessorPinR γl γr ∗
      ghostMapElem γr.2.1 l (DFrac.own 1) (∅ : GMap LeaseItem Unit) ∗ recLeaseR mt x l ⊢
    |={E}=> recDone γl mt x l := by
  iintro ⟨#Hrd, #Hp, He, Hl⟩
  iunfold recLeaseR at Hl
  icases Hl with ⟨%Hlnn, #HID, #Httl, Hrem, HexMu, Hexp, Hmu0, ⟨%sm, HiS, Hsm⟩, ⟨%c, Hrc, Hrcl⟩⟩
  ipersist Hrc
  icases revokeCloser_recv c $$ Hrcl with ⟨Hrcl, #Hrr⟩
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
    · iexists c; iframe Hrc Hrr
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

/-- **Every registered recovered lease's locks made** (`recover_locks` over the list). -/
theorem recover_locks_all (γl : GName) (γr : LessorRdNames) (mt : w64) (E : CoPset) :
    ∀ (xs : List ((w64 × w64 × w64) × Loc)),
    lessorRdInv (GF := GF) γl ∗ lessorPinR γl γr ∗
      ([∗list] p ∈ xs, iprop(ghostMapElem γr.2.1 p.2 (DFrac.own 1) (∅ : GMap LeaseItem Unit) ∗
        recLeaseR mt p.1 p.2)) ⊢
    |={E}=> [∗list] p ∈ xs, recDone γl mt p.1 p.2
  | [] => by
    iintro ⟨-, -, -⟩
    imodintro
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; itrivial
  | x :: xs => by
    iintro ⟨#Hrd, #Hp, Hl⟩
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ Hl with ⟨⟨He, Hx⟩, Hl⟩
    imod recover_locks γl γr mt x.1 x.2 E $$ [$Hrd $Hp $He $Hx] with Hx
    imod recover_locks_all γl γr mt E xs $$ [$Hrd $Hp $Hl] with Hl
    imodintro
    iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
    iframe Hx Hl

/-! ### The single recovered snapshot's facts -/

/-- The single snapshot's lookups (`[σ][i]?`). -/
theorem single_get {σ σ' : LSnap} {i : Nat} (h : [σ][i]? = some σ') : i = 0 ∧ σ' = σ := by
  cases i with
  | zero => simp at h; exact ⟨rfl, h.symm⟩
  | succ i => simp at h

/-- **The recovered snapshot alone agrees with the item sets' map** whose leases are exactly the
recovered ones, each at the empty set. -/
theorem recSnap_setsOk (mt : w64) (xs : List ((w64 × w64 × w64) × Loc))
    (Sm : GMap Loc (GMap LeaseItem Unit)) (hnd : (xs.map (·.1.1)).Nodup)
    (hSm : ∀ (l : Loc) (S : GMap LeaseItem Unit), Sm.lookup l = some S → l ∈ xs.map (·.2) ∧ S = ∅)
    (hSm2 : ∀ p ∈ xs, Sm.lookup p.2 = some ∅) :
    setsOk [recSnap mt xs] Sm := by
  refine ⟨fun i σ id l hi hl => ?_, fun l S hS => ?_⟩
  · obtain ⟨-, rfl⟩ := single_get hi
    obtain ⟨p, hp, -, rfl⟩ := (recMap_lookup xs id l hnd).1 hl
    rw [hSm2 p hp]; rfl
  · obtain ⟨hl, rfl⟩ := hSm l S hS
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
    refine Or.inr ⟨p.1.1, 0, recSnap mt xs, ⟨⟨recSnap mt xs, rfl, ?_⟩, ?_⟩, rfl, ?_⟩
    · exact (recMap_lookup xs p.1.1 p.2 hnd).2 ⟨p, hp, rfl, rfl⟩
    · intro j τ hj hτ
      cases j with
      | zero => omega
      | succ j => simp at hτ
    · intro it; simp only [GMap.lookup_empty, reduceCtorEq]

/-- **The recovered snapshot alone is a well-formed history**, its leases distinct. -/
theorem recSnap_histOk (mt : w64) (xs : List ((w64 × w64 × w64) × Loc))
    (hnd : (xs.map (·.1.1)).Nodup) (hnd2 : (xs.map (·.2)).Nodup) :
    histOk [recSnap mt xs] := by
  refine ⟨by simp, fun i j σ τ id id' l hi hj h1 h2 => ?_, fun σ hσ => ?_⟩
  · obtain ⟨-, rfl⟩ := single_get hi
    obtain ⟨-, rfl⟩ := single_get hj
    obtain ⟨p, hp, rfl, rfl⟩ := (recMap_lookup xs id l hnd).1 h1
    obtain ⟨q, hq, rfl, he⟩ := (recMap_lookup xs id' p.2 hnd).1 h2
    rw [nodup_map_inj (·.2) xs hnd2 hq hp he]
  · rw [List.mem_singleton] at hσ; subst hσ
    intro it id h; simp at h

theorem single_histMono (σ : LSnap) : histMono [σ] := by
  intro i j a b id _ hi hj h
  obtain ⟨-, rfl⟩ := single_get hi
  obtain ⟨-, rfl⟩ := single_get hj
  exact h

theorem single_histOnce (σ : LSnap) : histOnce [σ] := by
  intro i j k a b c id _ _ hi hj hk h _
  obtain ⟨-, rfl⟩ := single_get hi
  obtain ⟨-, rfl⟩ := single_get hj
  exact h

theorem recSnap_histIn (mt : w64) (xs : List ((w64 × w64 × w64) × Loc)) :
    histIn [recSnap mt xs] (xs.map (·.1.1)) := by
  intro i σ id hi h
  obtain ⟨-, rfl⟩ := single_get hi
  rcases h with h | ⟨it, h⟩
  · exact (recMap_isSome xs id).1 h
  · simp [recSnap, GMap.lookup_empty] at h

theorem recSnap_histCover (mt : w64) (xs : List ((w64 × w64 × w64) × Loc)) :
    histCover [recSnap mt xs] (xs.map (·.1.1)) := by
  intro u hu
  exact ⟨0, recSnap mt xs, rfl, (recMap_isSome xs u).2 hu⟩

/-- **The requests bound the recovered TTLs**: each request at most its record's TTL, which the lessor
raised to the minimum. -/
theorem recSnap_reqOk (mt : w64) (xs : List ((w64 × w64 × w64) × Loc)) (rq : w64 → w64)
    (Q : GMap w64 w64) (hnd : (xs.map (·.1.1)).Nodup)
    (hQ : ∀ id r, Q.lookup id = some r → id ∈ xs.map (·.1.1) ∧ r = rq id)
    (hrq : ∀ p ∈ xs, sint.Z (rq p.1.1) ≤ sint.Z p.1.2.1) :
    reqOk [recSnap mt xs] Q := by
  have hnd' : ((xs.map Prod.fst).map (·.1)).Nodup := by rw [List.map_map]; exact hnd
  refine ⟨fun i σ id t r hi _ ht hr => ?_, fun id r hr => ?_⟩
  · obtain ⟨-, rfl⟩ := single_get hi
    obtain ⟨hid, rfl⟩ := hQ id r hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hid
    have hl := recTTLs_lookup mt (xs.map Prod.fst) p.1 (List.mem_map_of_mem hp) hnd'
    change (recTTLs mt (xs.map Prod.fst)).lookup p.1.1 = some t at ht
    rw [hl] at ht
    cases ht
    exact Int.le_trans (hrq p hp) (grantTTL_ge mt p.1.2.1)
  · exact recSnap_histCover mt xs id (hQ id r hr).1

/-- **The recovered snapshot's TTLs are its leases' `ttl` fields.** -/
theorem recSnap_ttlTie (mt : w64) (xs : List ((w64 × w64 × w64) × Loc))
    (hnd : (xs.map (·.1.1)).Nodup) :
    ([∗list] p ∈ xs, lsF go!"ttl" p.2 ↦□ grantTTL mt p.1.2.1) ⊢ ttlTie (GF := GF) (recSnap mt xs) := by
  iintro #Httls
  iunfold ttlTie
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

/-- **The lessor's readers' invariant at the single recovered snapshot** (`newLessor`): a quarter of
the history `[recSnap]`, half of the item sets' map (the recovered leases at the empty set), half of
the ids it ever had (the records'), the requests' authority (each record's id at `rq`), half of the
windows' list (empty), the snapshot's TTLs tied, every lease's `ID` read-only. -/
theorem recSnap_rdBody (γr : LessorRdNames) (mt : w64) (xs : List ((w64 × w64 × w64) × Loc))
    (Sm : GMap Loc (GMap LeaseItem Unit)) (Q : GMap w64 w64) (rq : w64 → w64)
    (hnd : (xs.map (·.1.1)).Nodup) (hnd2 : (xs.map (·.2)).Nodup)
    (hSm : ∀ (l : Loc) (S : GMap LeaseItem Unit), Sm.lookup l = some S → l ∈ xs.map (·.2) ∧ S = ∅)
    (hSm2 : ∀ p ∈ xs, Sm.lookup p.2 = some ∅)
    (hQ : ∀ id r, Q.lookup id = some r → id ∈ xs.map (·.1.1) ∧ r = rq id)
    (hrq : ∀ p ∈ xs, sint.Z (rq p.1.1) ≤ sint.Z p.1.2.1) :
    monoListAuthOwn (GF := GF) γr.1 Qp.quarter [recSnap mt xs] ∗
      ghostMapAuth γr.2.1 (1 : Qp).half Sm ∗
      dghostVar γr.2.2.2.1 (DFrac.own (1 : Qp).half) (xs.map (·.1.1)) ∗
      ([∗list] p ∈ xs, lsF go!"ttl" p.2 ↦□ grantTTL mt p.1.2.1) ∗
      ([∗map] l ↦ _S ∈ Sm, ∃ id : w64, lsF go!"ID" l ↦□ id) ∗
      monoListAuthOwn γr.2.2.2.2.2.1 (1 : Qp).half ([] : List LWinRec) ∗
      ghostMapAuth γr.2.2.2.2.1 (1 : Qp) Q ⊢
    lessorRdBody γr := by
  iintro ⟨Ha, HS, HU, #Httls, #Hids, Hw, HQ⟩
  iunfold lessorRdBody
  iexists [recSnap mt xs], Sm
  iframe Ha HS Hids
  isplitr
  · ipureintro; exact ⟨recSnap_setsOk mt xs Sm hnd hSm hSm2, recSnap_histOk mt xs hnd hnd2⟩
  isplitr
  · ipureintro; intro _; exact single_histMono _
  isplitl [HU]
  · iexists xs.map (·.1.1)
    iframe HU
    ipureintro
    exact ⟨single_histOnce _, recSnap_histIn mt xs, recSnap_histCover mt xs⟩
  isplitr
  · iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)).2
    iapply recSnap_ttlTie mt xs hnd $$ Httls
  isplitl [Hw]
  · iunfold lessorWinBody
    iexists []
    iframe Hw
    ipureintro
    refine ⟨winsOk_nil _, fun σ hσ => ?_⟩
    rw [List.mem_singleton] at hσ; subst hσ
    intro it id h; simp [recSnap, GMap.lookup_empty] at h
  iexists Q
  iframe HQ
  ipureintro; exact recSnap_reqOk mt xs rq Q hnd hQ hrq

/-- No id is in the empty list. -/
theorem bigSepL_notin_nil (Q : w64 → IProp GF) :
    ∀ L : List w64, ⊢ [∗list] id ∈ L, iprop(⌜id ∉ ([] : List w64)⌝ ∨ Q id)
  | [] => by iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; itrivial
  | x :: L => by
    iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
    isplitr
    · ileft; ipureintro; simp
    iapply bigSepL_notin_nil Q L

/-- **The lessor's readers' names allocated at the recovered snapshot** (`newLessor`): with the item
sets' map `γS` (the recovered leases at the empty set, `recs_register`), a history `[recSnap]` (a
quarter in the readers' invariant, a half for the owner, a quarter for `le.mu`), the ids it ever had
(the records', halved), the requests' map (each record's id at `rq`, discarded elements), the
windows' list (empty: half in the invariant, a quarter each for the owner and the tie), `demotec`'s
ghost variable at `nil` (half in its invariant `demoteOuter`, half for `le.mu`), the notifier's cell
(idle: half the field, the notifier, `γk` whole; the shares' variable `γx` whole for `le.mu`, the
loop's token `γy`), the mode `mono`; and the readers' invariant. -/
theorem lessor_rd_alloc (lp np : Loc) (mt : w64) (xs : List ((w64 × w64 × w64) × Loc)) (mono : Bool)
    (rq : w64 → w64) (γS : GName) (Sm : GMap Loc (GMap LeaseItem Unit))
    (hnd : (xs.map (·.1.1)).Nodup) (hnd2 : (xs.map (·.2)).Nodup)
    (hSm : ∀ (l : Loc) (S : GMap LeaseItem Unit), Sm.lookup l = some S → l ∈ xs.map (·.2) ∧ S = ∅)
    (hSm2 : ∀ p ∈ xs, Sm.lookup p.2 = some ∅)
    (hrq : ∀ p ∈ xs, sint.Z (rq p.1.1) ≤ sint.Z p.1.2.1) :
    ghostMapAuth (GF := GF) γS 1 Sm ∗ ([∗map] l ↦ _S ∈ Sm, ∃ id : w64, lsF go!"ID" l ↦□ id) ∗
      □ ([∗list] p ∈ xs, lsF go!"ttl" p.2 ↦□ grantTTL mt p.1.2.1) ∗
      lF go!"leaseExpiredNotifier" lp ↦{DFrac.own (1 : Qp).half} np ∗ notifierAt np 1 ⊢
    |={⊤}=> ∃ γr : LessorRdNames, ⌜γr.2.1 = γS ∧ γr.2.2.1 = mono⌝ ∗
      inv lessorRdN (lessorRdBody γr) ∗ notifInv lp γr ∗
      inv demoteOuterN (demoteOuter γr.2.2.2.2.2.2.1) ∗
      monoListAuthOwn γr.1 (1 : Qp).half [recSnap mt xs] ∗
      monoListAuthOwn γr.1 (1 : Qp).half.half [recSnap mt xs] ∗
      monoListIdxOwn γr.1 0 (recSnap mt xs) ∗
      ghostMapAuth γr.2.1 (1 : Qp).half Sm ∗
      dghostVar γr.2.2.2.1 (DFrac.own (1 : Qp).half) (xs.map (·.1.1)) ∗
      □ ([∗list] id ∈ xs.map (·.1.1), id ↪[γr.2.2.2.2.1]□ rq id) ∗
      monoListAuthOwn γr.2.2.2.2.2.1 Qp.quarter ([] : List LWinRec) ∗
      monoListAuthOwn γr.2.2.2.2.2.1 Qp.quarter ([] : List LWinRec) ∗
      ghostVar γr.2.2.2.2.2.2.1 (1 : Qp).half chan.nil ∗
      ghostVar γr.2.2.2.2.2.2.2.1 (1 : Qp) () ∗ token γr.2.2.2.2.2.2.2.2.1 := by
  iintro ⟨HSa, #Hids, #Httls, Hnf, Hnot⟩
  have hqq : (1 : Qp).half.half = Qp.quarter := Subtype.ext (by simp; grind)
  have hq2 : Qp.quarter + Qp.quarter = (1 : Qp).half := Subtype.ext (by simp; grind)
  -- the history
  imod (mono_list_own_alloc (GF := GF) [recSnap mt xs]) with ⟨%γh, Hh, #Hhl⟩
  ihave ⟨Hh1, Hh2⟩ : monoListAuthOwn (GF := GF) γh (1 : Qp).half [recSnap mt xs] ∗
      monoListAuthOwn (GF := GF) γh (1 : Qp).half [recSnap mt xs] $$ [Hh]
  · iapply ((monoListAuthOwn_fractional (GF := GF) γh [recSnap mt xs]).fractional
      (1 : Qp).half (1 : Qp).half).1
    rw [Qp.half_add_half]; iexact Hh
  ihave ⟨Hh2, Hh3⟩ : monoListAuthOwn (GF := GF) γh (1 : Qp).half.half [recSnap mt xs] ∗
      monoListAuthOwn (GF := GF) γh (1 : Qp).half.half [recSnap mt xs] $$ [Hh2]
  · iapply ((monoListAuthOwn_fractional (GF := GF) γh [recSnap mt xs]).fractional
      (1 : Qp).half.half (1 : Qp).half.half).1
    rw [Qp.half_add_half]; iexact Hh2
  ihave #Hidx := monoListIdxOwn_get (γ := γh) 0 (recSnap mt xs) rfl $$ Hhl
  -- the item sets' map, halved
  icases (ghostMapAuth_halves γS Sm).1 $$ HSa with ⟨HSa1, HSa2⟩
  -- the ids ever had
  imod (dghostVar_alloc (GF := GF) (xs.map (·.1.1))) with ⟨%γU, HU⟩
  icases dghostVar_split γU _ (.own (1 : Qp).half) (.own (1 : Qp).half) $$ [HU] with ⟨HU1, HU2⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact HU
  -- the requests
  imod (ghost_map_alloc_empty (GF := GF) (K := w64) (V := w64)) with ⟨%γQ, HQ⟩
  imod (req_issue γQ [] rq ∅ (fun _ _ h => by simp at h) (xs.map (·.1.1)) [] ∅
      (fun _ _ h => by simp at h) (fun _ h => by simp at h)) $$ [HQ]
    with ⟨%Q, HQ, ⟨%HQ1, %HQ2⟩, #HQe⟩
  · iframe HQ
    isplitr
    · imodintro; iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; itrivial
    imodintro
    iapply (bigSepL_notin_nil (GF := GF) (fun id => iprop(id ↪[γQ]□ rq id)) (xs.map (·.1.1)))
  rw [List.nil_append] at *
  -- the windows
  imod (mono_list_own_alloc (GF := GF) ([] : List LWinRec)) with ⟨%γw, Hw, -⟩
  ihave ⟨Hw1, Hw2⟩ : monoListAuthOwn (GF := GF) γw (1 : Qp).half ([] : List LWinRec) ∗
      monoListAuthOwn (GF := GF) γw (1 : Qp).half ([] : List LWinRec) $$ [Hw]
  · iapply ((monoListAuthOwn_fractional (GF := GF) γw ([] : List LWinRec)).fractional
      (1 : Qp).half (1 : Qp).half).1
    rw [Qp.half_add_half]; iexact Hw
  ihave ⟨Hw2, Hw3⟩ : monoListAuthOwn (GF := GF) γw Qp.quarter ([] : List LWinRec) ∗
      monoListAuthOwn (GF := GF) γw Qp.quarter ([] : List LWinRec) $$ [Hw2]
  · iapply ((monoListAuthOwn_fractional (GF := GF) γw ([] : List LWinRec)).fractional
      Qp.quarter Qp.quarter).1
    rw [hq2]; iexact Hw2
  -- `demotec`
  imod (ghostVar_alloc (GF := GF) (chan.nil : GoChan)) with ⟨%γd, Hd⟩
  icases (ghostVar_split_half γd 1 (chan.nil : GoChan)).1 $$ Hd with ⟨Hd1, Hd2⟩
  imod (inv_alloc demoteOuterN ⊤ (demoteOuter (GF := GF) γd)) $$ [Hd2] with #Hdinv
  · inext; iunfold demoteOuter; iexists chan.nil; iframe Hd2; ileft; ipureintro; rfl
  -- the notifier's cell
  imod (ghostVar_alloc (GF := GF) ()) with ⟨%γx, Hx⟩
  imod (token_alloc (GF := GF)) with ⟨%γy, Hy⟩
  imod (ghostVar_alloc (GF := GF) false) with ⟨%γk, Hk⟩
  imod (inv_alloc notifN ⊤ (notifCell (GF := GF) lp γx γy γk)) $$ [Hnf Hnot Hk] with #Hninv
  · inext; iunfold notifCell; ileft; iexists np, false; iframe Hnf Hnot Hk
  -- the readers' invariant
  imod (inv_alloc lessorRdN ⊤ (lessorRdBody (GF := GF) (γh, γS, mono, γU, γQ, γw, γd, γx, γy, γk)))
    $$ [Hh3 HSa2 HU2 Hw1 HQ] with #Hrinv
  · inext
    iapply recSnap_rdBody (γh, γS, mono, γU, γQ, γw, γd, γx, γy, γk) mt xs Sm Q rq hnd hnd2 hSm hSm2
      (fun id r h => by
        rcases HQ1 id r h with h | ⟨-, h1, h2⟩
        · simp at h
        · exact ⟨h1, h2⟩) hrq
    rw [← hqq]
    iframe Hh3 HSa2 HU2 Httls Hids Hw1 HQ
  imodintro
  iexists (γh, γS, mono, γU, γQ, γw, γd, γx, γy, γk)
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  iframe Hrinv Hninv Hdinv Hh1 Hh2 Hidx HSa1 HU1 Hw2 Hw3 Hd1 Hx Hy
  iexact HQe

end lemmas

end lease
end EtcdGrove
end Perennial
