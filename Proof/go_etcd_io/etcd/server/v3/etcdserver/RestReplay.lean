/-
**A restarted member's replay of the rest model, and the closing identity** (R2d' probe, A1/A2,
2026-11-06; DRAFT: nothing here is frozen, `notes/restart-plan.md`, "R2d' Scope (approved
2026-11-06)", its probe). Lean-first (no Rocq counterpart).

At a restart (etcd pin `673da07c8`) Go's applied index `ep.appliedi` starts at the WAL snapshot's
index `σ.b` (`server.go:808-814`), the backend's consistent index `i` above it; raft hands the
committed entries from `σ.b + 1` again (`bootstrap.go:580-599`: no `Applied`), and `apply` replays
those at or below `i` v2-only (`shouldApplyV3 = e.Index > ConsistentIndex()`, `server.go:1940-1944`):
* a normal entry through `applyEntryNormal(e, false)` (`server.go:1975-2005`): `apply.Apply(…, false)`
  dispatches the cluster kinds v2-only (`apply/uber_applier.go:93-127`): `ClusterMemberAttrSet`'s
  `UpdateAttributes(…, false)` sets the in-memory member's attributes
  (`membership/cluster.go:467-496`), `ClusterVersionSet`'s `SetVersion(…, false)` only the in-memory
  version, which the model does not keep (`restSetVersion false` is the identity);
* a conf entry through `applyConfChange(cc, ep, false)` (`server.go:2037-2110`): not validated
  (`membership/cluster.go:306-309`), not applied to raft (`server.go:2053-2059`), and the membership's
  `AddMember` only logs (`membership/cluster.go:394-424`): `ccRest false` is the identity.

So the replay of an entry is `restEntry` at `v3 = false` (`restEntryV2`), and changes only the
in-memory members, by attribute overwrites (`memStep`). **The closing identity**
(`restReplay_close`): replaying any suffix of the committed log v2-only on its rest model gives the
rest model back. Its argument: past the bootstrap log no conf change changes the members (every
`AddNode` is of a voter whose record the `members` bucket already holds, so `ValidateConfiguration
Change` refuses it: `memSync`, `ccValidOn_false`; there is no `RemoveNode`, `ccApplyOk`), so the
model's members are the boot members overwritten by the log's attribute writes, in order (`foldMem`),
and an overwrite sequence replayed on its own result is a fixed point (`foldMem_idem`). The facts are
the ones every closed theorem rests on: the bootstrap log (`srvBootLogOk`, its peers distinct, its
URLs `bootURLsOk`) and the committed conf entries the server's (`ccApplyOk`); no attribute fact is
needed (an attribute write to a non-member is a no-op on both sides, and the member set is the same).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RestConf

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-! ## The restart point and the ghost log -/

/-- **A restart point** (R2d' A1, DRAFT): one constant per incarnation of a member. `b`, Go's start
index (`ep.appliedi`'s first value, the WAL snapshot's index `σ.b`: `server.go:808-814` at the pin
`673da07c8`, the snapshot `recoverSnapshot` built, `bootstrap.go:449-478`), as the length of the log
raft handed before it; `A₀`, the backend's ghost applied log through its consistent index `i`
(`bootstrap.go:255-273`, "restore consistentIndex"). A first start is `⟨0, []⟩` (`RestartPt.first`). -/
structure RestartPt where
  b : Nat
  A₀ : List EntryModel

/-- **A first start's restart point**: nothing handed, nothing applied. -/
def RestartPt.first : RestartPt := ⟨0, []⟩

/-- **The ghost applied log** (R2d' A1, DRAFT) after Go's log `G` (the log raft handed this
incarnation, through `ep.appliedi`): `G` and the backend's entries past it, `A₀.drop |G|` (the replays
pending; none once Go is past `i`). The KV's, the applied index's and the rest buckets' ghost rows are
at it; Go's rows (`ep.appliedi`, `loopOk`, the snapshot state) at `G`. -/
def ghostOf (rp : RestartPt) (G : List EntryModel) : List EntryModel := G ++ rp.A₀.drop G.length

/-- A first start's ghost log is Go's. -/
theorem ghostOf_first (G : List EntryModel) : ghostOf RestartPt.first G = G := by
  simp [ghostOf, RestartPt.first]

/-- The ghost log once Go is past the window: Go's. -/
theorem ghostOf_past (rp : RestartPt) (G : List EntryModel) (h : rp.A₀.length ≤ G.length) :
    ghostOf rp G = G := by
  simp [ghostOf, List.drop_eq_nil_of_le h]

/-- The ghost log inside the window, when Go's log is a prefix of the backend's: the backend's. -/
theorem ghostOf_in (rp : RestartPt) (G : List EntryModel) (h : G <+: rp.A₀) :
    ghostOf rp G = rp.A₀ := by
  obtain ⟨t, ht⟩ := h
  unfold ghostOf
  rw [← ht]; simp

/-! ## The v2-only step of an entry -/

/-- **An entry replayed v2-only** (R2d' A1, DRAFT): `restEntry` at `v3 = false` (see the file
header; `server.go:1946-1960` at the pin `673da07c8` with `shouldApplyV3` false). -/
def restEntryV2 (m : EntryModel) (r : apply.RestM) : apply.RestM :=
  if m.typ = W32 0 then
    if m.data = [] then r
    else match apply.irrDecode m.data with
      | some rq => apply.restAfter rq false r
      | none => r
  else match ccDecodeV1 m.data with
    | some cc => ccRest false cc r
    | none => r

/-- An entry at or below `c0` is replayed v2-only by `restEntry c0`. -/
theorem restEntry_v2 (c0 : w64) (m : EntryModel) (r : apply.RestM)
    (h : uint.Z m.index ≤ uint.Z c0) : restEntry c0 m r = restEntryV2 m r := by
  have hd : decide (uint.Z c0 < uint.Z m.index) = false := decide_eq_false (by omega)
  unfold restEntry restEntryV2
  simp only [hd]
  rfl

/-- The attribute write an entry makes (`dispatch`'s order: a version request first,
`apply.restAfter`). -/
def attrOf (m : EntryModel) : Option apply.MemberAttrModel :=
  if m.typ = W32 0 ∧ m.data ≠ [] then
    match apply.irrDecode m.data with
    | some rq =>
      match rq.clusterVersionSet with
      | some _ => none
      | none => rq.clusterMemberAttrSet
    | none => none
  else none

/-- `UpdateAttributes` on the in-memory members (both `v3`'s). -/
def memUpd (a : apply.MemberAttrModel) (mem : GMap w64 apply.MemberM) : GMap w64 apply.MemberM :=
  match mem.lookup a.memberID with
  | none => mem
  | some mm => mem.insert a.memberID (mm.withAttrs a)

/-- An entry's effect on the in-memory members, v2-only. -/
def memStep (m : EntryModel) (mem : GMap w64 apply.MemberM) : GMap w64 apply.MemberM :=
  match attrOf m with
  | none => mem
  | some a => memUpd a mem

/-- The members after the entries `S`, v2-only. -/
def foldMem (S : List EntryModel) (mem : GMap w64 apply.MemberM) : GMap w64 apply.MemberM :=
  S.foldl (fun mem m => memStep m mem) mem

theorem restUpdateAttrs_false_eq (a : apply.MemberAttrModel) (r : apply.RestM) :
    apply.restUpdateAttrs false a r = { r with mem := memUpd a r.mem } := by
  unfold apply.restUpdateAttrs memUpd
  cases h : r.mem.lookup a.memberID with
  | none => rfl
  | some mm => rfl

/-- **A v2-only step changes only the members**, by `memStep`. -/
theorem restEntryV2_eq (m : EntryModel) (r : apply.RestM) :
    restEntryV2 m r = { r with mem := memStep m r.mem } := by
  unfold restEntryV2 memStep attrOf
  by_cases ht : m.typ = W32 0
  · by_cases hd : m.data = []
    · simp only [ht, hd, ↓reduceIte, ne_eq, not_true_eq_false, and_false]
    · simp only [ht, hd, ↓reduceIte, ne_eq, not_false_eq_true, and_self]
      cases hq : apply.irrDecode m.data with
      | none => rfl
      | some rq =>
        simp only
        unfold apply.restAfter
        cases hv : rq.clusterVersionSet with
        | some v => simp only [apply.restSetVersion, Bool.false_eq_true, ↓reduceIte]
        | none =>
          simp only
          cases ha : rq.clusterMemberAttrSet with
          | none => rfl
          | some a => simp only; exact restUpdateAttrs_false_eq a r
  · simp only [ht, ↓reduceIte, false_and]
    cases hc : ccDecodeV1 m.data with
    | none => rfl
    | some cc => simp [ccRest]

/-- Replaying `S` v2-only changes only the members, by `foldMem`. -/
theorem fold_restEntryV2 (S : List EntryModel) (r : apply.RestM) :
    S.foldl (fun r m => restEntryV2 m r) r = { r with mem := foldMem S r.mem } := by
  induction S generalizing r with
  | nil => rfl
  | cons m S ih => rw [List.foldl_cons, ih, restEntryV2_eq]; rfl

/-! ## Attribute overwrites are idempotent -/

/-- The entry's effect on the member under `k`. -/
def attrStepK (k : w64) (m : EntryModel) (mm : apply.MemberM) : apply.MemberM :=
  match attrOf m with
  | some a => if a.memberID = k then mm.withAttrs a else mm
  | none => mm

/-- The entries' effect on the member under `k`. -/
def gK (S : List EntryModel) (k : w64) (mm : apply.MemberM) : apply.MemberM :=
  S.foldl (fun mm m => attrStepK k m mm) mm

theorem withAttrs_withAttrs (mm : apply.MemberM) (a b : apply.MemberAttrModel) :
    (mm.withAttrs a).withAttrs b = mm.withAttrs b := rfl

theorem memStep_lookup (m : EntryModel) (mem : GMap w64 apply.MemberM) (k : w64) :
    (memStep m mem).lookup k = (mem.lookup k).map (attrStepK k m) := by
  unfold memStep attrStepK
  cases h : attrOf m with
  | none => simp
  | some a =>
    simp only
    unfold memUpd
    cases hl : mem.lookup a.memberID with
    | none =>
      simp only
      by_cases e : a.memberID = k
      · subst e; rw [hl]; rfl
      · simp [e]
    | some mm =>
      simp only
      by_cases e : a.memberID = k
      · subst e
        rw [hl]
        show (if a.memberID = a.memberID then some (mm.withAttrs a) else _) = _
        simp
      · show (if a.memberID = k then some (mm.withAttrs a) else mem.lookup k) = _
        simp [e]

theorem foldMem_lookup (S : List EntryModel) (mem : GMap w64 apply.MemberM) (k : w64) :
    (foldMem S mem).lookup k = (mem.lookup k).map (gK S k) := by
  induction S generalizing mem with
  | nil =>
    show mem.lookup k = (mem.lookup k).map (gK [] k)
    cases mem.lookup k <;> rfl
  | cons m S ih =>
    show (foldMem S (memStep m mem)).lookup k = _
    rw [ih, memStep_lookup, Option.map_map]
    rfl

/-- The entries leave the member under `k`, or set its attributes to one value. -/
theorem gK_shape (S : List EntryModel) (k : w64) :
    (∀ mm, gK S k mm = mm) ∨ ∃ a, ∀ mm, gK S k mm = mm.withAttrs a := by
  induction S with
  | nil => left; intro mm; rfl
  | cons m S ih =>
    have hstep : (∀ mm, attrStepK k m mm = mm) ∨ ∃ b, ∀ mm, attrStepK k m mm = mm.withAttrs b := by
      unfold attrStepK
      cases attrOf m with
      | none => left; intro mm; rfl
      | some b =>
        by_cases e : b.memberID = k
        · right; exact ⟨b, fun mm => by simp [e]⟩
        · left; intro mm; simp [e]
    have hc : ∀ mm, gK (m :: S) k mm = gK S k (attrStepK k m mm) := fun mm => rfl
    rcases ih with h | ⟨a, h⟩
    · rcases hstep with h' | ⟨b, h'⟩
      · left; intro mm; rw [hc, h, h']
      · right; exact ⟨b, fun mm => by rw [hc, h, h']⟩
    · right
      refine ⟨a, fun mm => ?_⟩
      rw [hc, h]
      rcases hstep with h' | ⟨b, h'⟩
      · rw [h']
      · rw [h', withAttrs_withAttrs]

theorem gK_idem (S : List EntryModel) (k : w64) (mm : apply.MemberM) :
    gK S k (gK S k mm) = gK S k mm := by
  rcases gK_shape S k with h | ⟨a, h⟩
  · rw [h, h]
  · rw [h, h, withAttrs_withAttrs]

/-- **An overwrite sequence replayed on its own result is a fixed point.** -/
theorem foldMem_idem (S : List EntryModel) (mem : GMap w64 apply.MemberM) :
    foldMem S (foldMem S mem) = foldMem S mem := by
  apply GMap.ext
  intro k
  rw [foldMem_lookup, foldMem_lookup, Option.map_map]
  cases mem.lookup k with
  | none => rfl
  | some mm => exact congrArg some (gK_idem S k mm)

theorem foldMem_append (S T : List EntryModel) (mem : GMap w64 apply.MemberM) :
    foldMem (S ++ T) mem = foldMem T (foldMem S mem) := by
  unfold foldMem; rw [List.foldl_append]

/-- Conf entries leave the members v2-only. -/
theorem foldMem_conf (S : List EntryModel) (mem : GMap w64 apply.MemberM)
    (h : ∀ m ∈ S, m.typ ≠ W32 0) : foldMem S mem = mem := by
  induction S generalizing mem with
  | nil => rfl
  | cons m S ih =>
    show foldMem S (memStep m mem) = mem
    have hm : memStep m mem = mem := by
      unfold memStep attrOf
      rw [if_neg (fun h' => h m List.mem_cons_self h'.1)]
    rw [hm]
    exact ih mem (fun m' hm' => h m' (List.mem_cons_of_mem _ hm'))

/-! ## The members bucket in sync: refused `AddNode`s -/

/-- **The `members` bucket holds the records of members `ms`** of distinct ids covering the voters
`ps`, with valid peer URLs; nothing removed; the in-memory members under their own ids, with valid
peer URLs. What makes `ValidateConfigurationChange` refuse an `AddNode` of a voter
(`ccValidOn_false`). -/
def memSync (ps : List w64) (r : apply.RestM) : Prop :=
  (∃ ms : List apply.MemberM,
    (∀ k v, (memBktOf r.bk).lookup k = some v ↔
      ∃ mm ∈ ms, k = apply.memberKey mm.id ∧ v = apply.memberEnc mm) ∧
    (ms.map (·.id)).Nodup ∧ (∀ mm ∈ ms, ∀ u ∈ mm.peerURLs, utf8Valid u) ∧
    (∀ id ∈ ps, id ∈ ms.map (·.id))) ∧
  (r.bk.lookup go!"members_removed").getD ∅ = ∅ ∧
  (∀ id mm, r.mem.lookup id = some mm → mm.id = id ∧ ∀ u ∈ mm.peerURLs, utf8Valid u)

/-- **An `AddNode` of a voter is refused** once the bucket is in sync. -/
theorem ccValidOn_false (ps : List w64) (r : apply.RestM) (cc : ConfChangeM) (hs : memSync ps r)
    (hty : cc.type = W32 0) (hin : cc.nodeId ∈ ps) : membership.ccValidOn r.bk cc = false := by
  obtain ⟨⟨ms, hb, hnd, hu, hcov⟩, hrm, -⟩ := hs
  obtain ⟨hmems, -⟩ := membership.membersOf_decode (r.bk.lookup go!"members")
    (r.bk.lookup go!"members_removed") ms [] hb hnd hu (fun k => by rw [hrm]; simp)
  unfold membership.ccValidOn membership.membersOfBk
  classical
  apply decide_eq_false
  unfold membership.ccValidM
  rintro ⟨-, h2⟩
  rw [if_pos hty] at h2
  have h3 := h2.1
  rw [hmems] at h3
  obtain ⟨mm, hmm, hid⟩ := List.mem_map.1 (hcov _ hin)
  have := List.find?_eq_none.1 (Option.map_eq_none_iff.1 h3) mm hmm
  simp [hid] at this

/-- A put of another bucket keeps the sync. -/
theorem memSync_putIn_other (ps : List w64) (r : apply.RestM) (n k v : GoString)
    (h1 : n ≠ go!"members") (h2 : n ≠ go!"members_removed") (hs : memSync ps r) :
    memSync ps (r.putIn n k v) := by
  obtain ⟨⟨ms, hb, hnd, hu, hcov⟩, hrm, hm⟩ := hs
  refine ⟨⟨ms, ?_, hnd, hu, hcov⟩, ?_, hm⟩
  · rw [memBktOf_putIn_other _ _ _ _ h1]; exact hb
  · rw [putIn_other _ _ _ _ _ h2]; exact hrm

/-- **A member's record replaced**: the members `mm'` and the others. -/
theorem memSync_putMember (ps : List w64) (r : apply.RestM) (mm' : apply.MemberM)
    (mem' : GMap w64 apply.MemberM) (hs : memSync ps r)
    (hu' : ∀ u ∈ mm'.peerURLs, utf8Valid u)
    (hm' : ∀ id mm, mem'.lookup id = some mm → mm.id = id ∧ ∀ u ∈ mm.peerURLs, utf8Valid u) :
    memSync ps ({ r with mem := mem' }.putIn go!"members" (apply.memberKey mm'.id)
      (apply.memberEnc mm')) := by
  obtain ⟨⟨ms, hb, hnd, hu, hcov⟩, hrm, -⟩ := hs
  refine ⟨⟨mm' :: ms.filter (fun mm => decide (mm.id ≠ mm'.id)), fun k v => ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [memBktOf_putIn_members, GMap.lookup_insert_eq_iff]
    simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq]
    split
    · next hk =>
      constructor
      · intro hv; cases hv; exact ⟨mm', Or.inl rfl, hk.symm, rfl⟩
      · rintro ⟨mm, rfl | ⟨-, hne⟩, h1, h2⟩
        · rw [h2]
        · exact absurd (apply.memberKey_inj _ _ (hk.trans h1)).symm hne
    · next hk =>
      change (memBktOf r.bk).lookup k = some v ↔ _
      rw [hb]
      constructor
      · rintro ⟨mm, hmm, h1, h2⟩
        refine ⟨mm, Or.inr ⟨hmm, fun he => hk ?_⟩, h1, h2⟩
        rw [h1, he]
      · rintro ⟨mm, rfl | ⟨hmm, -⟩, h1, h2⟩
        · exact absurd h1.symm hk
        · exact ⟨mm, hmm, h1, h2⟩
  · simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ((List.filter_sublist (l := ms)).map _).nodup hnd⟩
    intro hmem
    obtain ⟨mm, hmm, he⟩ := List.mem_map.1 hmem
    have := (List.mem_filter.1 hmm).2
    simp only [ne_eq, decide_eq_true_eq] at this
    exact this he
  · intro mm hmm u hu0
    rcases List.mem_cons.1 hmm with rfl | hmm
    · exact hu' u hu0
    · exact hu mm (List.mem_filter.1 hmm).1 u hu0
  · intro id hid
    obtain ⟨mm, hmm, rfl⟩ := List.mem_map.1 (hcov id hid)
    by_cases he : mm.id = mm'.id
    · rw [he]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨mm, List.mem_filter.2 ⟨hmm, by simpa using he⟩, rfl⟩)
  · rw [removed_putIn_members]; exact hrm
  · exact hm'

/-- **A step of the committed log past the boot** keeps the sync and changes the members as the
v2-only step does: an attribute write overwrites (and with `v3` saves the record), a version
request does nothing to them, an `AddNode` of a voter is refused. -/
theorem restEntry_sync (ps : List w64) (c0 : w64) (e : EntryModel) (r : apply.RestM)
    (hs : memSync ps r)
    (hcc : e.typ ≠ W32 0 → ∀ cc, ccDecodeV1 e.data = some cc → ccApplyOk (GMap.listToSet ps) cc) :
    (restEntry c0 e r).mem = memStep e r.mem ∧ memSync ps (restEntry c0 e r) := by
  have hmemI := hs.2.2
  generalize hv : decide (uint.Z c0 < uint.Z e.index) = v3
  unfold restEntry memStep attrOf
  rw [hv]
  by_cases ht : e.typ = W32 0
  · by_cases hd : e.data = []
    · simp only [ht, hd, ↓reduceIte, ne_eq, not_true_eq_false, and_false]
      exact ⟨by first | trivial | rfl, hs⟩
    · simp only [ht, hd, ↓reduceIte, ne_eq, not_false_eq_true, and_self]
      cases hq : apply.irrDecode e.data with
      | none => exact ⟨by first | trivial | rfl, hs⟩
      | some rq =>
        simp only
        unfold apply.restAfter
        cases hver : rq.clusterVersionSet with
        | some ver =>
          simp only
          unfold apply.restSetVersion
          cases v3
          · exact ⟨by first | trivial | rfl, hs⟩
          · simp only [↓reduceIte]
            exact ⟨rfl, memSync_putIn_other ps r _ _ _ (by decide) (by decide) hs⟩
        | none =>
          simp only
          cases ha : rq.clusterMemberAttrSet with
          | none => exact ⟨by first | trivial | rfl, hs⟩
          | some a =>
            simp only
            unfold apply.restUpdateAttrs memUpd
            cases hl : r.mem.lookup a.memberID with
            | none => exact ⟨by first | trivial | rfl, hs⟩
            | some mm =>
              simp only
              have hmm := hmemI _ _ hl
              have hmI : ∀ id mm0, (r.mem.insert a.memberID (mm.withAttrs a)).lookup id = some mm0 →
                  mm0.id = id ∧ ∀ u ∈ mm0.peerURLs, utf8Valid u := by
                intro id mm0 h0
                simp only [GMap.lookup_insert_eq_iff] at h0
                split at h0
                · next he => cases h0; exact ⟨hmm.1.trans he, hmm.2⟩
                · exact hmemI id mm0 h0
              cases v3
              · simp only [Bool.false_eq_true, ↓reduceIte]
                exact ⟨by first | trivial | rfl, ⟨hs.1, hs.2.1, hmI⟩⟩
              · simp only [↓reduceIte, apply.RestM.putIn_mem]
                refine ⟨by first | trivial | rfl, ?_⟩
                have hid : (mm.withAttrs a).id = a.memberID := hmm.1
                have := memSync_putMember ps r (mm.withAttrs a) _ hs hmm.2 hmI
                rw [hid] at this
                exact this
  · simp only [ht, ↓reduceIte, false_and]
    cases hc : ccDecodeV1 e.data with
    | none => exact ⟨by first | trivial | rfl, hs⟩
    | some cc =>
      simp only
      obtain ⟨hty, hin, -⟩ := hcc ht cc hc
      have hin' : cc.nodeId ∈ ps := (GMap.elem_of_list_to_set _ _).1 hin
      have hf := ccValidOn_false ps r cc hs hty hin'
      unfold ccRest
      rw [if_neg (by rintro ⟨-, h⟩; rw [hf] at h; cases h)]
      exact ⟨by first | trivial | rfl, hs⟩

/-- **The log past the boot, in sync**: the model's members are the v2-only fold's. -/
theorem fold_sync (ps : List w64) (c0 : w64) (R : List EntryModel) (r : apply.RestM)
    (hs : memSync ps r)
    (hcc : ∀ e ∈ R, e.typ ≠ W32 0 → ∀ cc, ccDecodeV1 e.data = some cc →
      ccApplyOk (GMap.listToSet ps) cc) :
    (R.foldl (fun r m => restEntry c0 m r) r).mem = foldMem R r.mem := by
  induction R generalizing r with
  | nil => rfl
  | cons e R ih =>
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := restEntry_sync ps c0 e r hs (hcc e List.mem_cons_self)
    rw [ih _ h2 (fun e' he' => hcc e' (List.mem_cons_of_mem _ he')), h1]
    rfl

/-! ## The boot -/

/-- The in-memory members have their keys as ids and valid peer URLs. -/
def memValid (mem : GMap w64 apply.MemberM) : Prop :=
  ∀ id mm, mem.lookup id = some mm → mm.id = id ∧ ∀ u ∈ mm.peerURLs, utf8Valid u

/-- A boot member's peer URLs are valid. -/
theorem boot_member_valid (boot : List EntryM) (hurl : bootURLsOk boot) (e : EntryM)
    (he : e ∈ boot) (cc : ConfChangeM) (hd : ccDecodeV1 e.Data' = some cc) :
    ∀ u ∈ (membership.ccMemberAt cc).peerURLs, utf8Valid u := by
  intro u hu
  apply hurl.1 (membership.ccMemberOf cc.context) _ u hu
  exact List.mem_filterMap.2 ⟨e, he, by simp [hd]⟩

theorem memValid_memBoot (boot : List EntryM) (hurl : bootURLsOk boot) :
    memValid (memBoot boot) := by
  unfold memBoot
  suffices H : ∀ (l : List EntryM), (∀ e ∈ l, e ∈ boot) → ∀ acc, memValid acc →
      memValid (l.foldl (fun mem e => match ccDecodeV1 e.Data' with
        | some cc => mem.insert cc.nodeId (membership.ccMemberAt cc)
        | none => mem) acc) from H boot (fun _ h => h) ∅ (fun id mm h => by simp at h)
  intro l
  induction l with
  | nil => intro _ acc h; exact h
  | cons e l ih =>
    intro hl acc h
    rw [List.foldl_cons]
    apply ih (fun e' he' => hl e' (List.mem_cons_of_mem _ he'))
    split
    · next cc hd =>
      intro id mm hm
      simp only [GMap.lookup_insert_eq_iff] at hm
      split at hm
      · next he =>
        cases hm
        exact ⟨he, boot_member_valid boot hurl e (hl e List.mem_cons_self) cc hd⟩
      · exact h id mm hm
    · exact h

/-- The boot entries keep the members valid. -/
theorem memValid_boot_fold (boot : List EntryM) (hurl : bootURLsOk boot) (Q : List EntryM)
    (hQ : ∀ e ∈ Q, e ∈ boot) (r : apply.RestM) (h : memValid r.mem)
    (hty : ∀ e ∈ Q, e.Type' = W32 1) :
    memValid (Q.foldl (fun r e => restEntry (W64 0) (EntryModel.ofM e) r) r).mem := by
  induction Q generalizing r with
  | nil => exact h
  | cons e Q ih =>
    rw [List.foldl_cons]
    apply ih (fun e' he' => hQ e' (List.mem_cons_of_mem _ he')) _ ?_
      (fun e' he' => hty e' (List.mem_cons_of_mem _ he'))
    have htyne : (EntryModel.ofM e).typ ≠ W32 0 := by
      simp only [EntryModel.ofM, hty e List.mem_cons_self]; decide
    unfold restEntry
    rw [if_neg htyne]
    simp only [EntryModel.ofM]
    cases hd : ccDecodeV1 e.Data' with
    | none => exact h
    | some cc =>
      simp only
      unfold ccRest
      split
      · split
        · rw [apply.RestM.putIn_mem]
          intro id mm hm
          simp only [GMap.lookup_insert_eq_iff] at hm
          split at hm
          · next he =>
            cases hm
            exact ⟨he, boot_member_valid boot hurl e (hQ e List.mem_cons_self) cc hd⟩
          · exact h id mm hm
        · split
          · rw [apply.RestM.putIn_mem, apply.RestM.delIn_mem]
            intro id mm hm
            simp only [GMap.lookup_delete_iff] at hm
            split at hm
            · cases hm
            · exact h id mm hm
          · exact h
      · exact h

/-- **The rest model after the bootstrap log is in sync.** -/
theorem memSync_boot (ps : List w64) (boot : List EntryM)
    (hps : srvBootLogOk ps boot) (hnd : ps.Nodup) (hurl : bootURLsOk boot)
    (hbcc : ∀ e ∈ boot, ∀ cc, ccDecodeV1 e.Data' = some cc → ccApplyOk (GMap.listToSet ps) cc) :
    memSync ps (boot.foldl (fun r e => restEntry (W64 0) (EntryModel.ofM e) r) (restBoot boot)) := by
  have hids := bootSaved_ids ps boot hps
  have h0 : bootInv ps [] (restBoot boot) := by
    refine ⟨memOk_memBoot ps boot hbcc, fun k v => ?_, ?_⟩
    · simp [memBktOf, restBoot, restBootBk, GMap.lookup_insert_eq_iff, bootSaved]
    · simp [restBoot, restBootBk, GMap.lookup_insert_eq_iff]
  have hall : ∀ e ∈ boot, e.Type' = W32 1 ∧ 0 < uint.Z e.Index' ∧
      ∃ cc, ccDecodeV1 e.Data' = some cc ∧ ccApplyOk (GMap.listToSet ps) cc := by
    intro e he
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
    obtain ⟨-, -, hkk⟩ := hps
    obtain ⟨-, hix, hty, cc, hd, -, -⟩ := hkk k _ (List.getElem?_eq_getElem hk)
    exact ⟨hty, by rw [hix]; omega, cc, hd, hbcc _ he cc hd⟩
  have h1 := boot_fold ps [] boot _ h0 hall (by simpa [hids] using hnd) (by simpa using hurl)
  simp only [List.nil_append] at h1
  obtain ⟨-, hb, hrm⟩ := h1
  have hval := memValid_boot_fold boot hurl boot (fun _ h => h) (restBoot boot)
    (memValid_memBoot boot hurl) (fun e he => (hall e he).1)
  refine ⟨⟨bootSaved boot, hb, by rw [hids]; exact hnd, ?_, fun id hid => by rw [hids]; exact hid⟩,
    hrm, hval⟩
  intro mm hmm u hu
  obtain ⟨e, he, hmm'⟩ := List.mem_filterMap.1 hmm
  obtain ⟨cc, hd, rfl⟩ := Option.map_eq_some_iff.1 hmm'
  exact boot_member_valid boot hurl e he cc hd u hu

/-! ## The closing identity -/

/-- **The closing identity** (R2d' A2; DRAFT): replaying v2-only any suffix (`drop j`) of a
committed log that starts with the bootstrap log `boot` of the voters `ps` (distinct, their URLs
`bootURLsOk`), whose conf changes are all the server's (`ccApplyOk`), on its rest model gives the
rest model back (see the file header). -/
theorem restReplay_close (ps : List w64) (boot : List EntryM) (R : List EntryModel) (j : Nat)
    (hps : srvBootLogOk ps boot) (hnd : ps.Nodup) (hurl : bootURLsOk boot)
    (hbcc : ∀ e ∈ boot, ∀ cc, ccDecodeV1 e.Data' = some cc → ccApplyOk (GMap.listToSet ps) cc)
    (hcc : ∀ e ∈ R, e.typ ≠ W32 0 → ∀ cc, ccDecodeV1 e.data = some cc →
      ccApplyOk (GMap.listToSet ps) cc) :
    ((boot.map EntryModel.ofM ++ R).drop j).foldl (fun r m => restEntryV2 m r)
        (restModel (W64 0) boot (boot.map EntryModel.ofM ++ R)) =
      restModel (W64 0) boot (boot.map EntryModel.ofM ++ R) := by
  have hfold : restModel (W64 0) boot (boot.map EntryModel.ofM ++ R) =
      R.foldl (fun r m => restEntry (W64 0) m r)
        (boot.foldl (fun r e => restEntry (W64 0) (EntryModel.ofM e) r) (restBoot boot)) := by
    simp [restModel, List.foldl_append, List.foldl_map]
  have hsync := memSync_boot ps boot hps hnd hurl hbcc
  have hmem := fold_sync ps (W64 0) R _ hsync hcc
  rw [fold_restEntryV2]
  -- the replayed boot entries are conf entries
  have hbt : ∀ m ∈ boot.map EntryModel.ofM, m.typ ≠ W32 0 := by
    intro m hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
    obtain ⟨-, -, hkk⟩ := hps
    obtain ⟨-, -, hty, -⟩ := hkk k _ (List.getElem?_eq_getElem hk)
    simp only [EntryModel.ofM, hty]; decide
  rw [List.drop_append, foldMem_append,
    foldMem_conf _ _ (fun m hm => hbt m (List.mem_of_mem_drop hm))]
  generalize hX : restModel (W64 0) boot (boot.map EntryModel.ofM ++ R) = X
  have hXm : X.mem = foldMem R
      (boot.foldl (fun r e => restEntry (W64 0) (EntryModel.ofM e) r) (restBoot boot)).mem := by
    rw [← hX, hfold, hmem]
  generalize (boot.foldl (fun r e => restEntry (W64 0) (EntryModel.ofM e) r) (restBoot boot)).mem
    = M at hXm
  generalize j - (List.map EntryModel.ofM boot).length = i
  have e : foldMem R M = foldMem (R.drop i) (foldMem (R.take i) M) := by
    rw [← foldMem_append, List.take_append_drop]
  have hfin : foldMem (R.drop i) X.mem = X.mem := by rw [hXm, e, foldMem_idem]
  rw [hfin]

end pure

end EtcdGrove
end Perennial
