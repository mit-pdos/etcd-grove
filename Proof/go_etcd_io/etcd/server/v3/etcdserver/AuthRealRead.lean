/-
**The auth backend's read side over the real backend** (auth-schema-srv A6, 2026-11-17): schema's
read contracts (`schema.authReader`, `authRTx`, `authBE`, `InvAuthBackend.lean`) met by the backend's
shared read transaction (`readTx`). A held read transaction at the readers' state `rv` reads the auth
buckets `rvAuth P rv` (`rvBkt` of each): its point reads through `readTx.UnsafeRange` (`rtRange_single`),
its walk of `AuthUsers` through `readTx.UnsafeForEach` (`rtForEach`, a permutation of the bucket's
entries: `rtForEach_perm`). The token is `rtHeld … rv ∗ X` for any `X` (what a realization keeps beside
the read lock); `RLock`/`RUnlock` go through the caller's ghost steps (`authBE_real`: the ticket's
redemption for a reader slot and a share of the backend's open token, the observation of the buckets'
well-formedness), so that this file states no realization. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvAuthBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__UnsafeForEach
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__UnsafeRange
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__RLock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.readTx__RUnlock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__ReadTx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace schema

open Iris Iris.BI Iris.ProofMode backend

theorem strLt_irrefl' (a : GoString) : ¬ strLt a a := fun h => go.goStringLt_asymm h h

/-! ## The walk's entries -/

section pure
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]


theorem nodup_of_map {α β : Type} (f : α → β) {l : List α} (h : (l.map f).Nodup) : l.Nodup := by
  rw [List.Nodup, List.pairwise_map] at h
  exact h.imp (fun hne heq => hne (congrArg f heq))

theorem sorted_keys_nodup {es : List Ent} (h : entsSorted es) : (es.map Prod.fst).Nodup := by
  unfold entsSorted at h
  rw [List.Nodup, List.pairwise_map]
  exact h.imp (fun {a b} (hlt : strLt a.1 b.1) (heq : a.1 = b.1) => strLt_irrefl' b.1 (heq ▸ hlt))

/-- In sorted entries, an entry is the last value of its key. -/
theorem sorted_mem_iff {es : List Ent} (h : entsSorted es) (k v : GoString) :
    (k, v) ∈ es ↔ lastVal es k = some v := by
  induction es with
  | nil => simp [lastVal]
  | cons e l ih =>
    have hl : entsSorted l := (List.pairwise_cons.1 h).2
    have hlt : ∀ x ∈ l, strLt e.1 x.1 := (List.pairwise_cons.1 h).1
    rw [lastVal_cons, List.mem_cons, ih hl]
    obtain ⟨e1, e2⟩ := e
    by_cases he : e1 = k
    · subst he
      have hn : lastVal l e1 = none :=
        lastVal_eq_none (fun x hx hx' => strLt_irrefl' e1 (hx' ▸ hlt x hx))
      rw [hn]
      simp only [↓reduceIte, Option.none_or, Option.some.injEq, Prod.mk.injEq, true_and]
      constructor
      · rintro (h | h)
        · exact h.symm
        · cases h
      · intro h; exact Or.inl h.symm
    · simp only [he, ↓reduceIte, Option.or_none, Prod.mk.injEq]
      constructor
      · rintro (h | h)
        · exact absurd h.1.symm he
        · exact h
      · intro h; exact Or.inr h

theorem mem_bktEnts_iff (m : BktData) (k v : GoString) : (k, v) ∈ bktEnts m ↔ m.lookup k = some v := by
  unfold bktEnts
  rw [(List.mergeSort_perm m.toList entLe).mem_iff]
  exact GMap.mem_toList m k v

theorem bktEnts_nodup (m : BktData) : (bktEnts m).Nodup :=
  nodup_of_map Prod.fst (sorted_keys_nodup (bktEnts_sorted m))

/-- The read buffer's entries of a table bucket are sorted (`rv.2.Wf`). -/
theorem bkOf_sorted {rv : RView} (hw : rv.2.Wf) (i : w64) : entsSorted (bkOf rv.2.bks i) := by
  unfold bkOf
  cases h : rv.2.bks.lookup i with
  | none => exact List.Pairwise.nil
  | some es => exact hw i es h

/-- **A read transaction's walk visits the readers' view of the bucket**: `rtForEach` holds exactly
the entries of `rvBkt` (a table bucket, the read buffer canonical). -/
theorem rtForEach_mem {P : BParams} {rv : RView} {bi : BucketInfo} (hb : P.has bi) (hw : rv.2.Wf)
    (k v : GoString) : (k, v) ∈ rtForEach rv bi ↔ (rvBkt P rv bi.name).lookup k = some v := by
  have hs := bkOf_sorted hw bi.id
  rw [rvBkt_lookup]
  have hvOf : vOf P rv bi.name k =
      (lastVal (bkOf rv.2.bks bi.id) k).or ((bktOf rv.1 bi.name).lookup k) := by
    unfold vOf ovB
    unfold BParams.has at hb
    rw [hb]
    congr 1
    unfold dget bktOf
    cases rv.1.lookup bi.name <;> rfl
  rw [hvOf]
  unfold rtForEach
  rw [List.mem_append, List.mem_filter, mem_bktEnts_iff, sorted_mem_iff hs]
  have hkeys : k ∈ (bkOf rv.2.bks bi.id).map Prod.fst ↔ (lastVal (bkOf rv.2.bks bi.id) k).isSome := by
    constructor
    · intro hm
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
      have : (e.1, e.2) ∈ bkOf rv.2.bks bi.id := he
      rw [sorted_mem_iff hs] at this
      rw [this]; rfl
    · intro hs'
      obtain ⟨e, he, rfl⟩ := lastVal_isSome_mem hs'
      exact List.mem_map.2 ⟨e, he, rfl⟩
  simp only [decide_eq_true_eq]
  rw [hkeys]
  cases hl : lastVal (bkOf rv.2.bks bi.id) k with
  | none => simp
  | some w =>
    simp only [Option.isSome_some, not_true_eq_false, and_false, false_or, Option.some_or]

theorem rtForEach_nodup {rv : RView} {bi : BucketInfo} (hw : rv.2.Wf) :
    (rtForEach rv bi).Nodup := by
  have hs := bkOf_sorted hw bi.id
  unfold rtForEach
  rw [List.nodup_append]
  refine ⟨(bktEnts_nodup _).filter _, nodup_of_map Prod.fst (sorted_keys_nodup hs), ?_⟩
  intro a ha b hb' hab
  subst hab
  have := (List.mem_filter.1 ha).2
  simp only [decide_eq_true_eq] at this
  exact this (List.mem_map.2 ⟨a, hb', rfl⟩)

/-- **The walk is a permutation of the bucket's entries.** -/
theorem rtForEach_perm {P : BParams} {rv : RView} {bi : BucketInfo} (hb : P.has bi) (hw : rv.2.Wf) :
    (rtForEach rv bi).Perm (bktEnts (rvBkt P rv bi.name)) := by
  apply (List.perm_ext_iff_of_nodup (rtForEach_nodup hw) (bktEnts_nodup _)).2
  intro ⟨k, v⟩
  rw [rtForEach_mem hb hw, mem_bktEnts_iff]

end pure

/-! ## The auth buckets of a readers' state -/

/-- **The auth buckets a reader at the readers' state `rv` reads.** -/
def rvAuth (P : BParams) (rv : RView) : AuthData :=
  ⟨rvBkt P rv mvcc.authBI.name, rvBkt P rv mvcc.authUsersBI.name, rvBkt P rv mvcc.authRolesBI.name⟩

end schema
end EtcdGrove
end Perennial
