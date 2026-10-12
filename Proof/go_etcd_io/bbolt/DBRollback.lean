/-
The writer rolls back (`Tx.Rollback` of a write transaction: `freelist.Rollback(txid)`, then
`close`): the database without the writer (`DBState.removeWriter`: its fractions of the slots
and fields back, `rwtx` cleared), the freelist rolled back, keeps its facts (`dbOK_removeWriter`),
and the freelist's `Rollback` does not panic (`canRollback`: the writer freed no page it
allocated, every page it freed being of its view).

The pages the writer allocated from the freelist are neither free nor allocated afterwards
(bbolt drops them from `allocs`, as `FLState.rollback` does): they come back with the next
reload of the freelist. That keeps every fact (they are in no view).
-/
module

public import Proof.go_etcd_io.bbolt.DBFree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section pure

theorem foldl_rbStep_lookup (l : List (w64 × w64)) (m : GMap w64 w64) (k a : w64)
    (h : (l.foldl rbStep m) !! k = some a) : m !! k = some a ∨ (k, a) ∈ l := by
  induction l generalizing m with
  | nil => exact Or.inl h
  | cons x l ih =>
    rcases ih (rbStep m x) h with h1 | h1
    · unfold rbStep at h1
      split at h1
      · exact Or.inl h1
      · rcases (GMap.lookup_insert_Some _ _ _ _ _).1 h1 with ⟨e1, e2⟩ | ⟨_, h2⟩
        · right; subst e1 e2; exact List.mem_cons_self
        · exact Or.inl h2
    · exact Or.inr (List.mem_cons_of_mem _ h1)

theorem rb_allocs (fl : FLState) (txid k a : w64) (h : (fl.rollback txid).allocs !! k = some a) :
    fl.allocs !! k = some a ∨ ∃ pd, fl.pending !! txid = some pd ∧ (k, a) ∈ pd.pairs := by
  cases hp : fl.pending !! txid with
  | none => rw [rollback_none hp] at h; exact Or.inl h
  | some pd =>
    rw [rollback_some hp] at h
    simp only at h
    rw [GMap.lookup_filter] at h
    cases hf : (pd.pairs.foldl rbStep fl.allocs) !! k with
    | none => rw [hf] at h; cases h
    | some v =>
      rw [hf] at h
      simp only [Option.filter] at h
      split at h
      · obtain rfl := Option.some.inj h
        rcases foldl_rbStep_lookup _ _ _ _ hf with h1 | h1
        · exact Or.inl h1
        · exact Or.inr ⟨pd, rfl, h1⟩
      · cases h

theorem rb_pending (fl : FLState) (txid t : w64) (pd : Pending)
    (h : (fl.rollback txid).pending !! t = some pd) : t ≠ txid ∧ fl.pending !! t = some pd := by
  cases hp : fl.pending !! txid with
  | none =>
    rw [rollback_none hp] at h
    exact ⟨fun e => (by subst e; rw [hp] at h; cases h), h⟩
  | some pd0 =>
    rw [rollback_some hp] at h
    simp only at h
    obtain ⟨hne, h2⟩ := (GMap.lookup_delete_Some _ _ _ _).1 h
    exact ⟨Ne.symm hne, h2⟩

theorem rb_free (fl : FLState) (txid : w64) : (fl.rollback txid).free = fl.free := by
  cases hp : fl.pending !! txid with
  | none => rw [rollback_none hp]
  | some pd => rw [rollback_some hp]

theorem rb_readonly (fl : FLState) (txid : w64) : (fl.rollback txid).readonly = fl.readonly := by
  cases hp : fl.pending !! txid with
  | none => rw [rollback_none hp]
  | some pd => rw [rollback_some hp]

/-- A transaction of an entry whose two lists have the same length is in one of its pairs. -/
theorem mem_pairs_of_mem_alloctx (pd : Pending) (t : w64) (hl : pd.ids.length = pd.alloctx.length)
    (ht : t ∈ pd.alloctx) : ∃ x, (x, t) ∈ pd.pairs := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
  refine ⟨pd.ids[i]'(by omega), ?_⟩
  unfold Pending.pairs
  rw [List.mem_iff_getElem]
  exact ⟨i, by simp; omega, by simp⟩

end pure

section rollback
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- The database without the writer `w` (its fractions back; `Tx.close`). -/
def DBState.removeWriter (σ : DBState) (w : Reader) : DBState :=
  { σ with
    rwtx := null
    wr := none
    rem := fun s => if w.sees s then σ.rem s + w.q else σ.rem s
    frem := σ.frem + w.q }
proj_simps DBState.removeWriter

/-- The writer `w` (its meta's txid `w.txid + 1`) rolls back its freelist: `Rollback` does not
panic, and the database's facts are kept (the writer still open). -/
theorem dbOK_rollbackW (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (hwf : σ.fl.WF) (w : Reader) (hw : σ.wr = some w) :
    σ.fl.canRollback (w.txid + W64 1) ∧
    dbOK { σ with fl := σ.fl.rollback (w.txid + W64 1) } v0 v1 := by
  have h' := h
  obtain ⟨hps, hps2, hn, hsz, hdc, hm0, hm1, hv, hcur, hrd, hmv, hsl, hfl, hro, hrs, hwr⟩ := h'
  obtain ⟨cwf, cdisj, cin, calloc, cfree, cbelow, cagree⟩ := hcur
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := cbelow
  have hmt := congrArg (fun x : w64 => uint.Z x) (b4 w hw).2
  have htxz := txid_succ_z w.txid (w.txid + W64 1) (by omega) rfl
  -- the writer's pending pairs: allocated at or before its view
  have hpair : ∀ t pd p, σ.fl.pending !! t = some pd → p ∈ pd.pairs → t = w.txid + W64 1 →
      uint.Z p.2 ≤ uint.Z w.txid := by
    intro t pd p ht hp hteq
    rcases b3 t pd p ht hp with hle | ⟨w', hw', _, hp2⟩
    · subst hteq; omega
    · obtain rfl := Option.some.inj (hw.symm.trans hw'); exact hp2
  refine ⟨fun pd hpd t ht ht0 heq => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := mem_pairs_of_mem_alloctx pd t (hwf.2.2.2.2 _ pd hpd) ht
    have := hpair _ pd (x, t) hpd hx rfl
    simp only at this
    subst heq; omega
  -- a view keeps the rule: a page the writer freed that it covers, it saw allocated
  have hview : ∀ (T : w64) (P : GMap Nat (List w8)), mvccView σ T P →
      mvccView { σ with fl := σ.fl.rollback (w.txid + W64 1) } T P := by
    intro T P hm
    obtain ⟨m1, m2⟩ := hm
    refine ⟨fun id pg hid a hal => ?_, fun s hs => ⟨(m2 s hs).1,
      by simp only; rw [rb_free]; exact (m2 s hs).2.1,
      fun t pd a ht hp => (m2 s hs).2.2 t pd a (rb_pending _ _ _ _ ht).2 hp⟩⟩
    rcases rb_allocs _ _ _ _ hal with h1 | ⟨pd, hpd, hp⟩
    · exact m1 id pg hid a h1
    · exact ((m2 id (covers_self _ _ _ hid)).2.2 _ pd a hpd hp).1
  refine ⟨hps, hps2, hn, hsz, hdc, hm0, hm1, hv,
    ⟨cwf, cdisj, cin, fun id pg hid a hal => ?_,
      fun s hs => ⟨(cfree s hs).1, by simp only; rw [rb_free]; exact (cfree s hs).2.1,
        fun t pd a ht hp => (cfree s hs).2.2 t pd a (rb_pending _ _ _ _ ht).2 hp⟩,
      ⟨fun x hx => b1 x (by simp only at hx; rw [rb_free] at hx; exact hx),
        fun t pd p ht hp hle => b2 t pd p (rb_pending _ _ _ _ ht).2 hp hle,
        fun t pd p ht hp => b3 t pd p (rb_pending _ _ _ _ ht).2 hp, b4, b5,
        fun x hx => b6 x (by simp only at hx; rw [rb_free] at hx; exact hx),
        fun t pd p ht hp => b7 t pd p (rb_pending _ _ _ _ ht).2 hp⟩, cagree⟩,
    hrd, fun k r hk => hview _ _ (hmv k r hk), hsl, hfl,
    by show (σ.fl.rollback (w.txid + W64 1)).readonly.Perm _; rw [rb_readonly]; exact hro,
    hrs, ⟨hwr.1, fun w' hw' => ⟨(hwr.2 w' hw').1, hview _ _ (hwr.2 w' hw').2⟩⟩⟩
  -- the current tree's allocations: those before, or the writer's pending pairs'
  rcases rb_allocs _ _ _ _ hal with h1 | ⟨pd, hpd, hp⟩
  · exact calloc id pg hid a h1
  · have := hpair _ pd _ hpd hp rfl; simp only at this; omega

/-- The writer `w`, with nothing pending (rolled back), ends: the database's facts are kept
without it. -/
theorem dbOK_removeWriter (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (w : Reader) (hw : σ.wr = some w) (hnp : σ.fl.pending !! (w.txid + W64 1) = none) :
    dbOK (σ.removeWriter w) v0 v1 := by
  obtain ⟨hps, hps2, hn, hsz, hdc, hm0, hm1, hv, hcur, hrd, hmv, hsl, hfl, hro, hrs, hwr⟩ := h
  obtain ⟨cwf, cdisj, cin, calloc, cfree, cbelow, ⟨va1, va2⟩⟩ := hcur
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := cbelow
  refine ⟨hps, hps2, hn, hsz, hdc, hm0, hm1, hv,
    ⟨cwf, cdisj, cin, calloc, fun s hs => ⟨(cfree s hs).1, (cfree s hs).2.1,
        fun t pd a ht hp => ?_⟩,
      ⟨b1, b2, fun t pd p ht hp => ?_, fun w' h => by simp [DBState.removeWriter.proj_wr] at h, b5,
        b6, b7⟩,
      ⟨va1, fun w' h => by simp [DBState.removeWriter.proj_wr] at h⟩⟩,
    hrd, hmv, fun s hs => ?_, ?_, hro, hrs, ?_⟩
  · -- the current tree's slots: pending only for the writer, which has nothing pending
    obtain ⟨⟨w', hw', ht'⟩, _⟩ := (cfree s hs).2.2 t pd a ht hp
    obtain rfl := Option.some.inj (hw.symm.trans hw')
    rw [DBState.removeWriter.proj_fl, ht', hnp] at ht; cases ht
  · rcases b3 t pd p ht hp with h1 | ⟨w', hw', ht', -⟩
    · exact Or.inl h1
    · obtain rfl := Option.some.inj (hw.symm.trans hw')
      rw [DBState.removeWriter.proj_fl, ht', hnp] at ht; cases ht
  · -- the slots: the writer's fraction back
    have H := hsl s hs
    rw [hw] at H
    show fracSum (if w.sees s then σ.rem s + w.q else σ.rem s)
      (wQ none (fun r => r.sees s) (readersQ σ.readers (fun r => r.sees s))) halfQ
    unfold wQ at H ⊢
    cases hrs' : w.sees s
    · simp only [hrs', Bool.false_eq_true, ↓reduceIte] at H ⊢; exact H
    · simp only [hrs', ↓reduceIte] at H ⊢; exact fracSum_give _ _ _ _ H
  · -- the fields
    have H := hfl
    unfold fieldsOK at H
    rw [hw] at H
    show fracSum (σ.frem + w.q) (wQ none (fun _ => true) (readersQ σ.readers (fun _ => true))) 1
    unfold wQ at H ⊢
    simp only [↓reduceIte] at H
    exact fracSum_give _ _ _ _ H
  · exact ⟨⟨fun _ => rfl, fun _ => rfl⟩, fun w' h => by simp [DBState.removeWriter.proj_wr] at h⟩

theorem rb_pending_none (fl : FLState) (txid : w64) : (fl.rollback txid).pending !! txid = none := by
  cases h : (fl.rollback txid).pending !! txid with
  | none => rfl
  | some pd => exact absurd rfl (rb_pending fl txid txid pd h).1

open Iris.ProofMode in
/-- An ending writer gives back its pages and its part of the fields. -/
theorem wend_give (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (w : Reader) (hw : σ.wr = some w) (dbl : Loc) :
    slotsView (GF := GF) σ.data σ.bs σ.ps σ.rem (List.range σ.nslots) ∗
      structFieldRef DB go!"data" dbl ↦{DFrac.own σ.frem} σ.data ∗
      pagesView σ.data σ.ps w.q w.pages ∗
      structFieldRef DB go!"data" dbl ↦{DFrac.own w.q} σ.data ⊢
    slotsView σ.data σ.bs σ.ps (σ.removeWriter w).rem (List.range σ.nslots) ∗
      structFieldRef DB go!"data" dbl ↦{DFrac.own (σ.removeWriter w).frem} σ.data := by
  have hps := h.1
  obtain ⟨_, rdisj, rin⟩ := writer_readerOK σ v0 v1 h w hw
  have Hcarve := slots_carve (GF := GF) σ.data σ.bs σ.ps (σ.removeWriter w).rem σ.rem w.q
    σ.nslots w.pages (by omega) (nslots_mul_le σ)
    (fun id pg hid => ⟨(rin id pg hid).1.symm, by have := (rin id pg hid).2; omega⟩) rdisj
    (fun s _ hc => by
      show (if w.sees s then σ.rem s + w.q else σ.rem s) = σ.rem s + w.q
      rw [show w.sees s = true by unfold Reader.sees; simp only [decide_eq_true_eq]; exact hc]
      rfl)
    (fun s _ hc => by
      show (if w.sees s then σ.rem s + w.q else σ.rem s) = σ.rem s
      rw [show w.sees s = false by unfold Reader.sees; simp only [decide_eq_false_iff_not]; exact hc]
      rfl)
  rw [DBState.removeWriter.proj_frem]
  iintro ⟨Hs, Hd, Hpg, Hd'⟩
  isplitl [Hs Hpg]
  · iapply Hcarve.2; iframe
  · iapply (pointsto_split _ _ _ _).2; iframe

open Iris.ProofMode in
/-- The writer `w` rolls back its freelist: the database's freelist lent to `Rollback` (which
does not panic), and the database with it rolled back given back. -/
theorem ownDB_rollback (I : FLImpl (GF := GF)) (dbl : Loc) (γ : DBNames) (σ : DBState)
    (w : Reader) (hw : σ.wr = some w) :
    ownDB I dbl γ σ ⊢ ∃ (fls : Loc),
      ⌜σ.fl.canRollback (w.txid + W64 1)⌝ ∗ ownFL I fls σ.fl ∗
      (ownFL I fls (σ.fl.rollback (w.txid + W64 1)) -∗
        ownDB I dbl γ { σ with fl := σ.fl.rollback (w.txid + W64 1) }) := by
  iintro Hdb
  isimp only [ownDB] at Hdb
  iNamed Hdb
  isimp only [ownFL] at Hfl
  icases Hfl with ⟨#Hh, Hsh, Ho⟩
  ihave Hsh := ownShared_wf _ _ _ $$ Hsh
  icases Hsh with ⟨Hsh, %hwf⟩
  obtain ⟨hcan, hok'⟩ := dbOK_rollbackW σ v0 v1 Hok hwf w hw
  iexists fls
  isplitr
  · ipureintro; exact hcan
  isplitl [Hsh Ho]
  · simp only [ownFL]; iframe; iframe #
  iintro Hfl'
  simp only [ownDB]
  iexists dv, fls, v0, v1, dl
  isplitr
  · ipureintro; exact Hdv
  isplitr
  · ipureintro; exact hok'
  isplitr
  · ipureintro; exact Hdr
  isplitr
  · ipureintro; exact Hops
  iframe
  iframe #
  try (ipureintro; exact Hlog)

end rollback

end bbolt
end EtcdGrove
end Perennial
