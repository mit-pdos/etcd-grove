/-
**The flagged rollback's writer side** (maintainer 11, for `Tx.rollback_f`): `wdb_rollback'` from
`wdbOK' fr` (after `Commit`'s free of the synced freelist page, its slots pending for the writer):
the rollback deletes the writer's pending entry, so the relaxed slot clause (`flCurOKr`) becomes
`flCurOK`'s, and the page's slots, returned by `store_rollback` with the bytes the writer recorded
(`fbRel`), hold the page's bytes again.
-/
module

public import Proof.go_etcd_io.bbolt.Commit.RollbackFacts
public import Proof.go_etcd_io.bbolt.Inv.WdbFlag

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- **The relaxed freelist-page clause after the writer's rollback** is `flCurOK`'s (the page's
`allocs` entry comes back from the writer's pending entry, whose allocating transactions are
committed: `hpa`, `flBelow`'s writer clause). -/
theorem flCurOKr_rollback (fl : FLPg) (C : CommitSt) (pg : List w8) (wtx : w64)
    (hwtx : C.txid < wtx.toNat)
    (hpa : ∀ pd, fl.pending !! wtx = some pd → ∀ a ∈ pd.alloctx, a.toNat ≤ C.txid)
    (h : flCurOKr fl C wtx pg) :
    flCurOK (fl.rollback wtx) C pg := by
  intro f hf
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := h f hf
  have hfree : (fl.rollback wtx).free = fl.free := rollback_free _ _
  have hsub : ∀ t pd, (fl.rollback wtx).pending !! t = some pd → fl.pending !! t = some pd :=
    fun t pd hp => rollback_pending_sub _ _ t pd hp
  have hcp : ∀ x, committedPending (fl.rollback wtx) C x → committedPending fl C x := by
    rintro x ⟨t, pd, hp, hx, ht⟩
    exact ⟨t, pd, hsub t pd hp, hx, ht⟩
  refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, fun s h1 h2 => ⟨(a9 s h1 h2).1, ?_⟩,
    fun x hx => ?_, fun x hx => a11 x (hcp x hx), fun x hx => ?_, fun a ha => ?_, a14⟩
  · intro hm
    obtain ⟨-, -, hnf, hpt⟩ := a9 s h1 h2
    rcases List.mem_append.1 hm with hm | hm
    · rw [hfree] at hm
      exact hnf hm
    · obtain ⟨t, pd, hp, hx⟩ := (pendingIds_mem_iff _ _).1 hm
      have hp' := hsub t pd hp
      have ht := hpt t pd hp' hx
      subst ht
      have hnone : (fl.rollback t).pending !! t = none := by
        unfold FLPg.rollback
        split
        · assumption
        · unfold FLPg.rollbackEntry; simp
      rw [hnone] at hp
      cases hp
  · rw [hfree] at hx; exact a10 x hx
  · rcases a12 x hx with ⟨t, pd, hp, hx', ht⟩ | h
    · left
      have hne : t ≠ wtx := by intro e; subst e; omega
      exact ⟨t, pd, by rw [rollback_pending_ne _ _ _ hne]; exact hp, hx', ht⟩
    · exact .inr h
  · rcases rollback_allocs_lookup fl wtx _ a ha with h | ⟨pd, hpd, -, hin⟩
    · exact a13 a h
    · exact hpa pd hpd a hin

/-- `flBelow`'s writer clause: the live writer's (`C.txid + 1`) pending entry records committed
allocating transactions. -/
theorem flBelow_wtx_alloctx (fl : FLPg) (C : CommitSt) (wo : Option Nat) (hbl : flBelow fl C wo) :
    ∀ pd, fl.pending !! W64 ((C.txid + 1 : Nat) : Int) = some pd → ∀ a ∈ pd.alloctx,
      a.toNat ≤ C.txid := by
  intro pd hp a ha
  have hT : (W64 ((C.txid + 1 : Nat) : Int)).toNat = C.txid + 1 := toNat_W64_of_lt _ hbl.2.2.2.1
  rcases hbl.2.2.1 _ pd hp with h | ⟨-, h⟩
  · rw [hT] at h; omega
  · have := h a ha; rw [hT] at this; omega

/-- `extentBytes` reads only the extent's slots. -/
theorem extentBytes_congr' (wb wb' : Nat → List w8) (f : Nat)
    (h : ∀ s, f ≤ s → s < f + (1 + pageOverflow (wb f)) → wb' s = wb s) :
    extentBytes wb' f = extentBytes wb f := by
  have hf : wb' f = wb f := h f (Nat.le_refl _) (by omega)
  unfold extentBytes
  rw [hf]
  have key : ∀ l : List Nat, (∀ s ∈ l, wb' s = wb s) → l.flatMap wb' = l.flatMap wb := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.flatMap_cons]
      rw [hl a (List.mem_cons_self), ih (fun s hs => hl s (List.mem_cons_of_mem _ hs))]
  apply key
  intro s hs
  obtain ⟨h1, h2⟩ := List.mem_range'_1.1 hs
  exact h s h1 h2

end pure

section rb
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

omit [GooseSemantics] [GooseInterp] go_gctx hos sem in
/-- **The writer side's facts after the rollback, flagged** (`wdbOK_rolledBack'` from `wdbOK' fr`):
the returned slots of the synced page's extent hold the bytes the writer recorded (`hrec`, from
`store_rollback` under `fbCond`), which are `w.wb`'s there (`fbRel`). -/
theorem wdbOK_rolledBack_f (fr : Bool) (w : WDb) (fl' : FLPg) (S : List Nat)
    (bs : Nat → List w8) (F : GMap Nat (List w8))
    (hok : wdbOK' fr w) (hF : fbRel w F) (hfl' : fl' = w.fl.rollback (W64 ((w.C.txid + 1 : Nat) : Int)))
    (hpa : ∀ pd, w.fl.pending !! W64 ((w.C.txid + 1 : Nat) : Int) = some pd → ∀ a ∈ pd.alloctx,
      a.toNat ≤ w.C.txid)
    (hS : ∀ s, s ∈ S ↔ s ∈ slotsOf w.C w.fl ∧ s ∉ slotsOf w.C fl')
    (h2s : ∀ s ∈ pendSlots w.fl, 2 ≤ s) (hbs : ∀ s ∈ S, (bs s).length = 4096)
    (hrec : fbCond w.C w.fl (some (w.C.txid + 1)) false →
      ∀ s ∈ S, ∀ v, F !! s = some v → bs s = v) :
    wdbOK { w with fl := fl', W := w.W ++ S, wb := mergeWb S bs w.wb } := by
  cases fr
  · exact wdbOK_rolledBack' w fl' S bs hok hfl' hS h2s hbs
  have h0 := wdbOK'_noFl true w hok
  have h1 := wdbOK_rolledBack' w.noFl fl' S bs h0 hfl' hS h2s hbs
  have hc7 : w.C.txid + 1 < 2 ^ 64 := hok.2.2.2.2.2.2.1
  have hT : (W64 ((w.C.txid + 1 : Nat) : Int)).toNat = w.C.txid + 1 := toNat_W64_of_lt _ hc7
  refine wdbOK'_of_noFl false _ h1 ?_
  intro f hf
  have hr := ((wdbOK'_flClause true w hok) f hf).2
  -- the extent's bytes are kept
  have hSm : ∀ s ∈ S, s ∈ pendSlots w.fl := by
    intro s hs
    obtain ⟨h1, h2⟩ := (hS s).1 hs
    rcases (mem_slotsOf _ _ _).1 h1 with h | h
    · exact absurd ((mem_slotsOf _ _ _).2 (.inl h)) h2
    · exact h
  have hext : extentBytes (mergeWb S bs w.wb) f = extentBytes w.wb f := by
    refine extentBytes_congr' w.wb _ f (fun s hs1 hs2 => ?_)
    simp only [mergeWb]
    split
    · rename_i hsS
      obtain ⟨⟨pd, hpd, x, hx, hxf⟩, hFs⟩ := hF f hf s hs1 hs2 (hSm s hsS)
      have hcov := ((hr f hf).2.2.2.2.2.2.2.2.1 f (Nat.le_refl _) (by omega)).1
      exact hrec ⟨rfl, w.C.txid + 1, f, pd, rfl, hf, hcov, hpd, x, hx, hxf⟩ s hsS _ hFs
    · rfl
  simp only
  rw [hext, hfl']
  exact flCurOKr_rollback w.fl w.C _ _ (by rw [hT]; omega) hpa hr

omit sem in
/-- **`wdb_rollback'`, flagged.** -/
theorem wdb_rollback_f (p : GoString) (fr : Bool) (w : WDb) (fl' : FLPg) (S : List Nat)
    (bs : Nat → List w8) (F : GMap Nat (List w8))
    (hok : wdbOK' fr w) (hF : fbRel w F) (hfl' : fl' = w.fl.rollback (W64 ((w.C.txid + 1 : Nat) : Int)))
    (hpa : ∀ pd, w.fl.pending !! W64 ((w.C.txid + 1 : Nat) : Int) = some pd → ∀ a ∈ pd.alloctx,
      a.toNat ≤ w.C.txid)
    (hS : ∀ s, s ∈ S ↔ s ∈ slotsOf w.C w.fl ∧ s ∉ slotsOf w.C fl')
    (h2s : ∀ s ∈ pendSlots w.fl, 2 ≤ s) (hbs : ∀ s ∈ S, (bs s).length = 4096)
    (hrec : fbCond w.C w.fl (some (w.C.txid + 1)) false →
      ∀ s ∈ S, ∀ v, F !! s = some v → bs s = v) :
    wCells (GF := GF) w.ms w.W ∗ wBytes p w.W w.wb w.m.size ∗ slotsOwn w.ms p S bs ⊢
      ∃ w' : WDb, ⌜w'.C = w.C ∧ w'.fl = fl' ∧ w'.ms = w.ms ∧ w'.m = w.m ∧ w'.fli = w.fli ∧
          w'.junk = w.junk ∧ w'.f = w.f ∧ w'.fd = w.fd ∧ wdbOK w'⌝ ∗
        wCells w'.ms w'.W ∗ wBytes p w'.W w'.wb w'.m.size := by
  have hok' := wdbOK_rolledBack_f fr w fl' S bs F hok hF hfl' hpa hS h2s hbs hrec
  obtain ⟨-, -, c3, c4, -, -, -, -, c9, -, c11, -⟩ := hok
  have hpS : ∀ s ∈ S, s ∈ pendSlots w.fl := by
    intro s hs
    obtain ⟨h1, h2⟩ := (hS s).1 hs
    rcases (mem_slotsOf _ _ _).1 h1 with h | h
    · exact absurd ((mem_slotsOf _ _ _).2 (.inl h)) h2
    · exact h
  have hj := wjoin (GF := GF) p w.ms w.W S w.wb bs w.m.size
    (fun s hs hw => ((c4 s).1 hw).2.2.2 (hpS s hs))
    (fun s hs => by
      have := c11 s (.inr (hpS s hs))
      refine ⟨by omega, fun b l hbl => ?_, hbs s hs⟩
      have := c9 b l hbl; omega)
  iintro H
  ihave ⟨Hc, Hb⟩ := hj $$ H
  iexists { w with fl := fl', W := w.W ++ S, wb := mergeWb S bs w.wb }
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hok'⟩
  isplitl [Hc]
  · iexact Hc
  · iexact Hb

end rb

end bbolt
end EtcdGrove
end Perennial
