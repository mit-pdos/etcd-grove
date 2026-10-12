/-
A writer begins (`beginRWTx`): the database's state with the writer (`DBState.addWriter`: its
view of the current tree, carved as a reader's, and `rwtx`), its facts kept
(`dbOK_addWriter`), and what the new write transaction holds (`wtxInit`: the transaction's
objects as `Tx.init` leaves them, and the view), from which the transaction's predicate is
built (the object graph's side).
-/
module

public import Proof.go_etcd_io.bbolt.DBRelease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- The database with the writer `txl` begun, its view `w` (taking its fraction of the slots
it sees and of the fields, as a reader does). -/
def DBState.addWriter (σ : DBState) (txl : Loc) (w : Reader) : DBState :=
  { σ with
    rwtx := txl
    wr := some w
    rem := fun s => if w.sees s then qsub (σ.rem s) w.q else σ.rem s
    frem := qsub σ.frem w.q }
proj_simps DBState.addWriter

theorem dbOK_addWriter (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (hw : σ.wr = none) (txl : Loc) (htxl : txl ≠ null) :
    dbOK (σ.addWriter txl (newReader σ v0 v1 (beginQ σ))) v0 v1 := by
  obtain ⟨hps, hps2, hn, hsz, hdc, hm0, hm1, hv, hcur, hrd, hmv, hsl, hfl, hro, hrs, hwr⟩ := h
  have hcur' := hcur
  obtain ⟨cwf, cdisj, cin, calloc, cfree⟩ := hcur'
  have hps16 : 16 ≤ σ.ps := by omega
  have hsees : ∀ s, (newReader σ v0 v1 (beginQ σ)).sees s = true →
      s < σ.nslots ∧ 2 ≤ s ∧ W64 s ∉ σ.fl.free ∧
      ∀ t pd a, σ.fl.pending !! t = some pd → (W64 s, a) ∉ pd.pairs := by
    intro s hs
    simp only [Reader.sees, decide_eq_true_eq] at hs
    have hc := cfree s hs
    obtain ⟨id, pg, hid, h1, h2⟩ := hs
    have hspan := span_of_pageAt σ.bs σ.ps id pg hps16 (newReader_pages σ v0 v1 _ id pg hid)
    have hin := cin id pg hid
    exact ⟨by omega, hc⟩
  refine ⟨hps, hps2, hn, hsz, hdc, hm0, hm1, hv, hcur, hrd, hmv, ?_, ?_, hro, hrs, ?_⟩
  · -- the slots
    intro s hs
    have H := hsl s hs
    rw [hw] at H
    show fracSum (if (newReader σ v0 v1 (beginQ σ)).sees s then
        qsub (σ.rem s) (newReader σ v0 v1 (beginQ σ)).q else σ.rem s)
      (wQ (some (newReader σ v0 v1 (beginQ σ))) (fun r => r.sees s)
        (readersQ σ.readers (fun r => r.sees s))) halfQ
    unfold wQ at H ⊢
    cases hrs' : (newReader σ v0 v1 (beginQ σ)).sees s
    · simp only [hrs', Bool.false_eq_true, ↓reduceIte]; exact H
    · simp only [hrs', ↓reduceIte]
      exact fracSum_take _ _ _ _ _ H (qsub_add _ _ (beginQ_lt_rem σ s hs))
  · -- the fields
    have H := hfl
    unfold fieldsOK at H
    rw [hw] at H
    show fracSum (qsub σ.frem (newReader σ v0 v1 (beginQ σ)).q)
      (wQ (some (newReader σ v0 v1 (beginQ σ))) (fun _ => true)
        (readersQ σ.readers (fun _ => true))) 1
    unfold wQ at H ⊢
    simp only [↓reduceIte]
    exact fracSum_take _ _ _ _ _ H (qsub_add _ _ (beginQ_lt_frem σ))
  · -- the writer
    unfold writerOK
    simp only [DBState.addWriter.proj_wr, DBState.addWriter.proj_rwtx]
    refine ⟨by simp [htxl], fun w hw' => ?_⟩
    simp only [Option.some.injEq] at hw'
    subst hw'
    refine ⟨⟨cwf, cdisj, fun id pg hid =>
      ⟨(newReader_pages σ v0 v1 _ id pg hid).symm, cin id pg hid⟩⟩, ?_, fun s hs => ?_⟩
    · exact fun id pg hid a ha => calloc id pg hid a ha
    · have hs' : (newReader σ v0 v1 (beginQ σ)).sees s = true := by
        unfold Reader.sees; simp only [decide_eq_true_eq]; exact hs
      obtain ⟨_, h2, h3, h4⟩ := hsees s hs'
      exact ⟨h2, h3, fun t pd a ht hin => absurd hin (h4 t pd a ht)⟩

/-- What a new write transaction at `txl` holds (as `Tx.init` leaves it, writable): the
transaction (`txInitOf`; managed off), its meta copy (the current one, its txid incremented),
the root bucket's header copy, the empty page cache and bucket caches, and its view `w` of the
current tree (the pages it sees and its part of `data`, `pageSize`, at its fraction). The
object graph's predicate is built from it. -/
def wtxInit (dbl : Loc) (txl : Loc) (w : Reader) (data : Loc) (ps : Nat)
    (v0 v1 : internal.common.Meta) : IProp GF :=
  iprop(∃ (ml ibl : Loc) (pm bm nm : GoMap),
    txl ↦ txInitOf { (zero_val Tx) with writable' := true } txl dbl ml ibl pm bm nm ∗
    ml ↦ txMetaOf true v0 v1 ∗ ibl ↦ (if metaPick v0 v1 then v1 else v0).root' ∗
    pm ↦$ (∅ : GMap w64 Loc) ∗ bm ↦$ (∅ : GMap GoString Loc) ∗ nm ↦$ (∅ : GMap w64 Loc) ∗
    structFieldRef DB go!"data" dbl ↦{DFrac.own w.q} data ∗
    structFieldRef DB go!"pageSize" dbl ↦{DFrac.own w.q} W64 ps ∗
    pagesView data ps w.q w.pages)

end defs

end bbolt
end EtcdGrove
end Perennial
