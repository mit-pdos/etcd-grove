/-
`mmaplock`'s share of the database's file handle (`pmFile`, session S4) against the writer side's
half (`wdbCoreG`): moving it to another mapping state, building it, and joining the halves (for
`close`, which holds all three locks).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Locks

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section pmfile
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]


instance pmFile_timeless (B : BNs) (db : Loc) (dq : DFrac) (ms : MapSt) :
    Timeless (pmFile (GF := GF) B db dq ms) := by
  have : ∀ (f : Loc) (ti : Nat × Ino), Timeless (if f = null then iprop(emp : IProp GF)
      else iprop(∃ fn : w64 × GoString, fileOwn (GF := GF) f fn.1 fn.2 dq ∗
        osFd fn.1 dq (dbFd ti.2))) := by
    intro f ti; split <;> (try unfold fileOwn) <;> infer_instance
  unfold pmFile; infer_instance

/-- An open `*os.File` is not nil. -/
theorem fileOwn_nonnull (f : Loc) (fd : w64) (nm : GoString) (dq : DFrac) :
    fileOwn (GF := GF) f fd nm dq ⊢ ⌜f ≠ null⌝ ∗ fileOwn f fd nm dq := by
  unfold fileOwn
  iintro ⟨%inner, #Hf, Hd, #Hn, #Hnb⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hf with ⟨-, %h⟩
  isplitr
  · ipureintro; exact h
  iexists inner; iframe Hd; iframe #


/-- `mmaplock`'s share of the file handle at another mapping state, with the writer side's
half of `db.file` (which names the open file `f`). -/
theorem pmFile_remap (B : BNs) (db f : Loc) (fd : w64) (nm : GoString) (dq dq1 dq2 : DFrac)
    (ms ms' : MapSt) :
    db.[DB, go!"file"] ↦{dq1} f ∗ fileOwn (GF := GF) f fd nm dq2 ∗ pmFile B db dq ms ⊢
      db.[DB, go!"file"] ↦{dq1} f ∗ fileOwn f fd nm dq2 ∗ pmFile B db dq ms' := by
  iintro ⟨Hf, Ho, Hp⟩
  icases fileOwn_nonnull f fd nm dq2 $$ Ho with ⟨%hf, Ho⟩
  unfold pmFile
  icases Hp with ⟨%f', Hf', -, Hrest⟩
  icombine Hf Hf' gives %h
  have e : f = f' := by first | exact h.2 | exact h
  subst e
  iframe Hf Ho
  iexists f
  iframe Hf' Hrest
  ipureintro; exact fun _ => hf


/-- **`mmaplock`'s share of an open file** from its pieces. -/
theorem pmFile_intro (B : BNs) (db f : Loc) (fd : w64) (nm : GoString) (dq : DFrac)
    (t : Nat) (i : Ino) (ms : MapSt) :
    db.[DB, go!"file"] ↦{dq} f ∗ fileOwn (GF := GF) f fd nm dq ∗ osFd fd dq (dbFd i) ∗
      ghostMapElem B.t0 () DFrac.discard (t, i) ⊢ pmFile B db dq ms := by
  iintro ⟨Hf, Ho, Hd, #Ht⟩
  icases fileOwn_nonnull f fd nm dq $$ Ho with ⟨%hf, Ho⟩
  unfold pmFile
  iexists f
  iframe Hf
  isplitr
  · ipureintro; exact fun _ => hf
  iexists (t, i)
  iframe Ht
  simp only [hf, ↓reduceIte]
  iexists (fd, nm)
  iframe


/-- **A closed database's share**: `db.file` nil. -/
theorem pmFile_null (B : BNs) (db : Loc) (dq : DFrac) (ti : Nat × Ino) (ms : MapSt)
    (hms : ms = none) :
    db.[DB, go!"file"] ↦{dq} null ∗ ghostMapElem (GF := GF) B.t0 () DFrac.discard ti ⊢
      pmFile B db dq ms := by
  iintro ⟨Hf, #Ht⟩
  unfold pmFile
  iexists null
  iframe Hf
  isplitr
  · ipureintro; intro h; exact absurd hms h
  iexists ti
  iframe Ht
  simp only [↓reduceIte]
  iempintro


/-- **The file handle whole** (`close`): the writer side's half and `mmaplock`'s, on the
database's inode `p.ino` (the receipts' base names it, `t0At`). -/
theorem pmFile_join (B : BNs) (db f : Loc) (fd : w64) (nm : GoString) (i : Ino) (t0 : Nat)
    (ms : MapSt) :
    db.[DB, go!"file"] ↦{DFrac.own (1 : Qp).half} f ∗
      fileOwn (GF := GF) f fd nm (DFrac.own (1 : Qp).half) ∗
      osFd fd (DFrac.own (1 : Qp).half) (dbFd i) ∗ ghostMapElem B.t0 () DFrac.discard (t0, i) ∗
      pmFile B db (DFrac.own (1 : Qp).half) ms ⊢
    db.[DB, go!"file"] ↦ f ∗ fileOwn f fd nm (DFrac.own 1) ∗ osFd fd (DFrac.own 1) (dbFd i) := by
  iintro ⟨Hf, Ho, Hd, #Ht, Hp⟩
  icases fileOwn_nonnull f fd nm _ $$ Ho with ⟨%hf, Ho⟩
  unfold pmFile
  icases Hp with ⟨%f', Hf', -, %ti, #Ht', Hrest⟩
  icombine Hf Hf' gives %h
  have e : f = f' := by first | exact h.2 | exact h
  subst e
  simp only [hf, ↓reduceIte]
  icases Hrest with ⟨%fn, Ho', Hd'⟩
  ihave %ho := fileOwn_agree f fd fn.1 nm fn.2 _ _ $$ [Ho Ho']
  · iframe
  obtain ⟨e1, e2⟩ := ho
  obtain ⟨fd', nm'⟩ := fn
  simp only at e1 e2
  subst e1 e2
  icombine Ht Ht' gives %hti
  have eti : (t0, i) = ti := by first | exact hti.2 | exact hti
  subst eti
  isplitl [Hf Hf']
  · iapply ((typedPointsto_dfractional (GF := GF) _ f).dfractional
      (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)).2.trans (by rw [DFrac.op_own, Qp.half_add_half])
    iframe
  have h1 := ((fileOwn_fractional (GF := GF) f fd nm).fractional (1 : Qp).half (1 : Qp).half).2
  have h2 := ((osFd_fractional (GF := GF) fd (dbFd i)).fractional (1 : Qp).half (1 : Qp).half).2
  rw [Qp.half_add_half] at h1 h2
  isplitl [Ho Ho']
  · iapply h1; iframe
  · iapply h2; iframe

end pmfile

end bbolt
end EtcdGrove
end Perennial
