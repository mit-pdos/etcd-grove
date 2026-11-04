/-
`Commit`'s accessors (U10g of `notes/bbolt-proof-plan.md`): the parts of the writer's working
state `wtxW` that `Commit` reads and writes itself, out and back: its statistics token, its meta
copy (`tx.meta`, written back with a new meta), its `tx.db` share.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- The records with the meta copy `mv`. -/
def WX.withMv (X : WX) (mv : Meta) : WX := { X with t := { X.t with mv := mv } }

@[simp] theorem WX.withMv_tt (X : WX) (mv : Meta) : (X.withMv mv).t.t = X.t.t := rfl
@[simp] theorem WX.withMv_mv (X : WX) (mv : Meta) : (X.withMv mv).t.mv = mv := rfl

end pure

section acc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The statistics token** (with the core and registration) out of `wtxW`, and back. -/
theorem cm_stats_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ K.core ∗ reg tx K.B r ∗ statsTok r m 1 ∗
      (statsTok r m 1 -∗ wtxW K tx r m X) := by
  unfold wtxW wtxCore
  iintro ⟨⟨#Hpkg, #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdb, Hview, Hst⟩, Hcells, Hmap⟩
  iframe Hst; iframe Hcore; iframe Hreg
  iintro Hst
  iframe; iframe #
  ipureintro; exact Hr

/-- **The meta copy** out of `wtxW` (`tx.meta` and its meta), and back with any meta. -/
theorem cm_meta_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ tx.[Tx, go!"meta"] ↦ X.t.t.meta' ∗ X.t.t.meta' ↦ X.t.mv ∗
      (∀ mv : Meta, tx.[Tx, go!"meta"] ↦ X.t.t.meta' -∗ X.t.t.meta' ↦ mv -∗
        wtxW K tx r m (X.withMv mv)) := by
  unfold wtxW wtxCore wtxHeap txFields
  iintro ⟨⟨#Hpkg, #Hcore, %Hr, #Hreg, ⟨%Hhok, ⟨Hwr, Hmg, Hme, Hpgs, Hch, Hwfl, Hmv, Hpm, Hbufs⟩,
    Hrf, Hobj, Hbobj⟩, Hfills, Hbk, Hnl, Hdb, Hview, Hst⟩, Hcells, Hmap⟩
  iframe Hme Hmv
  iintro %mv Hme Hmv
  unfold WX.withMv
  iframe
  iframe #
  ipureintro; exact ⟨Hr, Hhok⟩

/-- **`tx.db`'s share** (with the core) out of `wtxW`, and back. -/
theorem cm_db_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ ⌜r.db = K.db⌝ ∗ tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db ∗
      (tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db -∗ wtxW K tx r m X) := by
  unfold wtxW wtxCore
  iintro ⟨⟨#Hpkg, #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdb, Hview, Hst⟩, Hcells, Hmap⟩
  rw [Hr.1]
  iframe Hdb
  isplitr
  · ipureintro; rfl
  iintro Hdb
  iframe; iframe #
  ipureintro; exact ⟨rfl, Hr.2⟩

/-- **The heap's facts** (`heapOK`: the root bucket is `tx.root`, ...), kept. -/
theorem cm_heapOK (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ ⌜heapOK (GF := GF) tx X⌝ ∗ wtxW K tx r m X := by
  unfold wtxW wtxCore
  iintro ⟨⟨Hpkg, Hcore, %Hr, Hreg, Hh, Hrest⟩, Hcells, Hmap⟩
  ihave %Hok := wtxHeap_heapOK tx (DFrac.own 1) X $$ Hh
  isplitr
  · ipureintro; exact Hok
  · iframe
    ipureintro; exact Hr

omit hos in
/-- **The meta's root-bucket header** out of a meta's points-to, and back with any header. -/
theorem cm_meta_root (mp : Loc) (mv : Meta) (hmp : mp ≠ null) :
    (mp ↦ mv : IProp GF) ⊢ (structFieldRef Meta go!"root" mp) ↦ mv.root' ∗
      (∀ ib : InBucket, (structFieldRef Meta go!"root" mp) ↦ ib -∗
        mp ↦ ({ mv with root' := ib } : Meta)) := by
  iintro Hmv
  iStructNamed Hmv
  iframe root
  iintro %ib Hroot
  iapply typedPointsto_combine _ _ _ hmp
  simp only [TypedPointsto.typedPointstoDef]
  iframe

omit [GooseSemantics] hos in
/-- The mapping's length is at most `maxMapSize`. -/
theorem cm_mapFields_len (db : Loc) (dq : DFrac) (ms : MapSt) :
    mapFields (GF := GF) db dq ms ⊢ ⌜mapLen ms ≤ 0xFFFFFFFFFFFF⌝ := by
  rcases ms with _ | ⟨b, l⟩
  · iintro -; ipureintro; simp [mapLen]
  · simp only [mapFields, mapLen]
    iintro ⟨-, -, -, -, %H⟩
    ipureintro; exact H.1

/-- **The writer side's bounds**: its freelist well-formed (`flPgOwn`), its high-water mark's pages
inside a mapping of at most `maxMapSize` (`wdbOK`, `mapFields`). -/
theorem cm_wdbW_bounds (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbW (GF := GF) K tx v w ⊢ ⌜w.fl.WF ∧ w.C.hwm < 2 ^ 48⌝ := by
  unfold wdbW wdbLive wdbCoreG flPgOwn
  iintro ⟨⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, Hmf, -⟩, ⟨%a, %s, %al, %ca, %pe, %c, %pp, -, -, -, -, -,
    -, -, -, -, -, %Hwf⟩, -⟩, %Hok⟩
  ihave %Hl := cm_mapFields_len K.db _ _ $$ Hmf
  ipureintro
  refine ⟨Hwf.2, ?_⟩
  have h9 := Hok.1.2.2.2.2.2.2.2.2.1 v.base (mapLen w.ms) Hok.2.1
  have : mapLen w.ms ≤ 0xFFFFFFFFFFFF := Hl
  omega

end acc

end bbolt
end EtcdGrove
end Perennial
