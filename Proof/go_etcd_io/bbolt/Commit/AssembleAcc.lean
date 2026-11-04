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

end acc

end bbolt
end EtcdGrove
end Perennial
