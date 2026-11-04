/-
The read path's (U6, `notes/bbolt-proof-plan.md`) accessors for iterations (`ForEachBucket`): the
reader's `db` field (never nil for a live reader).
-/
module

public import Proof.go_etcd_io.bbolt.Read.Open

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section iter
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem BC.core_db_nonnull (K : BC) : K.core (GF := GF) ⊢ ⌜K.db ≠ null⌝ := by
  unfold BC.core isBoltCoreP
  iintro ⟨-, -, %H, -⟩
  ipureintro; exact H.2

/-- **The reader's `db` field** (the database, not nil), out of `rdTxK` and back. -/
theorem rdTxK_db_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) :
    rdTxK (GF := GF) K tx src q T v ⊢ ∃ dd, tx.[Tx, go!"db"] ↦{dd} K.db ∗ ⌜K.db ≠ null⌝ ∗
      (tx.[Tx, go!"db"] ↦{dd} K.db -∗ rdTxK K tx src q T v) := by
  unfold rdTxK rtxFrac
  iintro ⟨%r, %c, %mv, %k, %Hc, #Hreg, #Hpk, #Hcore, Hv, Hex,
    ⟨%t, Hw, Hm, Hmeta, Hroot, Hfill, Hpages, Hch, Hwf, Hdb, Hmv, Hcells, Hmap, #Hvo, %Hf⟩, Hpool⟩
  ihave %Hnn := BC.core_db_nonnull K $$ Hcore
  have hdb := Hc.2.1
  rw [← hdb] at Hnn ⊢
  iexists _
  iframe Hdb
  isplitr
  · ipureintro; exact Hnn
  iintro Hdb
  iexists r, c, mv, k
  iframe; iframe #
  isplitr
  · ipureintro; exact ⟨Hc.1, rfl, Hc.2.2⟩
  ipureintro; exact Hf

end iter

end bbolt
end EtcdGrove
end Perennial
