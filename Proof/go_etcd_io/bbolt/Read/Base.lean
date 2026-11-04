/-
The read path's (U6, `notes/bbolt-proof-plan.md`) small facts about the shared contexts:
persistence instances the shared modules leave to unfolding.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section base
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance BC.core_persistent (K : BC) : Persistent (K.core (GF := GF)) := by
  unfold BC.core; infer_instance

instance BC.full_persistent (K : BC) : Persistent (K.full (GF := GF)) := by
  unfold BC.full isBoltP; infer_instance

instance reg_persistent (tx : Loc) (B : BNs) (r : TxReg) :
    Persistent (reg (GF := GF) tx B r) := by
  unfold reg; infer_instance

instance viewOf_persistent (r : TxReg) (v : View) : Persistent (viewOf (GF := GF) r v) := by
  unfold viewOf; infer_instance

/-- PENDING a shared fix: the mapping's base is not null (`DB.page` indexes `db.data`;
`mmap` returns a mapped address). `mapFields`' mapped case does not say it yet: the read path's
callers of `Tx.page` (`Tx.page_r`, `Bucket.pageNode_w`) rest on this one `sorry`. -/
theorem mapFields_base_nonnull (db : Loc) (dq : DFrac) (b : Loc) (l : Nat) :
    mapFields (GF := GF) db dq (some (b, l)) ⊢ ⌜b ≠ null⌝ := by
  sorry

theorem isBoltCoreP_pageSize (B : BNs) (N : Namespace) (db : Loc) (p : GoString) (sp : Loc)
    (t0 : Nat) :
    isBoltCoreP (GF := GF) B N db p sp t0 ⊢ db.[DB, go!"pageSize"] ↦□ W64 4096 := by
  unfold isBoltCoreP dbFixed
  iintro ⟨-, -, -, -, -, ⟨H, -⟩, -⟩
  iexact H

theorem BC.core_pageSize (K : BC) :
    K.core (GF := GF) ⊢ K.db.[DB, go!"pageSize"] ↦□ W64 4096 :=
  isBoltCoreP_pageSize K.B K.N K.db K.p K.sp K.t0

theorem isBoltCoreP_pkgInit' (B : BNs) (N : Namespace) (db : Loc) (p : GoString) (sp : Loc)
    (t0 : Nat) :
    isBoltCoreP (GF := GF) B N db p sp t0 ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt := by
  unfold isBoltCoreP
  iintro ⟨-, -, -, H, -⟩
  iexact H

end base

/-- Two halves of `q` (as `QpMul q ½`). -/
theorem qpMul_half_add (q : Qp) : QpMul q (1 : Qp).half + QpMul q (1 : Qp).half = q := by
  apply Subtype.ext
  show q.val * ((1 : Rat) / 2) + q.val * ((1 : Rat) / 2) = q.val
  grind

/-- `txDbQ q` is `QpMul q ½` and a quarter. -/
theorem txDbQ_eq (q : Qp) : txDbQ q = QpMul q (1 : Qp).half + QpMul q (1 : Qp).half.half := rfl

end bbolt
end EtcdGrove
end Perennial
