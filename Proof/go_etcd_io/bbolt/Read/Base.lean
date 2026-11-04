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

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

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

end base

end bbolt
end EtcdGrove
end Perennial
