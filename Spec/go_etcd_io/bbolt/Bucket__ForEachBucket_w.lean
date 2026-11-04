/-
`Bucket.ForEachBucket_w` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U6; used by U7 (`DeleteBucket`). Proof:
`Proof/go_etcd_io/bbolt/Bucket__ForEachBucket_w.lean` (a `sorry` until U6).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.ForEachBucket(fn)` of a writer's searchable bucket with no nested bucket (every bucket but
the root under `treeOK`, `rootShape`): the callback never runs; nil, nothing changed. -/
abbrev Bucket.ForEachBucket_w.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (fn : GoFunc),
  bktLocalOK X bl → pmFresh X → (∀ w ∈ X.allEnts bl, ¬ isBktFlag w.flags) →
  {{ wtxW (GF := GF) K tx r m X }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"ForEachBucket")) (Val #fn))
  {{ (err : GoInterface), RET #err; ⌜err = interface.nil⌝ ∗ wtxW K tx r m X }}

end spec

end bbolt
end EtcdGrove
end Perennial
