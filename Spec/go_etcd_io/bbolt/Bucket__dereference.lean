/-
`Bucket.dereference` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U9b; used by U4 (`DB.mmap`'s `db.rwtx.root.dereference()`). Proof:
`Proof/go_etcd_io/bbolt/Bucket__dereference.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`dereference`'s coverage contract** (design §4.2, A3): `tx.root.dereference()` copies the
keys and values of every live node (the live objects are those the code reaches, `liveReach`;
none stale, `liveFresh`; what its asserts and reads need, `derefPre`, batch 12) to the heap:
afterwards no live object holds a view slice (`derefOK`), and nothing else changed
(`derefRel`). The `NodeDeref` statistic grows. -/
abbrev Bucket.dereference.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX),
  derefPre X → liveFresh X → liveReach X →
  {{ wtxW (GF := GF) K tx r m X }}
    (App (Val (tx.[Tx, go!"root"] @!! go.GoType.PointerType Bucket.ty @!! go!"dereference"))
      (Val #()))
  {{ RET #(); ∃ X' : WX, wtxW K tx r m X' ∗ ⌜derefRel X X'⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
