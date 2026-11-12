/-
`b.dereference()` (`bucket.go`): every cached node of the bucket and its children copied off the mapping. Users: `Tx.allocate`'s remap.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)
**Changes (2026-11-12, `notes/specs-only/ledger.md`, bucket handles).** `bktH` (which object `b` is)
without the generations (the per-path generation counter it replaces was unobservable state,
redundant with ownership).
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- (internal) the same models off the mapping. -/
def Bucket.dereference.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (C : TxCore) (b : Loc) (p : BPath),
  {{ wtxCore (GF := GF) tx γ C ∗ bktH tx γ b p }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"dereference")) (Val #()))
  {{ RET #(); wtxCore tx γ C }}

end spec

end Bbolt
end EtcdGrove
end Perennial
