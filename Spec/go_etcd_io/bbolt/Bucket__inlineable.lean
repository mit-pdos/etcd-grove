/-
`b.inlineable()` (`bucket.go`): a leaf root of no bucket and at most a quarter page.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Changes** (integration I7): the result is stated (`inlineOk` of the root node, `TxCore.roots`):
`Bucket.write`'s premise, which `Bucket.spill` gets from it.
-/
module

public import Spec.go_etcd_io.bbolt.Internal

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

/-- (internal) whether the bucket fits inline: its root node is cached and `inlineOk`. -/
def Bucket.inlineable.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (C : TxCore) (b : Loc) (p : BPath) (gs : List Nat),
  {{ wtxCore (GF := GF) tx γ C ∗ bktH tx γ b p gs }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"inlineable")) (Val #()))
  {{ (r : Bool), RET #r; wtxCore tx γ C ∗
      ⌜r = true ↔ ∃ n N, C.roots b = some n ∧ C.nodes n = some N ∧ inlineOk N⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
