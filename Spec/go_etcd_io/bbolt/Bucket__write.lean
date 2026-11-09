/-
`b.write()` (`bucket.go`): an inline bucket's value: its header and its root node as a page.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)
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

/-- (internal) a fresh value: the bucket header then the root node's page. -/
def Bucket.write.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (C : TxCore) (b : Loc) (p : BPath) (gs : List Nat),
  {{ wtxCore (GF := GF) tx γ C ∗ bktH tx γ b p gs }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"write")) (Val #()))
  {{ (s : GoSlice), RET #s; wtxCore tx γ C ∗ ∃ bs : List w8, s ↦* bs }}

end spec

end Bbolt
end EtcdGrove
end Perennial
