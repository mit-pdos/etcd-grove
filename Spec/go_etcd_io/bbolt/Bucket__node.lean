/-
`b.node(pgid, parent)` (`bucket.go`): the cached node of a page, or a new one read from it, registered with its parent.
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

/-- (internal) the node of page `id` (cached, its parent `par`). -/
def Bucket.node.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (C : TxCore) (b : Loc) (p : BPath) (gs : List Nat) (id : w64) (par : Loc),
  {{ wtxCore (GF := GF) tx γ C ∗ bktH tx γ b p gs }}
    (App (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"node")) (Val #id)) (Val #par))
  {{ (n : Loc), RET #n; ∃ C' : TxCore, wtxCore tx γ C' ∗ ⌜∃ N, C'.nodes n = some N ∧ N.parent = par⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
