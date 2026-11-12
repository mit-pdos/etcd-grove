/-
`b.pageNode(id)` (`bucket.go`): the cached node of page `id`, else the page (an inline bucket's own page for id 0).
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)
**Changes (2026-11-12, `notes/specs-only/ledger.md`, bucket handles).** The handle premise `bktUse`
(the bucket's ownership share in a write transaction) in place of `bktH … gs` and the generation
check, given back (the per-path generation counter it replaces was unobservable state, redundant
with ownership).
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

/-- (internal) a page or a cached node of the bucket. -/
def Bucket.pageNode.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (p : BPath) (qb : Qp) (id : w64),
  {{ boltTx (GF := GF) tx γ q T ∗ bktUse tx γ T.rw b p qb }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"pageNode")) (Val #id))
  {{ (pg nd : Loc), RET (PairV #pg #nd); bktUse tx γ T.rw b p qb ∗ boltTx tx γ q T ∗ ⌜pg = Loc.null ∨ nd = Loc.null⌝ ∗ (⌜pg = Loc.null⌝ ∨ ∃ bs, txPage tx γ id pg bs) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
