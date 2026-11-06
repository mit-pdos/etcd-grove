/-
`Tx.page_r` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U6 (from U4's `Tx.page`); used by U10 (`tx_check`'s walks in `freepages`), U11. Proof:
`Proof/go_etcd_io/bbolt/Tx__page_r.lean` (a `sorry` until U6 (from U4's `Tx.page`)).
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

/-- `tx.page(id)` of a reader (the `rdTxK` corollary of `Tx.page`, design §4.2 row 2): page `id`
of its view, at the view's location (`pageLoc`). -/
abbrev Tx.page_r.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (id : w64)
    (pg : List w8),
  v.pages !! id.toNat = some pg →
  {{ rdTxK (GF := GF) K tx src q T v }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"page")) (Val #id))
  {{ RET #(pageLoc v id.toNat); rdTxK K tx src q T v }}

end spec

end bbolt
end EtcdGrove
end Perennial
