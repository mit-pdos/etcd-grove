/-
`Cursor.keyValue` of a reader on an empty page (bbolt, internal to U6h of
`notes/bbolt-proof-plan.md`): the top element's page has no element, at any index (`Last` on an
empty root leaf leaves it at `-1`, which `Cursor.keyValue_r`'s premise `0 ≤ index` excludes):
nil, nil, `0`. Proof: `Proof/go_etcd_io/bbolt/Cursor__keyValue_r0.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Read.Src

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

/-- `c.keyValue()` of a reader's cursor in bucket `b` (value `bv`) whose top element `e` refers
to the empty page `pg` at position `pid`. -/
abbrev Cursor.keyValue_r0.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (b : Loc) (dq : DFrac)
    (bv : List w8) (ibp pp c : Loc) (stk : GoSlice)
    (els : List elemRef) (e : elemRef) (pid : Nat) (pg : List w8),
  rPageAt v bv pp pid = some (e.page', pg) → e.node' = null → 16 ≤ pg.length →
  pageCount pg = 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ rdTxK (GF := GF) K tx src q T v ∗
      rBktP v tx b dq bv ibp pp ∗ c ↦ Cursor.mk b stk ∗ stk ↦* (els ++ [e]) }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"keyValue")) (Val #()))
  {{ RET (PairV (PairV #slice.nil #slice.nil) #(W32 0)); rdTxK K tx src q T v ∗
      rBktP v tx b dq bv ibp pp ∗ c ↦ Cursor.mk b stk ∗ stk ↦* (els ++ [e]) }}

end spec

end bbolt
end EtcdGrove
end Perennial
