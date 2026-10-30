module
public import Proof.go_etcd_io.bbolt.Inlineable
public import Proof.go_etcd_io.bbolt.WriteTxPred

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

open Classical in
/-- `b.inlineable()` on a bucket of a write transaction (record `B`, its root node, if any,
among its nodes): whether it is inlineable (`inlineableB`, for the view's page size); the
bucket, the transaction's `db` field and the view given back. -/
abbrev Bucket.inlineable.spec : Prop :=
  ∀ (W : WView) (bl : Loc) (B : BRec) (dt : DFrac),
  W.ps < 2 ^ 63 → (B.bv.rootNode' = null ∨ (B.ns !! B.bv.rootNode').isSome) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bktOwn W bl B ∗
      structFieldRef Tx go!"db" B.bv.tx' ↦{dt} W.dbl ∗ wView W }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"inlineable")) (Val #()))
  {{ RET #(decide (inlineableB B W.ps)); bktOwn W bl B ∗
      structFieldRef Tx go!"db" B.bv.tx' ↦{dt} W.dbl ∗ wView W }}

end spec

end bbolt
end EtcdGrove
end Perennial
