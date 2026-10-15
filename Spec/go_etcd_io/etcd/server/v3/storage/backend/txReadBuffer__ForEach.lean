/-
`txReadBuffer.ForEach` (`tx_buffer.go`). `txr.ForEach(bucket, visitor)`: the bucket's buffer's `ForEach` (`nil` if the bucket has
none); the read buffer unchanged (any fraction).
Lean-first (no Rocq counterpart); see `InvBuffer.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBuffer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `txr.ForEach(bucket, visitor)`: the bucket's buffer's `ForEach` (`nil` if the bucket has
none); the read buffer unchanged (any fraction). -/
abbrev backend.txReadBuffer.ForEach.spec : Prop :=
  ∀ (txr : Loc) (dq : DFrac) (m : GoMap) (P : BksPhys) (R : RBuf) (b : GoInterface)
    (bi : BucketInfo) (f : GoFunc) (Pv : Nat → IProp GF) (Q : GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ rbAt txr dq m P R ∗ isBucket b bi ∗ visitorSpec f (bkOf R.bks bi.id) Pv Q ∗
      Pv 0 }}
    (App (App (Val (txr @!! go.GoType.PointerType txReadBuffer.ty @!! go!"ForEach")) (Val #b)) (Val #f))
  {{ (err : GoInterface), RET #err; rbAt txr dq m P R ∗
      ((⌜err = GoInterface.nil⌝ ∗ Pv (bkOf R.bks bi.id).length) ∨
       (⌜err ≠ GoInterface.nil⌝ ∗ Q err)) }}

end spec

end EtcdGrove
end Perennial
