/-
`txReadBuffer.unsafeCopy` (`tx_buffer.go`). `txr.unsafeCopy()`: a new read buffer (by value, version 0) with a new map of copies of
the buckets' buffers (`CopyUsed`); the read buffer unchanged (any fraction).
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

/-- `txr.unsafeCopy()`: a new read buffer (by value, version 0) with a new map of copies of
the buckets' buffers (`CopyUsed`); the read buffer unchanged (any fraction). -/
abbrev backend.txReadBuffer.unsafeCopy.spec : Prop :=
  ∀ (txr : Loc) (dq : DFrac) (m : GoMap) (P : BksPhys) (R : RBuf),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ rbAt txr dq m P R }}
    (App (Val (txr @!! go.GoType.PointerType txReadBuffer.ty @!! go!"unsafeCopy")) (Val #()))
  {{ (c : txReadBuffer), RET #c; rbAt txr dq m P R ∗ ⌜c.bufVersion' = W64 0⌝ ∗
      ∃ P' : BksPhys, bksAt c.txBuffer'.buckets' (DFrac.own 1) P' R.bks }}

end spec

end EtcdGrove
end Perennial
