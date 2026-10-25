/-
`schema.UnsafeDeleteLease(tx, lpb)` (`server/storage/schema/lease.go`, translated names-only).
The trust boundary. Lean-first (no Rocq counterpart); the lessor's `Revoke`
(`notes/leases-plan.md`, L2d).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- `UnsafeDeleteLease(tx, lpb)` reads `lpb.ID` and deletes the lease's record from the `Lease`
bucket (`tx.UnsafeDelete(Lease, leaseIDToBytes(lpb.ID))`, its one call of `tx`; the key is the id
as 8 big-endian bytes, in a fresh slice the function does not touch again): given that delete's
triple from `R` to `Q` for the bucket `bk` the variable `schema.Lease` holds, for any 8-byte key
(as `MustUnsafePutLease`'s put), it goes from `R` to `Q`, leaving `*lpb` as it was. -/
abbrev schema.UnsafeDeleteLease.spec : Prop :=
  ∀ (tx : GoInterfaceOk) (lpb : Loc) (dq : DFrac) (v : go_etcd_io.etcd.server.v3.lease.leasepb.Lease)
    (bk : GoInterface) (R Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      globalAddr schema.Lease ↦□ bk ∗ lpb ↦{dq} v ∗ R ∗
      □ (∀ (key : GoSlice) (kb : GoString),
        {{ ⌜kb.length = 8⌝ ∗ key ↦*□ kb ∗ R }}
          (App (App (Val #(methods tx.ty go!"UnsafeDelete" tx.v)) (Val #bk)) (Val #key))
        {{ RET #(); Q }}) }}
    (App (App (Val (@! schema.UnsafeDeleteLease)) (Val #(GoInterface.ok tx))) (Val #lpb))
  {{ RET #(); lpb ↦{dq} v ∗ Q }}

end spec

end EtcdGrove
end Perennial
