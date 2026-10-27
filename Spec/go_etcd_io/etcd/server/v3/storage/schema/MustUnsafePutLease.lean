/-
`schema.MustUnsafePutLease(tx, lpb)` (`server/storage/schema/lease.go`, translated names-only).
The trust boundary. Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/lease/LessorBackend.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.LeaseRecord

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

/-- `MustUnsafePutLease(tx, lpb)` encodes `*lpb` (`proto.Marshal`, which cannot fail on a
`leasepb.Lease`, three `int64` fields: the panic branch is not taken; it may write the message's
size cache, so it takes `*lpb` whole and leaves some value) and puts it into the `Lease` bucket
under the lease's id as 8 big-endian bytes (`tx.UnsafePut(Lease, leaseIDToBytes(lpb.ID), val)`,
its one call of `tx`): given that put's triple from `R` to `Q` for the bucket `bk` the variable
`schema.Lease` holds, the key the id's bytes (`binary.BigEndian.PutUint64`, as
`UnsafeDeleteLease`'s) and the value the record's encoding (`lease.leaseEnc` of its id, TTL and
remaining TTL; a message with no unknown fields, as the lessor's `persistTo` builds), both fresh
slices the function does not touch again, it goes from `R` to `Q`. (Until 2026-10-27, leases T3
L3c: any 8-byte key and any value, too weak to say what a grant writes; unit N4, 2026-10-17: any
bytes until then, more than the backend gives: an empty key is fatal.) -/
abbrev schema.MustUnsafePutLease.spec : Prop :=
  ∀ (tx : GoInterfaceOk) (lpb : Loc) (v : go_etcd_io.etcd.server.v3.lease.leasepb.Lease)
    (bk : GoInterface) (R Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      globalAddr schema.Lease ↦□ bk ∗ lpb ↦ v ∗ R ∗
      ⌜v.unknownFields' = slice.nil⌝ ∗
      □ (∀ (key val : GoSlice),
        {{ key ↦*□ (u64Le v.ID').reverse ∗
            val ↦*□ lease.leaseEnc v.ID' v.TTL' v.RemainingTTL' ∗ R }}
          (App (App (App (Val #(methods tx.ty go!"UnsafePut" tx.v)) (Val #bk)) (Val #key))
            (Val #val))
        {{ RET #(); Q }}) }}
    (App (App (Val (@! schema.MustUnsafePutLease)) (Val #(GoInterface.ok tx))) (Val #lpb))
  {{ RET #(); (∃ v' : go_etcd_io.etcd.server.v3.lease.leasepb.Lease, lpb ↦ v') ∗ Q }}

end spec

end EtcdGrove
end Perennial
