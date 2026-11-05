/-
`(*lessor).Grant` (`server/lease/lessor.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`, `LessorBackend.lean`. Over mvcc's
API (strict M1, 2026-11-05): `notes/mvcc-api-clients/ServerSpecs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend
public import Proof.go_etcd_io.etcd.server.v3.lease.MvccShapes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc mvcc.api srvApi

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`le.Grant(id, ttl)`** (strict M1, 2026-11-05: the frozen draft's `lessor.Grant.specA`,
`notes/mvcc-api-clients/ServerSpecs.lean` §5: only the critical-section contract changes, over the
API's `hookRun`, the hook a `GoFunc`), by the lease owner (`leaseOwn γl L`: the apply thread) under
the batch lock's critical-section contract: for `id` 0, a TTL above `MaxLeaseTTL` or a lease
already granted (`id ∈ L`), one of the lessor's errors, nothing changed (`Pre` back); otherwise the
new lease `l` (its `ID` and `ttl` read-only: its `ttl` the larger of `ttl` and the lessor's
minimum), `id` added to the live set, its record (`leaseEnc` of the id, that TTL and a remaining
TTL of 0) put into the tracked buckets `Rb` holds, under the id's 8 big-endian bytes (`Post`). Only
a lease the lessor's grant guard admits (`leaseGranted γl id`). The owner's item map `I` is
unchanged: the new lease's item set is empty. -/
abbrev lease.lessor.Grant.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (id ttl : w64) (L : List w64) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64)
    (P : IProp GF) (f : GoFunc) (T R : IProp GF) (Rb : GMap GoString backend.BktData → IProp GF)
    (rb : GMap GoString backend.BktData) (Pre Q Post : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lease.lessorInv lp γl ∗
      lease.lessorCfg lp ∗ lease.lessorBackend lp P #f T R Rb ∗ lease.leaseOwn γl L I ∗
      lease.leaseRevokers γl L ∗ csContractA P f Pre Q Post ∗ T ∗ R ∗ Rb rb ∗
      lease.leaseGranted γl id }}
    (App (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty
      @!! go!"Grant")) (Val #id)) (Val #ttl))
  {{ (l : Loc) (err : GoInterface), RET (PairV #l #err); R ∗
      ((⌜err ≠ GoInterface.nil ∧ (id = W64 0 ∨ 9000000000 < sint.Z ttl ∨ id ∈ L)⌝ ∗
        lease.lessorErrIs err ∗ lease.leaseOwn γl L I ∗ lease.leaseRevokers γl L ∗ Pre ∗ Rb rb) ∨
      (⌜err = GoInterface.nil ∧ l ≠ null ∧ id ≠ W64 0 ∧ sint.Z ttl ≤ 9000000000 ∧ id ∉ L⌝ ∗
        lease.leaseOwn γl (L ++ [id]) I ∗ lease.leaseRevokers γl (L ++ [id]) ∗ Post ∗
        lease.lsF go!"ID" l ↦□ id ∗ ∃ mt : w64, lease.lF go!"minLeaseTTL" lp ↦□ mt ∗
        lease.lsF go!"ttl" l ↦□ lease.grantTTL mt ttl ∗
        Rb (mvcc.rbSet rb mvcc.leaseName (u64Le id).reverse
          (lease.leaseEnc id (lease.grantTTL mt ttl) (W64 0))))) }}

end spec

end EtcdGrove
end Perennial
