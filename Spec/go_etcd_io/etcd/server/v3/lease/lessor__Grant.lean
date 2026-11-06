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

/-- `le.Grant(id, ttl)`, by the lease owner (`leaseOwn γl L`: the apply thread) under the batch
lock's critical-section contract: for `id` 0, a TTL above `MaxLeaseTTL` or a lease already
granted (`id ∈ L`), one of the lessor's errors, nothing changed (`Pre` back); otherwise the new
lease `l` (its `ID` and `ttl` read-only: its `ttl` the larger of `ttl` and the lessor's minimum),
`id` added to the live set, its record written to the backend (`Post`). Since D19n (2026-10-18)
only a lease the lessor's grant guard admits (`leaseGranted γl id`), which the lessor's lock then
keeps for every lease of its map. (Unit T3, L2b) The owner's item map `I` is unchanged: the new
lease's item set is empty. (L3c, 2026-10-27) The error case exactly when `id` is 0, the TTL above
`MaxLeaseTTL` (`9000000000`) or `id` live; the new lease's TTL is `grantTTL` of the lessor's
minimum (its `minLeaseTTL`) and `ttl`, and its record (`leaseEnc` of the id, that TTL and a
remaining TTL of 0) is put into the tracked buckets `Rb` holds, under the id's 8 big-endian bytes;
on an error they are left. (The lease-grant plan's D2, 2026-11-02) The new lease is in the lessor's
history (`leaseLiveFrom γl 0 id l`: the snapshot `Grant` appends under `le.mu`, with `l` at `id`),
which a monotone lessor keeps (`leaseGrantedAt_of_live`). (The lease-expiry plan's E3 (c),
2026-11-05) The ids the lessor ever had, `U` (`leaseEver`): `id` must be new to them unless the
lessor is monotone (so that an id is live over an interval of the history), and is added. (The
lease-expiry plan's S2–S4, Q-S8, 2026-11-05) The new lease's request is `ttl` (`leaseReqIs`): every
TTL the history gives `id` is at least `ttl` (`leaseTTLAt_ge_req`). (Strict M1, 2026-11-05: the
frozen draft's `lessor.Grant.specA`, `notes/mvcc-api-clients/ServerSpecs.lean` §5: the
critical-section contract over mvcc's API's `hookRun`, `csContractA`, the hook a `GoFunc`; merged
with `lean`'s on 2026-11-06.) -/
abbrev lease.lessor.Grant.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (id ttl : w64) (L : List w64) (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64)
    (P : IProp GF) (f : GoFunc) (T Ln R : IProp GF) (Rb : GMap GoString backend.BktData → IProp GF)
    (rb : GMap GoString backend.BktData) (Pre Q Post : IProp GF) (U : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lease.lessorInv lp γl ∗
      lease.lessorCfg lp ∗ lease.lessorBackend lp P #f T Ln R Rb ∗ lease.leaseOwn γl L I ∗
      lease.leaseRevokers γl L ∗ csContractA P f Pre Q Post ∗ T ∗ Ln ∗ R ∗ Rb rb ∗
      lease.leaseGranted γl id ∗ lease.leaseEver γl U ∗ (lease.lessorModeIs γl true ∨ ⌜id ∉ U⌝) }}
    (App (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty
      @!! go!"Grant")) (Val #id)) (Val #ttl))
  {{ (l : Loc) (err : GoInterface), RET (PairV #l #err); R ∗ Ln ∗
      ((⌜err ≠ GoInterface.nil ∧ (id = W64 0 ∨ 9000000000 < sint.Z ttl ∨ id ∈ L)⌝ ∗
        lease.lessorErrIs err ∗ lease.leaseOwn γl L I ∗ lease.leaseRevokers γl L ∗ Pre ∗ Rb rb ∗
        lease.leaseEver γl U) ∨
      (⌜err = GoInterface.nil ∧ l ≠ null ∧ id ≠ W64 0 ∧ sint.Z ttl ≤ 9000000000 ∧ id ∉ L⌝ ∗
        lease.leaseOwn γl (L ++ [id]) I ∗ lease.leaseRevokers γl (L ++ [id]) ∗ Post ∗
        lease.lsF go!"ID" l ↦□ id ∗ lease.leaseLiveFrom γl 0 id l ∗
        ∃ mt : w64, lease.lF go!"minLeaseTTL" lp ↦□ mt ∗
        lease.lsF go!"ttl" l ↦□ lease.grantTTL mt ttl ∗
        Rb (mvcc.rbSet rb mvcc.leaseName (u64Le id).reverse
          (lease.leaseEnc id (lease.grantTTL mt ttl) (W64 0))) ∗
        lease.leaseEver γl (U ++ [id]) ∗ lease.leaseReqIs γl id ttl)) }}

end spec

end EtcdGrove
end Perennial
