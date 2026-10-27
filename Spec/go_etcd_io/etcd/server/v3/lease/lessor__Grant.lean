/-
`(*lessor).Grant` (`server/lease/lessor.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean` and `LessorBackend.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

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
on an error they are left. -/
abbrev lease.lessor.Grant.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (id ttl : w64) (L : List w64) (I : GMap LeaseItem w64) (P : IProp GF)
    (f : val) (T R : IProp GF) (Rb : GMap GoString backend.BktData → IProp GF)
    (rb : GMap GoString backend.BktData) (Pre Q Post : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl ∗
      lessorCfg lp ∗ lessorBackend lp P f T R Rb ∗ leaseOwn γl L I ∗ leaseRevokers γl L ∗ mvcc.csContract P f Pre Q Post ∗
      T ∗ R ∗ Rb rb ∗ leaseGranted γl id }}
    (App (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"Grant")) (Val #id)) (Val #ttl))
  {{ (l : Loc) (err : GoInterface), RET (PairV #l #err); R ∗
      ((⌜err ≠ GoInterface.nil ∧ (id = W64 0 ∨ 9000000000 < sint.Z ttl ∨ id ∈ L)⌝ ∗ lessorErrIs err ∗
        leaseOwn γl L I ∗ leaseRevokers γl L ∗ Pre ∗ Rb rb) ∨
      (⌜err = GoInterface.nil ∧ l ≠ null ∧ id ≠ W64 0 ∧ sint.Z ttl ≤ 9000000000 ∧ id ∉ L⌝ ∗ leaseOwn γl (L ++ [id]) I ∗ leaseRevokers γl (L ++ [id]) ∗ Post ∗
        lsF go!"ID" l ↦□ id ∗ ∃ mt : w64, lF go!"minLeaseTTL" lp ↦□ mt ∗
        lsF go!"ttl" l ↦□ grantTTL mt ttl ∗
        Rb (mvcc.rbSet rb mvcc.leaseName (u64Le id).reverse (leaseEnc id (grantTTL mt ttl) (W64 0))))) }}

end spec

end EtcdGrove
end Perennial
