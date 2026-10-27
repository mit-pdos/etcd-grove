/-
`(*lessor).Checkpoint` (`server/lease/lessor.go`). Lean-first (no Rocq counterpart); see
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

/-- `le.Checkpoint(id, remainingTTL)` under the batch lock's critical-section contract: sets the
lease's remaining TTL if it is granted, writes its record to the backend if the lessor persists
checkpoints (`Post`, the record, `leaseEnc` of the id, the lease's TTL and `remainingTTL`, put into
the tracked buckets `Rb` holds under the id's 8 big-endian bytes: leases T3, L3c, 2026-10-27;
otherwise `Pre` back, the buckets left), schedules the next checkpoint if primary; `nil`. -/
abbrev lease.lessor.Checkpoint.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (id rem : w64) (P : IProp GF) (f : val) (T R : IProp GF)
    (Rb : GMap GoString backend.BktData → IProp GF) (rb : GMap GoString backend.BktData)
    (Pre Q Post : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl ∗
      lessorCfg lp ∗ lessorBackend lp P f T R Rb ∗ mvcc.csContract P f Pre Q Post ∗ T ∗ R ∗
      Rb rb }}
    (App (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"Checkpoint")) (Val #id))
      (Val #rem))
  {{ (err : GoInterface), RET #err; R ∗ ⌜err = GoInterface.nil⌝ ∗
      ((Post ∗ ∃ t : w64,
          Rb (mvcc.rbSet rb mvcc.leaseName (u64Le id).reverse (leaseEnc id t rem))) ∨
        (Pre ∗ Rb rb)) }}

end spec

end EtcdGrove
end Perennial
