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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `le.Checkpoint(id, remainingTTL)` under the batch lock's critical-section contract: sets the
lease's remaining TTL if it is granted, writes its record to the backend if the lessor persists
checkpoints (`Post`; otherwise `Pre` back), schedules the next checkpoint if primary; `nil`. -/
abbrev lease.lessor.Checkpoint.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (id rem : w64) (P : IProp GF) (f : val) (Pre Q Post : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl ∗
      lessorCfg lp ∗ lessorBackend lp P f ∗ mvcc.csContract P f Pre Q Post }}
    (App (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"Checkpoint")) (Val #id))
      (Val #rem))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ (Post ∨ Pre) }}

end spec

end EtcdGrove
end Perennial
