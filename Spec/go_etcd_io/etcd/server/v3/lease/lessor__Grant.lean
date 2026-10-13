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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `le.Grant(id, ttl)`, by the lease owner (`leaseOwn γl L`: the apply thread) under the batch
lock's critical-section contract: for `id` 0, a TTL above `MaxLeaseTTL` or a lease already
granted (`id ∈ L`), one of the lessor's errors, nothing changed (`Pre` back); otherwise the new
lease `l` (its `ID` and `ttl` read-only: its `ttl` the larger of `ttl` and the lessor's minimum),
`id` added to the live set, its record written to the backend (`Post`). -/
abbrev lease.lessor.Grant.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (id ttl : w64) (L : List w64) (P : IProp GF) (f : val)
    (Pre Q Post : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl ∗
      lessorCfg lp ∗ lessorBackend lp P f ∗ leaseOwn γl L ∗ mvcc.csContract P f Pre Q Post }}
    (App (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"Grant")) (Val #id)) (Val #ttl))
  {{ (l : Loc) (err : GoInterface), RET (PairV #l #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ lessorErrIs err ∗ leaseOwn γl L ∗ Pre) ∨
      (⌜err = GoInterface.nil ∧ l ≠ null ∧ id ∉ L⌝ ∗ leaseOwn γl (L ++ [id]) ∗ Post ∗
        lsF go!"ID" l ↦□ id ∗ ∃ t : w64, lsF go!"ttl" l ↦□ t) }}

end spec

end EtcdGrove
end Perennial
