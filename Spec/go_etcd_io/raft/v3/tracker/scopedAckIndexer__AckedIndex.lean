/-
`scopedAckIndexer.AckedIndex` (raft#168, `tracker/tracker.go`; 2026-10-20, witness support).
-/
module

public import Proof.go_etcd_io.raft.v3.InvTracker

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `s.AckedIndex(id)` of an indexer scoped to `S` whose inner indexer reports `acked` (with
the resource `P`): `acked id` for an id of `S`, `(0, false)` otherwise (`scopedAcked`). -/
abbrev tracker.scopedAckIndexer.AckedIndex.spec : Prop :=
  ∀ (s : tracker.scopedAckIndexer) (P : IProp GF) (acked : w64 → Option w64) (S : GSet w64)
    (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗
      isAckedIndexer s.indexer' P acked ∗ ownScope s.scope' S ∗ P }}
    (App (Val (s @!! tracker.scopedAckIndexer.ty @!! go!"AckedIndex")) (Val #id))
  {{ RET (PairV #((scopedAcked S acked id).getD (W64 0)) #((scopedAcked S acked id).isSome)); P }}

/-- The scoped indexer, as an `AckedIndexer` interface value. -/
theorem scopedAckIndexer_isAckedIndexer
    (H : tracker.scopedAckIndexer.AckedIndex.spec (GF := GF) (hG := hG))
    (s : tracker.scopedAckIndexer) (P : IProp GF) (acked : w64 → Option w64) (S : GSet w64) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker -∗
      isAckedIndexer s.indexer' P acked -∗ ownScope s.scope' S -∗
      isAckedIndexer (interface.mkOk tracker.scopedAckIndexer.ty #s) P (scopedAcked S acked) := by
  iintro #Hpkg #Hi #Hs
  iunfold isAckedIndexer
  iexists _
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %id %Ψ
  imodintro
  iintro HP HΨ
  dsimp only
  iapply H s P acked S id $$ [$HP] HΨ
  iframe Hpkg Hi Hs

end spec

end EtcdGrove
end Perennial
