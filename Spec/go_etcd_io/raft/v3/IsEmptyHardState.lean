/-
Port of `election_proof/spec_IsEmptyHardState.v` (feb5c73d4).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

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

/-- `IsEmptyHardState st` is `st == emptyState`, and `emptyState` is the zero
`HardState` (`isInitialized`, `Proof.go_etcd_io.raft.v3.Base`; Rocq `v3_proof/base.v`).

raft v3.7 (2026-10-15, stage R4): `st` is a `*pb.HardState`, `st == nil ||
isHardStateEqual(st, emptyState)` (`node.go:122`), with `emptyState = &pb.HardState{}`: the
pointer may be `nil` (`hsOpt`, read as the zero record, which is empty), the record `hs`. -/
abbrev IsEmptyHardState.spec : Prop :=
  ∀ (st : Loc) (hs : HardStateM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "#Hst" ∷ hsOpt st hs }}
    (App (Val #(functions IsEmptyHardState [])) (Val #st))
  {{ RET #(decide (hs.Term' = W64 0 ∧ hs.Vote' = W64 0 ∧ hs.Commit' = W64 0));
      True }}

end spec

end EtcdGrove
end Perennial
