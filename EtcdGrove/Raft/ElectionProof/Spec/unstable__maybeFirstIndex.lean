/-
Port of `election_proof/spec_unstable__maybeFirstIndex.v`.
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

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

/-- **The `unstable` suffix.**

Three `maybe*` methods, all on a bare `*unstable` so they can be reused wherever the
field is split out. Each takes `snapshot = nil` as a premise -- with a snapshot present
all three have an extra branch, and none of them is reachable under our scope. -/
abbrev unstable.maybeFirstIndex.spec : Prop :=
  ∀ (u : Loc) (uv : unstable) (uents : List raftpb.Entry),
  uv.snapshot' = Loc.null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownUnstable u uv uents }}
    (App (Val (u @!! go.GoType.PointerType unstable.ty @!! go!"maybeFirstIndex")) (Val #()))
  {{ (i : w64), RET (PairV #i #false); ownUnstable u uv uents }}

end spec

end EtcdGrove
end Perennial
