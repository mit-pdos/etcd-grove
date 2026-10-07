/-
Port of `election_proof/spec_unstable__nextSnapshot.v` (857d09190).
-/
import EtcdGrove.Raft.InvReadylog

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

/-- `u.nextSnapshot()` (`log_unstable.go:106`): the pending snapshot unless it is
already in progress -- `nil` when there is none. Whether a pending snapshot is in
progress (`snapshotInProgress`) is not tracked, so only the no-snapshot case is
pinned. -/
abbrev unstable.nextSnapshot.spec : Prop :=
  ∀ (u : Loc) (uv : unstable) (uents : List raftpb.Entry) (snap : Option entryID),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hun" ∷ ownUnstable u uv uents ∗
      "#Hsnap" ∷ ownSnap uv.snapshot' snap }}
    (App (Val (u @!! go.GoType.PointerType unstable.ty @!! go!"nextSnapshot")) (Val #()))
  {{ (p : Loc), RET #p; ownUnstable u uv uents ∗ ⌜snap = none → p = null⌝ }}

end spec

end EtcdGrove
end Perennial
