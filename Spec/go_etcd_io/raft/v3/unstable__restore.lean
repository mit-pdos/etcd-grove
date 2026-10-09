/- Port of election_proof/spec_unstable__restore.v (857d09190). -/
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `u.restore(s)` (`log_unstable.go:188`, `unstable.restore.impl`):

    u.offset = s.Metadata.Index + 1
    u.offsetInProgress = u.offset
    u.entries = nil
    u.snapshot = &s
    u.snapshotInProgress = false

`&s` is the address of the by-value parameter, a fresh heap cell; it becomes the
state's `snap`, the snapshot's id (`snapId`), held as `ownSnap` together with the
caller's read-only `ConfState.Voters` (since 2026-10-03: `raftLog.snapshot()` hands the
stored snapshot's voters to `maybeSendSnapshot`). The old entries are dropped (the
suffix is empty, a `nil` slice); the logger is left alone, which `ownUnstable` keeps
without saying (until 2026-10-08 the post said so, on the Goose value). -/
abbrev unstable.restore.spec : Prop :=
  ∀ (u : Loc) (us : UnstableSt) (sv : raftpb.Snapshot) (voters : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hun" ∷ ownUnstable u us ∗
      "#Hvoters" ∷ sv.Metadata'.ConfState'.Voters' ↦*□ voters }}
    (App (Val (u @!! go.GoType.PointerType unstable.ty @!! go!"restore")) (Val #sv))
  {{ RET #();
      ownUnstable u { ents := [], offset := sv.Metadata'.Index' + W64 1,
                      inprogress := sv.Metadata'.Index' + W64 1,
                      snap := some (snapId sv) } }}

end spec

end EtcdGrove
end Perennial
