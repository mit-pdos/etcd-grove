/- Port of election_proof/spec_unstable__restore.v (857d09190). -/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvReadylog

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
without saying (until 2026-10-08 the post said so, on the Goose value). (2026-10-15, stage S)
The snapshot, with its lists, joins the ones the node may send (`ksn`, `pendKsn`).

raft v3.7 (stage R3, 2026-10-15): `s` is a `*pb.Snapshot`, read at any fraction and given back,
and `u.snapshot = proto.Clone(s)` (`log_unstable.go:196`): the log holds a fresh clone,
read-only for good (`ownSnap`; until the retarget `&s` of the by-value parameter with the
caller's `ConfState` slices, `ownCSL` of the lists `voters`, now the record's own). -/
abbrev unstable.restore.spec : Prop :=
  ∀ (u : Loc) (us : UnstableSt) (sp : Loc) (dq : DFrac) (sv : SnapshotM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hun" ∷ ownUnstable u us ∗
      "Hsnap" ∷ ownSnapM sp dq sv }}
    (App (Val (u @!! go.GoType.PointerType unstable.ty @!! go!"restore")) (Val #sp))
  {{ RET #();
      ownSnapM sp dq sv ∗
      ownUnstable u { ents := [], offset := sv.Metadata'.Index' + W64 1,
                      inprogress := sv.Metadata'.Index' + W64 1,
                      snap := some (snapId sv),
                      ksn := us.ksn ++ [snapTrip sv sv.Metadata'.ConfState'.lists] } }}

end spec

end EtcdGrove
end Perennial
