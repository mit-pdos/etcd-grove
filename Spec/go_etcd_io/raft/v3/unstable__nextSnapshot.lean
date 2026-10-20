/-
Port of `election_proof/spec_unstable__nextSnapshot.v` (857d09190).
-/
module

public import Proof.go_etcd_io.raft.v3.InvReadylog

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

/-- `u.nextSnapshot()` (`log_unstable.go:106`): the pending snapshot unless it is
already in progress -- `nil` when there is none or it is in progress (`sip`, since D22
S-d1, 2026-10-20; until then only the no-snapshot case was pinned).

raft v3.7 (stage R3, 2026-10-15): the snapshot returned is a fresh clone of the pending one
(`proto.Clone(u.snapshot)`, `log_unstable.go:114`), owned by the caller, holding the pending
snapshot's record (until the retarget the log's own pointer, which the post did not describe). -/
abbrev unstable.nextSnapshot.spec : Prop :=
  ∀ (u : Loc) (us : UnstableSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hun" ∷ ownUnstable u us }}
    (App (Val (u @!! go.GoType.PointerType unstable.ty @!! go!"nextSnapshot")) (Val #()))
  {{ (p : Loc), RET #p; ownUnstable u us ∗ ⌜p = null ↔ (us.snap = none ∨ us.sip = true)⌝ ∗
      (⌜p = null⌝ ∨ ∃ (sid : entryID) (sv : SnapshotM),
        ⌜us.snap = some sid ∧ us.sip = false ∧ snapId sv = sid ∧
          snapTrip sv sv.Metadata'.ConfState'.lists ∈ us.ksn⌝ ∗
        ownSnapM p (DFrac.own 1) sv) }}

end spec

end EtcdGrove
end Perennial
