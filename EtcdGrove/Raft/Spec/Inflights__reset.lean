/-
Port of `election_proof/spec_Inflights__reset.v` (feb5c73d4).

Lean notes: `inflights.t` is `Inflights`, `own_Inflights` is `ownInflights` (the
record-indexed predicate), `inflights_reset` is `inflightsReset` (`Defs.lean`);
Rocq's `Inflights__resetⁱᵐᵖˡ` is `tracker.Inflights.reset.impl`.
-/
import EtcdGrove.Raft.InvRaftPhys

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

/-- `in.reset()` (`tracker.Inflights.reset.impl`, Rocq
new/code/go_etcd_io/raft/v3/tracker.v): `in.start = 0; in.count = 0; in.bytes = 0`.
Called by `Progress.ResetState`, on the way to `BecomeReplicate` and friends.

Stated on `ownInflights` at the exact new record, `inflightsReset i` (`Defs.lean`);
`start` is internal. The ring-buffer invariant survives: `start` and `count` go to `0`
and the buffer is untouched. (Until 2026-10-02 stated on `ownInflightsRaw` at the
Goose value; until 2026-09-23 on the raw field points-to.) -/
abbrev tracker.Inflights.reset.spec : Prop :=
  ∀ (l : Loc) (i : Inflights),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ ownInflights l i }}
    (App (Val (l @!! go.GoType.PointerType tracker.Inflights.ty @!! go!"reset")) (Val #()))
  {{ RET #(); ownInflights l (inflightsReset i) }}

end spec

end EtcdGrove
end Perennial
