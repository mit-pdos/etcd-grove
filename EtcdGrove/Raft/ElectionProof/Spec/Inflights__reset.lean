/-
Port of `election_proof/spec_Inflights__reset.v`.

Lean notes:
* Rocq's `iv <| start' := W64 0 |> <| count' := W64 0 |> <| bytes' := W64 0 |>` is
  `{ iv with start' := W64 0, count' := W64 0, bytes' := W64 0 }` (the same value).
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

/-- ### Two internal helpers on the way to `BecomeReplicate`.

Stated on `ownInflights` at the exact new value (until 2026-09-23, on the raw field
points-to). The ring-buffer invariant survives a reset: `start` and `count` go to `0`
and the buffer is untouched. -/
abbrev tracker.Inflights.reset.spec : Prop :=
  ∀ (l : Loc) (iv : tracker.Inflights) (buf : List tracker.inflight),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ ownInflights l iv buf }}
    (App (Val (l @!! go.GoType.PointerType tracker.Inflights.ty @!! go!"reset")) (Val #()))
  {{ RET #(); ownInflights l { iv with start' := W64 0, count' := W64 0, bytes' := W64 0 } buf }}

end spec

end EtcdGrove
end Perennial
