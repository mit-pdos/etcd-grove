/-
Port of `election_proof/spec_unstable__shrinkEntriesArray.v` (857d09190).
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

/-- `u.shrinkEntriesArray()` (`log_unstable.go:166`): with no entries left the slice
becomes `nil`; when most of the backing array is unused the entries are copied into a
fresh array of exactly their length; otherwise nothing changes. Only `u.entries` is
written, and it holds the same entries (read-only, as always: the copy is
persisted), so the state is unchanged (until 2026-10-08 the post named the new slice,
`ownUnstable u { uv with entries' := sl } uents`). -/
abbrev unstable.shrinkEntriesArray.spec : Prop :=
  ∀ (u : Loc) (us : UnstableSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hun" ∷ ownUnstable u us }}
    (App (Val (u @!! go.GoType.PointerType unstable.ty @!! go!"shrinkEntriesArray"))
      (Val #()))
  {{ RET #(); ownUnstable u us }}

end spec

end EtcdGrove
end Perennial
