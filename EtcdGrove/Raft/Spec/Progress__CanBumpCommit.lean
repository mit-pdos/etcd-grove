/- Port of election_proof/spec_Progress__CanBumpCommit.v (feb5c73d4). -/
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

/-- `pr.CanBumpCommit(index)` is a pure test on the `Progress`
(`tracker.Progress.CanBumpCommit.impl`, `EtcdRaft/Code/go_etcd_io/raft/v3/tracker.lean`;
progress.go:189):

    return index > pr.sentCommit && pr.sentCommit < pr.Next-1

One exit, no panic, no call, no write. `pr.Next-1` is `uint64` arithmetic and wraps to
`2^64-1` at `Next = 0` (the body does not guard it; `ownProgress` does not bound
`Next`), so the subtraction is `w64` subtraction in `progressCanBumpCommit`
(`Defs.lean`). -/
abbrev tracker.Progress.CanBumpCommit.spec : Prop :=
  ∀ (pr : Loc) (p : Progress) (index : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗
      "Hpr" ∷ ownProgress pr p }}
    (App (Val (pr @!! go.GoType.PointerType tracker.Progress.ty @!! go!"CanBumpCommit"))
      (Val #index))
  {{ RET #(progressCanBumpCommit p index); ownProgress pr p }}

end spec

end EtcdGrove
end Perennial
