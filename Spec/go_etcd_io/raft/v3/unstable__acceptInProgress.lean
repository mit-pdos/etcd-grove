/-
Port of `election_proof/spec_unstable__acceptInProgress.v` (857d09190).
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

/-- `u.acceptInProgress()` (`log_unstable.go:118`):

    if len(u.entries) > 0 {
        u.offsetInProgress = u.entries[len(u.entries)-1].Index + 1
    }
    if u.snapshot != nil { u.snapshotInProgress = true }

Every unstable entry is in progress afterwards. With the indices contiguous from
`offset` (what `ownRaftLog`'s `LogIndicesOk` and `Hoffset` give) the last entry's index
is `offset + len - 1`, so `offsetInProgress` becomes `offset + len`;
`snapshotInProgress` is not tracked. -/
abbrev unstable.acceptInProgress.spec : Prop :=
  ∀ (u : Loc) (uv : unstable) (uents : List raftpb.Entry),
  (∀ (k : Nat) (e : raftpb.Entry), uents[k]? = some e →
     uint.Z e.Index' = uint.Z uv.offset' + (k : Int)) →
  uint.Z uv.offset' + (uents.length : Int) < 2^64 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hun" ∷ ownUnstable u uv uents }}
    (App (Val (u @!! go.GoType.PointerType unstable.ty @!! go!"acceptInProgress"))
      (Val #()))
  {{ (uv' : unstable), RET #();
      ownUnstable u uv' uents ∗
      ⌜uv'.entries' = uv.entries' ∧
        uv'.offset' = uv.offset' ∧
        uv'.snapshot' = uv.snapshot' ∧
        uv'.logger' = uv.logger' ∧
        (uents = [] → uv'.offsetInProgress' = uv.offsetInProgress') ∧
        (uents ≠ [] → uint.Z uv'.offsetInProgress'
                      = uint.Z uv.offset' + (uents.length : Int))⌝ }}

end spec

end EtcdGrove
end Perennial
