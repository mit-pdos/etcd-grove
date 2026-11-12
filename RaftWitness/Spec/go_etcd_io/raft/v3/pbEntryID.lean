/- Port of election_proof/spec_pbEntryID.v (feb5c73d4). -/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvReadylog
public import RaftWitness.Proof.go_etcd_io.raft.v3.Plog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `pbEntryID(entry)`: the id (`term`, `index`) of the entry behind the pointer --
`entId` (`Plog.lean`). Two field loads and a struct literal (`pbEntryID.impl`,
`Code/go_etcd_io/raft/v3.lean`). The entry is lent at any fraction:
`findConflict` calls it on `&ents[i]` of a batch it holds read-only.

raft v3.7 (stage R3, 2026-10-15): the entry is a `*pb.Entry` read through `GetTerm()`/`GetIndex()`
(`types.go:35`): `entPts` at any fraction (a log entry's `entRO`), given back. -/
abbrev pbEntryID.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (e : EntryM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "He" ∷ entPts p dq e }}
    (App (Val #(functions pbEntryID [])) (Val #p))
  {{ RET #(entId e); entPts p dq e }}

end spec

end EtcdGrove
end Perennial
