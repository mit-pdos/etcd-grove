-- The copy for the part `KvRaft/` of `RaftNoAx/Spec/go_etcd_io/raft/v3/raftpb/CloneEntry.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`raftpb.CloneEntry` (`raftpb/noax.go`): the part's own (raft without hand-written axioms,
`notes/raft-noax-part.md`). Stated as the `proto` trust-boundary spec it replaces.
-/
module

public import KvRaft.Proof.go_etcd_io.raft.v3.InvPb
public import KvRaft.Proof.go_etcd_io.raft.v3.PbContentOwnCore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `CloneEntry(e)` (`raftpb/noax.go`, the fork's branch raft37-goose-lean-noax,
`notes/raft-noax.md`): what `proto.Clone` of a frozen message of a registered type was stated to do
(`Spec/google_golang_org/protobuf/proto/ClonePb.lean`), at `Entry`'s instance `pbEntryC` (so without
the registration premise `pbModelOf … = some pbEntryC`: the function is `Entry`'s own): of a frozen
`*Entry` holding the wire content `c` (`entRoC`, `pbEntryC`'s `roC`), a fresh `*Entry` owned at the
same content (`entPtsCC`, its `decC`; `ClonePb`'s `c' = c`, since every entry marshals). -/
abbrev raftpb.CloneEntry.spec : Prop :=
  ∀ (l : Loc) (c : EntryC),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ entRoC l c }}
    (App (Val #(functions raftpb.CloneEntry [])) (Val #l))
  {{ (l' : Loc), RET #l'; entPtsCC l' (DFrac.own 1) c }}

end spec

end EtcdGrove
end Perennial
