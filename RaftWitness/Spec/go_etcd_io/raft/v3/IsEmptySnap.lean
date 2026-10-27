/-
Port of election_proof/spec_IsEmptySnap.v (feb5c73d4).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvRaftPhys

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

/-- `IsEmptySnap(sp)` (`IsEmptySnap.impl`, `Code/go_etcd_io/raft/v3.lean`)
is one field test:

    return sp.Metadata.Index == 0

Pure, so the triple says exactly that. It matters because `raft.maybeSendSnapshot`
follows it with `panic("need non-empty snapshot")`: the proof there has to know the
answer is `false`, which it gets from `isStorage`'s `HSnapshot` (`InvStorage.lean`).

raft v3.7 (2026-10-15, stage R4): `sp` is a `*pb.Snapshot`, `sp.GetMetadata().GetIndex() == 0`
(`node.go:127`): a `nil` pointer (`o = none`) is empty; otherwise the snapshot, at any fraction,
is given back. -/
abbrev IsEmptySnap.spec : Prop :=
  ∀ (sp : Loc) (dq : DFrac) (o : Option SnapshotM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hsp" ∷ snapOpt sp dq o }}
    (App (Val #(functions IsEmptySnap [])) (Val #sp))
  {{ (b : Bool), RET #b;
      ⌜b = o.elim true (fun sv => decide (sv.Metadata'.Index' = W64 0))⌝ ∗ snapOpt sp dq o }}

end spec

end EtcdGrove
end Perennial
