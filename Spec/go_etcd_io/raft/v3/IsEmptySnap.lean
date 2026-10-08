/-
Port of election_proof/spec_IsEmptySnap.v (feb5c73d4).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

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

/-- `IsEmptySnap(sp)` (`IsEmptySnap.impl`, `Code/go_etcd_io/raft/v3.lean`)
is one field test:

    return sp.Metadata.Index == 0

Pure, so the triple says exactly that. It matters because `raft.maybeSendSnapshot`
follows it with `panic("need non-empty snapshot")`: the proof there has to know the
answer is `false`, which it gets from `isStorage`'s `HSnapshot` (`InvStorage.lean`). -/
abbrev IsEmptySnap.spec : Prop :=
  ∀ (sp : raftpb.Snapshot),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val #(functions IsEmptySnap [])) (Val #sp))
  {{ (b : Bool), RET #b; ⌜b = decide (sp.Metadata'.Index' = W64 0)⌝ }}

end spec

end EtcdGrove
end Perennial
