/-
Port of `election_proof/spec_payloadSize.v` (feb5c73d4).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvReadylog

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

/-- `payloadSize(e)`: the size of one entry's payload, i.e. `len(e.Data)`
(`payloadSize.impl`, `Code/go_etcd_io/raft/v3.lean`).

The entry is passed **by value** -- Goose allocates a local for it -- so the triple
needs no ownership at all: the length of a slice *value* is a projection of that value,
not something read out of the heap. The result is therefore pinned exactly,
`e.Data.len`, which is what `payloadsSize`'s caller needs in order to see that a batch
of empty entries has zero payload.

raft v3.7 (stage R3, 2026-10-15): `payloadSize(e *pb.Entry)` reads `len(e.GetData())`, so the
entry is a pointer, at any fraction (`entPts`; a log entry's `entRO`), given back; the result
is still exactly the length of the entry's `Data` slice, which since D6 (stage R4) is the
length of its bytes `e.Data'`. -/
abbrev payloadSize.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (e : EntryM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "He" ∷ entPts p dq e }}
    (App (Val #(functions payloadSize [])) (Val #p))
  {{ RET #(W64 e.Data'.length); entPts p dq e }}

end spec

end EtcdGrove
end Perennial
