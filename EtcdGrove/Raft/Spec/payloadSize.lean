/-
Port of `election_proof/spec_payloadSize.v` (feb5c73d4).
-/
import EtcdGrove.Raft.InvRaftPhys

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

/-- `payloadSize(e)`: the size of one entry's payload, i.e. `len(e.Data)`
(`payloadSize.impl`, `Perennial/Code/go_etcd_io/raft/v3.lean`).

The entry is passed **by value** -- Goose allocates a local for it -- so the triple
needs no ownership at all: the length of a slice *value* is a projection of that value,
not something read out of the heap. The result is therefore pinned exactly,
`e.Data.len`, which is what `payloadsSize`'s caller needs in order to see that a batch
of empty entries has zero payload. -/
abbrev payloadSize.spec : Prop :=
  ∀ (e : raftpb.Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val #(functions payloadSize [])) (Val #e))
  {{ RET #(e.Data'.len); True }}

end spec

end EtcdGrove
end Perennial
