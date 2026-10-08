/- Port of election_proof/spec_Inflights__FreeLE.v (feb5c73d4). -/
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

/-- `in.FreeLE(to)` frees the in-flight messages with index `<= to`
(`tracker.Inflights.FreeLE.impl`, `EtcdRaft/Code/go_etcd_io/raft/v3/tracker.lean`;
inflights.go:98):

    if in.count == 0 || to < in.buffer[in.start].index {
      return                                     // exit 1
    }
    idx := in.start
    var i int; var bytes uint64
    for i = 0; i < in.count; i++ {
      if to < in.buffer[idx].index { break }
      bytes += in.buffer[idx].bytes
      size := in.size
      if idx++; idx >= size { idx -= size }
    }
    in.count -= i
    in.bytes -= bytes
    in.start = idx
    if in.count == 0 { in.start = 0 }
    return                                       // exit 2

**Panics**: none of its own; the two slice reads `in.buffer[in.start]` and
`in.buffer[idx]` would panic out of range, and are in range by `InflightsOk`
(`ownInflights`'s invariant): every occupied slot `[start, start+count)` (mod `size`)
lies inside the buffer. The `||` short-circuits, so `in.buffer[in.start]` is read only
when `count > 0`. No call.

The postcondition is what downstream needs, on the record (`InflightsFreed`,
`Defs.lean`): `size` and `maxBytes` are unchanged and the occupancy does not grow; the
ring stays well-formed inside `ownInflights`. The result is not a function of the
record (it depends on the indices in the buffer), hence the relation. `bytes` is **not**
bounded: `in.bytes -= bytes` is `uint64` arithmetic and nothing relates `in.bytes` to
the sizes in the buffer, so the subtraction can wrap; hence `Full()` is *not* claimed
to become false here -- only `count' ≤ count`. -/
abbrev tracker.Inflights.FreeLE.spec : Prop :=
  ∀ (l : Loc) (i : Inflights) (to : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗
      "Hin" ∷ ownInflights l i }}
    (App (Val (l @!! go.GoType.PointerType tracker.Inflights.ty @!! go!"FreeLE")) (Val #to))
  {{ (i' : Inflights), RET #();
      ownInflights l i' ∗ ⌜InflightsFreed i i'⌝ }}

end spec

end EtcdGrove
end Perennial
