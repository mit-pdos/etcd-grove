/-
Port of election_proof/spec_Inflights__Add.v (feb5c73d4).
-/
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

/-- `in.Add(index, bytes)` records one dispatched message (`Inflights.Add.impl`,
`EtcdRaft/Code/go_etcd_io/raft/v3/tracker.lean`).

Two things make the premise necessary rather than convenient.

1. The body opens with `if in.Full() { panic("cannot add into a Full inflights") }`.
   A triple without `inflightsFull i = false` would be false, not merely weak.
2. It then writes `in.buffer[(in.start+in.count) mod in.size]`, growing the buffer on
   demand. That the slot is in range is the content of `InflightsOk` in
   `ownInflights` (`InvTracker.lean`); without it the triple is *also* false
   (start = 100, count = 0, size = 1000, empty buffer is not `Full`, grows to one slot
   and indexes slot 100).

The new record is `inflightsAdd i bytes` (`Defs.lean`): one more message, `bytes` more
bytes (wrapping, as `uint64`). `SentEntries` immediately re-tests `Full()` on it.
(Until 2026-10-02 the result was existential, on `ownInflights` at the Goose value.) -/
abbrev tracker.Inflights.Add.spec : Prop :=
  ∀ (l : Loc) (i : Inflights) (index bytes : w64),
  inflightsFull i = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗
      "Hin" ∷ ownInflights l i }}
    (App (App (Val (l @!! go.GoType.PointerType tracker.Inflights.ty @!! go!"Add"))
      (Val #index)) (Val #bytes))
  {{ RET #(); ownInflights l (inflightsAdd i bytes) }}

end spec

end EtcdGrove
end Perennial
