/-
Port of `election_proof/spec_Inflights__Add.v`.
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

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

/-- `in.Add(index, bytes)` records one dispatched message (`Inflights.Add.impl`,
`Perennial/Code/go_etcd_io/raft/v3/tracker.lean`).

Two things make the premise necessary rather than convenient.

1. The body opens with `if in.Full() { panic("cannot add into a Full inflights") }`.
   A triple without `inflightsFull iv = false` would be false, not merely weak.
2. It then writes `in.buffer[(in.start+in.count) mod in.size]`, growing the buffer on
   demand. That the slot is in range is the content of `InflightsOk` in
   `ownInflights` (`InvTracker.lean`); without it the triple is *also* false
   (start = 100, count = 0, size = 1000, empty buffer is not `Full`, grows to one slot
   and indexes slot 100).

The resulting `Inflights` value is existential: nothing on the election path reads the
window back. `SentEntries` immediately re-tests `Full()`, and stores the answer in
`MsgAppFlowPaused`, which only `IsPaused` reads -- and either answer there is fine. -/
abbrev tracker.Inflights.Add.spec : Prop :=
  ∀ (l : Loc) (iv : tracker.Inflights) (buf : List tracker.inflight) (index bytes : w64),
  inflightsFull iv = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗
      "Hin" ∷ ownInflights l iv buf }}
    (App (App (Val (l @!! go.GoType.PointerType tracker.Inflights.ty @!! go!"Add"))
      (Val #index)) (Val #bytes))
  {{ RET #(); ∃ iv' buf', ownInflights l iv' buf' }}

end spec

end EtcdGrove
end Perennial
