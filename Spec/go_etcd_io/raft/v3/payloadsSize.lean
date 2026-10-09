/- Port of election_proof/spec_payloadsSize.v (feb5c73d4). -/
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

/-- `payloadsSize(ents)`: the summed payload size of the entries (`payloadsSize.impl`,
`Code/go_etcd_io/raft/v3.lean`) -- a `slice.for_range` accumulating
`payloadSize(e)`, exactly `entsSize`'s shape.

The result is **not** pinned to the sum of the `len(e.Data)`: that sum is computed in
`uint64` with no overflow check, so a triple stating it would have to carry a bound
premise that nothing on the election path can supply. What is pinned is the case the
callers care about -- a batch of empty payloads weighs `0`.

`increaseUncommittedSize`, reached from `appendEntry`, is called on the new leader's
single empty `EntryNormal` and uses that implication. `maybeSendAppend` is the other
caller and does not: it passes the result straight to `Progress.SentEntries`, which
forwards it to `Inflights.Add`'s `bytes` field, which only `Full` reads back (against
`maxBytes`). The
unconditional half of the postcondition (an unspecified `n`) exists for it -- the
entries it weighs come out of the log and may carry data. Widened from the
`Forall`-premised form on 2026-09-20; the old conclusion is the new implication applied
to the old premise. -/
abbrev payloadsSize.spec : Prop :=
  ∀ (s : GoSlice) (es : List raftpb.Entry) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hs" ∷ s ↦*{dq} es }}
    (App (Val #(functions payloadsSize [])) (Val #s))
  {{ (n : w64), RET #n;
      s ↦*{dq} es ∗
      ⌜(∀ e ∈ es, sint.Z e.Data'.len = 0) → n = W64 0⌝ }}

end spec

end EtcdGrove
end Perennial
