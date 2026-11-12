/-
Port of election_proof/spec_entsSize.v (feb5c73d4).
-/
module

public import Proof.go_etcd_io.raft.v3.InvReadylog

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

/-- `entsSize(ents)`: the summed encoded size of the entries (`util.go:274`).

(out_size C3) The entries at their contents (`entsPtsC sz`). When they are sized, the result is the
sum of protobuf's sizes (`entrySize`), if that sum is below `2^64` (each size is `proto.SizePb`'s at
`Entry`'s registered instance, exact for a sized entry; the `uint64` sum wraps silently above):
`raftLog.slice` compares it against `maxSize` to cut the unstable part it appends. -/
abbrev entsSize.spec : Prop :=
  ∀ (sz : Bool) (s : GoSlice) (cs : List EntryC) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hs" ∷ entsPtsC sz s dq cs }}
    (App (Val #(functions entsSize [])) (Val #s))
  {{ (n : w64), RET #n; entsPtsC sz s dq cs ∗
      ⌜sz = true → (cs.map entrySize).sum < 2 ^ 64 → uint.nat n = (cs.map entrySize).sum⌝ }}

end spec

end EtcdGrove
end Perennial
