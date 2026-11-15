/-
Port of election_proof/spec_limitSize.v (feb5c73d4).
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

/-- `limitSize(ents, maxSize)`: the longest prefix of `ents` whose encoded size fits in
`maxSize`, except that a non-empty input always yields at least its first entry
(`util.go:286`).

The result is `ents` itself or `ents[:limit]`, so it **aliases** the input and is lent:
the postcondition gives the prefix's points-to and a wand back to the whole slice.

(out_size C3) The entries at their contents (`entsPtsC sz`). When they are sized and
`maxSize ≤ entsCutMax`, the prefix is cut at `maxSize` (`entsCut`: one entry, or protobuf's sizes
sum to at most `maxSize`): the sizes are `proto.Size(ents[i])` (`proto.SizePb` at `Entry`'s registered
instance, exact below `2^63`, which a sized entry is), and the running sum stays far from wrapping. -/
abbrev limitSize.spec : Prop :=
  ∀ (sz : Bool) (s : GoSlice) (cs : List EntryC) (dq : DFrac) (maxSize : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hs" ∷ entsPtsC sz s dq cs }}
    (App (App (Val #(functions limitSize [])) (Val #s)) (Val #maxSize))
  {{ (s' : GoSlice) (n : Nat), RET #s';
      ⌜n ≤ cs.length ∧ (cs ≠ [] → 1 ≤ n) ∧
        (sz = true → uint.nat maxSize ≤ entsCutMax → entsCut maxSize (cs.take n))⌝ ∗
      entsPtsC sz s' dq (cs.take n) ∗
      (entsPtsC sz s' dq (cs.take n) -∗ entsPtsC sz s dq cs) }}

end spec

end EtcdGrove
end Perennial
