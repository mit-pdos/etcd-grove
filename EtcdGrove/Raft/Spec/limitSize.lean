/-
Port of election_proof/spec_limitSize.v (feb5c73d4).
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

/-- `limitSize(ents, maxSize)`: the longest prefix of `ents` whose encoded size fits in
`maxSize`, except that a non-empty input always yields at least its first entry
(`util.go:268`).

The result is `ents` itself or `ents[:limit]`, so it **aliases** the input and is lent:
the postcondition gives the prefix's points-to and a wand back to the whole slice.
Which prefix is not specified beyond its length bounds, because the sizes come from
`Entry.Size` (pointer receiver) (`Spec/Entry__Size.lean`), about whose value nothing is
known -- and nothing on the election path cares where the slice is cut. -/
abbrev limitSize.spec : Prop :=
  ∀ (s : GoSlice) (es : List raftpb.Entry) (dq : DFrac) (maxSize : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hs" ∷ s ↦*{dq} es }}
    (App (App (Val #(functions limitSize [])) (Val #s)) (Val #maxSize))
  {{ (s' : GoSlice) (n : Nat), RET #s';
      ⌜n ≤ es.length ∧ (es ≠ [] → 1 ≤ n)⌝ ∗
      s' ↦*{dq} es.take n ∗
      (s' ↦*{dq} es.take n -∗ s ↦*{dq} es) }}

end spec

end EtcdGrove
end Perennial
