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

/-- `entsSize(ents)`: the summed encoded size of the entries. The value is
unspecified, since `Entry.Size` (pointer receiver) is (`spec_Entry__Size.v`);
`raftLog.slice` only compares it against `maxSize` to decide whether to append the
unstable part of its result, and either answer is fine.

raft v3.7 (stage R3, 2026-10-15): the size of each entry is `proto.Size(ent)` (`util.go:277`,
`proto.SizeEntry.spec`: some `n ≥ 0`), not gogoproto's `Entry.Size`; the statement is unchanged
(the value was unspecified already). -/
abbrev entsSize.spec : Prop :=
  ∀ (s : GoSlice) (es : List EntryM) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hs" ∷ entsPts s dq es }}
    (App (Val #(functions entsSize [])) (Val #s))
  {{ (n : w64), RET #n; entsPts s dq es }}

end spec

end EtcdGrove
end Perennial
