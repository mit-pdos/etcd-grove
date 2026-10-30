/-
Lean-first (no Rocq counterpart).

# A `Ready`'s entries are consecutive (2026-10-30, kvreconf's `run`): a stand-in for a raft law

`MemoryStorage.Append` takes a batch whose indices follow its first one's. `readyRest` gives this
only for a snapshot `Ready` (`readySnap`'s `LogIndicesOk`). This raft law is requested (a law out of
`readyRest`, proved from raft's `LogIndicesOk` of its unstable entries). Until it lands this is a
**`sorry`**, stated exactly as requested so that the swap is a rename.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.DefsCluster

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section law
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [StorageModel GF] [AllG GF]

/-- **Stand-in (sorry)** for the requested raft law: a `Ready`'s entries are consecutive. -/
theorem kvr_readyRest_indices (γ : Cluster) (N : Namespace) (id : w64) (rd : Ready)
    (st : NodeDriverState) (ce : List LogEntry) (es : List EntryM) (h : HardStateM)
    (L : Option SnapLoan) :
    readyRest (GF := GF) γ N id rd st ce es h L ⊢
      ⌜∀ e0, es.head? = some e0 → ∀ j e, es[j]? = some e →
        uint.nat e.Index' = uint.nat e0.Index' + j⌝ ∗ readyRest γ N id rd st ce es h L := by
  sorry

end law

end kvreconf
end EtcdGrove
end Perennial
