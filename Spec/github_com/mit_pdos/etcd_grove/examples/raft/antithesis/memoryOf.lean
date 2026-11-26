/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessRun.lean`'s).
`memoryOf(d)`: a fresh `MemoryStorage` holding the disk `w` (its hard state, its entries from index
1), the storage `start` gives raft. The disk's entries are numbered from 1, within raft's index
bound (`MemoryStorage.Append`'s premises; `Append` panics on a gap).
It also returns `NewMemoryStorage`'s snapshot resources (no snapshot yet; the storage fresh, no
reader holds it), which `start` needs to attach the storage to raft.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessRun

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- See the file header. -/
abbrev memoryOf.spec : Prop :=
  ∀ (d : Loc) (w : AntSim.DurW),
    (∀ (i : Nat) (e : EntryM), w.log[i]? = some e → uint.nat e.Index' = 1 + i) → 1 + w.log.length ≤ 2 ^ 61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      diskOwn d w }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.antithesis.memoryOf)) (Val #d))
  {{ (ms : Loc), RET #ms; diskOwn d w ∗ ∃ γs : MemStorNames, memStorLock ms γs ∗
      memStorMeta ms γs (HardStateM.mk w.term w.vote w.commit) ∗ memLog γs 1 (DFrac.own 1) w.log ∗
      memEnd γs (1 + w.log.length) ∗ memSnapNone γs memSnapEmpty ∗ memStorFresh ms γs 0 memSnapEmpty ∗
      ⌜γs.sz = false⌝ }}

end spec

end AntHarness
end EtcdGrove
end Perennial
