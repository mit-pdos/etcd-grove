/-
Lean-first (no Rocq counterpart). #33 parity B1, specs first (`notes/antithesis-parity-design.md` §3;
the vocabulary is `HarnessRun.lean`'s).
`(*node).storeSave(hs, ents)`: raft's storage takes the write (`SetHardState` if any, `Append` if
any entries).
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
abbrev node.storeSave.spec : Prop :=
  ∀ (n ms : Loc) (γs : MemStorNames) (h : HardStateM) (hp : Loc) (oh : Option HardStateM) (k : Nat)
    (old es : List EntryM) (sl : GoSlice) (dq : DFrac), (∀ (i : Nat) (e : EntryM), es[i]? = some e → uint.nat e.Index' = k + i) → k + es.length ≤ 2 ^ 61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
      n.[H.node, go!"store"] ↦ ms ∗ memStorLock ms γs ∗ memStorMeta ms γs h ∗ hsOptRO hp oh ∗
      (if es = [] then emp else memLog γs k (DFrac.own 1) old ∗ memEnd γs (k + old.length)) ∗
      entsPtsZ γs.sz sl dq es }}
    (App (App (Val (n @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.ty @!! go!"storeSave")) (Val #hp)) (Val #sl))
  {{ RET #(); n.[H.node, go!"store"] ↦ ms ∗ memStorMeta ms γs (oh.getD h) ∗ entsPtsZ γs.sz sl dq es ∗
      (if es = [] then emp else memLog γs k (DFrac.own 1) es ∗ memEnd γs (k + es.length)) }}

end spec

end AntHarness
end EtcdGrove
end Perennial
