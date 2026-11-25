/-
`c.fresh(next)` (kvcheck.go), `next` one of the checker's counters (`&c.nextOp`, `w = false`;
`&c.nextRead`, `w = true`): under `c.mu`, the counter's next number `n`, with what the caller's minting
law gives at it (`L n`), fired under the lock on the counter's predicate (`γ w`, `checkerInv`): so
the numbers are minted in the counter's order. Once the counter is at `2^64 - 1` it never returns.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Assumptions]

/-- See the file header. -/
abbrev checker.fresh.spec : Prop :=
  ∀ (c : Loc) (γ : CheckerCnt GF) (ls : List GoString) (w : Bool) (next : Loc) (L : w64 → IProp GF),
  next = (if w then c.[github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker, go!"nextRead"] else c.[github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker, go!"nextOp"]) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck ∗ isChecker c γ ls ∗
      (∀ a : w64, ⌜uint.Z a + 1 < 2 ^ 64⌝ -∗ γ w a ={⊤}=∗ γ w (a + W64 1) ∗ L (a + W64 1)) }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker.ty @!! go!"fresh")) (Val #next))
  {{ (n : w64), RET #n; L n }}

end spec

end raft_kvcheck
end EtcdGrove
end Perennial
