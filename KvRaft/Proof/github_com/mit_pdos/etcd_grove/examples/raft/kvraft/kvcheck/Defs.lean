/-
# kvcheck's checker: its predicates (2026-11-21)

`checker` (`examples/raft/kvraft/kvcheck/kvcheck.go`) is a run's clients' shared state: the replicas'
addresses `addrs` (written once, at construction: read-only for good), and, under `mu`, the next
operation id `nextOp`, the next read sequence number `nextRead`, and the latest configuration a
replica reported `lastConf`.

* `checkerInv c γ`: `mu`'s invariant: the two counters `a`, `b`, `lastConf` (a read-only conf
  state, or `nil`), and the caller's predicate of the counters `γ false a ∗ γ true b` (2026-11-22:
  at the top, the store's operation counter and read sequence numbers, so that `fresh` mints under
  the lock, in the counter's order; until then ghost maps of the issued numbers).
* `isChecker c γ ls` (persistent): `addrs` holds `ls`, read-only, and `mu` guards `checkerInv`.

A change's shape (`ccToV2`, `ccTransOk`, `ccTransOk_v1`) is kvreconf's, from its pure model
(`kvreconf/Pure.lean`), exported here.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Base
public import KvRaft.Proof.go_etcd_io.raft.v3.InvPbLog
public import KvRaft.Proof.go_etcd_io.raft.v3.CCModel
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Pure

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

export raft_kvreconf (ccToV2 ccTransOk ccTransOk_v1)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A checker's counters' predicate: `γ w a` for the counter `w` (`false`: `nextOp`, `true`:
`nextRead`) at `a`; the caller's (at the top, the store's: `kvCnt`). -/
abbrev CheckerCnt (GF : BundledGFunctors) := Bool → w64 → IProp GF

/-- `mu`'s invariant (see the file header). -/
def checkerInv (c : Loc) (γ : CheckerCnt GF) : IProp GF :=
  iprop(∃ (a b : w64) (lc : Loc) (cs : ConfStateM),
    c.[github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker, go!"nextOp"] ↦ a ∗
    c.[github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker, go!"nextRead"] ↦ b ∗
    c.[github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker, go!"lastConf"] ↦ lc ∗
    csOpt lc DFrac.discard cs ∗ γ false a ∗ γ true b)

/-- The checker at `c` (see the file header). -/
def isChecker (c : Loc) (γ : CheckerCnt GF) (ls : List GoString) : IProp GF :=
  iprop(∃ (sl : GoSlice),
    c.[github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker, go!"addrs"] ↦□ sl ∗
    sl ↦*□ ls ∗
    sync.isMutex (c.[github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker, go!"mu"])
      (checkerInv c γ))

instance isChecker_persistent (c : Loc) (γ : CheckerCnt GF) (ls : List GoString) :
    Persistent (isChecker (GF := GF) c γ ls) := by
  unfold isChecker; infer_instance

end defs

end raft_kvcheck
end EtcdGrove
end Perennial
