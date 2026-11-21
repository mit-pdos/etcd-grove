/-
# kvcheck's checker: its predicates (2026-11-21)

`checker` (`examples/raft/kvnet/kvcheck/kvcheck.go`) is a run's clients' shared state: the replicas'
addresses `addrs` (written once, at construction: read-only for good), and, under `mu`, the next
operation id `nextOp`, the next read sequence number `nextRead`, and the latest configuration a
replica reported `lastConf`.

* `checkerInv c γ`: `mu`'s invariant: the two counters `a`, `b`, `lastConf` (a read-only conf
  state, or `nil`), and for each counter the ghost map of the numbers `fresh` has issued from it
  (`γ.op`, `γ.rd`), all of them at most the counter (so the counter's next value is not issued).
* `isChecker c γ ls` (persistent): `addrs` holds `ls`, read-only, and `mu` guards `checkerInv`.
* `issued γ w n`: `fresh` issued `n` from the counter `w` (`false`: `nextOp`, `true`: `nextRead`),
  exclusively: no number is issued twice (`issued_excl`).

Also kvreconf's `ccToV2`/`ccTransOk`/`ccTransOk_v1` (`kvreconf/Rule.lean`), restated here over the
same definitions (raft's `ConfChangeIM`, `enterJointOf`): the part does not translate kvreconf,
whose `Rule` module names its translation.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Base
public import KvNet.Proof.go_etcd_io.raft.v3.InvPbLog
public import KvNet.Proof.go_etcd_io.raft.v3.CCModel
public import Perennial.Ghost.GhostMap

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section conf
variable [GooseExts]

/-- `AsV2`'s answer on a change (kvreconf's `ccToV2`). -/
def ccToV2 : ConfChangeIM → ConfChangeV2M
  | .v1 c => c.asV2
  | .v2 cc => cc

/-- A change's transition is defined for its changes (kvreconf's `ccTransOk`). -/
def ccTransOk (o : ConfChangeIM) : Prop :=
  enterJointOf (ccToV2 o).transition (ccToV2 o).changes.length ≠ none

theorem ccTransOk_v1 (c : ConfChangeM) : ccTransOk (.v1 c) := by
  simp [ccTransOk, ccToV2, ConfChangeM.asV2, enterJointOf]

end conf

/-- The ghost names of a checker: the numbers issued from `nextOp` and from `nextRead`. -/
structure CheckerNames where
  op : GName
  rd : GName

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]

/-- The ghost map of the issued numbers of the counter `w`. -/
def issuedName (γ : CheckerNames) (w : Bool) : GName := if w then γ.rd else γ.op

/-- Every number of `M` is at most `a`. -/
def IssuedLe (M : GMap w64 Unit) (a : w64) : Prop :=
  ∀ k, (M.lookup k).isSome → uint.Z k ≤ uint.Z a

/-- `mu`'s invariant (see the file header). -/
def checkerInv (c : Loc) (γ : CheckerNames) : IProp GF :=
  iprop(∃ (a b : w64) (Ma Mb : GMap w64 Unit) (lc : Loc) (cs : ConfStateM),
    c.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker, go!"nextOp"] ↦ a ∗
    c.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker, go!"nextRead"] ↦ b ∗
    c.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker, go!"lastConf"] ↦ lc ∗
    csOpt lc DFrac.discard cs ∗
    ghostMapAuth γ.op 1 Ma ∗ ghostMapAuth γ.rd 1 Mb ∗ ⌜IssuedLe Ma a ∧ IssuedLe Mb b⌝)

/-- The checker at `c` (see the file header). -/
def isChecker (c : Loc) (γ : CheckerNames) (ls : List GoString) : IProp GF :=
  iprop(∃ (sl : GoSlice),
    c.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker, go!"addrs"] ↦□ sl ∗
    sl ↦*□ ls ∗
    sync.isMutex (c.[github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker, go!"mu"])
      (checkerInv c γ))

instance isChecker_persistent (c : Loc) (γ : CheckerNames) (ls : List GoString) :
    Persistent (isChecker (GF := GF) c γ ls) := by
  unfold isChecker; infer_instance

/-- `fresh` issued `n` from the counter `w` (see the file header). -/
def issued (γ : CheckerNames) (w : Bool) (n : w64) : IProp GF :=
  ghostMapElem (issuedName γ w) n (DFrac.own 1) ()

/-- No number is issued twice from one counter. -/
theorem issued_excl (γ : CheckerNames) (w : Bool) (n : w64) :
    issued (GF := GF) γ w n -∗ issued γ w n -∗ False := by
  unfold issued
  iintro H1 H2
  ihave %h := ghostMapElem_valid_2 n (issuedName γ w) (DFrac.own 1) (DFrac.own 1) () () $$ H1 H2
  exfalso
  have := DFrac.valid_own_op h.1
  simp only [Qp.val_one] at this; exact absurd this (by decide)

end defs

end raft_kvcheck
end EtcdGrove
end Perennial
