/-
Lean-first (no Rocq counterpart).

# `run`'s loop invariant (2026-10-30, stage P of the client repair; kvreconf's `runInv`, at kv's
state)

At the top of `run`'s loop, for the delivered log `D` (the committed log applied):
- the node's driver at `D`, handling no `Ready`, and the loop's whole `nodeRunning` (refuting
  `Advance`'s stopped answer, `nodeRunning_stopped`);
- the replicated state at `D` (`runOwn`) and the node's view (`appNode`, at the voters'
  membership: the store's log has no conf entry, `kv_noConf`);
- `applied` at `|D|`; a known compaction point `c` at most `snapIndex` (the latest snapshot taken or
  installed), at most `applied`, with `D` frozen above it (`frozenTo`);
- `reconf` unset (no conf entry is ever applied);
- the pending read states (`rsOk` of each).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.KvRunSnap

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section inv
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- **`run`'s loop invariant** (see the file header); `rp`, `pp`, `ap`, `sp`, `cp` are its `rd`,
`pending`, `applied`, `snapIndex` and `reconf`. -/
def kvRunInv (γr : RKVNames) (r n st : Loc) (γs : MemStorNames) (rp pp ap sp cp : Loc) :
    IProp GF :=
  iprop(∃ (D : List LogEntry) (hd : HardStateM) (rdv : Ready) (pv : GoSlice) (ps : List ReadState)
      (a sI : w64) (c : Nat),
    "Hrd" ∷ rp ↦ rdv ∗
    "Hdrv" ∷ nodeDriver n γr.cluster kvRaftN
      { storage := kvStorIface st, delivered := D, hardState := hd, handling := none } ∗
    "Hrun" ∷ nodeRunning n γr.cluster kvRaftN 1 ∗
    "Hown" ∷ runOwn γr r D ∗
    "Hview" ∷ appNode γr n D D.length kvMembership ∗
    "pending" ∷ pp ↦ pv ∗
    "Hpv" ∷ pv ↦* ps ∗
    "Hpcap" ∷ ownSliceCap ReadState pv (DFrac.own 1) ∗
    "#Hps" ∷ ([∗list] v ∈ ps, rsOk γr.cluster v) ∗
    "applied" ∷ ap ↦ a ∗
    "snapIndex" ∷ sp ↦ sI ∗
    "reconf" ∷ cp ↦ false ∗
    "#Hcp" ∷ memCompacted γs c ∗
    "#Hfz" ∷ frozenTo γs c D ∗
    "%Ha" ∷ ⌜uint.nat a = D.length ∧ c ≤ uint.nat sI ∧ uint.nat sI ≤ uint.nat a⌝)

end inv

end kv
end EtcdGrove
end Perennial
