/- Lean-first (no Rocq counterpart).

# A purge's client commit (unit `locks`, session 9; `notes/wal-units/locks.md`)

`walPurgeAcc dir Pc`: the caller's **repeatable commit** for the removals of a purge round of the WAL in
`dir` (session 4's shape): with its token `Pc`, an atomic accessor to `walDiskAt dir d` (aborted back to
`Pc`) committing `pur` raised to some `p` and the read position moved to some `k` with `d.cut ≤ k ≤ p ≤
d.unl`, giving `Pc` back. Persistent, so a round commits once per removal: each removal moves the WAL's
read position (`WalAbsD.cut`: the first named segment's start), so one atomic update for the round does
not fit. The tester supplies it from its invariant (`notes/wal-units/locks.md`, session 5: its oracle
covers any such purge once every candidate's `pur` is raised to its `unl`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **A purge's repeatable client commit** (see the file header). -/
def walPurgeAcc (dir : GoString) (inc : Nat) (Pc : IProp GF) : IProp GF :=
  iprop(□ (Pc -∗ AACC <{ ∃∃ d : WalDur, walDiskAtI (W := W) dir inc d, ABORT Pc }> @ walAuMask, ∅
    <{ ∀∀ (p k : Nat), ⌜d.cut ≤ k ∧ k ≤ p ∧ p ≤ d.unl⌝ ∗
        walDiskAtI (W := W) dir inc { d with pur := max d.pur p, cut := k }, COMM Pc }>))

instance walPurgeAcc_persistent (dir : GoString) (inc : Nat) (Pc : IProp GF) :
    Persistent (walPurgeAcc (W := W) dir inc Pc) := by
  unfold walPurgeAcc; infer_instance

end defs

end WalFs
end EtcdGrove
end Perennial

end
