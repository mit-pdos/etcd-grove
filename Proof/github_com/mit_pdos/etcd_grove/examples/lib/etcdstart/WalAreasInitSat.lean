/- Lean-first (no Rocq counterpart).

# The members' WAL areas premise is satisfiable

`etcdWalAreasInit st Ds` (`WalAreasInit.lean`), the etcd examples' `HWal` premise on the file
extension's start state, holds of `fsRoots (etcdAreaRoots Ds)` (`Robustness/FsStart.lean`): one empty
root per member's WAL area and per data directory, nothing else, whenever each directory of `Ds` is a
member's. A building block of the etcd statements' satisfiability witnesses (`Robustness/PremiseSat.lean`,
`etc/premise-witness.py`); those statements stay in `etc/premise-witness-baseline.txt` for their other
premises (`BootFacts`, the opaque environment propositions). Untrusted: nothing uses it but witnesses.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WalAreasInit
public import Robustness.FsStart

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Robustness

section premise
variable [GooseExts]

/-- The roots of the start state: each data directory's WAL area, then the directory itself. -/
def etcdAreaRoots (Ds : List GoString) : List GoString := Ds.flatMap fun d => [walAreaOf d, d]

/-- **`HWal` holds of the start state with a root per WAL area and per data directory, all empty.** -/
theorem etcdWalAreasInit_fsRoots (Ds : List GoString) (hD : ∀ d ∈ Ds, ∃ n, d = memberDataDir n) :
    etcdWalAreasInit (fsRoots (etcdAreaRoots Ds)) Ds := by
  intro d hd
  refine ⟨hD d hd, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := fsRoots_root (etcdAreaRoots Ds) (r := walAreaOf d)
      (List.mem_flatMap.2 ⟨d, hd, by simp⟩)
    exact ⟨j, hj, fun b _ => fsRoots_entry _ _ _⟩
  · obtain ⟨j, hj⟩ := fsRoots_root (etcdAreaRoots Ds) (r := d) (List.mem_flatMap.2 ⟨d, hd, by simp⟩)
    exact ⟨j, hj, fun b => fsRoots_entry _ _ _⟩

end premise

end EtcdGrove
end Perennial

end
