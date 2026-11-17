/-
The `cellmint` cell's vocabulary and the Hoare triples of its operations
(`examples/axiomcx/cellmint`). A `Cell` is a `uint64` under a mutex, safe for concurrent use;
these triples are its trust boundary (the axioms are in `Trusted.lean`), as `rate.Limiter`'s and
`bytes.Buffer`'s are.

The cell is named by a pair of ghost names `γ` (`CellNames`): `γ.val` tracks its value, `γ.lock`
its lock. A client sees:
- `cellInv c γ` (persistent): `c` is a cell over `γ`, safe for concurrent use.
- `cellVal γ v`: the cell's current value is `v`, held by the lock holder.
- `availTok γ`: the cell is free to be locked.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint.Base
public import Perennial.Ghost.GhostVar

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The ghost names of a cell: `val` tracks its value, `lock` its lock. -/
structure CellNames where
  val : GName
  lock : GName
deriving DecidableEq

/-- `cellInv`'s fact, raw (opaque). -/
opaque cellInvRaw (c : Loc) (γ : CellNames) : IProp GF

/-- **`c` is a cell over `γ`** (persistent): what `New` returns. A `Cell` is safe for concurrent
use (its operations take its own mutex). -/
def cellInv (c : Loc) (γ : CellNames) : IProp GF := iprop(□ cellInvRaw c γ)

instance cellInv_persistent (c : Loc) (γ : CellNames) : Persistent (cellInv (GF := GF) c γ) := by
  unfold cellInv; infer_instance

/-- **The cell's value is `v`**: the authoritative value, held by whoever holds the lock. -/
def cellVal (γ : CellNames) (v : w64) : IProp GF := ghostVar γ.val 1 v

/-- **The cell is free to be locked.** -/
def availTok (γ : CellNames) : IProp GF := ghostVar γ.lock 1 (() : Unit)

/-- `seen`'s fact, raw (opaque). -/
opaque seenRaw (γ : CellNames) (v : w64) : IProp GF

/-- **The cell was observed to hold `v`** (persistent): a reading of the cell, as `Snapshot` and
`Get` return. Persistent, so a reading can be kept and shared. -/
def seen (γ : CellNames) (v : w64) : IProp GF := iprop(□ seenRaw γ v)

instance seen_persistent (γ : CellNames) (v : w64) : Persistent (seen (GF := GF) γ v) := by
  unfold seen; infer_instance

end defs

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`New()`**: a fresh unlocked cell. -/
abbrev cellmint.New.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint }}
    (App (Val (@! _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint.New)) (Val #()))
  {{ (c : Loc), RET #c; ∃ γ : CellNames, cellInv c γ ∗ availTok γ }}

/-- **`Lock(c)`**: acquire the cell, obtaining its value. Blocks until the cell is free. -/
abbrev cellmint.Lock.spec : Prop :=
  ∀ (c : Loc) (γ : CellNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint ∗
      cellInv c γ ∗ availTok γ }}
    (App (Val (@! _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint.Lock)) (Val #c))
  {{ RET #(); ∃ v : w64, cellVal γ v }}

/-- **`Unlock(c)`**: release the cell. The caller holds the lock. -/
abbrev cellmint.Unlock.spec : Prop :=
  ∀ (c : Loc) (γ : CellNames) (v : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint ∗
      cellInv c γ ∗ cellVal γ v }}
    (App (Val (@! _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint.Unlock)) (Val #c))
  {{ RET #(); availTok γ }}

/-- **`Get(c)`**: read the value under the lock. -/
abbrev cellmint.Get.spec : Prop :=
  ∀ (c : Loc) (γ : CellNames) (v : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint ∗
      cellInv c γ ∗ cellVal γ v }}
    (App (Val (@! _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint.Get)) (Val #c))
  {{ (w : w64), RET #w; ⌜w = v⌝ ∗ cellVal γ v }}

/-- **`Set(c, x)`**: store `x` under the lock. -/
abbrev cellmint.Set.spec : Prop :=
  ∀ (c : Loc) (γ : CellNames) (v x : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint ∗
      cellInv c γ ∗ cellVal γ v }}
    (App (App (Val (@! _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint.Set')) (Val #c)) (Val #x))
  {{ RET #(); cellVal γ x }}

/-- **`Snapshot(c)`**: a lock-free best-effort read of the current value, returning the reading as
a (persistent) `seen`. -/
abbrev cellmint.Snapshot.spec : Prop :=
  ∀ (c : Loc) (γ : CellNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint ∗
      cellInv c γ }}
    (App (Val (@! _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.axiomcx.cellmint.Snapshot)) (Val #c))
  {{ (w : w64), RET #w; ∃ v : w64, ⌜w = v⌝ ∗ seen γ v }}

end specs

end EtcdGrove
end Perennial
