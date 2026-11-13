/-
`checkWALNames(lg, names)` (S/util.go:90-106): the names `parseWALName` accepts, in order (the
others logged, unless `.tmp`). `parseWALName` accepts a `.wal` name `%016x-%016x.wal` scans
(`fmt.scanWalName`), rejects one that is not `.wal` or does not scan; `fmt.Sscanf`'s model leaves
some inputs undecided (`.unknown`), so the result is pinned only on the names that scan or fail
(`walNameMay`, `walNameParses`). Proved in
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/checkWALNames.lean`. W5 of
`notes/wal-fsext-plan.md`; Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.parseWALName
public import Spec.go_uber_org.zap.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section pure
variable [GooseExts]

/-- **`parseWALName` accepts `b`** (`.wal` and scanning). -/
def walNameParses (b : GoString) : Prop := go!".wal" <:+ b ∧ ∃ x y, fmt.scanWalName b = .ok x y

/-- **`parseWALName` may accept `b`** (`.wal`, and not refused by the scan). -/
def walNameMay (b : GoString) : Prop := go!".wal" <:+ b ∧ fmt.scanWalName b ≠ .err

theorem walNameParses_may {b : GoString} (h : walNameParses b) : walNameMay b := by
  obtain ⟨h1, x, y, h2⟩ := h
  exact ⟨h1, by rw [h2]; simp⟩

theorem walNameParses_walNameStr (s i : w64) : walNameParses (fmt.walNameStr s i) :=
  ⟨⟨fmt.hexPad 16 (uint.nat s) ++ W8 45 :: fmt.hexPad 16 (uint.nat i), by simp [fmt.walNameStr]⟩,
    s, i, fmt.scanWalName_walNameStr s i⟩

/-- **`checkWALNames`' result `ws` from `names`**: an order-preserving selection holding every name
that parses and only names that may. -/
def WalNamesSel (names ws : List GoString) : Prop :=
  ws.Sublist names ∧ (∀ b ∈ ws, walNameMay b) ∧ (∀ b ∈ names, walNameParses b → b ∈ ws)

end pure

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.checkWALNames.spec : Prop :=
  ∀ (lg : Loc) (sl : GoSlice) (names : List GoString) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ zapLoggerOk lg ∗
      sl ↦*{dq} names }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.checkWALNames)) (Val #lg)) (Val #sl))
  {{ (r : GoSlice), RET #r; sl ↦*{dq} names ∗ ∃ ws, ⌜WalNamesSel names ws⌝ ∗ r ↦* ws }}

end spec

end EtcdGrove
end Perennial
