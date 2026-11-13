/-
`searchIndex(lg, names, index)` (S/util.go:47-61): the last position of `names` whose name's index
(`walNameIdx`) is at most `index`, or `(-1, false)`. Over a WAL directory's names, each a segment's
(`fmt.walNameStr`), so `parseWALName` succeeds and the `lg.Panic` is unreachable. Proved in
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/searchIndex.lean`. W5 of
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

/-- The index of a WAL file name (`parseWALName`'s second result on a name that scans). -/
def walNameIdx (n : GoString) : w64 :=
  match fmt.scanWalName n with
  | .ok _ i => i
  | _ => 0

/-- The last position below `k` whose index is at most `index`. -/
def walSearchFrom (idxs : List w64) (index : w64) : Nat → Option Nat
  | 0 => none
  | k + 1 => if uint.Z (idxs.getD k 0) ≤ uint.Z index then some k else walSearchFrom idxs index k

/-- `searchIndex`'s result: the last position whose index is at most `index`. -/
def walSearch (idxs : List w64) (index : w64) : Option Nat := walSearchFrom idxs index idxs.length

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.searchIndex.spec : Prop :=
  ∀ (lg : Loc) (sl : GoSlice) (names : List GoString) (dq : DFrac) (index : w64),
  (∀ n ∈ names, ∃ s i, n = fmt.walNameStr s i) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ sl ↦*{dq} names }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.searchIndex)) (Val #lg))
      (Val #sl)) (Val #index))
  {{ RET (PairV #(match walSearch (names.map walNameIdx) index with
                  | some k => W64 (k : Int) | none => W64 (-1))
          #((walSearch (names.map walNameIdx) index).isSome));
      sl ↦*{dq} names }}

end spec

end EtcdGrove
end Perennial
