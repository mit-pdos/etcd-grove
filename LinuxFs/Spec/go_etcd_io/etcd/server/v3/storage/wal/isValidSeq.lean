/-
`isValidSeq(lg, names)` (S/util.go:63-76): the names' sequence numbers (`walNameSeq`) increase by
one, a zero restarting the check (`walSeqOk 0`, Go's `lastSeq != 0` test). Over a WAL directory's
names, each a segment's (`fmt.walNameStr`), so `parseWALName` succeeds and the `lg.Panic` is
unreachable. Proved in `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/isValidSeq.lean`. W5 of
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

/-- The sequence number of a WAL file name (`parseWALName`'s first result on a name that scans). -/
def walNameSeq (n : GoString) : w64 :=
  match fmt.scanWalName n with
  | .ok s _ => s
  | _ => 0

/-- `isValidSeq`'s loop from the last sequence number `last` (`0`: none checked yet). -/
def walSeqOk : w64 → List w64 → Bool
  | _, [] => true
  | last, s :: ss => if last ≠ 0 ∧ last ≠ s - 1 then false else walSeqOk s ss

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.isValidSeq.spec : Prop :=
  ∀ (lg : Loc) (sl : GoSlice) (names : List GoString) (dq : DFrac),
  (∀ n ∈ names, ∃ s i, n = fmt.walNameStr s i) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ sl ↦*{dq} names }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.isValidSeq)) (Val #lg)) (Val #sl))
  {{ RET #(walSeqOk 0 (names.map walNameSeq)); sl ↦*{dq} names }}

end spec

end EtcdGrove
end Perennial
