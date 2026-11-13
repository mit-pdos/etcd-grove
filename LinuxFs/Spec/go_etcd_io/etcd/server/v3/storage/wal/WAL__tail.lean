/-
`w.tail()` (S/wal.go:1175-1180): the last of `w.locks`, when there is one. Stated for a nonempty
`locks` (every caller's: `Create`'s pre-rename `w` holds one locked file, an open WAL its segments'):
`ls ++ [lt]` gives `lt`. Proved in
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/WAL__tail.lean`. W4 of
`notes/wal-fsext-plan.md`; Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.EncDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec : Prop :=
  ∀ (w : Loc) (locks : GoSlice) (ls : List Loc) (lt : Loc) (dq1 dq2 : DFrac),
  {{ (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦{dq1} locks ∗
      locks ↦*{dq2} (ls ++ [lt]) : IProp GF) }}
    (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.WAL.ty @!!
      go!"tail")) (Val #()))
  {{ RET #lt; structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦{dq1} locks ∗
      locks ↦*{dq2} (ls ++ [lt]) }}

end spec

end EtcdGrove
end Perennial
