/-
`rec.GetType()` (record.pb.go, translated): the record's type. Proved in
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/walpb/Record__GetType.lean`.
W3a of `notes/wal-fsext-plan.md`; Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.walpb.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open WalEnc WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.walpb.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.GetType.spec : Prop :=
  ∀ (l : Loc) (r : WalRec),
  {{ ownRec (GF := GF) l r }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.ty @!! go!"GetType")) (Val #()))
  {{ RET #r.typ; ownRec l r }}

end spec

end EtcdGrove
end Perennial
