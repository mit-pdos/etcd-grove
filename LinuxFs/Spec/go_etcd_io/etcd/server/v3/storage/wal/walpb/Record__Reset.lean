/-
`rec.Reset()` of a `*walpb.Record` (record.pb.go, names-only in the part: protobuf plumbing):
**a hypothesis** of the decoder's proofs (no model, no axiom): the record zeroed (`*x =
Record{}`, then the message state's reset, which leaves it the zero value).
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
abbrev go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.Reset.spec : Prop :=
  ∀ (l : Loc),
  {{ ownRecAny (GF := GF) l }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.ty @!! go!"Reset")) (Val #()))
  {{ RET #(); l ↦ zero_val go_etcd_io.etcd.server.v3.storage.wal.walpb.Record }}

end spec

end EtcdGrove
end Perennial
