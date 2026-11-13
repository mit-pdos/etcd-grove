/-
`rec.Reset()` of a `*walpb.Record` (record.pb.go, names-only in the part: protobuf plumbing):
**a hypothesis** of the decoder's proofs (no model, no axiom; its body, `*x = Record{}` then
`protoimpl.X.MessageStateOf(x).StoreMessageInfo(...)`, is the protobuf runtime plumbing the
configuration leaves out on purpose): a record owned whole is left blank, as the registered
`walpb.Record` instance's `blank` says (`PbRecord.lean`: what `proto.Unmarshal` takes), whatever
the message state then holds (2026-11-13).
W3a of `notes/wal-fsext-plan.md`; Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.walpb.Defs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.walpb.PbRecord

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
  {{ RET #(); (pbRecordC (GF := GF)).data.blank l }}

end spec

end EtcdGrove
end Perennial
