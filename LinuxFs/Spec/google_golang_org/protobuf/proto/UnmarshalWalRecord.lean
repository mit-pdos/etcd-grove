/-
`proto.Unmarshal(b, rec)` into a blank `*walpb.Record` (the registered instance's `blank`,
`PbRecord.lean`), the form the decoder needs (decoder.go:125): it returns `nil` and the record is
the canonical decoding of `b` (`recDecode`, the codec's `decRec`), owned (`ownRec`, its `Data` a
fresh slice); or it returns an error, and then `b` is no record's encoding (`UFail`: the weaker
model of W3a, 2026-11-13; the record is not given back). `b` is read, not kept.
Derived from `proto.UnmarshalPb.spec` at the registration (`LinuxFs/Proof/google_golang_org/protobuf/proto/UnmarshalWalRecord.lean`).
W3a of `notes/wal-fsext-plan.md`; Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.walpb.Defs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Codec
public import LinuxFs.Proof.google_golang_org.protobuf.proto.PkgInit
public import Proof.go_etcd_io.etcd.server.v3.storage.WalEncDecoder

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

/-- See the file header. -/
abbrev proto.UnmarshalWalRecord.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (dq : DFrac) (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ b ↦*{dq} bs ∗
      (pbRecordC (GF := GF)).data.blank l }}
    (App (App (Val (@! google_golang_org.protobuf.proto.Unmarshal)) (Val #b))
      (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.ty) #l)))
  {{ (err : GoInterface), RET #err; b ↦*{dq} bs ∗
      ((∃ r, ⌜err = GoInterface.nil ∧ walCodec.decRec bs = some r⌝ ∗ ownRec l r) ∨
       ⌜err ≠ GoInterface.nil ∧ UFail walCodec bs⌝) }}

end spec

end EtcdGrove
end Perennial
