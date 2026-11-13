/-
`proto.Unmarshal(b, rec)` into a zero `*walpb.Record`: **a hypothesis** of the decoder's proofs
(the registration of `walpb.Record` as a protobuf message is on branch `wal-leaf-enc`; this is
the form the decoder needs, to be derived from it): it succeeds exactly when the codec's
`decRec` does (`WalCodec`, `WalEncDecode.lean`), the record then holding `decRec`'s record, its
`Data` a fresh slice; `b` is read, not kept.
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
abbrev proto.UnmarshalWalRecord.spec (C : WalCodec) : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (dq : DFrac) (l : Loc),
  {{ b ↦*{dq} bs ∗ (l ↦ zero_val go_etcd_io.etcd.server.v3.storage.wal.walpb.Record : IProp GF) }}
    (App (App (Val (@! _root_.Perennial.google_golang_org.protobuf.proto.Unmarshal)) (Val #b))
      (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.ty) #l)))
  {{ (err : GoInterface), RET #err; b ↦*{dq} bs ∗
      ((∃ r, ⌜err = GoInterface.nil ∧ C.decRec bs = some r⌝ ∗ ownRec l r) ∨
       (⌜err ≠ GoInterface.nil ∧ C.decRec bs = none⌝ ∗ ownRecAny l)) }}

end spec

end EtcdGrove
end Perennial
