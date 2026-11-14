/-
`proto.Unmarshal(b, rec)` into a blank `*walpb.Record` as `proto.UnmarshalWalRecord.spec`, and of a
failure's error, that it is not `io.EOF` and `errors.Is(err, io.EOF)` answers `false` (`errIsNot`):
**a hypothesis** of the WAL decoder's proof (`decodeRecord`), not proved here and not an axiom.
The trust-boundary axiom it would follow from, `proto.UnmarshalPb.spec`
(`LinuxFs/Proof/google_golang_org/protobuf/proto/UnmarshalPb.lean`), says nothing of the error but that it
is not `nil`; extending it is a trust-base change for the user (`notes/perennial-changes.md`, 2026-11-14,
"`errors.Is` on `fmt.Errorf`'s result", which records it too).
Why it holds in Go (protobuf-go v1.36, `proto/decode.go`, `internal/impl/decode.go`,
`encoding/protowire/wire.go`): `Unmarshal` of a byte slice fails with `internal/errors`' errors
(`*prefixError`, `*wrapError` wrapping another of these, which unwrap to `errors.Error`, "protobuf
error"), `protowire.ParseError`'s (`io.ErrUnexpectedEOF`, `errors.New` values of `internal/errors`), or
`errors.RequiredNotSet`: none is `io.EOF` or wraps it, since nothing reads an `io.Reader`.
W3a of `notes/wal-fsext-plan.md` (ledger 2026-11-14, "the error's identity"); Lean-first.
-/
module

public import LinuxFs.Spec.google_golang_org.protobuf.proto.UnmarshalWalRecord
public import LinuxFs.Spec.fmt.ErrorfErrsNot

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
abbrev proto.UnmarshalWalRecordE.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (dq : DFrac) (l : Loc) (t : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ b ↦*{dq} bs ∗
      (pbRecordC (GF := GF)).data.blank l ∗ globalAddr _root_.Perennial.io.EOF ↦□ t }}
    (App (App (Val (@! google_golang_org.protobuf.proto.Unmarshal)) (Val #b))
      (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.ty) #l)))
  {{ (err : GoInterface), RET #err; b ↦*{dq} bs ∗
      ((∃ r, ⌜err = GoInterface.nil ∧ walCodec.decRec bs = some r⌝ ∗ ownRec l r) ∨
       ⌜err ≠ GoInterface.nil ∧ UFail walCodec bs⌝ ∗ errIsNot err t) }}

end spec

end EtcdGrove
end Perennial
