/-
`d.Decode(rec)` (decoder.go:81-86) as a reader looping to the end needs it (`ReadAll`, S/wal.go:523-611;
W3/W5 of `notes/wal-fsext-plan.md`, fourteenth session): `decPost`, and of the error returned,
`errors.Is(err, io.EOF)`'s answer (`isEofAns`) and that `io.EOF` itself is returned only at the end
(`goDecode`'s `.eof` stop). `decPost` does not give either: `stopErr`'s catch-all (`e ≠ nil`) allows `io.EOF`
for a bad frame, after which `ReadAll` would take a stop in the middle of the WAL for its end and succeed with
records missing; and `isEofOk` answers `errors.Is` only on `nil`, `io.EOF`, `io.ErrUnexpectedEOF` and the
readers' errors, not on the decoder's own (`fmt.Errorf`'s, `proto.Unmarshal`'s). Ledger,
`notes/specs-only/ledger.md`, 2026-11-14, "`decoder.Decode.spec`: the error's identity". A hypothesis of
`WAL.ReadAll.wp_proof` until `Decode.spec` (and `decodeRecord.spec`) give it. Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__Decode

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
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- **`errors.Is(e, io.EOF)` answers whether `e` is `io.EOF`** (persistent). -/
def WalFs.isEofAns (e eof : GoInterface) : IProp GF :=
  iprop(□ {{ (True : IProp GF) }}
      (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #e)) (Val #eof))
    {{ (b : Bool), RET #b; ⌜b = decide (e = eof)⌝ }})

instance WalFs.isEofAns_persistent (e eof : GoInterface) : Persistent (WalFs.isEofAns (GF := GF) e eof) := by
  unfold WalFs.isEofAns; infer_instance

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.decoder.Decode.specR : Prop :=
  ∀ (C : WalCodec) (d rp : Loc) (IoE : GoInterface → Prop) (eof ueof : GoInterface)
    (fs : List (DecFile GF)) (off : Nat) (c : w32),
  C = walCodec →
  {{ decEnv IoE eof ueof ∗ ownDecoder d IoE eof fs off c true ∗ ownRecAny rp }}
    (App (Val (d @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.decoder.ty @!! go!"Decode")) (Val #rp))
  {{ (err : GoInterface), RET #err; decPost C d rp IoE eof ueof fs off c err ∗
      ⌜err = eof → ∃ fs' off' c', goDecode C (fs.map (·.bs)) off c = .stop .eof fs' off' c'⌝ ∗
      (⌜err = GoInterface.nil⌝ ∨ WalFs.isEofAns err eof) }}

end spec

end EtcdGrove
end Perennial
