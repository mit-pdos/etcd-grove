/-
`readInt64(r)` (decoder.go:230-234) of a reader read as a stream: `binary.Read` of an `int64`,
little-endian, which is one `io.ReadFull` of 8 bytes: the bytes `ys` it delivered and its error
(`io.readFullRes`, with the reader's error evidence), the value their little-endian word when it succeeded. Proved in
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/readInt64.lean`.
W3a of `notes/wal-fsext-plan.md`; Lean-first.
-/
module

public import LinuxFs.GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal
public import Proof.io.ReaderStream
public import Perennial.Proof.encoding.binary.Base
public import LinuxFs.Proof.bufio.PkgInit

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
variable [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.readInt64.spec : Prop :=
  ∀ (ri : GoInterfaceOk) (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF)
    (r0 : List w8) (eof ueof : GoInterface),
  ⊢ io.readerStream ri S E -∗
    {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
        globalAddr _root_.Perennial.io.EOF ↦□ eof ∗
        globalAddr _root_.Perennial.io.ErrUnexpectedEOF ↦□ ueof ∗ ⌜r0.length + 8 < 2 ^ 62⌝ ∗ S r0 }}
      (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.readInt64)) (Val #(GoInterface.ok ri)))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ ys : List w8, io.readFullRes E eof ueof r0 ys 8 err ∗
          ⌜err = GoInterface.nil → n = leToU64 ys⌝ ∗ S (r0 ++ ys) }}

end spec

end EtcdGrove
end Perennial
