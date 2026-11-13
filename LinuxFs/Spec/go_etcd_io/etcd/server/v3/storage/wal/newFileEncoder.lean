/-
`newFileEncoder(f, prevCrc)` (`server/storage/wal/encoder.go:58-64`): the encoder over the `*os.File`
`f` (as an `io.Writer`, `wal.fileWi f`) at its current offset `o` (`f.Seek(0, io.SeekCurrent)`,
`os.File.Seek.wp_cur`: an open fd, `0 ≤ o ≤` ext4's maximum), its CRC at `prevCrc`, nothing pending;
`f`'s handle and offset are handed back (the client's stream predicate over the file, `W` of
`io.writerStream`, holds the offset; `os.File.writerStream` is the bridge). Seek cannot fail there,
so the error is `nil`; the encoder is a fresh allocation, `e ≠ null` (`w.encoder`'s, which `cut` and
`sync` test). Proved in
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/newFileEncoder.lean`. W6; Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.EncDefs
public import LinuxFs.Proof.os.Off

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open WalEnc WalFs

/-- A `*os.File` as an `io.Writer` (`newFileEncoder`'s conversion). -/
abbrev wal.fileWi [GooseExts] [GoGlobalContext] (f : Loc) : GoInterfaceOk :=
  interface.mk (go.GoType.PointerType os.File.ty) #f

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk]
  [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions] [os.file.FieldAssumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.newFileEncoder.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (o : w64) (prev : w32),
  0 ≤ fd.toInt → 0 ≤ o.toInt → o.toInt ≤ 0xffffffff000 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.ioutil ∗ walCrcTable ∗
      os.ownFile f fd name dqf ∗ os.ownOff f o }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.newFileEncoder)) (Val #f))
      (Val #prev))
  {{ (e : Loc), RET (PairV #e #GoInterface.nil);
      ownEncoder e (wal.fileWi f) prev [] ∗ os.ownFile f fd name dqf ∗ os.ownOff f o ∗ ⌜e ≠ null⌝ }}

end spec

end EtcdGrove
end Perennial
