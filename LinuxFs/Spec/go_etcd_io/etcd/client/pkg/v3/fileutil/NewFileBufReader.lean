/-
`NewFileBufReader(fr)` (client/pkg/fileutil/filereader.go, with the local fork fix
`notes/wal-fsext-fork/0001-*.patch`): a fresh `*FileBufReader` over a fresh `bufio.Reader` of `fr`
(a stream reader, `bufio.NewReader`'s spec) and what `fr.FileInfo()` returned (`Q`, the client's
triple for it, from any state of the stream, which it keeps: an `*os.File`'s `Stat` needs the
file's resources), kept as it is: a failed `FileInfo` is no longer a panic. Proved in `LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/NewFileBufReader.lean`.
W3a of `notes/wal-fsext-plan.md`; Lean-first.
-/
module

public import LinuxFs.GeneratedProof.go_etcd_io.etcd.client.pkg.v3.fileutil
public import LinuxFs.Proof.bufio.Defs

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
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.NewFileBufReader.spec : Prop :=
  ∀ (ri : GoInterfaceOk) (S : List w8 → IProp GF) (E : List w8 → GoInterface → Prop)
    (r : List w8) (Q : GoInterface → GoInterface → IProp GF),
  ri.ty ≠ go.GoType.PointerType _root_.Perennial.bufio.Reader.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ S r ∗
      (∀ r' : List w8, {{ S r' }} (App (Val #(methods ri.ty go!"FileInfo" ri.v)) (Val #()))
        {{ (fi err : GoInterface), RET (PairV #fi #err); S r' ∗ Q fi err }}) }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.NewFileBufReader)) (Val #(GoInterface.ok ri)))
  {{ (fbr : Loc), RET #fbr; ∃ (b : Loc) (fi err : GoInterface),
      fbr ↦ go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.mk b fi err ∗ bufio.ownReader b ri S E r ∗ Q fi err }}

end spec

end EtcdGrove
end Perennial
