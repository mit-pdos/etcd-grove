/-
`NewDecoder(r...)` (decoder.go:72-74, `NewDecoderAdvanced(false, r...)`, :60-70): a live decoder
over the files, at offset 0 and CRC 0, each file's `FileBufReader` over its `FileReader` (whose
contract is `decFile`, at the start of its stream). Proved in `LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/NewDecoder.lean`.
W3a of `notes/wal-fsext-plan.md`; Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.DecDefs

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

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.NewDecoder.spec : Prop :=
  ∀ (sl : GoSlice) (fs : List (DecFile GF)) (IoE : GoInterface → Prop) (eof : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ walCrcTable ∗
      sl ↦* fs.map (fun F => GoInterface.ok F.fr) ∗
      [∗list] F ∈ fs, decFile IoE eof F ∗ F.S [] }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.NewDecoder)) (Val #sl))
  {{ (dI : GoInterface), RET #dI; ∃ d : Loc,
      ⌜dI = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.wal.decoder.ty) #d⌝ ∗
      sl ↦* fs.map (fun F => GoInterface.ok F.fr) ∗ ownDecoder d IoE eof fs 0 0#32 true }}

end spec

end EtcdGrove
end Perennial
