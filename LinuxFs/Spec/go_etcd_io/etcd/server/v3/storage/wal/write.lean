/-
`write(w, uint64buf, data, lenField)` (`server/storage/wal/encoder.go:124-140`), at the encoder's
writer, a `*ioutil.PageWriter` (`ioutil.ownPageWriter`) over a stream writer `wi`
(`io.writerStream wi W`): puts the length word in `uint64buf` (`binary.LittleEndian.PutUint64`),
writes it, then `data`, through the page writer (the metrics in between have no effect the model
sees). On success the page writer has accepted `u64Le lenField ++ data` after its pending bytes; on
an error (the first write's, or the second's) its buffer is dropped and the writer has a prefix of
pending ++ the frame. Premise: `len(data) < 2^62` (`PageWriter.Write`'s). Proved in
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/write.lean`. W6; Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.EncDefs

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

/-- See the file header. -/
abbrev go_etcd_io.etcd.server.v3.storage.wal.write.spec : Prop :=
  ∀ (pw : Loc) (wi : GoInterfaceOk) (W : List w8 → IProp GF) (out pend : List w8)
    (u : GoSlice) (us : List w8) (d : GoSlice) (ds : List w8) (dq : DFrac) (lenField : w64),
  us.length = 8 → ds.length < 2 ^ 62 →
  ⊢ io.writerStream wi W -∗
    {{ encEnv ∗ ioutil.ownPageWriter pw wi pend ∗ W out ∗ u ↦* us ∗ d ↦*{dq} ds }}
      (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.write))
        (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.ioutil.PageWriter.ty)
          #pw))) (Val #u)) (Val #d)) (Val #lenField))
    {{ (err : GoInterface), RET #err;
        ∃ ys pend' : List w8, W (out ++ ys) ∗ ioutil.ownPageWriter pw wi pend' ∗
          u ↦* u64Le lenField ∗ d ↦*{dq} ds ∗
          ⌜(err = GoInterface.nil → ys ++ pend' = pend ++ u64Le lenField ++ ds) ∧
            (err ≠ GoInterface.nil → pend' = [] ∧ ys <+: pend ++ u64Le lenField ++ ds)⌝ }}

end spec

end EtcdGrove
end Perennial
