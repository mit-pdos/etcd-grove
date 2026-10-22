/-
`(*messageDecoder).decodeLimit(numBytes)` (`msg_codec.go`): rafthttp's message decoder, the
pipeline handler's and the `streamTypeMessage` stream reader's. Lean-first; the vocabulary:
`rafthttp/Codec.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Codec

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`dec.decodeLimit(numBytes)`** from the decoder's reader `r` at the bytes `rs` (a limit below
`2^63`, as `int(l)` needs): the reader at some bytes `rs'` and, if the error is nil, `rs'` is `rs`
followed by the frame of an encoding `bs` of a message `st` (no longer than the limit), what is
known of `rs'` (`B`), and the decoded message, owned, at `ml`. -/
abbrev rafthttp.messageDecoder.decodeLimit.spec : Prop :=
  ∀ (dec : Loc) (r : GoInterface) (Rd B : List w8 → IProp GF) (rs : List w8) (numBytes : w64),
  uint.Z numBytes < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      dec.[go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.messageDecoder, go!"r"] ↦□ r ∗
      readFullAt r Rd B ∗ Rd rs }}
    (App (Val (dec @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.messageDecoder.ty @!! go!"decodeLimit"))
      (Val #numBytes))
  {{ (ml : Loc) (err : GoInterface), RET (PairV #ml #err);
      ∃ rs' : List w8, Rd rs' ∗
        (⌜err = GoInterface.nil⌝ -∗ ∃ (bs : List w8) (st : MsgSt),
          ⌜rs' = rs ++ msgFrame bs ∧ bs.length ≤ uint.Z numBytes ∧ MsgWireOk st bs⌝ ∗
          □ B rs' ∗ msgPtsC ml (DFrac.own 1) (DFrac.own 1) true st) }}

end spec

end EtcdGrove
end Perennial
