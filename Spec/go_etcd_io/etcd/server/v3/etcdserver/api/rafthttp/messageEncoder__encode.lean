/-
`(*messageEncoder).encode(m)` (`msg_codec.go`): rafthttp's message encoder, the pipeline's and
the `streamTypeMessage` stream's. Lean-first; the vocabulary: `rafthttp/Codec.lean`.
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

/-- **`enc.encode(m)`** of a frozen message `st` that marshals, to the encoder's writer `wi` at the
bytes `h`, permitted to write the frame of any encoding of `st` (and its length prefix): the frame
of an encoding of `st` is written, or an error is returned (the writer at some bytes); (2026-10-24,
stage 7d) none if the writer never fails (`writerAtF true`). -/
abbrev rafthttp.messageEncoder.encode.spec : Prop :=
  ∀ (enc : Loc) (wi : GoInterfaceOk) (ml : Loc) (st : MsgSt) (Wr A : List w8 → IProp GF)
    (h : List w8) (nf : Bool),
  MsgMarshals st →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      enc.[go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.messageEncoder, go!"w"] ↦□
        GoInterface.ok wi ∗
      writerAtF nf wi Wr A ∗ Wr h ∗ msgOwn ml DFrac.discard st ∗
      □ (∀ bs : List w8, ⌜MsgWireOk st bs ∧ bs.length < 2 ^ 63⌝ -∗
          A (h ++ u64Be (W64 bs.length)) ∗ A (h ++ msgFrame bs)) }}
    (App (Val (enc @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.messageEncoder.ty @!! go!"encode")) (Val #ml))
  {{ (err : GoInterface), RET #err; http.errStrOk err ∗ ⌜nf = true → err = GoInterface.nil⌝ ∗
      ∃ h' : List w8, Wr h' ∗
        (⌜err = GoInterface.nil⌝ -∗ ∃ bs : List w8, ⌜MsgWireOk st bs ∧ bs.length < 2 ^ 63 ∧ h' = h ++ msgFrame bs⌝) }}

end spec

end EtcdGrove
end Perennial
