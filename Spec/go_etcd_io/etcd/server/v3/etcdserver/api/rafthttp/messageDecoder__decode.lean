/-
`(*messageDecoder).decode()` (`msg_codec.go`): rafthttp's message decoder, the
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

/-- **`dec.decode()`**: `decodeLimit(readBytesLimit)`, the limit 512 MiB (rafthttp's package
fact; 2026-10-23, stage 5c). -/
abbrev rafthttp.messageDecoder.decode.spec : Prop :=
  ∀ (dec : Loc) (r : GoInterface) (Rd B : List w8 → IProp GF) (rs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      dec.[go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.messageDecoder, go!"r"] ↦□ r ∗
      readFullAt r Rd B ∗ Rd rs ∗
      □ (∀ bs : List w8, B (rs ++ msgFrame bs) -∗ ⌜bs.length < 2 ^ 63 → ∃ st, MsgWireOk st bs⌝) }}
    (App (Val (dec @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.messageDecoder.ty @!! go!"decode")) (Val #()))
  {{ (ml : Loc) (err : GoInterface), RET (PairV #ml #err); http.errStrOk err ∗
      ∃ rs' : List w8, Rd rs' ∗
        (⌜err = GoInterface.nil⌝ -∗ ∃ (bs : List w8) (st : MsgSt),
          ⌜rs' = rs ++ msgFrame bs ∧ bs.length ≤ 536870912 ∧ MsgWireOk st bs⌝ ∗
          □ B rs' ∗ msgPtsC ml (DFrac.own 1) (DFrac.own 1) true st) }}

end spec

end EtcdGrove
end Perennial
