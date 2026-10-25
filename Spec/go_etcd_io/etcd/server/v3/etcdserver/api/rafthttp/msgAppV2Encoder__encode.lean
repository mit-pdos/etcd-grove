/-
`(*msgAppV2Encoder).encode(m)` (`msgappv2_codec.go`): the encoder of rafthttp's `msgappv2` stream
(the leader's `MsgApp`s to one follower). Lean-first; the model: `rafthttp/MsgAppV2.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.MsgAppV2

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

/-- **`enc.encode(m)`** of a frozen message `st` the encoder may be given on the connection from
`frm` to `to` (`V2EncOk`), the encoder at the state `cs`, its writer at the bytes `h` and permitted
to write any prefix of a frame of `st`'s content from `cs`: it writes such a frame, leading to a
state `cs'`, or returns an error (the writer and the encoder at some bytes and state). -/
abbrev rafthttp.msgAppV2Encoder.encode.spec : Prop :=
  ∀ (enc : Loc) (wi : GoInterfaceOk) (fs : Loc) (cs : V2St) (frm to : w64) (ml : Loc) (st : MsgSt)
    (Wr A : List w8 → IProp GF) (h : List w8),
  V2EncOk frm to st →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      v2EncOwn enc wi fs cs ∗ writerAt wi Wr A ∗ Wr h ∗ msgOwn ml DFrac.discard st ∗
      □ (∀ (bs : List w8) (cs' : V2St) (k : Nat), ⌜V2Frame frm to cs (wireOf st) bs cs'⌝ -∗
          A (h ++ bs.take k)) }}
    (App (Val (enc @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Encoder.ty @!! go!"encode")) (Val #ml))
  {{ (err : GoInterface), RET #err; http.errStrOk err ∗
      ∃ (h' : List w8) (cs' : V2St), Wr h' ∗ v2EncOwn enc wi fs cs' ∗
        (⌜err = GoInterface.nil⌝ -∗ ⌜∃ bs, V2Frame frm to cs (wireOf st) bs cs' ∧ h' = h ++ bs⌝) }}

end spec

end EtcdGrove
end Perennial
