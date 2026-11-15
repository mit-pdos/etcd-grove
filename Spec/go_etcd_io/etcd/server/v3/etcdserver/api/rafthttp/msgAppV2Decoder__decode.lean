/-
`(*msgAppV2Decoder).decode()` (`msgappv2_codec.go`): the decoder of rafthttp's `msgappv2` stream
(a follower's reading of the leader's `MsgApp`s). Lean-first; the model: `rafthttp/MsgAppV2.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.MsgAppV2

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`dec.decode()`** of the decoder of the connection from `frm` to `to` at the state `cs`, its
reader at the bytes `rs`, any bytes `ys` it may read next being compatible with a frame from `cs`
(`V2Compat`: what is known of them, `B`, says so): the reader at some bytes `rs'` and the decoder
at some state `cs'`, and, if the error is nil, `rs'` is `rs` followed by a frame from `cs` to `cs'`
of some content `w`, what is known of `rs'`, and the decoded message, of content `w`, owned, without
responses (2026-10-23, stage 5c: what `netRecv` asks of a received copy); (raft-entsize §4,
2026-11-10) at its content `c` (`msgPtsCC`), of bounded size when `Sz` but for a link heartbeat (an
App frame's is the sender's content, `MsgEncSz`, by D2; an AppEntries frame's has a fresh header and
the sender's entries' contents, `EntsSz`, by D2 on each). -/
abbrev rafthttp.msgAppV2Decoder.decode.spec : Prop :=
  ∀ (Sz : Prop) (dec : Loc) (r : GoInterface) (frm to : w64) (cs : V2St) (Rd B : List w8 → IProp GF)
    (rs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      v2DecOwn dec r frm to cs ∗ readFullAt r Rd B ∗ Rd rs ∗
      □ (∀ ys : List w8, B (rs ++ ys) -∗ ⌜V2Compat Sz frm to cs ys⌝) }}
    (App (Val (dec @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Decoder.ty @!! go!"decode")) (Val #()))
  {{ (ml : Loc) (err : GoInterface), RET (PairV #ml #err); http.errStrOk err ∗
      ∃ (rs' : List w8) (cs' : V2St), Rd rs' ∗ v2DecOwn dec r frm to cs' ∗
        (⌜err = GoInterface.nil⌝ -∗ ∃ (w : MsgWire) (bs : List w8) (c : MsgC),
          ⌜V2Frame Sz frm to cs w bs cs' ∧ rs' = rs ++ bs ∧ wireOf c.model = w ∧ c.resps = [] ∧
            c.csUfNil ∧ (Sz → ¬ isHB c.model.msg → msgSizeOk c)⌝ ∗ □ B rs' ∗
          msgPtsCC ml (DFrac.own 1) (DFrac.own 1) true c) }}

end spec

end EtcdGrove
end Perennial
