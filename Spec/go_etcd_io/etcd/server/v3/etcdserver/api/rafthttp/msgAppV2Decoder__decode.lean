/-
## `(*msgAppV2Decoder).decode()`

**Users.** `streamReader.decodeLoop` (the msgappv2 stream).

**Proof sketch.** `io.ReadFull` of the tag; a heartbeat: a clone of `linkHeartbeatMessage`; `AppEntries`: the count, each entry's size and bytes (`MustUnmarshalMessage`: `v2Compat` says they are an encoder's), the commit, the message rebuilt from the state; a full frame: `binary.Read`, the bytes, `MustUnmarshalMessage`, the state; another tag: `fmt.Errorf`. `v2Compat` is only an obligation of the reader's protocol (`raftProto`'s stream response), never of untrusted input.

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rafthttp

open Iris Iris.BI Raft
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) **Reads one msgappv2 frame**, the bytes being an encoder's (`v2Compat`: the decoder allocates and unmarshals what the stream says, `nonissues/etcd-rafthttp-msgappv2-unbounded-lengths.md`): a fresh message of the frame and the next state, or an error. -/
def msgAppV2Decoder.decode.spec : Prop :=
  ∀ (dec : Loc) (rd : GoInterface) (src dst : w64) (st : w64 × w64) (Pre Φ : List w8 → IProp GF) (r : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ v2DecAt dec rd src dst st ∗ Http.readerAt rd Pre Φ r ∗ □ (∀ ys, Pre (r ++ ys) -∗ ⌜v2Compat st src dst ys⌝) }}
    (App (Val (dec @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Decoder.ty @!! go!"decode")) (Val #()))
  {{ (ml : Loc) (err : GoInterface), RET (PairV #ml #err); Http.errOk err ∗ ((⌜err = interface.nil⌝ ∗ ∃ (m : Msg) (fb : List w8) (st' : w64 × w64), msgPts ml (DFrac.own 1) m ∗ ⌜v2Frame st src dst m fb st'⌝ ∗ v2DecAt dec rd src dst st' ∗ Http.readerAt rd Pre Φ (r ++ fb) ∗ □ Pre (r ++ fb)) ∨ (⌜err ≠ interface.nil⌝ ∗ ∃ r' st', v2DecAt dec rd src dst st' ∗ Http.readerAt rd Pre Φ r')) }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
