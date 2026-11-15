/-
## `(*messageDecoder).decode()`

**Users.** `streamReader.decodeLoop` (the message stream).

**Proof sketch.** `decodeLimit` with the package variable `readBytesLimit`.

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour. verify-round (A8 F8, A5 F4): the encoding is raftpb's `msgEncodes` (was the provisional `pbEncodes`), the frame the transparent `msgFrame`; the message is delivered as `msgRecv` (a fresh message, owned with its `Entries` capacity: what `Process` and raft's `Step` take), was `msgPts` at `own 1`.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

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

/-- (internal) `decodeLimit(readBytesLimit)` (512 MiB). -/
def messageDecoder.decode.spec : Prop :=
  ∀ (dec : Loc) (rd : GoInterface) (Pre Φ : List w8 → IProp GF) (r : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ msgDecAt dec rd ∗ Http.readerAt rd Pre Φ r }}
    (App (Val (dec @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.messageDecoder.ty @!! go!"decode")) (Val #()))
  {{ (ml : Loc) (err : GoInterface), RET (PairV #ml #err); Http.errOk err ∗ ((⌜err = interface.nil⌝ ∗ ∃ (m : Msg) (e : List w8), msgRecv ml m ∗ ⌜RaftPb.msgEncodes e m⌝ ∗ Http.readerAt rd Pre Φ (r ++ msgFrame e) ∗ □ Pre (r ++ msgFrame e)) ∨ (⌜err ≠ interface.nil⌝ ∗ ∃ r', Http.readerAt rd Pre Φ r')) }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
