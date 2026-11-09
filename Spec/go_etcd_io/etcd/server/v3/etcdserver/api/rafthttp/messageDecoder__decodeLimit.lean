/-
## `(*messageDecoder).decodeLimit(numBytes)`

**Users.** `messageDecoder.decode`, `snapshotHandler.ServeHTTP` (64 MiB).

**Proof sketch.** `binary.Read` of a `uint64`, the bound check, `make([]byte, l)` (at most `n`, below `2^63`), `io.ReadFull` (Perennial's `io`, over `Http.readerAt_read`), `proto.Unmarshal` (3h: success gives a message `e` encodes). `Pre` of the bytes read lets the caller identify the frame (frames are self-delimiting).

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

/-- (internal) **Reads one message frame** of at most `n` bytes: a fresh message decoded from the frame's bytes, or an error (a frame too long: `ErrExceedSizeLimit`; a short read; an unmarshal error). -/
def messageDecoder.decodeLimit.spec : Prop :=
  ∀ (dec : Loc) (rd : GoInterface) (Pre Φ : List w8 → IProp GF) (r : List w8) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ msgDecAt dec rd ∗ Http.readerAt rd Pre Φ r }}
    (App (Val (dec @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.messageDecoder.ty @!! go!"decodeLimit")) (Val #n))
  {{ (ml : Loc) (err : GoInterface), RET (PairV #ml #err); Http.errOk err ∗ ((⌜err = interface.nil⌝ ∗ ∃ (m : Msg) (e : List w8), msgPts ml (DFrac.own 1) m ∗ ⌜pbEncodes e m⌝ ∗ Http.readerAt rd Pre Φ (r ++ msgFrame e) ∗ □ Pre (r ++ msgFrame e)) ∨ (⌜err ≠ interface.nil⌝ ∗ ∃ r', Http.readerAt rd Pre Φ r')) }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
