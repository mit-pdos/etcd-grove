/-
`(*streamWriter).closeUnlocked` (`stream.go`; rafthttp stage 5b). Lean-first; the writer's predicates:
`rafthttp/Writer.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Writer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`cw.closeUnlocked()`** with `mu` held (the fields whole: `run`'s halves and the lock's): if
working, closes the connection, giving it `Q` (`closeRight`), and reports the peer unreachable if
messages were queued (with one of the `Raft`'s resources `Rr`); then a fresh `msgc` (a new bag),
not working; returns whether it was. -/
abbrev rafthttp.streamWriter.closeUnlocked.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (ty : StreamTy) (lid pid : w64) (Rr : IProp GF) (cw : Loc) (mc : GoChan)
    (γm : ChanNames) (wk : Bool) (cl : GoInterface) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      swFixed Rh ty lid pid Rr cw ∗
      cw.[rafthttp.streamWriter, go!"msgc"] ↦ mc ∗ cw.[rafthttp.streamWriter, go!"working"] ↦ wk ∗
      cw.[rafthttp.streamWriter, go!"closer"] ↦ cl ∗ isChanBag γm mc (swMsg Rh ty lid pid) ∗
      (if wk then iprop(closeRight cl Q ∗ Q) else iprop(True)) ∗ Rr }}
    (App (Val (cw @!! go.GoType.PointerType rafthttp.streamWriter.ty @!! go!"closeUnlocked")) (Val #()))
  {{ (b : Bool), RET #b; ⌜b = wk⌝ ∗ Rr ∗ ∃ (mc' : GoChan) (γm' : ChanNames),
      cw.[rafthttp.streamWriter, go!"msgc"] ↦ mc' ∗ cw.[rafthttp.streamWriter, go!"working"] ↦ false ∗
      cw.[rafthttp.streamWriter, go!"closer"] ↦ cl ∗ isChanBag γm' mc' (swMsg Rh ty lid pid) }}

end spec

end EtcdGrove
end Perennial
