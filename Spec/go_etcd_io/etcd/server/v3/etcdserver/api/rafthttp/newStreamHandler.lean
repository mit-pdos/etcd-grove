/-
`newStreamHandler(t, pg, r, id, cid)` (`http.go`; rafthttp stage 6c, `Transport.Handler`).
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamHandler__ServeHTTP

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`newStreamHandler(t, pg, r, id, cid)`** of a transport whose logger is set and whose id is
`id`, the member owning `a`; `r` its `Raft`, `pg` a peer getter (`Get`, borrowing `Rs`), the
transport's `AddRemote` returning: a stream handler of `a` (`streamHandlerOk`). -/
abbrev rafthttp.newStreamHandler.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (a : GoString) (γd : GName) (Rs : IProp GF) (t : Loc) (gi : GoInterfaceOk)
    (r : GoInterface) (id cid : go_etcd_io.etcd.client.pkg.v3.types.ID) (lg : Loc),
  lg ≠ null → Rh.owner a = id →
  {{ t.[rafthttp.Transport, go!"Logger"] ↦□ lg ∗ t.[rafthttp.Transport, go!"ID"] ↦□ id ∗
      □ netRaftOk Rh.γn id γd Rs r ∗
      □ (∀ pid : w64, {{ Rs }}
          (App (Val #(methods gi.ty go!"Get" gi.v)) (Val #pid))
        {{ (pi : GoInterface), RET #pi; Rs ∗ (⌜pi = GoInterface.nil⌝ ∨
            ∃ pl : Loc, ⌜pi = interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #pl⌝ ∗
              peerStreams Rh id pid pl) }}) ∗
      □ (∀ (pid : w64) (sl : GoSlice) (us : List GoString),
        {{ sl ↦* us ∗ ⌜Rh.member pid ∧ pid ≠ id⌝ }}
          (App (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"AddRemote"))
            (Val #pid)) (Val #sl))
        {{ RET #(); True }}) ∗
      globalAddr rafthttp.RaftStreamPrefix ↦□ go!"/raft/stream" }}
    (App (App (App (App (App (Val (@! rafthttp.newStreamHandler)) (Val #t))
      (Val #(GoInterface.ok gi))) (Val #r)) (Val #id)) (Val #cid))
  {{ (h : GoInterface), RET #h; ∃ hl : Loc,
      ⌜h = interface.mkOk (go.GoType.PointerType rafthttp.streamHandler.ty) #hl⌝ ∗
      streamHandlerOk Rh a γd Rs hl }}

end spec

end EtcdGrove
end Perennial
