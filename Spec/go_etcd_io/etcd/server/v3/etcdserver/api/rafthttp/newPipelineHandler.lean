/-
`newPipelineHandler(t, r, cid)` (`http.go`; rafthttp stage 6c, `Transport.Handler`). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.pipelineHandler__ServeHTTP

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`newPipelineHandler(t, r, cid)`** of a transport whose logger is set and whose member `lid`
owns `a`, `r` its `Raft` (borrowing `Rs` per call), `addRemoteFromRequest` of the transport
returning: a pipeline handler of `a` (`pipeHandlerOk`). -/
abbrev rafthttp.newPipelineHandler.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (a : GoString) (γd : GName) (Rs : IProp GF) (t : Loc) (r : GoInterface)
    (cid : go_etcd_io.etcd.client.pkg.v3.types.ID) (lg : Loc) (lid : w64),
  lg ≠ null → Rh.owner a = lid →
  {{ t.[rafthttp.Transport, go!"Logger"] ↦□ lg ∗ t.[rafthttp.Transport, go!"ID"] ↦□ lid ∗
      □ netRaftOk Rh.γn lid γd Rs r ∗
      □ (∀ (r' : Loc) (R : http.HReq) (rd : GoInterface),
        {{ http.reqAt r' R rd ∗ ⌜fromOkAt Rh lid R.hdr⌝ }}
          (App (App (Val (@! rafthttp.addRemoteFromRequest))
            (Val #(interface.mkOk (go.GoType.PointerType rafthttp.Transport.ty) #t))) (Val #r'))
        {{ RET #(); True }}) }}
    (App (App (App (Val (@! rafthttp.newPipelineHandler)) (Val #t)) (Val #r)) (Val #cid))
  {{ (h : GoInterface), RET #h; ∃ hl : Loc,
      ⌜h = interface.mkOk (go.GoType.PointerType rafthttp.pipelineHandler.ty) #hl⌝ ∗
      pipeHandlerOk Rh a γd Rs hl }}

end spec

end EtcdGrove
end Perennial
