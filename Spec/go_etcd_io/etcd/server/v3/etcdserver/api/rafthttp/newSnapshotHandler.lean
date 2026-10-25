/-
`newSnapshotHandler(t, r, snapshotter, cid)` (`http.go`; rafthttp stage 6c, `Transport.Handler`;
the trust boundary until stage 7e). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.snapshotHandler__ServeHTTP

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

/-- **`newSnapshotHandler(t, r, ss, cid)`** of a transport whose logger is set and whose member
`lid` owns `a`, `r` its `Raft` (borrowing `Rs` per call), the snapshotter `ss` and its directory,
`addRemoteFromRequest` of the transport returning: a snapshot handler of `a` (`snapHandlerOk`; as
`newPipelineHandler`'s; 2026-10-25, stage 7e: was a handler of the snapshot path, lending `R` and
any `T`, at the trust boundary). -/
abbrev rafthttp.newSnapshotHandler.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (a : GoString) (γd : GName) (Rs : IProp GF) (t : Loc) (r : GoInterface)
    (ss : Loc) (cid : go_etcd_io.etcd.client.pkg.v3.types.ID) (lg : Loc) (lid : w64)
    (Rm : w64 → IProp GF),
  lg ≠ null → Rh.owner a = lid →
  {{ t.[rafthttp.Transport, go!"Logger"] ↦□ lg ∗ t.[rafthttp.Transport, go!"ID"] ↦□ lid ∗
      □ netRaftOk Rh.γn lid γd Rs r ∗
      snap.isSnapshotter ss ∗ inv snapDirN (snapDirInv ss γd Rh.γn.N.img Rm) ∗
      □ (∀ (r' : Loc) (R' : http.HReq) (rd : GoInterface),
        {{ http.reqAt r' R' rd ∗ ⌜fromOkAt Rh lid R'.hdr⌝ }}
          (App (App (Val (@! rafthttp.addRemoteFromRequest))
            (Val #(interface.mkOk (go.GoType.PointerType rafthttp.Transport.ty) #t))) (Val #r'))
        {{ RET #(); True }}) }}
    (App (App (App (App (Val (@! rafthttp.newSnapshotHandler)) (Val #t)) (Val #r)) (Val #ss))
      (Val #cid))
  {{ (h : GoInterface), RET #h; ∃ hl : Loc,
      ⌜h = interface.mkOk (go.GoType.PointerType rafthttp.snapshotHandler.ty) #hl⌝ ∗
      snapHandlerOk Rh a γd Rs hl }}

end spec

end EtcdGrove
end Perennial
