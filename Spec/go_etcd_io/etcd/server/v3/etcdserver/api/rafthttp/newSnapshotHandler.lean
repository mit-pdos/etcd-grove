/-
`newSnapshotHandler(t, r, snapshotter, cid)` (`http.go`, untranslated: the snapshot stream, D22's
contract; rafthttp stage 6c, `Transport.Handler`): the trust boundary (the user's choice: the
snapshot stream a smaller axiom, cut at its own functions). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Stream

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

/-- **`newSnapshotHandler(t, r, ss, cid)`** for the member `lid` owning `a`, its `Raft` `r`
(`netRaftOk`, borrowing `R` per call), the snapshotter `ss` and its directory: a handler of the
requests to `a` routed to the snapshot path, lending each invocation `R` (and anything else, `T`).
`addRemoteFromRequest` of the transport, which it calls, returns (a premise, as the pipeline
handler's). -/
abbrev rafthttp.newSnapshotHandler.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (a : GoString) (γd : GName) (R : IProp GF) (t : Loc) (r : GoInterface)
    (ss : Loc) (cid : go_etcd_io.etcd.client.pkg.v3.types.ID) (lid : w64) (Rm : w64 → IProp GF),
  Rh.owner a = lid →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      t.[rafthttp.Transport, go!"ID"] ↦□ lid ∗ □ netRaftOk Rh.γn lid γd R r ∗
      snap.isSnapshotter ss ∗ inv snapDirN (snapDirInv ss γd Rh.γn.N.img Rm) ∗
      □ (∀ (r' : Loc) (R' : http.HReq) (rd : GoInterface),
        {{ http.reqAt r' R' rd ∗ ⌜fromOkAt Rh lid R'.hdr⌝ }}
          (App (App (Val (@! rafthttp.addRemoteFromRequest))
            (Val #(interface.mkOk (go.GoType.PointerType rafthttp.Transport.ty) #t))) (Val #r'))
        {{ RET #(); True }}) }}
    (App (App (App (App (Val (@! rafthttp.newSnapshotHandler)) (Val #t)) (Val #r)) (Val #ss))
      (Val #cid))
  {{ (h : GoInterface), RET #h;
      □ ∀ (T : IProp GF) (pats : List GoString),
        http.handlerFor (raftHttpNet Rh) a iprop(R ∗ T) pats snapPath h }}

end spec

end EtcdGrove
end Perennial
