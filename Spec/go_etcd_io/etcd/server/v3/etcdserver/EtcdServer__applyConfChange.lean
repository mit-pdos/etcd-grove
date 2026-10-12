/-
`(*EtcdServer).applyConfChange(cc, ep, shouldApplyV3)` (server.go): the trust boundary for
what a membership change writes. Lean-first (no Rocq counterpart); see `InvApplier.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The membership change's contract.** `s.applyConfChange(cc, ep, v3)` validates the
change `cc` and applies it to the cluster (`s.cluster`, whose backend is the server's: the
batch lock `E.P` with the post-lock hook `E.f`: the environment `E` of `s.uberApply`,
`apply.applierFor`), to raft and to
`ep.confState`. For `v3` (`ApplyBoth`) its writes to the backend happen in one critical
section of the batch lock, after the hook (as `apply.Apply`'s: the caller's hook triple and
writes update), or, if the validation fails, there are none and it stores the applying index
`(i, t)` into the consistent index `s.consistIndex = ci` (the caller's triple for that store,
`Pre -∗ WP ci.SetConsistentIndex(i, t) {Adv}`). Without `v3` it writes nothing to the backend.
It may change `cc` (it sets `NodeId` on a failed validation), but not its `Id`. -/
abbrev EtcdServer.applyConfChange.spec : Prop :=
  ∀ (s cc ep : Loc) (v : raftpb.ConfChange) (cs : Loc) (v3 : Bool) (ci : Loc) (ua : GoInterface)
    (E : apply.AEnv GF) (Pre Q Post Adv : IProp GF) (i t : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvCIAddr s ↦□ ciIface ci ∗ srvUberApplyAddr s ↦□ ua ∗ apply.applierFor ua E ∗
      cc ↦ v ∗ epConfStateAddr ep ↦ cs ∗
      (if v3 then iprop(□ ({{ E.P ∗ Pre }} (App (Val E.f) (Val #())) {{ RET #(); Q }}) ∗
          (Q ={⊤}=∗ E.P ∗ Post) ∗
          (Pre -∗ WP (App (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!!
            go!"SetConsistentIndex")) (Val #i)) (Val #t)) {{ _v, Adv }}))
       else iprop(True)) ∗ Pre }}
    (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyConfChange"))
      (Val #cc)) (Val #ep)) (Val #v3))
  {{ (removed : Bool) (err : GoInterface), RET (PairV #removed #err);
      (∃ (v' : raftpb.ConfChange) (cs' : Loc), cc ↦ v' ∗ ⌜v'.Id' = v.Id'⌝ ∗
        epConfStateAddr ep ↦ cs') ∗
      (if v3 then iprop(Post ∨ Adv) else Pre) }}

end spec

end EtcdGrove
end Perennial
