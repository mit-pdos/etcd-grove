/-
`(*bootstrappedWAL).NewConfigChangeEntries()` (`server/v3/etcdserver/bootstrap.go:755`). Lean-first.

Calls `serverstorage.GetEffectiveNodeIDsFromWALEntries(wal.lg, wal.snapshot, wal.ents)` followed by
`serverstorage.CreateConfigChangeEnts(wal.lg, nodeIDs, wal.meta.nodeID, wal.st.GetTerm(),
wal.st.GetCommit())` to construct the configuration-change entries `ccEnts` at `hs.Term'` with
consecutive indices starting at `hs.Commit' + 1`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBootWAL

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

abbrev bootstrappedWAL.NewConfigChangeEntries.spec : Prop :=
  ∀ (w : Loc) (dq dqs dqe dqm : DFrac) (bw : bootstrappedWAL)
    (sv : SnapshotM) (hs : HardStateM) (es ccEnts : List EntryM) (mv : snapshotMetadata),
  bw.lg' ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      "Hwal" ∷ w ↦{dq} bw ∗
      "Hst" ∷ hsPts bw.st' dqs hs ∗
      "Hents" ∷ entsPts bw.ents' dqe es ∗
      "Hmeta" ∷ bw.meta' ↦{dqm} mv ∗
      "#Hsnap" ∷ snapOptRO bw.snapshot' sv ∗
      "#Hcc" ∷ bootConfChangeEntsOk sv es mv.nodeID' ccEnts }}
    (App (Val (w @!! go.GoType.PointerType bootstrappedWAL.ty @!! go!"NewConfigChangeEntries"))
      (Val #()))
  {{ (cs : GoSlice), RET #cs;
      w ↦{dq} bw ∗
      hsPts bw.st' dqs hs ∗
      entsPts bw.ents' dqe es ∗
      bw.meta' ↦{dqm} mv ∗
      entsPts cs (DFrac.own 1) ccEnts ∗
      ownSliceCap Loc cs (DFrac.own 1) ∗
      ⌜(∀ e ∈ ccEnts, e.Term' = hs.Term') ∧
        (∀ (i : Nat) (e : EntryM), ccEnts[i]? = some e →
          uint.Z e.Index' = uint.Z hs.Commit' + 1 + (i : Int))⌝ }}

end spec

end EtcdGrove
end Perennial
