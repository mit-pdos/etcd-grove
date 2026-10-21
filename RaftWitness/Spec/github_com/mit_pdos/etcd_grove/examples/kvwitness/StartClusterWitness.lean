/- Lean-first (no Rocq counterpart). (2026-10-20, W4)

`StartClusterWitness(voters, witness)` (witness.go), at the voters `1, 2` and the witness `3`
(`MainWitness`'s): a cluster of three members, `1, 2, 3`, of which `3` is a witness that runs no
replica, in raft's static mode (its configuration never changes: the cluster admits no conf-change
entry, `KVCCS`); a replica of the store on a raft node of each regular voter (`RestartNode` on a
storage whose conf state has the members and the witness), each with its own `Witness` on one
shared `WitnessStore` (whose states the witness's protocol history follows), the transport between
them and a node's ticks. As `StartCluster`'s: the replicas, of one store, at the empty store.
-/
module

public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]
variable [KVStor GF]

/-- See the file header. -/
abbrev StartClusterWitness.spec : Prop :=
  ∀ (vsl : GoSlice),
  -- the time receipts' bound (D19b): raft's term budget is backed by receipts
  receiptBound GF ≤ 2 ^ 64 - 2 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness ∗
      kvStorInv (GF := GF) ∗ vsl ↦*□ [W64 1, W64 2] }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvwitness.StartClusterWitness))
      (Val #vsl)) (Val #(W64 3)))
  {{ (ksl : GoSlice), RET #ksl; ∃ (γr : RKVNames) (rs : List Loc), ksl ↦* rs ∗
      ⌜rs.length = 2⌝ ∗ ([∗list] r ∈ rs, ∃ γp, isKV γr γp r) ∗ rkvVal γr kvEmpty }}

end spec

end kvwitness
end EtcdGrove
end Perennial
