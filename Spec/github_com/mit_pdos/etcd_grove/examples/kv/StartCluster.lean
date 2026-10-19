/- Lean-first (no Rocq counterpart).

`StartCluster(voters)` (cluster.go), on the voters `1, 2, 3`: a replica of the store on a raft
node of each (raft's `RestartNode`, in its dynamic mode: the cluster's only configuration
change is `RemoveMember(3)`'s, `KVCC`), with its storage, the transport between them
(`deliver`) and each node's ticks (`tick`). Everything the cluster needs is allocated here,
from nothing but the storage registry (`kvStorInv`, for the storages): raft's ghost state, the
term budget and its tick credits, the store's invariant. It returns the replicas (a fresh
slice of three, of one store, `isKV γr`) and the client's half of the store's state, the empty
store (`rkvVal γr kvEmpty`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- See the file header. -/
abbrev StartCluster.spec : Prop :=
  ∀ (vsl : GoSlice),
  -- the time receipts' bound (D19b, 2026-10-18): raft's term budget is backed by receipts
  receiptBound GF ≤ 2 ^ 64 - 2 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗ kvStorInv (GF := GF) ∗
      vsl ↦*□ [W64 1, W64 2, W64 3] }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kv.StartCluster)) (Val #vsl))
  {{ (ksl : GoSlice), RET #ksl; ∃ (γr : RKVNames) (rs : List Loc), ksl ↦* rs ∗
      ⌜rs.length = 3⌝ ∗ ([∗list] r ∈ rs, ∃ γp, isKV γr γp r) ∗ rkvVal γr kvEmpty }}

end spec

end kv
end EtcdGrove
end Perennial
