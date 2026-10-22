/- Lean-first (no Rocq counterpart).

`(*KV).install(kv, applied)` (kv.go, 2026-10-22, the snapshot-liveness fix): the replica's state
replaced by a snapshot's, the maps `K` and `A` of the committed log `D` (as `runOwn` holds them:
every key's value after `D`'s client history, and its decodable data each with its answer,
`AppliedOk`); every waiter of this replica's whose operation is among `A`'s gets its answer
(`waitP`, the same obligation as `apply`'s), so the applier's state is `runOwn` at `D`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- See the file header. -/
abbrev KV.install.spec : Prop :=
  ∀ (γr : RKVNames) (γp : RepNames) (r : Loc) (id : w64) (n st : Loc)
    (ap D : List EntryM) (ods : List (Option (List w8))) (mK mA : Loc)
    (K A : GMap (List w8) (List w8)),
  (∀ k, (K !! k).getD [] = kvFold (firstOcc ods) k) → AppliedOk A (firstOcc ods) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗
      isReplica γr γp r id n st ∗ runOwn γr r ap ∗ mK ↦$ K ∗ mA ↦$ A ∗
      isCommitted γr.raft D ∗ ([∗list] e;o ∈ D;ods, entDataIs γr.raft e o) }}
    (App (App (Val (r @!! go.GoType.PointerType rKVTy @!! go!"install")) (Val #mK)) (Val #mA))
  {{ RET #(); runOwn γr r D }}

end spec

end kv
end EtcdGrove
end Perennial
