/-
The proof of `Tx.rollback.spec` (`Proof/go_etcd_io/bbolt/Commit/RollbackSpec.lean`; U10d of
`notes/bbolt-proof-plan.md`, design §3.11 "Commit's error paths"): the flagged rollback
(`Tx.rollback_f.wp_proof`, `Tx__rollback_f.lean`) at `fr = false` (`Tx.rollback.spec_of_f`). The
proof itself (a published writer only closes; otherwise the freelist is rolled back, reloaded while
mapped, and the writer closes) is `Tx__rollback_f.lean`'s.
-/
module

public import Proof.go_etcd_io.bbolt.Tx__rollback_f

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Tx.rollback.wp_proof
    (wp_meta : DB.meta.spec (GF := GF) (hG := hG))
    (wp_Txid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
    (wp_Freelist : internal.common.Meta.Freelist.spec (GF := GF) (hG := hG))
    (wp_FlRollback : internal.freelist.Interface.Rollback.spec (GF := GF) (hG := hG))
    (wp_hasSynced : DB.hasSyncedFreelist.spec (GF := GF) (hG := hG))
    (wp_freepages : DB.freepages.spec (GF := GF) (hG := hG))
    (wp_NSR : internal.freelist.Interface.NoSyncReload.spec (GF := GF) (hG := hG))
    (wp_Reload : internal.freelist.Interface.Reload.spec (GF := GF) (hG := hG))
    (wp_page : DB.page.spec (GF := GF) (hG := hG))
    (wp_close : Tx.close_w.spec (GF := GF) (hG := hG)) :
    Tx.rollback.spec (GF := GF) (hG := hG) :=
  Tx.rollback.spec_of_f (Tx.rollback_f.wp_proof wp_meta wp_Txid wp_Freelist wp_FlRollback
    wp_hasSynced wp_freepages wp_NSR wp_Reload wp_page wp_close)

end proof

end bbolt
end EtcdGrove
end Perennial
