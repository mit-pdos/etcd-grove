/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/schema/CreateMetaBucket.lean`: `LockOutsideApply`,
`UnsafeCreateBucket(Meta)` (an untracked hook's bucket: no part of the tracked buckets, nothing the
readers see), the deferred `Unlock` (`Unlock.bare`). Lean-first; claim #34, stage 4 (2026-11-23).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.CreateMetaBucket
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__LockOutsideApply
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeCreateBucket
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__ID
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__Name
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__IsSafeRangeBucket
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.UnlockBare

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.CreateMetaBucket.wp_proof
    (hLO : backend.batchTxBuffered.LockOutsideApply.spec (GF := GF) (hG := hG))
    (hCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG))
    (hUL : backend.batchTxBuffered.Unlock.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) :
    schema.CreateMetaBucket.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b t qo hm hRB
  wp_start as ⟨#HB, #Ht, Ho, Hwb⟩
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave Hsi : (schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨⟨%mb, #HM, -⟩, -⟩
  ihave #Hbm := mvcc.meta_isBucket hID hName hSafe mb $$ [$Hpkg $HM]
  icases backend.isBackend_b γ P W Pk b $$ HB with ⟨%t', %rt, %db, %lg, -, -, -, -, -, -, -, -,
    -, -, -, %HPw⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (hLO γ P W Pk b t qo) $$ [$Hbpkg $HB $Ht $Ho] as ⟨%st, Hl, %Hfree, ⟨HW, HPk⟩, Ho⟩
  (try wp_auto)
  have hlim := HPw.2.2.1
  have hp0 := Hfree.2.1
  ihave Hn : backend.rbPut (GF := GF) γ P mvcc.metaBI.name st.S $$ []
  · unfold backend.rbPut; rw [hRB]; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  wp_apply (hCB γ P W Pk b t st mb mvcc.metaBI hm (by decide) (by decide) (by omega) false false
      (_hkc := by decide)) $$ [$Hbpkg $HB $Ht $Hl $Hbm $Hn] as ⟨Hl, -⟩
  (try wp_auto)
  -- the deferred `Unlock()`: nothing the readers see changed
  have hvs := mvcc.viewSame_create mvcc.metaBI (backend.viewSame_of_freeOk Hfree)
  have hroom : sint.Z (st.create mvcc.metaBI).pend + P.hookMax < 2 ^ 58 := by
    have h2 := HPw.2.2.2.1
    have : sint.Z (st.create mvcc.metaBI).pend = sint.Z st.pend + 1 := by
      show sint.Z (st.pend + W64 1) = _; word
    omega
  ihave ⟨#Hth, %Hnw⟩ := backend.viewSame_thin γ P _ hvs
  wp_apply (backend.batchTxBuffered.Unlock.bare hUL γ P W Pk b t (st.create mvcc.metaBI) iprop(True)
      Hfree.2.2.2.2.1 hroom) $$ [$Hbpkg $HB $Ht $Hl $Hwb HW HPk]
  · ileft; iframe HW HPk Hth; ipureintro; exact Hnw
  (try wp_auto)
  iapply HΦ
  iframe Ho

end proof

end EtcdGrove
end Perennial
