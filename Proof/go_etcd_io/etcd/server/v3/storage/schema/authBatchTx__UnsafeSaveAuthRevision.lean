/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/schema/authBatchTx__UnsafeSaveAuthRevision.lean`. Lean-first (no Rocq
counterpart); the authstore-noax stage (2026-11-18).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBatchTx__UnsafeSaveAuthRevision
public import Spec.encoding.binary.bigEndian__PutUint64
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__ID
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__Name
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__IsSafeRangeBucket

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.authBatchTx.UnsafeSaveAuthRevision.wp_proof
    (hP : binary.bigEndian.PutUint64.spec (GF := GF) (hG := hG))
    (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) :
    schema.authBatchTx.UnsafeSaveAuthRevision.spec (GF := GF) (hG := hG) := by
  intro atl γ P W Pk b t st rev hhas hsb hhk hpend
  wp_start as ⟨#Htx, #HB, #Ht, Hl, Hrb⟩
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, ⟨%ab, #HAuth, -⟩, -, -, -, ⟨%srk, #HRK, #HRKb⟩, -⟩
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  ihave #Hbk := schema.auth_isBucket hID hName hSafe ab $$ [$Hpkg $HAuth]
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (t := go.byte)) as %bs1 ⟨Hbs1, -⟩
  · ipureintro; decide
  wp_apply wp_bePutUint64 hP bs1 _ rev (by simp) $$ [$Hbin $Hbs1] as Hbs1
  (try wp_auto)
  imod ownSlice_persist $$ Hbs1 with #Hbs1
  ihave #HRKb' : (srk ↦*□ schema.authRevisionKey : IProp GF) $$ []
  · unfold schema.authRevisionKey; iexact HRKb
  ihave Hhk : hkPut γ P mvcc.authBI.name schema.authRevisionKey st.S $$ []
  · unfold hkPut; rw [hhk]; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  ihave Hfk : fkPut γ mvcc.authBI.name schema.authRevisionKey $$ []
  · unfold fkPut
    rw [if_neg (by unfold fkKey mvcc.authBI schema.authRevisionKey; decide)]
    itrivial
  wp_apply (hPut γ P W Pk b t st ab mvcc.authBI srk bs1 schema.authRevisionKey (u64Be rev) hhas
      (by decide) (by decide) hpend (fun h => by rw [hsb] at h; cases h)
      (fun h => absurd h (by unfold fkKey mvcc.authBI schema.authRevisionKey; decide)))
    $$ [$Hbpkg $HB $Ht $Hl $Hbk $HRKb' $Hbs1 $Hhk $Hrb $Hfk] as ⟨Hl, -, Hrb, -⟩
  (try wp_auto)
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
