/-
**The membership backend's buckets over the real backend** (prove-ps2-members, 2026-11-22): schema's
`Members`, `MembersRemoved` and `Cluster` bucket values are the backend's `Bucket`s `mvcc.membersBI`,
`membersRemovedBI`, `clusterBI` (from `schemaInit`), and the tracked-bucket bookkeeping of one bucket's
write inside a part of a bucket set (`rbPart_focus`, `rbPut_tracked`), for the proofs of
`MustCreateBackendBuckets` and `MustDeleteMemberFromBackend`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace schema

open Iris Iris.BI Iris.ProofMode backend

section buckets
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- schema's `Members` bucket is the `Bucket` `membersBI`. -/
theorem members_isBucket (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) (b : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      globalAddr go_etcd_io.etcd.server.v3.storage.schema.Members ↦□ b ⊢ isBucket b mvcc.membersBI := by
  unfold mvcc.membersBI
  iintro ⟨#Hpkg, #Hk⟩
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%b0, #Hk0, #Hb0⟩, -⟩
  icombine Hk Hk0 gives %Heq
  subst Heq
  iapply mvcc.bucketIs_isBucket hID hName hSafe $$ [$Hpkg $Hb0]

/-- schema's `MembersRemoved` bucket is the `Bucket` `membersRemovedBI`. -/
theorem membersRemoved_isBucket (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) (b : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      globalAddr go_etcd_io.etcd.server.v3.storage.schema.MembersRemoved ↦□ b ⊢
      isBucket b mvcc.membersRemovedBI := by
  unfold mvcc.membersRemovedBI
  iintro ⟨#Hpkg, #Hk⟩
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%b0, #Hk0, #Hb0⟩, -⟩
  icombine Hk Hk0 gives %Heq
  subst Heq
  iapply mvcc.bucketIs_isBucket hID hName hSafe $$ [$Hpkg $Hb0]

/-- schema's `Cluster` bucket is the `Bucket` `clusterBI`. -/
theorem cluster_isBucket (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) (b : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      globalAddr go_etcd_io.etcd.server.v3.storage.schema.Cluster ↦□ b ⊢ isBucket b mvcc.clusterBI := by
  unfold mvcc.clusterBI
  iintro ⟨#Hpkg, #Hk⟩
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hsi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%b0, #Hk0, #Hb0⟩⟩
  icombine Hk Hk0 gives %Heq
  subst Heq
  iapply mvcc.bucketIs_isBucket hID hName hSafe $$ [$Hpkg $Hb0]

end buckets

section params
variable [GooseExts]

/-- A bucket other than `Meta` holds no hook key of the real backend. -/
theorem kb_HK (d : mvcc.KBReal) (n k : GoString) (hn : n ≠ go!"meta") : d.P.HK n k = false := by
  show decide (n = go_etcd_io.etcd.server.v3.storage.schema.metaName ∧ _) = false
  exact decide_eq_false (fun h => hn h.1)

/-- A bucket other than `Meta` holds no hook-owned key of the real backend. -/
theorem kb_hk (d : mvcc.KBReal) (n k : GoString) (hn : n ≠ go!"meta") : d.P.hk n k = false := by
  unfold BParams.hk; rw [kb_HK d n k hn]; simp

/-- A bucket other than `Key` is a hook's bucket of the real backend. -/
theorem kb_HB (d : mvcc.KBReal) (n : GoString) (hn : n ≠ go!"key") : d.P.HB n = true := by
  show decide (n ≠ go_etcd_io.etcd.server.v3.storage.schema.keyName) = true
  exact decide_eq_true hn

/-- A bucket other than `Key` is not safe-range in the real backend. -/
theorem kb_SB (d : mvcc.KBReal) (n : GoString) (hn : n ≠ go!"key") : d.P.SB n = false := by
  show decide (n = go_etcd_io.etcd.server.v3.storage.schema.keyName) = false
  exact decide_eq_false hn

/-- The rest buckets are tracked by the real backend. -/
theorem kb_RB (d : mvcc.KBReal) (n : GoString) (h : n ∈ mvcc.restBuckets) : d.P.RB n = true := by
  show decide (n ∈ mvcc.restBuckets) = true
  exact decide_eq_true h

end params

section parts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- **One bucket of a part, focused**: the part of a set `S` containing `n` is the part of `n` and
what puts any part of `n` back, at that bucket's new contents. -/
theorem rbPart_focus (γ : BNames) (S : GoString → Prop) (r : GMap GoString BktData) (n : GoString)
    (hS : S n) :
    rbPart (GF := GF) γ S r ⊢ rbPart γ (· = n) r ∗
      (∀ v : BktData, rbPart γ (· = n) (r.insert n v) -∗ rbPart γ S (r.insert n v)) := by
  have hsplit : ∀ m, S m ↔ (m = n ∨ (S m ∧ m ≠ n)) := by
    intro m; by_cases hm : m = n
    · subst hm; exact ⟨fun _ => Or.inl rfl, fun _ => hS⟩
    · exact ⟨fun h => Or.inr ⟨h, hm⟩, fun h => h.elim (fun e => absurd e hm) And.left⟩
  iintro Hrb
  ihave Hrb := (rbPart_set γ S _ r hsplit).1 $$ Hrb
  icases (rbPart_split γ (· = n) (fun m => S m ∧ m ≠ n) r (fun m h1 h2 => h2.2 h1)).1 $$ Hrb
    with ⟨Hn, Hrest⟩
  iframe Hn
  iintro %v Hn
  ihave Hrest : rbPart γ (fun m => S m ∧ m ≠ n) (r.insert n v) $$ [Hrest]
  · iapply (rbPart_congr γ _ _ _ (fun m hm => by
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hm.2)])).1 $$ Hrest
  ihave Hrb := (rbPart_split γ (· = n) (fun m => S m ∧ m ≠ n) _ (fun m h1 h2 => h2.2 h1)).2
    $$ [$Hn $Hrest]
  iapply (rbPart_set γ S _ _ hsplit).2 $$ Hrb

/-- A tracked bucket's `rbPut` is the part of that bucket. -/
theorem rbPut_tracked (γ : BNames) (P : BParams) (n : GoString) (S : Data) (h : P.RB n = true) :
    rbPut (GF := GF) γ P n S = rbPart γ (· = n) (rbData P S) := by
  unfold rbPut; rw [h]; rfl

end parts

section create
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`UnsafeCreateBucket` of a present tracked bucket** in a part of a set `S` containing it: the
writer's contents unchanged (bbolt's `ErrBucketExists`, ignored), the part given back. -/
theorem create_present (hCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc) (st : BSess) (bk : GoInterface)
    (bi : BucketInfo) (S : GoString → Prop) (r : GMap GoString BktData)
    (hS : S bi.name) (hRB : P.RB bi.name = true) (hhas : P.has bi) (hn0 : 0 < bi.name.length)
    (hn1 : bi.name.length ≤ maxKeySize) (hpend : sint.Z st.pend + 1 < 2 ^ 58)
    (hr : (r.lookup bi.name).isSome) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ isBucket bk bi ∗
        rbPart γ S r }}
      (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"UnsafeCreateBucket")) (Val #bk))
    {{ RET #(); batchLocked γ P b (st.create bi) ∗ rbPart γ S r ∗ ⌜(st.create bi).S = st.S⌝ }} := by
  iintro %Φ ⟨#Hpkg, #HB, #Ht, Hl, #Hbk, Hrb⟩ HΦ
  icases rbPart_focus γ S r bi.name hS $$ Hrb with ⟨Hn, Hback⟩
  icases batchLocked_rbPart γ P b st (· = bi.name) r $$ [$Hl $Hn] with ⟨Hl, Hn, %Hag⟩
  have hSr : st.S.lookup bi.name = r.lookup bi.name := by
    have h := Hag bi.name rfl
    rw [rbData_lookup, hRB] at h
    simpa using h
  have hcS : (st.create bi).S = st.S := by
    show (if st.S.lookup bi.name = none then st.S.insert bi.name ∅ else st.S) = st.S
    rw [hSr]
    rcases hc : r.lookup bi.name with _ | x
    · rw [hc] at hr; cases hr
    · simp
  ihave Hn : rbPut γ P bi.name st.S $$ [Hn]
  · rw [rbPut_tracked γ P bi.name st.S hRB]
    iapply (rbPart_congr γ _ (rbData P st.S) r (fun n hn => Hag n hn)).2 $$ Hn
  wp_apply (hCB γ P W Pk b t st bk bi hhas hn0 hn1 hpend false false (_hkc := by decide))
    $$ [$Hpkg $HB $Ht $Hl $Hbk $Hn] as ⟨Hl, Hn⟩
  have hlk : ∀ n, n = bi.name → (rbData P st.S).lookup n =
      (r.insert bi.name ((r.lookup bi.name).getD ∅)).lookup n := by
    intro n hn
    subst hn
    rw [GMap.lookup_insert, Hag _ rfl]
    rcases hc : r.lookup bi.name with _ | x
    · rw [hc] at hr; cases hr
    · rfl
  ihave Hn : rbPut γ P bi.name st.S $$ [Hn]
  · rw [← hcS]; iexact Hn
  rw [rbPut_tracked γ P bi.name st.S hRB]
  ihave Hn := (rbPart_congr γ _ _ _ hlk).1 $$ Hn
  ihave Hrb := Hback $$ %((r.lookup bi.name).getD ∅) Hn
  ihave Hrb : rbPart γ S r $$ [Hrb]
  · iapply (rbPart_congr γ _ _ _ (fun n _ => by
      by_cases hn : n = bi.name
      · subst hn
        rw [GMap.lookup_insert]
        rcases hc : r.lookup bi.name with _ | x
        · rw [hc] at hr; cases hr
        · rfl
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hn)])).1 $$ Hrb
  iapply HΦ
  iframe Hl Hrb
  ipureintro; exact hcS

end create

end schema
end EtcdGrove
end Perennial
