/-
**The membership buckets created on a fresh backend** (claim #34, stage 2, 2026-11-25): `withMemBkts`,
a part's contents with the three membership buckets created (empty if absent, kept if present: bbolt's
`CreateBucket`, `ErrBucketExists` ignored by the backend), and `create_any`, `UnsafeCreateBucket` of a
tracked bucket of a part, present or absent (`create_present`'s generalization), for
`MustCreateBackendBuckets.specFresh` (`bootstrap`'s `Finalize` on a new backend). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.schema.MemberBkts

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace schema

open Iris Iris.BI Iris.ProofMode backend

/-- **The contents `D` with the membership's buckets created** (`MustCreateBackendBuckets`:
`Members`, `MembersRemoved`, `Cluster`, each empty if absent, kept if present). -/
def withMemBkts [GooseExts] (D : GMap GoString BktData) : GMap GoString BktData :=
  ((D.insert go!"members" (bktOf D go!"members")).insert go!"members_removed"
    (bktOf D go!"members_removed")).insert go!"cluster" (bktOf D go!"cluster")

theorem withMemBkts_lookup [GooseExts] (D : GMap GoString BktData) (n : GoString) :
    (withMemBkts D).lookup n =
      if n = go!"cluster" ∨ n = go!"members_removed" ∨ n = go!"members" then
        some (bktOf D n) else D.lookup n := by
  unfold withMemBkts
  simp only [GMap.lookup_insert_eq_iff]
  by_cases h1 : go!"cluster" = n
  · subst h1; simp
  by_cases h2 : go!"members_removed" = n
  · subst h2; simp
  by_cases h3 : go!"members" = n
  · subst h3; simp
  have h : ¬ (n = go!"cluster" ∨ n = go!"members_removed" ∨ n = go!"members") := by
    rintro (h | h | h) <;> simp_all
  simp only [h1, h2, h3, h, ite_false]

section create
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`UnsafeCreateBucket` of a tracked bucket, present or absent**, in a part of a set `S`
containing it: the part at the bucket's contents, created empty if absent. -/
theorem create_any (hCB : backend.batchTxBuffered.UnsafeCreateBucket.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t : Loc) (st : BSess) (bk : GoInterface)
    (bi : BucketInfo) (S : GoString → Prop) (r : GMap GoString BktData)
    (hS : S bi.name) (hRB : P.RB bi.name = true) (hhas : P.has bi) (hn0 : 0 < bi.name.length)
    (hn1 : bi.name.length ≤ maxKeySize) (hpend : sint.Z st.pend + 1 < 2 ^ 58) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ isBucket bk bi ∗
        rbPart γ S r }}
      (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty @!! go!"UnsafeCreateBucket")) (Val #bk))
    {{ RET #(); batchLocked γ P b (st.create bi) ∗ rbPart γ S (r.insert bi.name (bktOf r bi.name)) }} := by
  iintro %Φ ⟨#Hpkg, #HB, #Ht, Hl, #Hbk, Hrb⟩ HΦ
  icases rbPart_focus γ S r bi.name hS $$ Hrb with ⟨Hn, Hback⟩
  icases batchLocked_rbPart γ P b st (· = bi.name) r $$ [$Hl $Hn] with ⟨Hl, Hn, %Hag⟩
  have hSr : st.S.lookup bi.name = r.lookup bi.name := by
    have h := Hag bi.name rfl
    rw [rbData_lookup, hRB] at h
    simpa using h
  ihave Hn : rbPut γ P bi.name st.S $$ [Hn]
  · rw [rbPut_tracked γ P bi.name st.S hRB]
    iapply (rbPart_congr γ _ (rbData P st.S) r (fun n hn => Hag n hn)).2 $$ Hn
  wp_apply (hCB γ P W Pk b t st bk bi hhas hn0 hn1 hpend false false (_hkc := by decide))
    $$ [$Hpkg $HB $Ht $Hl $Hbk $Hn] as ⟨Hl, Hn⟩
  have hlk : ∀ n, n = bi.name →
      (rbData P (if st.S.lookup bi.name = none then st.S.insert bi.name ∅ else st.S)).lookup n =
      (r.insert bi.name (bktOf r bi.name)).lookup n := by
    intro n hn
    subst hn
    rw [rbData_lookup, if_pos hRB, GMap.lookup_insert]
    show _ = some ((r.lookup bi.name).getD ∅)
    rw [← hSr]
    rcases hc : st.S.lookup bi.name with _ | x
    · simp
    · simp [hc]
  rw [rbPut_tracked γ P bi.name _ hRB]
  ihave Hn := (rbPart_congr γ _ _ _ hlk).1 $$ Hn
  ihave Hrb := Hback $$ %(bktOf r bi.name) Hn
  iapply HΦ
  iframe Hl Hrb

end create

end schema
end EtcdGrove
end Perennial
