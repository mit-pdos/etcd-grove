/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/BackendHooks__OnPreCommitUnsafe.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.BackendHooks__OnPreCommitUnsafe
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.MustUnsafeSaveConfStateToBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafePut

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage backend storage

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

theorem storage.BackendHooks.OnPreCommitUnsafe.wp_proof
    (hCS : schema.MustUnsafeSaveConfStateToBackend.spec (GF := GF) (hG := hG))
    (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) :
    storage.BackendHooks.OnPreCommitUnsafe.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b t bh ix lg st hP
  wp_start as ⟨#Hh, #Hsave, #Hb, #Ht, Hl, HPk, %Hpre⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isBackendHooks at Hh
  icases Hh with ⟨#Hix, #Hlg, #Hmu⟩
  wp_apply wp_with_defer as %defer defer
  iunfold saveSpec at Hsave
  wp_apply Hsave $$ %st [$Hl $HPk] as ⟨%st1, Hl, HPk, %Hs1⟩
  · ipureintro; exact Hpre
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold csInv at HR
  icases HR with ⟨%cs, %d, Hcs, Hd⟩
  icases isBackend_b γ P W Pk b $$ Hb with ⟨%t', %rt, %db, %lg', -, -, -, -, -, -, -, -, -, -, -,
    %HPw⟩
  cases d
  · -- not dirty: nothing saved
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hcs Hd]
    · inext; iunfold csInv; iexists cs, false; iframe Hcs Hd
    iapply HΦ
    iexists st1
    iframe Hl HPk
    ipureintro; exact hookStep_of_save Hs1
  · -- dirty: the `confState` saved into `Meta`, one put
    wp_auto
    have hpend : sint.Z st1.pend + 1 < 2 ^ 58 := by
      have h1 := Hs1.2.2.2.2.2.1
      have h2 := Hpre.2.1
      omega
    have hSB : P.SB mvcc.metaBI.name = true → ∀ kc vc,
        (bktOf st1.S mvcc.metaBI.name).lookup kc = some vc → strLt kc schema.confStateKeyBytes := by
      intro h
      have := HPw.2.2.2.2 _ h
      rw [hP.2.1] at this
      cases this
    have hhk : P.hk mvcc.metaBI.name schema.confStateKeyBytes = false := by
      unfold BParams.hk; rw [hP.2.2.1]; simp
    wp_apply (hCS lg ⟨go.GoType.PointerType
        go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered.ty, #t⟩ cs
        (batchLocked γ P b st1)
        iprop(∃ st2 : BSess, batchLocked γ P b st2 ∗ ⌜hookStep P st st2⌝)) $$ [$Hl]
      as ⟨%st2, Hl, %Hs2⟩
    · iintro !> %bk %key %val %vb %Φ' !> ⟨#HM, #Hkey, #Hval, Hl⟩ HΦ'
      ihave #Hbk := mvcc.meta_isBucket hID hName hSafe bk $$ [$Hpkg3 $HM]
      wp_apply (hPut γ P W Pk b t st1 bk mvcc.metaBI key val schema.confStateKeyBytes vb hP.1
          (by decide) (by decide) Hs1.2.2.2.2.2.2.2.2.2 hpend hSB)
        $$ [$Hb $Ht $Hl $Hbk $Hkey $Hval] as ⟨Hl, -⟩
      · iframe #
        simp only [hkPut, hhk, Bool.false_eq_true, ↓reduceIte]
        itrivial
      iapply HΦ'
      iexists (st1.put mvcc.metaBI schema.confStateKeyBytes vb false)
      iframe Hl
      ipureintro; exact hookStep_save_put HPw hP Hpre Hs1
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hcs Hd]
    · inext; iunfold csInv; iexists cs, false; iframe Hcs Hd
    iapply HΦ
    iexists st2
    iframe Hl HPk
    ipureintro; exact Hs2

end proof

end EtcdGrove
end Perennial
