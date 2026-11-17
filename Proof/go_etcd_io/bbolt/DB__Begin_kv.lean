/-
`DB.Begin_kv`'s proof: bbolt's proved `DB.Begin` at the program's file extension (`theFs`), over
the backend's vocabulary (`InvBbolt.lean`; stage S1 of `notes/bbolt-integration-plan.md`).
-/
module

public import Spec.go_etcd_io.bbolt.DB__Begin_kv
public import Spec.go_etcd_io.bbolt.DB__Begin

@[expose] public section

set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- An unfired read update over the whole committed data, fired by the caller itself: the data
back (what `Begin(false)`'s error case gives back of `boltState_read_au`). -/
theorem bbolt.boltState_au_back [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (γ : DBNames)
    (D : backend.Data) :
    (AU <{ ∃∃ (q : Qp) (D' : bbolt.Data), bbolt.boltState (GF := GF) γ q D' }> @ ⊤ \ ↑γ.ns, ∅
        <{ bbolt.boltState γ q D', COMM bbolt.boltState γ 1 D ∗ ⌜D' = D⌝ }>) ⊢
    |={⊤}=> bbolt.boltState γ 1 D := by
  iintro Hau
  ihave Hau := atomic_update_mask_weaken (Eo2 := ⊤) (fun _ _ => CoPset.mem_full) $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%q, %D', Hx, Hucl⟩
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  imod Hcommit $$ Hx with ⟨Hs, -⟩
  imodintro
  iexact Hs

theorem bbolt.DB.Begin_kv.wp_proof
    (h : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [os.file.FieldAssumptions]
      [os.fileStat.FieldAssumptions], bbolt.DB.Begin.spec (GF := GF) (hG := hG)) :
    bbolt.DB.Begin_kv.spec (GF := GF) (hG := hG) := by
  intro db γ D w
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax⟩
  · simp only [backend.ownDB, onFs_none hfs]
    iintro %Φ ⟨-, H, -⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.ownWTx, backend.ownWTxG,
      backend.txDB, onFs_some hfs]
    cases w <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      iintro %Φ ⟨-, ⟨#Hdb, Hs⟩, Htok⟩ HΦ
    · ihave Hau := bbolt.boltState_read_au γ D $$ Hs
      have h' := h db γ false (fun D' => iprop(bbolt.boltState γ 1 D ∗ ⌜D' = D⌝))
      simp only [Bool.false_eq_true, ↓reduceIte] at h'
      iapply wp_fupd
      wp_apply h' $$ [$Hdb $Htok $Hau] as %tx %err Hr
      icases Hr with (⟨%He, #Htd, %D', Htx, Hs, %HD⟩ | ⟨%He, Htok, Hau⟩)
      · subst HD
        imodintro
        iapply HΦ; iframe Hs Hdb
        iright; isplitr; · ipureintro; exact He
        iframe Htd Htx
      · imod (bbolt.boltState_au_back γ D) $$ Hau with Hs
        imodintro
        iapply HΦ; iframe Hs Hdb
        ileft; iframe Htok; ipureintro; exact He
    · have h' := h db γ true (fun _ => iprop(emp))
      simp only [↓reduceIte] at h'
      wp_apply h' $$ [$Hdb] as %tx %err Hr
      icases Hr with (⟨%He, #Htd, %D', Htx⟩ | ⟨%He, -⟩)
      · icases persistent_entails_right (bbolt.boltTx_base tx γ 1 1 (TxView.wr D') D) $$ [Htx Hs]
          with ⟨%Hb, Htx, Hs⟩
        · iframe Htx Hs
        have HD : D' = D := Hb rfl
        subst HD
        iapply HΦ; iframe Hs Hdb
        iright; isplitr; · ipureintro; exact He
        iframe Htd
        iexists (fun _ => 0)
        rw [← wView_wr]
        iexact Htx
      · iapply HΦ; iframe Hs Hdb
        ileft; unfold wrTok; isplitr; · ipureintro; exact He
        itrivial

end proof

end EtcdGrove
end Perennial
