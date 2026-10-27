/-
Proof of `Spec/k8s_io/client_go/tools/cache/RealFIFO__Replace.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.RealFIFO__Replace
public import Spec.k8s_io.client_go.tools.cache.RealFIFO__checkSynced_locked
public import Spec.k8s_io.client_go.tools.cache.RealFIFO__addReplaceToItemsLocked

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem RealFIFO.Replace.wp_proof
    (wp_check : RealFIFO.checkSynced_locked.spec (GF := GF) (hG := hG))
    (wp_addr : RealFIFO.addReplaceToItemsLocked.spec (GF := GF) (hG := hG)) :
    RealFIFO.Replace.spec (GF := GF) (hG := hG) := by
  intro f γ OK KF osl objs rv
  iintro %Φ ⟨#Hpkg, #Hf, Hosl, #Hok⟩ HAU
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isFIFO at Hf
  icases Hf with ⟨%ch, %kf, %mp, %g, %h, %uwp, #Hkf, #Hkey, #Htr, #Hae, #Hbm, #Huwp, #Hbs,
    #Hch, #Hmp, #Hg, #Hgok, #Hh, #Hhok, #Hguard, #Hcond, #Hinv⟩
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_with_defer as %defer defer
  wp_apply (lc := 3) sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hlk, Htok⟩
  imod fifo_acquire f γ OK ch $$ Hinv Hlc1 Hlc2 Htok with HR
  iunfold fifoRes at HR
  icases HR with ⟨%q, %sl, %vs, Hex, Hst, Hsy, Hitems, Hsl, Hcap, Hds, Hpop, Hinit, %Hic,
    Hsc, Hcl, Hbc⟩
  imod fifoSt_update γ q (FQ.replace objs rv) (FQ.replace_synced objs rv) _ $$ [$Hst $HAU]
    with ⟨Hst, HK⟩
  (try wp_auto)
  wp_apply (wp_addr f mp g _ osl rv sl vs) $$ [$Hpkg $Htr $Hmp $Hg $Hgok $Hcond $Hitems $Hsl $Hcap]
    as ⟨%sl', Hitems, Hsl, Hcap⟩
  ihave Hds := fifo_push OK q.items vs (.replaced objs rv) _ $$ [$Hds Hosl]
  · iunfold fdAt; dsimp only; iexists osl; iframe; iframe #; ipureintro; rfl
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave %Hlen2 := (BigSepL2.bigSepL2_length (Φ := fun _ x y => fdAt OK x y)) $$ Hds
  (try wp_auto)
  cases hp : q.populated with
  | true =>
    (try wp_auto)
    imod fifo_release f γ OK ch $$ Hinv Hlc3 [Hex Hst Hsy Hitems Hsl Hcap Hds Hpop Hinit Hsc Hcl Hbc]
      with Htok
    · iunfold fifoRes
      iexists (FQ.replace objs rv q), sl', _
      simp only [FQ.replace, hp, ↓reduceIte]
      iframe
      ipureintro; exact Hic
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hsync $Hlk $Htok]
    (try wp_auto)
    iapply HK; itrivial
  | false =>
    (try wp_auto)
    have hn : sint.nat sl'.len = q.items.length + 1 := by
      rw [← Hlen.1, ← Hlen2]; simp
    have hlt : q.items.length + 1 < 2 ^ 63 := by have := Hlen.2; word
    have hw : sl'.len = W64 ((q.items.length + 1 : Nat) : Int) := by word
    rw [hw]
    wp_apply (wp_check f ch γ.ch (fifoSyncedLb γ) true (q.items.length + 1) q.synced)
      $$ [$Hpop $Hinit $Hsc $Hch $Hbc] as ⟨Hpop, Hinit, Hsc, Hbc⟩
    · isplitr
      · ipureintro; exact hlt
      iintro %hs
      simp [syncsNow] at hs
    have hs : syncsNow true (q.items.length + 1) q.synced = false := by simp [syncsNow]
    rw [hs, Bool.or_false]
    (try wp_auto)
    imod fifo_release f γ OK ch $$ Hinv Hlc3 [Hex Hst Hsy Hitems Hsl Hcap Hds Hpop Hinit Hsc Hcl Hbc]
      with Htok
    · iunfold fifoRes
      iexists (FQ.replace objs rv q), sl', _
      simp only [FQ.replace, hp, Bool.false_eq_true, ↓reduceIte]
      iframe
      ipureintro; exact hlt
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hsync $Hlk $Htok]
    (try wp_auto)
    iapply HK; itrivial

end proof

end cache
end EtcdGrove
end Perennial
