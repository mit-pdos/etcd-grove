/-
Proof of `Spec/go_etcd_io/etcd/cache/v3/New.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.New
public import Spec.go_etcd_io.etcd.cache.v3.defaultConfig
public import Spec.go_etcd_io.etcd.cache.v3.newCache
public import Spec.go_etcd_io.etcd.cache.v3.realClock__NewTimer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- The real clock is a `Clock`. -/
theorem isClock_realClock (wp_NewTimer : realClock.NewTimer.spec (GF := GF) (hG := hG))
    (rc : realClock) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ⊢
      isClock (interface.mk realClock.ty #rc) := by
  iintro #Hpkg
  unfold isClock
  iintro %d
  imodintro
  iintro %Φ _ HΦ
  iapply wp_NewTimer rc d $$ Hpkg HΦ

theorem New.wp_proof (wp_defaultConfig : defaultConfig.spec (GF := GF) (hG := hG))
    (wp_newCache : newCache.spec (GF := GF) (hG := hG))
    (wp_NewTimer : realClock.NewTimer.spec (GF := GF) (hG := hG)) :
    New.spec (GF := GF) (hG := hG) := fun client pfx sl gs => by
  wp_start as ⟨#Hcci, #Hcl, #Hopts, #Hb, #Hthr⟩
  unfold cfgOptsAt
  icases Hopts with ⟨%fs, #Hfs, %Hlen, #Hf⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hfs
  wp_auto
  wp_apply wp_defaultConfig
  irename «prefix» => Hprefix
  ihave IH : iprop(∃ (n : w64) (f0 : GoFunc),
      "i" ∷ i_ptr ↦ n ∗ "cfg" ∷ cfg_ptr ↦ cfgApply (gs.take (sint.nat n)) defaultConfigVal ∗
      "opt" ∷ opt_ptr ↦ f0 ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (fs.length : Int)⌝) $$ [i cfg opt]
  · iexists W64 0, _
    simp only [named]
    rw [show sint.nat (W64 0) = 0 by rfl, List.take_zero]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < fs.length := by word
    obtain ⟨f, Hfi⟩ : ∃ f, fs[sint.nat n]? = some f := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨g, Hgi⟩ : ∃ g, gs[sint.nat n]? = some g :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hlt)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) fs DFrac.discard f Hn.1 $$ [Hfs] as -
    · iframe #; ipureintro; exact Hfi
    ihave #Hg := Hf $$ %(sint.nat n) %f %g %Hfi %Hgi
    unfold cfgOptSpec
    wp_apply Hg $$ [$cfg] as cfg
    wp_for_post
    iframe
    iexists n + W64 1, f
    simp only [named]
    rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, cfgApply_take_succ gs _ _ g Hgi]
    iframe
    ipureintro; constructor <;> word
  · have Hge : sint.nat n = gs.length := by rw [← Hlen]; word
    rw [Hge, List.take_length]
    ihave #Hclk := isClock_realClock wp_NewTimer (zero_val realClock) $$ Hpkg
    wp_apply wp_newCache client pfx (cfgApply gs defaultConfigVal) _
      $$ [$Hpkg $Hcci $Hcl $Hclk $Hb $Hthr]
      as %c %err Hr
    iapply HΦ $$ Hr

end proof

end EtcdGrove
end Perennial
