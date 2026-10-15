/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/wait/list__IsRegistered.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.wait.list__IsRegistered

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.wait.Assumptions]

theorem wait.list.IsRegistered.wp_proof : wait.list.IsRegistered.spec (GF := GF) (hG := hG) := by
  intro l γi γw R id ot
  wp_start as ⟨Hrd, #Hreg⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold waitListReader at Hrd
  icases Hrd with ⟨%sl, #He, %Hlen, Hrs⟩
  wp_apply wp_with_defer as %defer defer
  have hidx : 0 ≤ sint.Z (id % W64 64) ∧ sint.Z (id % W64 64) < sint.Z sl.len := by
    rw [Hlen]; word
  simp only [hidx, and_self, ↓reduceIte]
  generalize hn : (sint.Z (id % W64 64)).toNat = n
  have hn' : sint.Z (id % W64 64) = (n : Int) := by omega
  have hn64 : n < 64 := by omega
  have hk : (W64 (n : Int)) = id % W64 64 := by rw [← hn']; simp [W64, sint.Z]
  rw [hn']
  have hl : (List.replicate 64 ())[n]? = some () := by simp [hn64]
  icases (BigSepL.bigSepL_lookup_acc (PROP := IProp GF) (Φ := fun i (_ : Unit) => waitShardReader (GF := GF) γi γw R (waitShardAddr sl i) (W64 i)) hl).1 $$ Hrs with ⟨Hr, Hrs⟩
  iunfold waitShardReader at Hr
  icases Hr with ⟨%mref, %γs, %γr, #Hnm, #Hm, Hrw, #Hinv⟩
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrw] as ⟨Hrl, HP⟩
  simp only [hidx, and_self, ↓reduceIte]
  rw [hn']
  wp_auto_lc 1
  simp only [hidx, and_self, ↓reduceIte]
  rw [hn']
  iunfold waitShardP at HP
  icases HP with ⟨%M, Hmap, Hg⟩
  (try wp_auto)
  wp_apply wp_map_lookup2 $$ [$Hmap] as Hmap
  ihave Hgone : iprop(|={⊤}=> ghostMapAuth γs _ M ∗
      (⌜decide ((M !! id).isSome = true) = true⌝ ∨ waitGoneOpt γw id ot)) $$ [Hg Hlc1]
  · cases hM : M !! id with
    | some ch =>
      imodintro; iframe Hg; ileft; ipureintro; simp
    | none =>
      cases ot with
      | none =>
        imodintro; iframe Hg; iright; iunfold waitGoneOpt; itrivial
      | some t =>
        iunfold waitRegdOpt at Hreg
        iunfold waitRegd at Hreg
        icases Hreg with ⟨%γs', %γr', %g, #Hnm', #Hrg⟩
        rw [← hk]
        ihave %Hagree := ghostMapElem_agree $$ Hnm Hnm'
        cases Hagree
        imod waitShard_gone γi R γs γr id M _ t g hM $$ Hinv Hlc1 Hg Hrg with ⟨Hg, #Hd⟩
        imodintro
        iframe Hg
        iright
        iunfold waitGoneOpt
        iunfold waitGone
        iexists γs, γr, g
        rw [← hk]
        iframe #
  imod Hgone with ⟨Hg, Hb⟩
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hg Hmap] as Hrw
  · inext; iunfold waitShardP; iexists M; iframe
  (try wp_auto)
  iapply HΦ
  isplitl [Hrs Hrw]
  · iunfold waitListReader
    iexists sl
    iframe He
    isplitr
    · ipureintro; exact Hlen
    ihave Hrs := Hrs $$ %() [Hrw]
    · iunfold waitShardReader; iexists mref, γs, γr; iframe Hm Hrw Hnm Hinv
    rw [List.set_replicate_self] at *
    iexact Hrs
  · iexact Hb

end proof

end EtcdGrove
end Perennial
