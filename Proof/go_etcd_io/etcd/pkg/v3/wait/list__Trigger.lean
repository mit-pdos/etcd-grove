/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/wait/list__Trigger.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.wait.list__Trigger

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

theorem wait.list.Trigger.wp_proof : wait.list.Trigger.spec (GF := GF) (hG := hG) := by
  intro l γi γw R id x
  wp_start as ⟨#Hl, Hpre⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold waitList at Hl
  icases Hl with ⟨%sl, #He, %Hlen, #Hsh⟩
  have hidx : 0 ≤ sint.Z (id % W64 64) ∧ sint.Z (id % W64 64) < sint.Z sl.len := by
    rw [Hlen]; word
  generalize hn : (sint.Z (id % W64 64)).toNat = n
  have hn' : sint.Z (id % W64 64) = (n : Int) := by omega
  have hn64 : n < 64 := by omega
  have hk : (W64 (n : Int)) = id % W64 64 := by rw [← hn']; simp [W64, sint.Z]
  ihave #Hs := Hsh $$ %n %hn64
  iunfold waitShard at Hs
  icases Hs with ⟨%mref, %γs, %γr, #Hnm, #Hm, #Hg, #Hinv⟩
  wp_auto
  simp only [hidx, and_self, ↓reduceIte]
  rw [hn']
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hg] as ⟨Hlk, HP⟩
  iunfold waitShardP at HP
  icases HP with ⟨%M, Hmap, Hga⟩
  simp only [hidx, and_self, ↓reduceIte]
  rw [hn']
  wp_auto
  wp_apply wp_map_lookup1 $$ [$Hmap] as Hmap
  simp only [hidx, and_self, ↓reduceIte]
  rw [hn']
  wp_auto
  wp_apply wp_mapDelete $$ [$Hmap] as Hmap
  simp only [hidx, and_self, ↓reduceIte]
  rw [hn']
  wp_auto_lc 1
  imod waitShard_take γi R γs γr id M $$ Hinv Hlc1 Hga with ⟨Hga, Hent⟩
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk Hga Hmap]
  · inext; iunfold waitShardP; iexists _; iframe
  cases hM : M !! id with
  | none =>
    wp_auto
    iapply HΦ; itrivial
  | some ch =>
    iunfold waitEntry at Hent
    icases Hent with ⟨%γh, %Ψ, %g, #Hh, Hp, #HR, #Hr⟩
    ihave #Hh' := Hh
    iunfold isHandoff at Hh'
    icases Hh' with ⟨#Hch, -⟩
    ihave %Hnn := isChan_not_null $$ Hch
    simp only [Option.getD_some]
    rw [decide_eq_false (show ¬ ch = chan.nil from Hnn)]
    wp_auto
    ihave HV : iprop(waitVal γh Ψ x) $$ [Hpre]
    · iunfold waitVal
      icases Hpre with (⟨%γh', %Hx, Hc, #Hr'⟩ | Ht)
      · iright
        iunfold waitRegd at Hr'
        icases Hr' with ⟨%γs', %γr', %g', #Hnm', #Hr'⟩
        rw [← hk]
        ihave %Hag := ghostMapElem_agree $$ Hnm Hnm'
        cases Hag
        ihave %Ht := ghostMapElem_agree $$ Hr Hr'
        have hc : handoffConsumer (GF := GF) γh false = handoffConsumer γh' false := by
          unfold handoffConsumer; rw [(Prod.mk.inj Ht).1]
        rw [hc]
        iframe Hc
        ipureintro; exact Hx
      · ileft
        iunfold waitTrig at Ht
        iapply Ht $$ HR
    wp_apply wp_handoff_send γh ch (waitVal γh Ψ) iprop(True) iprop(False) x $$ [$Hh $Hp $HV] as Hp
    wp_apply wp_handoff_close (V := GoInterface) γh ch (waitVal γh Ψ) iprop(True) iprop(False) true
      $$ [$Hh $Hp]
    · simp only [↓reduceIte]; itrivial
    (try wp_auto)
    iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
