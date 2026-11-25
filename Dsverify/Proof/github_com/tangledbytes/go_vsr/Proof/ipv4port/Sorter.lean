/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/ipv4port/Sorter.lean (lab master 915f964; notes/dsv-vr.md):
over any `GF`, on the net extension.
-/
/-
`ByLess` as a `sort.Interface` on parsed configured addresses: `Less` compares their ports
(the port's addresses share their IP; the lab's: `Less` is always false there).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.ipv4port
public import Perennial.Proof.sort.SorterBasics

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : ipv4port.Assumptions]

theorem ipv4port.wp_GetIP_ptr (p : Loc) (dq : DFrac) (v : ipv4port.IPv4Port) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.ipv4port ∗
        p ↦{dq} v }}
      (App (Val (p @!! go.GoType.PointerType ipv4port.IPv4Port.ty @!! go!"GetIP")) (Val #()))
    {{ RET #v.First'; p ↦{dq} v }} := by
  wp_start as Hp
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  iapply HΦ $$ Hp

theorem ipv4port.wp_GetPort_ptr (p : Loc) (dq : DFrac) (v : ipv4port.IPv4Port) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.ipv4port ∗
        p ↦{dq} v }}
      (App (Val (p @!! go.GoType.PointerType ipv4port.IPv4Port.ty @!! go!"GetPort")) (Val #()))
    {{ RET #v.Second'; p ↦{dq} v }} := by
  wp_start as Hp
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  iapply HΦ $$ Hp

theorem ipv4port.wp_ip4 (ip : GoSlice) (bs : List w8) (h : bs.length = 16) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.ipv4port ∗
        ip ↦*□ bs }}
      (App (Val (@! ipv4port.ip4)) (Val #ip))
    {{ RET #(slice.slice ip w8 (W64 12) (W64 16)); True }} := by
  wp_start as #Hip
  ihave %Hlen := ownSlice_len _ _ _ $$ Hip
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hip
  wp_auto
  wp_if_destruct
  · rw [if_pos (by word)]
    wp_auto
    wp_end
  · exfalso; apply Hif; word

theorem ipv4port.ip_sub (s : GoSlice) :
    (s ↦*□ ([W8 0, W8 0, W8 0, W8 0, W8 0, W8 0, W8 0, W8 0, W8 0, W8 0,
      W8 255, W8 255, W8 127, W8 0, W8 0, W8 1] : List w8) : IProp GF) ⊢
      slice.slice s w8 (W64 12) (W64 16) ↦*□ ([W8 127, W8 0, W8 0, W8 1] : List w8) := by
  iintro #H
  ihave %Hlen := ownSlice_len _ _ _ $$ H
  simp only [List.length_cons, List.length_nil] at Hlen
  icases (ownSlice_slice (W64 12) (W64 16) s DFrac.discard _ ⟨by word, by word, by word⟩).1 $$ H
    with ⟨-, H2, -⟩
  iExactEq H2
  rfl

theorem ipv4port.wp_Less_cfg (a b : ipv4port.IPv4Port) (sa sb : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.ipv4port ∗
        ipv4port.ipCfg a sa ∗ ipv4port.ipCfg b sb }}
      (App (Val (a @!! ipv4port.IPv4Port.ty @!! go!"Less")) (Val #b))
    {{ RET #(decide (sint.Z a.Second' < sint.Z b.Second')); True }} := by
  wp_start as ⟨#Ha, #Hb⟩
  rw [show ipv4port.ipCfg (GF := GF) (hG := hG) a sa = ipv4port.ipCfgDef a sa by with_unfolding_all rfl,
    show ipv4port.ipCfg (GF := GF) (hG := hG) b sb = ipv4port.ipCfgDef b sb by with_unfolding_all rfl]
  unfold ipv4port.ipCfgDef
  icases Ha with ⟨%Ha, #Hsa⟩
  icases Hb with ⟨%Hb, #Hsb⟩
  wp_auto
  wp_apply ipv4port.wp_GetIP_ptr $$ [$ipPort] as ipPort
  wp_apply ipv4port.wp_ip4 a.First' _ (by rfl) $$ [$Hsa]
  wp_apply ipv4port.wp_GetIP_ptr $$ [$other] as other
  wp_apply ipv4port.wp_ip4 b.First' _ (by rfl) $$ [$Hsb]
  ihave #Ha4 := ipv4port.ip_sub $$ Hsa
  ihave #Hb4 := ipv4port.ip_sub $$ Hsb
  repeat (first
    | (wp_apply (wp_load_slice_index _ _ _ _ _ (by word)) $$ [$Ha4] as -; ipureintro; rfl)
    | (wp_apply (wp_load_slice_index _ _ _ _ _ (by word)) $$ [$Hb4] as -; ipureintro; rfl)
    | wp_auto)
  wp_apply ipv4port.wp_GetPort_ptr $$ [$ipPort] as ipPort
  wp_apply ipv4port.wp_GetPort_ptr $$ [$other] as other
  iapply HΦ
  try itrivial

theorem ipv4port.cfgs_swap (l : List ipv4port.IPv4Port) (i j : Nat) (a b : ipv4port.IPv4Port)
    (ha : l[i]? = some a) (hb : l[j]? = some b) :
    ([∗list] v ∈ l, ∃ s : GoString, ipv4port.ipCfg (GF := GF) (hG := hG) v s) ⊢
      [∗list] v ∈ (l.set i b).set j a, ∃ s : GoString, ipv4port.ipCfg v s := by
  iintro #H
  ihave #H2 := BigSepL.bigSepL_forall_intro $$ H
  iapply BigSepL.bigSepL_forall_elim
  iintro %k %x %hx
  have hmem : ∃ k' : Nat, l[k']? = some x := by
    simp only [List.getElem?_set] at hx
    split at hx
    · exact ⟨i, by rw [ha]; split at hx <;> simp_all⟩
    · split at hx
      · exact ⟨j, by rw [hb]; simp_all⟩
      · exact ⟨k, hx⟩
  obtain ⟨k', hk'⟩ := hmem
  iapply H2 $$ %k' %x %hk'

theorem ipv4port.ByLess.sorter.wp_proof : ipv4port.ByLess.sorter.spec (GF := GF) (hG := hG) := fun sl => by
  iintro #Hpkg
  iapply sort.isSorter_intro
  isplitr
  · iintro !> %l %Φ !> Hown HΦ
    dsimp only
    rw [method_unfold (t := ipv4port.ByLess.ty)]
    wp_auto
    unfold ipv4port.cfgList
    icases Hown with ⟨Hsl, Hcfg⟩
    ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
    rw [show sl.len = W64 (l.length : Int) by word]
    iapply HΦ
    iframe
  isplitr
  · iintro !> %l %i %j %a %b %Hij %Φ !> Hown HΦ
    dsimp only
    rw [method_unfold (t := ipv4port.ByLess.ty)]
    wp_auto
    unfold ipv4port.cfgList
    icases Hown with ⟨Hsl, #Hcfg⟩
    ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
    obtain ⟨hi, hj, ha, hb⟩ := Hij
    have hib : sint.nat i < l.length := (List.getElem?_eq_some_iff.1 ha).1
    have hjb : sint.nat j < l.length := (List.getElem?_eq_some_iff.1 hb).1
    ihave Ha := BigSepL.bigSepL_lookup ha $$ Hcfg
    ihave Hb := BigSepL.bigSepL_lookup hb $$ Hcfg
    icases Ha with ⟨%sa, #Ha⟩
    icases Hb with ⟨%sb, #Hb⟩
    rw [if_pos ⟨hj, by word⟩]
    wp_apply (wp_load_slice_index _ _ _ _ _ hj) $$ [$Hsl] as Hsl
    · ipureintro; exact hb
    rw [if_pos ⟨hi, by word⟩]
    wp_auto
    wp_method_call
    wp_call
    wp_apply (wp_load_slice_index _ _ _ _ _ hi) $$ [$Hsl] as Hsl
    · ipureintro; exact ha
    wp_apply ipv4port.wp_Less_cfg a b sa sb $$ [$Ha $Hb]
    iapply HΦ
    iframe Hsl
    isplitl []
    · iexact Hcfg
    · ipureintro; simp [ipv4port.portLt]
  · iintro !> %l %i %j %a %b %Hij %Φ !> Hown HΦ
    dsimp only
    rw [method_unfold (t := ipv4port.ByLess.ty)]
    wp_auto
    unfold ipv4port.cfgList
    icases Hown with ⟨Hsl, #Hcfg⟩
    ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
    obtain ⟨hi, hj, ha, hb⟩ := Hij
    have hib : sint.nat i < l.length := (List.getElem?_eq_some_iff.1 ha).1
    have hjb : sint.nat j < l.length := (List.getElem?_eq_some_iff.1 hb).1
    rw [if_pos ⟨hi, by word⟩]
    wp_auto
    rw [if_pos ⟨hj, by word⟩]
    wp_auto
    rw [if_pos ⟨hj, by word⟩]
    wp_apply (wp_load_slice_index _ _ _ _ _ hj) $$ [$Hsl] as Hsl
    · ipureintro; exact hb
    rw [if_pos ⟨hi, by word⟩]
    wp_apply (wp_load_slice_index _ _ _ _ _ hi) $$ [$Hsl] as Hsl
    · ipureintro; exact ha
    wp_apply wp_store_slice_index $$ [$Hsl] as Hsl
    · ipureintro; word
    wp_apply wp_store_slice_index $$ [$Hsl] as Hsl
    · ipureintro; simp only [List.length_set]; word
    iapply HΦ
    iframe Hsl
    iapply ipv4port.cfgs_swap l _ _ a b ha hb
    iexact Hcfg

end proofs
end Perennial.github_com.tangledbytes.go_vsr.pkg
