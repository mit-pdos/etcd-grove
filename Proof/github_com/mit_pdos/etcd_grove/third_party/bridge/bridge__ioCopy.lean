/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/third_party/bridge/bridge__ioCopy.lean`. The loop
keeps everything read from the source written to the destination (`relayDir l s t rd rd`), so
each `Write` of the bytes just read keeps the written bytes a prefix of the read ones.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.third_party.bridge.bridge__ioCopy
public import Spec.io.Copy

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bridge

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.third_party

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.third_party.bridge.Assumptions]

theorem bridge.ioCopy.wp_proof (wp_Copy : io.Copy.spec (GF := GF) (hG := hG)) :
    bridge.ioCopy.spec (GF := GF) (hG := hG) := by
  intro b q ch γbh l s t rd
  wp_start as ⟨Hbh, #Hbhc, Hdir⟩
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hioi := io.isInit_access $$ Hio
  icases Hioi with ⟨⟨%w, #Hdisc⟩, #Hesw, -⟩
  iunfold errors.newVar at Hesw
  icases Hesw with ⟨%xe, #Hesw, -⟩
  wp_auto
  wp_apply wp_slice_make2 (V := w8) $$ [] as %sl ⟨Hsl, -⟩
  · ipureintro; word
  ihave HI : iprop(∃ (rd' : List w8) (bs : List w8) (e : GoInterface), "Hsl" ∷ sl ↦* bs ∗
      "%Hlen" ∷ ⌜bs.length = sint.nat (W64 32768)⌝ ∗ "Hdir" ∷ relayDir l s t rd' rd' ∗ "err" ∷ err_ptr ↦ e)
    $$ [Hsl Hdir err]
  · iexists rd, _, GoInterface.nil
    iframe
    ipureintro; exact List.length_replicate
  wp_for HI
  wp_apply_core chan.wp_select_nonblocking_alt [iprop(True)]
      iprop((∀ err, bF b go!"blackholec" ↦{DFrac.own q} ch -∗ Φ #err) ∗
        bF b go!"blackholec" ↦{DFrac.own q} ch ∗ b_ptr ↦ b ∗
        src_ptr ↦ (interface.ok s : GoInterface) ∗ dst_ptr ↦ (interface.ok t : GoInterface) ∗
        buf_ptr ↦ sl ∗ sl ↦* bs ∗ relayDir l s t rd' rd' ∗ err_ptr ↦ e)
      $$ [] [HΦ Hbh b src dst buf Hsl Hdir err] []
  · iapply BigSepL2.bigSepL2_singleton.2
    iintro ⟨HΦ, Hbh, b, src, dst, buf, Hsl, Hdir, err⟩
    simp only [chan.nonblockingAltClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γbh
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ Hbhc
    iapply ownBroadcastChan_nonblocking_receive _ _ _ _ _ _ $$ Hbhc
    isplit
    · iintro -
      wp_auto
      wp_apply wp_Copy w l s t rd' rd' $$ [Hdir] as %n %err' Hdir
      · iframe #; iframe
      wp_for_post
      wp_pures
      iapply HΦ
      iexact Hbh
    · iintro -
      iframe
  · iframe
  · iintro ⟨HΦ, Hbh, b, src, dst, buf, Hsl, Hdir, err⟩ -
    wp_auto
    wp_apply relay.Read l s t rd' rd' sl bs $$ [Hdir Hsl] as %nr %er ⟨%bs', Hsl, %Hrd, Hdir⟩
    · iframe
    ihave %Hsllen := ownSlice_len _ _ _ $$ Hsl
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
    obtain ⟨Hbl, Hnr0, Hnrl⟩ := Hrd
    wp_if_destruct
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
      wp_auto
      icases (ownSlice_split_all nr sl _ _ ⟨by word, by word⟩).1 $$ Hsl with ⟨Hsl1, Hsl2⟩
      wp_apply relay.Write l s t (rd' ++ bs'.take (sint.nat nr)) rd' (slice.slice sl w8 (W64 0) nr)
          (DFrac.own 1) (bs'.take (sint.nat nr)) $$ [Hdir Hsl1] as %nw %ew ⟨Hsl1, %Hnw, Hdir⟩
      · iframe
        ipureintro; exact List.prefix_refl _
      cases ew with
      | ok ei =>
        wp_auto
        wp_for_post
        wp_pures
        iapply HΦ; iexact Hbh
      | nil =>
        wp_auto
        wp_if_destruct
        · subst Hif
          ihave Hsl := (ownSlice_split_all nr sl _ _ ⟨by word, by word⟩).2 $$ [Hsl1 Hsl2]
          · iframe
          have htt : List.take (sint.nat nr) (List.take (sint.nat nr) bs') = List.take (sint.nat nr) bs' :=
            List.take_take.trans (by rw [Nat.min_self])
          rw [htt]
          cases er with
          | ok ei =>
            wp_auto
            wp_for_post
            iapply HΦ; iexact Hbh
          | nil =>
            wp_auto
            wp_for_post
            iframe
            iexists _, bs', e
            iframe
            ipureintro; omega
        · wp_for_post
          wp_pures
          iapply HΦ; iexact Hbh
    · cases er with
      | ok ei =>
        wp_auto
        wp_for_post
        iapply HΦ; iexact Hbh
      | nil =>
        wp_auto
        wp_for_post
        have h0 : sint.nat nr = 0 := by word
        rw [h0, List.take_zero, List.append_nil]
        iframe
        iexists rd', bs', e
        iframe
        ipureintro; omega

end proof

end bridge
end EtcdGrove
end Perennial
