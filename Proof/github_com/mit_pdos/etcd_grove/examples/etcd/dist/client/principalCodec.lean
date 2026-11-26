/- Lean-first (no Rocq counterpart).

Proof of `principalCodec.spec` (#50 F7 S7; `writerCodec`'s, for a string in and a bool out).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.principalCodec
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__Str
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Enc__Bool
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.NewDec
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__Str
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__Bool
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Dec__Done

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net client
open etcd_dist
open github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]

theorem principalCodec.wp_proof
    (wp_EncStr : Enc.Str.spec (GF := GF) (hG := hG))
    (wp_EncBool : Enc.Bool.spec (GF := GF) (hG := hG))
    (wp_NewDec : NewDec.spec (GF := GF) (hG := hG))
    (wp_DecStr : Dec.Str.spec (GF := GF) (hG := hG))
    (wp_DecBool : Dec.Bool.spec (GF := GF) (hG := hG))
    (wp_Done : Dec.Done.spec (GF := GF) (hG := hG)) :
    principalCodec.spec (GF := GF) (hG := hG) := by
  intro P Q
  wp_start
  ihave #Penc : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc $$ []
  · iPkgInit
  wp_auto
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold wireOk
  simp only [principalWire]
  isplitr
  · -- EncIn
    iintro %x %w !> %Φ' %Hx HΦ'
    obtain ⟨Hx, Hlen⟩ := Hx
    subst Hx
    wp_auto
    ihave He : ownEnc «$r0_ptr» [] $$ [«$r0»]
    · unfold ownEnc
      iexists slice.nil
      iframe
      isplitl []
      · iapply ownSlice_nil
      · iapply ownSliceCap_nil
    wp_apply wp_EncStr _ _ w $$ [He] as He
    · iframe
    (try wp_auto)
    isimp only [List.nil_append] at He
    iunfold ownEnc at He
    icases He with ⟨%s, He, Hs, -⟩
    (try wp_auto)
    iapply HΦ'
    rw [capped_of _ Hlen]
    iexact Hs
  isplitr
  · -- DecIn
    iintro %w %b %dq !> %Φ' Hb HΦ'
    wp_auto
    wp_apply wp_NewDec b _ dq $$ [Hb] as %d Hd
    · iframe
    (try wp_auto)
    wp_apply wp_DecStr d _ true $$ [Hd] as %s Hd
    · iframe
    icases decPost_elim _ _ _ _ _ $$ Hd with ⟨%r1, %ok1, Hd, %H1⟩
    (try wp_auto)
    wp_apply wp_Done d r1 ok1 $$ [Hd] as %dn %Hdn
    · iframe
    (try wp_auto)
    iapply HΦ'
    iintro %hdn
    obtain ⟨hok, hnil⟩ := Hdn hdn
    obtain ⟨-, hb⟩ := H1 hok
    rw [hnil] at hb
    obtain ⟨rfl, hlen⟩ := strBytes_dec hb
    ipureintro
    exact ⟨rfl, hlen⟩
  isplitr
  · -- EncOut
    iintro %v %o !> %Φ' %Hv HΦ'
    subst Hv
    wp_auto
    ihave He : ownEnc «$r0_ptr» [] $$ [«$r0»]
    · unfold ownEnc
      iexists slice.nil
      iframe
      isplitl []
      · iapply ownSlice_nil
      · iapply ownSliceCap_nil
    wp_apply wp_EncBool _ _ o $$ [He] as He
    · iframe
    (try wp_auto)
    isimp only [List.nil_append] at He
    iunfold ownEnc at He
    icases He with ⟨%s, He, Hs, -⟩
    (try wp_auto)
    iapply HΦ'
    iexact Hs
  isplitr
  · -- DecOut
    iintro %o %b %dq !> %Φ' Hb HΦ'
    wp_auto
    wp_apply wp_NewDec b _ dq $$ [Hb] as %d Hd
    · iframe
    (try wp_auto)
    wp_apply wp_DecBool d _ true $$ [Hd] as %x Hd
    · iframe
    icases decPost_elim _ _ _ _ _ $$ Hd with ⟨%r1, %ok1, Hd, %H1⟩
    (try wp_auto)
    wp_apply wp_Done d r1 ok1 $$ [Hd] as %dn %Hdn
    · iframe
    (try wp_auto)
    iapply HΦ'
    iintro %hdn
    obtain ⟨hok, hnil⟩ := Hdn hdn
    obtain ⟨-, hb⟩ := H1 hok
    rw [hnil] at hb
    obtain ⟨rfl, -⟩ := encBool_append_inj (r := []) (r' := []) (by simpa using hb)
    ipureintro
    rfl
  isplitr
  · -- the unknown answers' encoding: a report has none
    iintro %i %v %h
    exact False.elim h
  · iintro %i %v %b %dq %h
    exact False.elim h

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
