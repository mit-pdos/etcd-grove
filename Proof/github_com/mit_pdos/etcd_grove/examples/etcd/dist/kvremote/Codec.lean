/-
The proof of `Codec` (`Spec/.../dist/kvremote/Codec.lean`): the seven function literals, each
against its part of `codecOk (kvR γk)`. The encoders return their bytes in a slice, which bounds
them (`ownSlice_len`), so the store's cut encodings are the bytes (`inEnc_eq`, `outEnc_eq`); a
decoder's accepted bytes are the encoding of the value it returns, which is the value encoded
(`inEnc_dec`, `outEnc_dec`: the encodings' injectivity). `IsRead` is `!IsWrite`, the model input's
`!isWrite` (`isWriteL_dec`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Codec
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.EncInput
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.DecInput
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.EncOutput
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.DecOutput
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.txnwork.IsWrite

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote

open github_com.mit_pdos.etcd_grove.examples.lib.txnwork
open github_com.mit_pdos.etcd_grove.examples.lib.remote
open EtcdGrove EtcdGrove.etcd_txnlin
open EtcdGrove EtcdGrove.etcd_txnlin
open go_etcd_io.etcd.server.v3.etcdserver mvcc
open github_com.mit_pdos.etcd_grove.examples.lib

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]

theorem Codec.wp_proof (wp_EncInput : EncInput.spec (GF := GF) (hG := hG))
    (wp_DecInput : DecInput.spec (GF := GF) (hG := hG))
    (wp_EncOutput : EncOutput.spec (GF := GF) (hG := hG))
    (wp_DecOutput : DecOutput.spec (GF := GF) (hG := hG))
    (wp_IsWrite : IsWrite.spec (GF := GF) (hG := hG)) :
    Codec.spec (GF := GF) (hG := hG) := by
  intro γk
  wp_start
  ihave #Ptx : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.txnwork $$ []
  · iPkgInit
  wp_auto
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold codecOk
  simp only [kvR]
  isplitr
  · -- EncIn
    iintro %x
    iintro !> %Φ' - HΦ'
    wp_auto
    wp_apply wp_EncInput x.1 as %b Hb
    ihave %Hlen := ownSlice_len _ _ _ $$ Hb
    try wp_auto
    iapply HΦ'
    rw [inEnc_eq _ (by obtain ⟨h1, h2⟩ := Hlen; word)]
    iexact Hb
  isplitr
  · -- DecIn
    iintro %x %b %dq
    iintro !> %Φ' Hb HΦ'
    wp_auto
    wp_apply wp_DecInput b (inEnc x.1) dq $$ [Hb] as %x' %ok %Hok
    · iexact Hb
    try wp_auto
    iapply HΦ'
    ipureintro
    intro h
    rw [inEnc_dec (Hok h)]
  isplitr
  · -- EncOut
    iintro %v %Hv
    obtain ⟨y, rfl⟩ : ∃ y : Output, v = boxOut y := by
      rcases Hv with ⟨o, h⟩ | ⟨_, h⟩
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
    iintro !> %Φ' - HΦ'
    wp_auto
    wp_apply wp_EncOutput y as %b Hb
    ihave %Hlen := ownSlice_len _ _ _ $$ Hb
    try wp_auto
    iapply HΦ'
    rw [kvEncOut_boxOut (package_sem := package_sem.import_txnwork_Assumption),
      outEnc_eq _ (by obtain ⟨h1, h2⟩ := Hlen; word)]
    iexact Hb
  isplitr
  · -- DecOut
    iintro %v %b %dq %Hv
    obtain ⟨y, rfl⟩ : ∃ y : Output, v = boxOut y := by
      rcases Hv with ⟨o, h⟩ | ⟨_, h⟩
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
    iintro !> %Φ' Hb HΦ'
    rw [kvEncOut_boxOut (package_sem := package_sem.import_txnwork_Assumption)]
    wp_auto
    wp_apply wp_DecOutput b (outEnc y) dq $$ [Hb] as %y' %ok %Hok
    · iexact Hb
    try wp_auto
    iapply HΦ'
    ipureintro
    intro h
    rw [outEnc_dec (Hok h)]
  isplitr
  · -- IsRead
    iintro %x
    iintro !> %Φ' - HΦ'
    wp_auto
    wp_apply wp_IsWrite x.1
    try wp_auto
    have e : isWriteL x.1 = TSo.isWrite (kvMi x) := isWriteL_dec x.1 (kvMi x) (kvMi_dec x)
    rw [e]
    iapply HΦ'
    itrivial
  isplitr
  · -- Unknown
    iintro %x
    iintro !> %Φ' - HΦ'
    wp_auto
    change Iris.ProofMode.Entails' _ (Φ' #(boxOut errOut))
    iapply HΦ'
    itrivial
  isplitr
  · -- IsUnknown, an output
    iintro %o
    iintro !> %Φ' - HΦ'
    wp_auto
    rw [o.2.1]
    iapply HΦ'
    itrivial
  · -- IsUnknown, an unknown output
    iintro %x
    iintro !> %Φ' - HΦ'
    wp_auto
    iapply HΦ'
    itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
