/-
Proof of `authStore.selectPassword` (`server/auth/store.go`) over its translated body
(prove-authcrypto, 2026-11-21; until then an axiom at the trust boundary, the code names only):
bcrypt's `GenerateFromPassword` (the trust boundary) when a password is given without a hash, else
base64's `StdEncoding.DecodeString` of the hash (proved over the real `encoding/base64`, reached
through the package fact `stdDecInit`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__selectPassword
public import Spec.golang_org.x.crypto.bcrypt.GenerateFromPassword

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.selectPassword.wp_proof
    (h_gen : bcrypt.GenerateFromPassword.spec (GF := GF) (hG := hG)) :
    auth.authStore.selectPassword.spec (GF := GF) (hG := hG) := by
  intro st password hashed
  wp_start as ⟨%Hst, %c, #Hc, %Hc31⟩
  ihave #Hb64 : isPkgInit (PROP := IProp GF) pkg_id.encoding.base64 $$ []
  · iPkgInit
  ihave ⟨%e, #He, #Hdec⟩ := encoding.base64.stdDecInit_access $$ Hb64
  ihave #Hbc : isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.crypto.bcrypt $$ []
  · iPkgInit
  try wp_auto
  wp_if_destruct
  · -- `password == ""`: decoded
    try wp_auto
    wp_bind (App (Val _) (Val _))
    iapply Hdec
    inext
    iintro %b %err %bs Hb %Herr
    imod ownSlice_persist b _ _ $$ Hb with #Hb
    try wp_auto
    iapply HΦ
    iexists bs; iframe Hb; ipureintro
    unfold selectPwOk; rw [if_neg (by simp_all)]; exact Herr
  · -- `password != ""`
    have hpw := Hif
    wp_if_destruct
    · -- `hashedPassword == ""`: hashed with bcrypt
      have hh := Hif
      try wp_auto
      wp_apply wp_string_to_bytes password as %psl ⟨Hpsl, -⟩
      try wp_auto
      wp_bind (App (App (Val _) (Val _)) (Val _))
      iapply h_gen $$ [Hpsl]
      · iframe; iPkgInit
      inext
      iintro %h %err ⟨Hpsl, Hor⟩
      icases Hor with (⟨%ei, %Hei, #Hm, %Hnil, %Hcond⟩ | ⟨%Hnil, %Hcond, %hs, Hh⟩)
      · subst Hnil
        try wp_auto
        iapply HΦ
        iexists []
        isplitr
        · iapply ownSlice_nil
        ipureintro
        unfold selectPwOk
        rw [if_pos (by constructor <;> simp_all)]
        constructor
        · intro h; rw [Hei.1] at h; cases h
        · intro h; omega
      · imod ownSlice_persist h _ _ $$ Hh with #Hh
        try wp_auto
        iapply HΦ
        iexists hs; iframe Hh; ipureintro
        unfold selectPwOk
        rw [if_pos (by constructor <;> simp_all)]
        exact ⟨fun _ => Hcond.1, fun _ => Hnil⟩
    · -- decoded
      have hh := Hif
      try wp_auto
      wp_bind (App (Val _) (Val _))
      iapply Hdec
      inext
      iintro %b %err %bs Hb %Herr
      imod ownSlice_persist b _ _ $$ Hb with #Hb
      try wp_auto
      iapply HΦ
      iexists bs; iframe Hb; ipureintro
      unfold selectPwOk; rw [if_neg (by simp_all)]; exact Herr

end proof

end EtcdGrove
end Perennial
