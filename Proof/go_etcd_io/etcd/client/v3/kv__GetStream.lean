/-
Proof of `Spec/go_etcd_io/etcd/client/v3/kv__GetStream.lean` (etcd#21330). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.kv__GetStream
public import Proof.go_etcd_io.etcd.client.v3.OpGetRes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem kv.GetStream.wp_proof
    (wp_NewOp : NewOp.spec (GF := GF) (hG := hG)) :
    kv.GetStream.spec (GF := GF) (hG := hG) := by
  intro api ci key sl gs R
  wp_start as ⟨#Hopts, HR, %Hnp, #Hek⟩
  obtain ⟨Hnp, -, hk⟩ := Hnp
  iunfold emptyKeyOk at Hek
  icases Hek with ⟨%e, #He, %Hev, #Hse⟩
  wp_auto
  wp_apply (opGet_res wp_NewOp key sl gs R) $$ [$HR] as %opv ⟨#Hat, HR⟩
  · iframe #; ipureintro; exact Hnp
  ihave Hat' := Hat
  iunfold opFullAt at Hat'
  icases Hat' with ⟨-, #Hkey0, -, -, -⟩
  ihave %Hklen := ownSlice_len _ _ _ $$ Hkey0
  have hkz : opv.key'.len = W64 0 := by
    have h := Hklen; rw [hk] at h; simp at h; word
  rw [decide_eq_true hkz]
  wp_auto
  iapply HΦ
  iframe HR
  iframe #
  ipureintro
  exact ⟨rfl, Hev⟩

end proof

end EtcdGrove
end Perennial
