module
public import Spec.go_etcd_io.bbolt.DB__View

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

variable [AllG GF]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

theorem DB.View.wp_proof (hBegin : DB.Begin.spec (GF := GF) (hG := hG))
    (hRollback : Tx.Rollback.spec (GF := GF) (hG := hG)) :
    DB.View.spec (GF := GF) (hG := hG) := by
  intro I dbl γ σ fn P Q hAdd hRem hsize hfn
  wp_start as ⟨Hdb, HP⟩
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  wp_apply hBegin I dbl γ σ hAdd hsize $$ [Hdb] as %txl ⟨%k, %r, %Hk, Hdb, Hrtx⟩
  · iframe
  try wp_auto
  -- `t.managed = true`
  simp only [ownReadTx]
  iNamed Hrtx
  try wp_auto
  try simp only
  ihave Hrtx : ownReadTx dbl γ txl k r σ.data σ.ps true $$ [Htx Hmeta Hroot Hrdata Hrps Hpages Hrl Hkey]
  · simp only [ownReadTx]; iexists _, mv; iframe; ipureintro
    obtain ⟨a, b, c, _, rest⟩ := Ht; exact ⟨a, b, c, rfl, rest⟩
  have Hk' : (σ.addReader k r).readers !! k = some r := GMap.lookup_insert _ _ _
  have hfn' := hfn txl k r (σ.addReader k r) Hk'
  simp only [DBState.addReader.proj_data, DBState.addReader.proj_ps] at hfn'
  wp_apply hfn' $$ [Hdb Hrtx HP] as %e ⟨%σ2, %Hσ2, Hdb, Hrtx, HQ⟩
  · iframe
  try wp_auto
  -- `t.managed = false`
  simp only [ownReadTx]
  iNamed Hrtx
  try wp_auto
  try simp only
  obtain ⟨Hd2, Hp2⟩ := Hσ2
  ihave Hrtx : ownReadTx dbl γ txl k r σ2.data σ2.ps false $$ [Htx Hmeta Hroot Hrdata Hrps Hpages Hrl Hkey]
  · simp only [ownReadTx]; rw [Hd2, Hp2]; iexists _, mv; iframe; ipureintro
    obtain ⟨a, b, c, _, rest⟩ := Ht; exact ⟨a, b, c, rfl, rest⟩
  cases e with
  | nil =>
    try wp_auto
    wp_apply hRollback I dbl γ σ2 txl k r hRem $$ [Hdb Hrtx] as ⟨%ro, %t2, %Hk2, Hdb, Htx, %Ht2⟩
    · iframe
    try wp_auto
    rw [Ht2, decide_eq_true rfl]
    try wp_auto
    iapply HΦ; iexists _; iframe
  | ok i =>
    try wp_auto
    wp_apply hRollback I dbl γ σ2 txl k r hRem $$ [Hdb Hrtx] as ⟨%ro, %t2, %Hk2, Hdb, Htx, %Ht2⟩
    · iframe
    try wp_auto
    rw [Ht2, decide_eq_true rfl]
    try wp_auto
    iapply HΦ; iexists _; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
