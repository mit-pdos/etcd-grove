/-
`Bucket.Put_kv`'s proof: bbolt's proved `Bucket.Put` at the program's file extension (`theFs`), over
the backend's vocabulary (`InvBbolt.lean`; stage S1b of `notes/bbolt-integration-plan.md`).
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__Put_kv
public import Spec.go_etcd_io.bbolt.Bucket__Put

@[expose] public section

set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem bbolt.Bucket.Put_kv.wp_proof
    (h : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [os.file.FieldAssumptions]
      [os.fileStat.FieldAssumptions], bbolt.Bucket.Put.spec (GF := GF) (hG := hG)) :
    bbolt.Bucket.Put_kv.spec (GF := GF) (hG := hG) := by
  intro tx γ D S G b n g m key value kb vb dk hg hm hk0 hk1 hkv
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax⟩
  · simp only [backend.ownWTxG, backend.txLive, backend.wBkt, onFs_none hfs]
    iintro %Φ ⟨-, H, -⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.ownWTxG, backend.txLive, backend.wBkt, onFs_some hfs]
    iintro %Φ ⟨-, Hl, #Hb, Hk, #Hv⟩ HΦ
    subst hg
    have h' := h tx γ (wView D S G) b n m key value kb vb dk
    try simp only [wView.proj_rw, wView.proj_base, wView.proj_cur, wView.proj_gen, wView_setBkt] at h'
    wp_apply h' $$ [$Hl $Hb $Hk $Hv] as %err ⟨Hk, Hres⟩
    · ipureintro; exact ⟨trivial, hm, hkv⟩
    have hne : ¬ (kb.length = 0 ∨ bbolt.maxKeySize < kb.length) := by
      unfold backend.maxKeySize at hk1; unfold bbolt.maxKeySize; omega
    rw [if_neg hne]
    icases Hres with ⟨%He, Hl⟩
    subst He
    iapply HΦ; iframe

end proof

end EtcdGrove
end Perennial
