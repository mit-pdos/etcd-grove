/-
`state.apply`: `Updater.Apply` of the typed configuration, not forced, its result stored (the
premise excludes conflicts). The state's pieces are persistent (`*_persistent`); a returned
object is not nil (`isTV_isTVv`). Lean-first (2026-11-19).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.state__apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.state__typedObj
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__Apply
public import Proof.sigs_k8s_io.structured_merge_diff.v7.Laws
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.WalkerLaws
public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Persist
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open smd

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.smd.Assumptions]

/-- A typed value's pointer is not nil. -/
theorem isTV_not_null (hTVv : isTV_isTVv.law (GF := GF)) (p sc : Loc) (S : Schema) (t : TypeRef)
    (x : UVal) : isTV (GF := GF) p sc S t x ⊢ ⌜p ≠ null⌝ := by
  iintro Hp
  ihave Hp := (hTVv p sc S t x).1 $$ Hp
  icases Hp with ⟨%tv, Hp, -⟩
  iapply typedPointsto_not_null $$ Hp

theorem state.apply.wp_proof_of
    (hSchP : isSchema_persistent.law (GF := GF)) (hTVP : isTV_persistent.law (GF := GF))
    (hMFP : isMF_persistent.law (GF := GF)) (hUP : isUpdater_persistent.law (GF := GF))
    (hCvP : isIdentityConverter_persistent.law (GF := GF)) (hTVv : isTV_isTVv.law (GF := GF))
    (wp_typedObj : state.typedObj.spec (GF := GF))
    (wp_Apply : smd.merge.Updater.Apply.spec (GF := GF)) :
    state.apply.spec (GF := GF) := fun s sc st m kvs mgr msg obj mf' => by
  wp_start as ⟨Hst, Hm, %hconf, %hpre, %hsmall, %hres⟩
  unfold ownState
  icases Hst with ⟨%u, %lv, %mfm, %cv, Hs, Hsc, Hu, Hcv, Hlv, Hmf⟩
  ihave #Hsc := hSchP _ _ $$ Hsc
  ihave #Hu := hUP _ _ _ _ _ $$ Hu
  ihave #Hcv := hCvP _ $$ Hcv
  ihave #Hlv := hTVP _ _ _ _ _ $$ Hlv
  ihave #Hmf := hMFP _ _ $$ Hmf
  wp_auto
  wp_apply (wp_typedObj s sc u lv mfm m kvs) $$ [Hs Hm] as %cp ⟨Hs, Hcp⟩
  · iframe Hs Hsc Hm
    ipureintro; exact hconf
  ihave #Hcp := hTVP _ _ _ _ _ $$ Hcp
  wp_apply (wp_Apply u cv false sc sc0 rootRef lv cp st.live (.map kvs) version mfm st.mf mgr false)
    as %op %mfm2 %err Hpost
  · iframe Hu Hcv Hlv Hcp Hmf
    ipureintro; exact ⟨hpre, hsmall⟩
  rw [hres]
  icases Hpost with ⟨%herr, Hmf2, Hop⟩
  subst herr
  ihave #Hmf2 := hMFP _ _ $$ Hmf2
  cases obj with
  | none =>
    icases Hop with %hop
    subst hop
    wp_auto
    simp only [Option.isSome_none, Option.isSome_some, Option.getD_none, Option.getD_some]
    iapply HΦ
    iexists u, lv, mfm2, cv
    iframe Hs Hsc Hu Hcv Hlv Hmf2
  | some x =>
    ihave #Hop := hTVP _ _ _ _ _ $$ Hop
    ihave %hop : ⌜op ≠ null⌝ $$ [Hop]
    · iapply isTV_not_null hTVv $$ Hop
    wp_auto
    simp only [hop, decide_false]
    wp_auto
    simp only [Option.isSome_none, Option.isSome_some, Option.getD_none, Option.getD_some]
    iapply HΦ
    iexists u, op, mfm2, cv
    iframe Hs Hsc Hu Hcv Hop Hmf2

theorem state.apply.wp_proof
    (wp_typedObj : state.typedObj.spec (GF := GF))
    (wp_Apply : smd.merge.Updater.Apply.spec (GF := GF)) :
    state.apply.spec (GF := GF) :=
  state.apply.wp_proof_of isSchema_persistent_law_holds isTV_persistent_law_holds
    isMF_persistent_law_holds isUpdater_persistent_law_holds isIdentityConverter_persistent_law_holds
    isTV_isTVv_law_holds wp_typedObj wp_Apply

end proof

end k8s_smd
end EtcdGrove
end Perennial
