/-
Lean-first (no Rocq counterpart).

The proof of `(*Replay).InitialEvents`: the state at `rv` (`replayAt`'s map), then its
`initialEvents`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Replay__InitialEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__initialEvents

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)


section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem Replay.InitialEvents.wp_proof
    (wp_initialEvents : Model.initialEvents.spec (GF := GF) (hG := hG)) :
    Replay.InitialEvents.spec (GF := GF) (hG := hG) := by
  intro rp R x req rv hrv
  wp_start as ⟨#HR, #Hreq⟩
  unfold replayAt
  icases HR with ⟨#Hdrv, %sm, %M, %csl, %cvs, #Hrp, #Hsm, %HMs, %HMrv, %HMch, #HMm, #Hcsl, #Hcvs⟩
  unfold wreqRep
  icases Hreq with ⟨%p, %hreq, #Hsie⟩
  subst hreq
  iStructNamed Hrp
  wp_auto
  wp_apply (wp_map_lookup2 (K := w64) (V := Loc) go.uint64 _ sm M rv DFrac.discard) $$ Hsm as -
  obtain ⟨st, hst⟩ := Option.isSome_iff_exists.1 hrv
  obtain ⟨mp, hmp⟩ : ∃ mp, M !! rv = some mp := by
    have := HMs rv
    rw [hrv] at this
    exact Option.isSome_iff_exists.1 this
  rw [hmp]
  simp only [Option.isSome_some, decide_true, Option.getD_some]
  wp_auto
  ihave ⟨%m, %hm, #Hq⟩ := BigSepM.bigSepM_lookup (Φ := fun rv mp =>
    iprop(∃ m, ⌜R.states !! rv = some m⌝ ∗ modelAt (GF := GF) mp m)) hmp $$ HMm
  rw [hst] at hm
  cases hm
  wp_apply (wp_initialEvents mp st x x.WKey' (watchOptsV x p) x.Bookmarks' rfl rfl) $$ [Hq]
    as %sl %err ⟨%herr, #Hsl⟩
  · iexact Hq
  iapply HΦ
  isplitr
  · ipureintro; exact herr
  iexists ((listItemsL x x.WKey' st).map fun o => ⟨evAdded, .obj o⟩)
  isplitr
  · ipureintro; simp [initialEventsR, hst]
  · iexact Hsl

end proof

end k8s_correctness
end EtcdGrove
end Perennial
