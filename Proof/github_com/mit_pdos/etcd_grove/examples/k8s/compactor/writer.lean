/-
The proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/compactor/writer.lean`. Lean-first.

Each round: a context with the request timeout (`client.wp_WithTimeout_bg`), `Itoa(i)` (`fmtInt i 10`),
the client's put at its KV handle (`client_Put_kv`) with the invariant's update for a put of another
key (`putAu_other`: `writeKey` is not `compact_rev_key`), the cancel.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.writer
public import Spec.strconv.Itoa
public import Perennial.Spec.context.Background
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Aus

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_compactor

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver k8s

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Assumptions]

/-- The writer's key. -/
abbrev writeKeyS : GoString := go!"/registry/objs/w"

theorem writer.wp_proof
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Itoa : EtcdGrove.strconv.Itoa.spec (GF := GF) (hG := hG)) :
    writer.spec (GF := GF) (hG := hG) := by
  intro _ _ _ _ cl γk γ
  wp_start as ⟨#Hko, #Hinv⟩
  rw [show github_com.mit_pdos.etcd_grove.examples.k8s.compactor.writeKey = #writeKeyS from rfl]
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Pstr : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  iunfold clientKvOk at Hko
  icases Hko with ⟨%api, %dup, #Hkvf, #Hkv⟩
  ihave #Hnil : optsAt (GF := GF) slice.nil [] $$ []
  · iunfold optsAt
    iexists ([] : List GoFunc)
    isplitl
    · iapply ownSlice_nil
    isplitl
    · ipureintro; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    simp at Hf
  wp_auto
  ihave IH : (∃ n : w64, "i" ∷ i_ptr ↦ n : IProp GF) $$ [i]
  · iexists _; iframe
  wp_for IH
  wp_if_destruct
  · wp_apply wp_Background
    (try iintro -)
    (try wp_auto)
    wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny EtcdGrove.rpctypesEtcdError_asTarget _) $$ []
      as %ctx %cd %cancel ⟨#Hcancel, #Hctx, #Hce, -⟩
    (try wp_auto)
    wp_apply (wp_Itoa n) as %str %Hstr
    subst Hstr
    (try wp_auto)
    wp_apply (client.client_Put_kv cl api γk dup ctx cd writeKeyS (fmtInt n (W64 10)) slice.nil
        (fun _ => iprop(True))
        (opSizeOk_opPutModel (K := 16) (E := 0) (V := 66) (optsKeep_nil _ _ _) (by decide)
          (fmtInt_length_le _ _) (by decide))) $$ [] as %resp %err -
    · iframe #
      ihave #Hau := putAu_other γk γ writeKeyS (fmtInt n (W64 10)) (by decide) $$ Hinv
      cases dup <;> simp only [intuitionisticallyIf, Bool.false_eq_true, ↓reduceIte] <;> iexact Hau
    (try wp_auto)
    wp_apply Hcancel
    (try iintro -)
    (try wp_auto)
    wp_for_post
    iframe
    iexists _; iframe
  · (try wp_auto)
    iapply HΦ
    itrivial

end proof

end k8s_compactor
end EtcdGrove
end Perennial
