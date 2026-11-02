/-
Proofs of `Spec/github_com/mit_pdos/etcd_grove/examples/restart3/put.lean` (the restart plan's R2,
2026-11-02): the context with the request timeout (`client.wp_WithTimeout_bg`), `cli.Put`
(`client.client_Put_own`, `client.client_Put_other`), `cancel()`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.restart3.put
public import Perennial.Spec.context.Background
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace restart3

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.restart3.Assumptions]

theorem put.wp_proof
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG)) :
    put.spec (GF := GF) (hG := hG) := by
  intro CS CRE CEC cl ep V E γr γf cid mid key val hsz hAs
  wp_start as ⟨#Hcl, #Hregs, #Hinv⟩
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %pctx %pcd %pcancel ⟨#Hpcancel, #Hpctx, #Hpce, -⟩
  (try wp_auto)
  imod mvcc.idxCert_nil (GF := GF) E.γ.idx with #HF0
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
  wp_apply (client.client_Put_own cl ep V E γr γf cid mid pctx pcd key val slice.nil [] hsz)
    as %presp %perr Hput
  · iframe #
  (try wp_auto)
  wp_apply Hpcancel
  (try wp_auto)
  iapply HΦ
  icases Hput with (⟨%Hperr, -, #Hflag⟩ | ⟨%Hperr, -⟩)
  · iright; iframe #; ipureintro; exact Hperr
  · ileft; ipureintro; exact Hperr

theorem put.wp_proofOther
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG)) :
    put.specOther (GF := GF) (hG := hG) := by
  intro CS CRE CEC cl ep V E γr γf cid mid key val key' val' hne hsz hAs
  wp_start as ⟨#Hcl, #Hregs, #Hinv⟩
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %pctx %pcd %pcancel ⟨#Hpcancel, #Hpctx, #Hpce, -⟩
  (try wp_auto)
  imod mvcc.idxCert_nil (GF := GF) E.γ.idx with #HF0
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
  wp_apply (client.client_Put_other cl ep V E γr γf cid mid pctx pcd key val key' val' hne
      slice.nil [] hsz) as %presp %perr Hput
  · iframe #
  (try wp_auto)
  wp_apply Hpcancel
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end restart3
end EtcdGrove
end Perennial
