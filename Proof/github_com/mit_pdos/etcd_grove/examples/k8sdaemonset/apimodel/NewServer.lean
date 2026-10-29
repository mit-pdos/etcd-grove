/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/NewServer.lean`.
Lean-first: the server's fields and tables allocated, its ghost state (the history `[St.empty]`,
its halves the lock invariant's and the caller's; no watcher) created, and its lock initialized.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.NewServer
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.newTable
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.emptyPod
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.emptyNode
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.emptyDaemonSet
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.emptyRevision
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.HistLemmas
public import Perennial.Spec.sync.NewCond

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

theorem St.empty_wf : St.empty.wf := by
  refine ⟨by simp [St.empty], ?_, ?_, ?_, ?_, by simp [St.empty], ?_⟩ <;>
    first
    | (intro r; cases r <;> simp [St.empty, St.tbl, replay])
    | (intro r c hc; cases r <;> simp [St.empty, St.tbl] at hc)

theorem histOk_empty : histOk ([] ++ [St.empty]) :=
  ⟨by simpa using St.empty_wf, by simp⟩

theorem decStr_one : decStr (W64 1) = go!"1" := by
  rw [decStr_eq]
  rw [show (W64 1).toNat = 1 from rfl, baseDigits]
  simp [digitChar]

theorem issuedMap_one : issuedMap 1 = <[go!"1" := W64 1]> (∅ : GMap GoString w64) := by
  show <[decStr (W64 1) := W64 1]> (∅ : GMap GoString w64) = _
  rw [decStr_one]

theorem NewServer.wp_proof
    (wp_newTable : newTable.spec (GF := GF) (hG := hG))
    (wp_emptyPod : emptyPod.spec (GF := GF) (hG := hG))
    (wp_emptyNode : emptyNode.spec (GF := GF) (hG := hG))
    (wp_emptyDaemonSet : emptyDaemonSet.spec (GF := GF) (hG := hG))
    (wp_emptyRevision : emptyRevision.spec (GF := GF) (hG := hG))
    (wp_NewCond : sync.NewCond.spec (GF := GF) (hG := hG)) :
    NewServer.spec (GF := GF) (hG := hG) := by
  intro _ cfg
  wp_start as %Hbound
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #HemptyPod : (emptyOk (GF := GF) Res.pods (functions apimodel.emptyPod [])) $$ []
  · unfold emptyOk
    imodintro
    iintro %Φ' - HΦ'
    wp_apply wp_emptyPod as %x Hx
    iapply HΦ'
    iexact Hx
  ihave #HemptyNode : (emptyOk (GF := GF) Res.nodes (functions apimodel.emptyNode [])) $$ []
  · unfold emptyOk
    imodintro
    iintro %Φ' - HΦ'
    wp_apply wp_emptyNode as %x Hx
    iapply HΦ'
    iexact Hx
  ihave #HemptyDaemonSet : (emptyOk (GF := GF) Res.daemonSets (functions apimodel.emptyDaemonSet [])) $$ []
  · unfold emptyOk
    imodintro
    iintro %Φ' - HΦ'
    wp_apply wp_emptyDaemonSet as %x Hx
    iapply HΦ'
    iexact Hx
  ihave #HemptyRevision : (emptyOk (GF := GF) Res.revisions (functions apimodel.emptyRevision [])) $$ []
  · unfold emptyOk
    imodintro
    iintro %Φ' - HΦ'
    wp_apply wp_emptyRevision as %x Hx
    iapply HΦ'
    iexact Hx
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := w64)) as %rvs Hrvs
  (try wp_auto)
  wp_apply (wp_mapInsert go.string rvs ∅ (go!"1") (W64 1)) $$ Hrvs as Hrvs
  (try wp_auto)
  rename_i s
  iStructNamedSuffix «$r0» "_f"
  wp_apply wp_NewCond $$ [$Hsync] as %cond #Hcond
  (try wp_auto)
  have hTp := wp_newTable Res.pods (functions apimodel.emptyPod [])
  simp only [grOf, Res.namespaced] at hTp
  wp_apply hTp $$ [$HemptyPod] as %tp %op ⟨#Hfp, Htp⟩
  (try wp_auto)
  have hTn := wp_newTable Res.nodes (functions apimodel.emptyNode [])
  simp only [grOf, Res.namespaced] at hTn
  wp_apply hTn $$ [$HemptyNode] as %tn %on ⟨#Hfn, Htn⟩
  (try wp_auto)
  have hTd := wp_newTable Res.daemonSets (functions apimodel.emptyDaemonSet [])
  simp only [grOf, Res.namespaced] at hTd
  wp_apply hTd $$ [$HemptyDaemonSet]
    as %td %od ⟨#Hfd, Htd⟩
  (try wp_auto)
  have hTc := wp_newTable Res.revisions (functions apimodel.emptyRevision [])
  simp only [grOf, Res.namespaced] at hTc
  wp_apply +noauto hTc $$ [$HemptyRevision]
    as %tc %oc ⟨#Hfc, Htc⟩
  iapply wp_fupd
  (try wp_auto)
  iStructNamedSuffix cfg_f "_c"
  ipersist changed_f
  ipersist rvs_f
  ipersist pods_f
  ipersist nodes_f
  ipersist daemonSets_f
  ipersist revisions_f
  ipersist FailWrites_c
  ipersist AmbiguousWrites_c
  ipersist FailReads_c
  ipersist EndWatches_c
  ipersist ExpireWatches_c
  ipersist Bookmarks_c
  ipersist FaultPercent_c
  imod (mono_list_own_alloc (GF := GF) ([] ++ [St.empty])) with ⟨%γh, Hh, -⟩
  icases (monoList_halves (GF := GF) γh ([] ++ [St.empty])).2 $$ Hh with ⟨Hh1, Hh2⟩
  imod (ghost_map_alloc (GF := GF) (∅ : GMap Loc (List Nat))) with ⟨%γw, Hw, -⟩
  imod (receipt_zero (GF := GF)) with Hrc
  imod (sync.init_Mutex (lockInv «$r0_ptr» ⟨γh, γw⟩ ⟨cond, rvs,
      ⟨tp, op, functions apimodel.emptyPod []⟩, ⟨tn, on, functions apimodel.emptyNode []⟩,
      ⟨td, od, functions apimodel.emptyDaemonSet []⟩, ⟨tc, oc, functions apimodel.emptyRevision []⟩⟩)
      ⊤ _) $$ mu_f [rev_f uids_f Hrvs Htp Htn Htd Htc Hrc Hh1 Hw] with #Hmu
  · inext
    iunfold lockInv
    iexists St.empty, []
    isplitl [rev_f uids_f Hrvs Htp Htn Htd Htc Hrc]
    · iunfold srvLocked
      simp only [named, St.empty]
      iframe
      isplitl [Hrvs]
      · rw [show (W64 1).toNat = 1 from rfl, issuedMap_one]
        iexact Hrvs
      isplitl [Htp Htn Htd Htc]
      · iunfold tablesLocked
        iframe
      ipureintro; decide
    iframe
    isplitr
    · ipureintro; exact histOk_empty
    iunfold watchersLocked
    iexists ∅
    iframe
    iapply (BigSepM.bigSepM_empty (PROP := IProp GF)).2
    itrivial
  imodintro
  ihave HΦ' := HΦ $$ %«$r0_ptr» %(ApiNames.mk γh γw)
  iapply HΦ'
  isplitr [Hh2]
  · iunfold isServer
    iexists (⟨cond, rvs, ⟨tp, op, functions apimodel.emptyPod []⟩, ⟨tn, on, functions apimodel.emptyNode []⟩, ⟨td, od, functions apimodel.emptyDaemonSet []⟩, ⟨tc, oc, functions apimodel.emptyRevision []⟩⟩ : SrvLocs)
    unfold srvFixed cfgAt
    simp only [named, tableOf, resField]
    iframe #
    ipureintro; exact Hbound
  iunfold apiState
  iexists []
  iframe
  ipureintro; exact histOk_empty

end proof

end apimodel
end EtcdGrove
end Perennial
