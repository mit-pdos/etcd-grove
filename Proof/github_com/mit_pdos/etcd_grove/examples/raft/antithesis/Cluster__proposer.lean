/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Cluster__proposer.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__proposer
public import Perennial.Spec.strconv.FormatUint
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__running
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__pick
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__deliver
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessPersist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem Cluster.proposer.wp_proof (wp_FormatUint : strconv.FormatUint.spec (GF := GF) (hG := hG))
    (wp_running : Cluster.running.spec (GF := GF) (hG := hG))
    (wp_pick : Cluster.pick.spec (GF := GF) (hG := hG))
    (wp_deliver : Cluster.deliver.spec (GF := GF) (hG := hG)) :
    Cluster.proposer.spec (GF := GF) (hG := hG) := by
  intro c γ
  wp_start as ⟨#Hc, Htok⟩
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, %Hmode, #Hr, #Hrec, #Hro, #Hnodes, #Hstop, #Hbc,
    #Hnj, #Hmu, #Hinv, %Hfits, #Hpm, #_Hsinv⟩
  ihave Hcf := Hcfg
  iStructNamed Hcf
  wp_auto
  ihave #Hsc : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  ihave IH : iprop(∃ kv : w64, "c" ∷ c_ptr ↦ c ∗ "k" ∷ k_ptr ↦ kv) $$ [c k]
  · iframe
  wp_for IH
  wp_apply wp_running c γ $$ [$Hpkg $Hc] as %b -
  wp_if_destruct
  · try wp_auto
    wp_apply wp_pick c γ $$ [$Hpkg $Hc] as %n ⟨%j, #Hn⟩
    try wp_auto
    wp_apply wp_FormatUint kv (W64 10) (by decide) (by decide) $$ [$Hsc]
    try wp_auto
    wp_apply wp_string_to_bytes as %ds ⟨Hds, -⟩
    imod ownSlice_persist $$ Hds with #Hds
    ihave #Hpm' := Hpm
    iunfold propMinter at Hpm'
    ihave Hp : iprop(|={⊤}=> propOk γ (go!"v" ++ internal.strconv.fmtUint kv (W64 10))) $$ []
    · iapply Hpm'
    imod Hp with Hp
    try wp_auto
    wp_apply wp_deliver c γ n j _ $$ [$Hpkg $Hc $Hn Hds Hp]
    · iunfold inputOk
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _
      iframe
      iexact Hds
    try wp_auto
    wp_for_post
    iframe
    iexists _
    iframe
  · wp_if_destruct
    · try wp_auto
      iapply HΦ
      iframe
    · exfalso; cases b <;> simp_all

end proof

end AntHarness
end EtcdGrove
end Perennial
