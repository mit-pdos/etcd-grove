/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/partition/startCluster.lean` (W4 of
`notes/watch-cut-plan.md`, 2026-10-22; `Main`'s proof's start until then; over the cluster's
library `cluster3` since 2026-11-05). Lean-first (no Rocq counterpart).

The configuration (`config`, `clusterCfg`, which meets `cluster3.cfgOk`); the members and the
bridges (`cluster3.StartCluster`, the named premises `premises` its own at `clusterCfg`); then
three clients (`cluster3.NewClient`), each at the watch environment of the three members
(`cluster3.watchEnv`, at the members' watch servers that `cluster3.clusterUp` names); the
clients' slice and `clusterUp`. Every step's error ends with `ok = false`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.partition.startCluster
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.partition.config
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartCluster
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.NewClient

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_partition

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.partition.Assumptions]

set_option maxHeartbeats 1000000 in
theorem startCluster.wp_proof
    (wp_config : config.spec (GF := GF) (hG := hG))
    (wp_StartCluster : cluster3.StartCluster.spec (GF := GF) (hG := hG))
    (wp_NewClient : cluster3.NewClient.spec (GF := GF) (hG := hG)) :
    startCluster.spec (GF := GF) (hG := hG) := by
  intro CS N id₁ id₂ id₃ ps ctxs boot lg pfx Hbf Hlg Htb Hrb48 HrbN HwbN Hck Haf Hbuq Hrf Hdbo Hms
  wp_start as ⟨Hstart, Htok, #Hprem⟩
  iunfold premises at Hprem
  (try wp_auto)
  -- `cfg := config()`
  wp_apply wp_config
  (try wp_auto)
  -- `cluster3.StartCluster(cfg, lg)`: the members and the bridges
  wp_apply (wp_StartCluster clusterCfg N id₁ id₂ id₃ ps ctxs boot lg false .none clusterCfg_ok Hbf Hlg Htb Hrb48
      HrbN HwbN Hck Haf Hbuq Hrf Hdbo Hms lease.runCfg_none (by decide) (fun h => absurd rfl h))
    $$ [Hstart Htok] as %srvs %brs %ok Hup
  · iframe; iframe #
  icases Hup with (%Hok | ⟨%Hok, Htok, Hup⟩)
  · subst Hok
    wp_auto
    iapply HΦ; ileft; ipureintro; rfl
  subst Hok
  wp_auto
  iunfold cluster3.clusterUp at Hup
  icases Hup with ⟨%γ, %γn, %ρ₁, %ρ₂, %ρ₃, %E₁, %E₂, %E₃, %cid₁, %cid₂, %cid₃, %mid₁, %mid₂,
    %mid₃, %R₁, %R₂, %R₃, %s₁, %s₂, %s₃, %br₁, %br₂, %br₃, Hcl⟩
  -- three clients, each of every bridge (failover, 2026-10-21, D27), at the members' watch
  -- environment
  wp_apply (wp_NewClient clusterCfg lg (cluster3.watchEnv clusterCfg R₁ R₂ R₃ ρ₁.rd pfx)
      clusterCfg_ok (by omega) Hlg) as %cl₁ %cerr₁ Hcl₁
  icases Hcl₁ with (Hok₁ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr₁ with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; ipureintro; rfl
  icases Hok₁ with ⟨%Hcerr, #Hnc₁, -⟩
  subst Hcerr
  wp_auto
  wp_apply (wp_NewClient clusterCfg lg (cluster3.watchEnv clusterCfg R₁ R₂ R₃ ρ₁.rd pfx)
      clusterCfg_ok (by omega) Hlg) as %cl₂ %cerr₂ Hcl₂
  icases Hcl₂ with (Hok₂ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr₂ with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; ipureintro; rfl
  icases Hok₂ with ⟨%Hcerr, #Hnc₂, -⟩
  subst Hcerr
  wp_auto
  wp_apply (wp_NewClient clusterCfg lg (cluster3.watchEnv clusterCfg R₁ R₂ R₃ ρ₁.rd pfx)
      clusterCfg_ok (by omega) Hlg) as %cl₃ %cerr₃ Hcl₃
  icases Hcl₃ with (Hok₃ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr₃ with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; ipureintro; rfl
  icases Hok₃ with ⟨%Hcerr, #Hnc₃, -⟩
  subst Hcerr
  wp_auto
  -- `clis := []*clientv3.Client{cli1, cli2, cli3}`
  wp_apply wp_slice_literal (V := Loc) (l := [cl₁, cl₂, cl₃])
  try (isplitr; (ipureintro; rfl))
  iintro %clisp ⟨Hclis, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  imod ownSlice_persist _ _ _ $$ Hclis with #Hclis
  (try wp_auto)
  iapply HΦ
  iright
  isplitr
  · ipureintro; rfl
  iframe Htok
  iunfold clusterUp
  iexists γ, γn, ρ₁, ρ₂, ρ₃, E₁, E₂, E₃, cid₁, cid₂, cid₃, mid₁, mid₂, mid₃, R₁, R₂, R₃,
    s₁, s₂, s₃, cl₁, cl₂, cl₃, br₁, br₂, br₃
  iframe; iframe #

end proof

end etcd_partition
end EtcdGrove
end Perennial
