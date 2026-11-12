/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leasecatchup/run.lean` (lease-mono3
step 1, 2026-11-06, `notes/lease-mono3-plan.md`, Scope §2). Lean-first.

The steps: `config()`; `cluster3.StartCluster` at the monotone lease mode (`lease.runCfg_mono`,
`leasePeersOk`), whose success gives each member at its bridge (`cluster3.memberAt … .mono`), and
of it the grant and listing at its lessor's history registered at the bridge's address
(`cluster3.memberAt_mono`); `etcdstart.NewClients` of member 3's bridge, then of member 1's;
`grant(c3)` at `etcdLeaseGrantSpec (mvcc.api.mvccLeases E₃.γ)`, `Q` keeping `g1` granted at an index of member 3's
lessor history; the two cuts (`cluster3.PeerStep`, over the members' `srvPeerCtl`s); the fillers
(`grant(c1)` at member 1's spec, `Q = True`: only the last filler's id is kept); the two mends; the
polls, each `leases(c3)` at `etcdLeaseLeasesSpec (mvcc.api.mvccLeases E₃.γ)` handing in `[g1]` with its grant, so
that `Q` says the listing lists `g1`, and `listed`; the panic is unreachable.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.run
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.config
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.grant
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.leases
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.listed
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartCluster
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.PeerStep
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NewClients

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leasecatchup

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Assumptions]

/-- A loop counter below its bound `b` (`b < 2 ^ 62`) stays in `[0, b]` once incremented. -/
theorem incr_le (j : w64) (b : Nat) (h0 : 0 ≤ sint.Z j) (h1 : sint.Z j < (b : Int))
    (hb : b < 2 ^ 62) : 0 ≤ sint.Z (j + W64 1) ∧ sint.Z (j + W64 1) ≤ (b : Int) := by
  constructor <;> word

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8192 in
/-- See the file header. -/
theorem run.wp_proof
    (wp_config : config.spec (GF := GF) (hG := hG))
    (wp_StartCluster : cluster3.StartCluster.spec (GF := GF) (hG := hG))
    (wp_NewClients : etcdstart.NewClients.spec (GF := GF) (hG := hG))
    (wp_grant : grant.spec (GF := GF) (hG := hG))
    (wp_leases : leases.spec (GF := GF) (hG := hG))
    (wp_listed : listed.spec (GF := GF) (hG := hG))
    (wp_PeerStep : cluster3.PeerStep.spec (GF := GF) (hG := hG)) :
    run.spec (GF := GF) (hG := hG) := by
  intro CS CRE CEC N id₁ id₂ id₃ ps ctxs boot lg
  wp_start as ⟨Hstart, Htok, #Hprem, %Hbf, #Hzlg, %Hp₂, %Hp₃, %Hp₄, %Hp₅⟩
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hzlg
  obtain ⟨Htb, HLv, Hrb48, HrbN, HwbN⟩ := Hp₂
  obtain ⟨Haf, Hbuq, Hrf, Hdbo⟩ := Hp₃
  obtain ⟨HlP, HnE⟩ := Hp₄
  obtain ⟨Hms, hAs⟩ := Hp₅
  ihave #Pc3 : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.cluster3 $$ []
  · iPkgInit
  ihave #Pes : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  (try wp_auto)
  -- `cfg := config()`
  wp_apply wp_config
  (try wp_auto)
  -- `cluster3.StartCluster(cfg, lg)`, in the monotone lease mode
  wp_apply (wp_StartCluster clusterCfg N id₁ id₂ id₃ ps ctxs boot lg false .mono clusterCfg_ok Hbf
      Htb HLv Hrb48 HrbN HwbN Haf Hbuq Hrf Hdbo Hms (lease.runCfg_mono HnE) (by decide)
      (fun _ => HlP))
    $$ [Hstart Htok] as %srvs %brs %ok Hup
  · iframe; iframe #
  icases Hup with (%Hok | ⟨%Hok, Htok, Hup⟩)
  · subst Hok
    (try wp_auto)
    iapply HΦ; itrivial
  subst Hok
  (try wp_auto)
  iunfold cluster3.clusterUp at Hup
  icases Hup with ⟨%γ, %γn, %ρ₁, %ρ₂, %ρ₃, %E₁, %E₂, %E₃, %cid₁, %cid₂, %cid₃, %mid₁, %mid₂,
    %mid₃, %R₁, %R₂, %R₃, %s₁, %s₂, %s₃, %br₁, %br₂, %br₃, Hcl⟩
  iunfold cluster3.clusterAt at Hcl
  icases Hcl with ⟨#Hsrvs, #Hbrs, #Hm₁, -, #Hm₃, Hctl₁, Hctl₂, Hctl₃, -, -, -, -⟩
  -- members 1 and 3: the grant and the listing at their lessors' histories, at their bridges
  ihave ⟨#HG₁b, -⟩ := cluster3.memberAt_mono _ _ _ _ _ _ _ _ _ _ _ _ $$ Hm₁
  ihave ⟨#HG₃b, #HL₃b⟩ := cluster3.memberAt_mono _ _ _ _ _ _ _ _ _ _ _ _ $$ Hm₃
  -- `c3, err := etcdstart.NewClients([]string{cfg.Bridge3}, lg)`
  wp_apply wp_slice_literal (V := GoString) (l := [clusterCfg.Bridge3'])
  try (isplitr; (ipureintro; rfl))
  iintro %eps3 ⟨Heps3, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Heps3 with #Heps3
  wp_apply (wp_NewClients _ [clusterCfg.Bridge3'] lg
      (EtcdGrove.client.srvWEnv R₃ (etcdstart.srvWOf R₃.E ρ₃.rd false) ρ₃.rd clusterCfg.Bridge3' [] null null [] null default) (by omega)
      (plainEndpoints_singleton _ clusterCfg_ok.bp3)) $$ [] as %c3 %cerr Hc3
  · iframe #
  icases Hc3 with (⟨%Hc3err, #Hnc3, -⟩ | %Hc3fail)
  rotate_left
  · obtain ⟨Hc3err, -⟩ := Hc3fail
    cases cerr with
    | nil => exact absurd rfl Hc3err
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hc3err
  wp_auto
  -- `c1, err := etcdstart.NewClients([]string{cfg.Bridge1}, lg)`
  wp_apply wp_slice_literal (V := GoString) (l := [clusterCfg.Bridge1'])
  try (isplitr; (ipureintro; rfl))
  iintro %eps1 ⟨Heps1, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Heps1 with #Heps1
  wp_apply (wp_NewClients _ [clusterCfg.Bridge1'] lg
      (EtcdGrove.client.srvWEnv R₁ (etcdstart.srvWOf R₁.E ρ₁.rd false) ρ₁.rd clusterCfg.Bridge1' [] null null [] null default) (by omega)
      (plainEndpoints_singleton _ clusterCfg_ok.bp1)) $$ [] as %c1 %cerr Hc1
  · iframe #
  icases Hc1 with (⟨%Hc1err, #Hnc1, -⟩ | %Hc1fail)
  rotate_left
  · obtain ⟨Hc1err, -⟩ := Hc1fail
    cases cerr with
    | nil => exact absurd rfl Hc1err
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hc1err
  wp_auto
  -- 1. `g1, err := grant(c3)`, `Q`: `g1` granted at an index of member 3's lessor history
  wp_apply (wp_grant c3 [clusterCfg.Bridge3'] _
      (etcdLeaseGrantSpec (EM := v3rpc.etcdModelOfServer E₃ ρ₃.rd false) (mvcc.api.mvccLeases E₃.γ))
      (fun m => iprop(∃ i : Nat, lease.leaseGrantedAt (mvcc.api.mvccLeases E₃.γ) i m.id))) as %g1 %gerr Hg1
  · iframe #
    isplitl; rotate_left; · ipureintro; exact hAs
    imodintro; inext
    iunfold etcdLeaseGrantSpec
    iintro %m - - Hgi
    iexact Hgi
  icases Hg1 with (⟨%Hgerr, %mg, #Hgid, #HQg⟩ | %Hgfail)
  rotate_left
  · cases gerr with
    | nil => exact absurd rfl Hgfail
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hgerr
  wp_auto
  -- 2. member 3 cut off the two others
  ihave Hmem : ([∗list] s ∈ [s₁, s₂, s₃], ∃ id : w64, etcdstart.srvPeerCtl γn s id)
    $$ [Hctl₁ Hctl₂ Hctl₃]
  · iapply (BigSepL.bigSepL_cons
      (Φ := fun _ s => iprop(∃ id : w64, etcdstart.srvPeerCtl (GF := GF) γn s id))).2
    isplitl [Hctl₁]
    · iexists id₁; iexact Hctl₁
    iapply (BigSepL.bigSepL_cons
      (Φ := fun _ s => iprop(∃ id : w64, etcdstart.srvPeerCtl (GF := GF) γn s id))).2
    isplitl [Hctl₂]
    · iexists id₂; iexact Hctl₂
    iapply (BigSepL.bigSepL_cons
      (Φ := fun _ s => iprop(∃ id : w64, etcdstart.srvPeerCtl (GF := GF) γn s id))).2
    isplitl [Hctl₃]
    · iexists id₃; iexact Hctl₃
    iapply BigSepL.bigSepL_nil.2
    itrivial
  wp_apply (wp_PeerStep inferInstance γn srvs [s₁, s₂, s₃] _ _ _) $$ [Hmem] as Hmem
  · iframe #; iframe Hmem
  (try wp_auto)
  wp_apply (wp_PeerStep inferInstance γn srvs [s₁, s₂, s₃] _ _ _) $$ [Hmem] as Hmem
  · iframe #; iframe Hmem
  (try wp_auto)
  -- 3. the fillers, through member 1: only the last one's id is kept
  ihave HF : (∃ (j lv : w64) (gb : Bool), "i" ∷ i_ptr ↦ j ∗ "last" ∷ last_ptr ↦ lv ∗
      "granted" ∷ granted_ptr ↦ gb ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 20⌝ : IProp GF)
      $$ [i last granted]
  · iexists W64 0, _, false
    simp only [named]
    iframe
    ipureintro; constructor <;> decide
  wp_for HF
  wp_if_destruct
  · -- a filler
    have Hlt : sint.Z j < (20 : Nat) := by
      have h : sint.Z j < sint.Z (W64 20) := by simpa using Hif
      exact h
    wp_apply (wp_grant c1 [clusterCfg.Bridge1'] _
        (etcdLeaseGrantSpec (EM := v3rpc.etcdModelOfServer E₁ ρ₁.rd false) (mvcc.api.mvccLeases E₁.γ))
        (fun _ => iprop(True))) as %f %ferr Hf
    · iframe #
      isplitl; rotate_left; · ipureintro; exact hAs
      imodintro; inext
      iunfold etcdLeaseGrantSpec
      iintro %m - - -
      itrivial
    icases Hf with (⟨%Hferr, %mf, #Hfid, -⟩ | %Hffail)
    · subst Hferr
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, mf.id, true
      simp only [named]
      iframe
      ipureintro; exact incr_le j 20 Hj.1 Hlt (by decide)
    · cases ferr with
      | nil => exact absurd rfl Hffail
      | ok ei => ?_
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, lv, gb
      simp only [named]
      iframe
      ipureintro; exact incr_le j 20 Hj.1 Hlt (by decide)
  -- 4. the links mended
  (try wp_auto)
  -- no filler granted: no check
  cases gb
  · (try wp_auto)
    iapply HΦ; itrivial
  (try wp_auto)
  wp_apply (wp_PeerStep inferInstance γn srvs [s₁, s₂, s₃] _ _ _) $$ [Hmem] as Hmem
  · iframe #; iframe Hmem
  (try wp_auto)
  wp_apply (wp_PeerStep inferInstance γn srvs [s₁, s₂, s₃] _ _ _) $$ [Hmem] as Hmem
  · iframe #; iframe Hmem
  (try wp_auto)
  -- 5. member 3's listings, each at `etcdLeaseLeasesSpec`, handing in `g1` with its grant
  ihave HP : (∃ q : w64, "p" ∷ p_ptr ↦ q ∗ "%Hq" ∷ ⌜0 ≤ sint.Z q ∧ sint.Z q ≤ 60⌝ : IProp GF)
      $$ [p]
  · iexists W64 0
    simp only [named]
    iframe
    ipureintro; constructor <;> decide
  wp_for HP
  wp_if_destruct
  · have Hlt : sint.Z q < (60 : Nat) := by
      have h : sint.Z q < sint.Z (W64 60) := by simpa using Hif
      exact h
    wp_apply (wp_leases c3 [clusterCfg.Bridge3'] _ (etcdLeaseLeasesSpec (mvcc.api.mvccLeases E₃.γ))
        (fun m => iprop(⌜mg.id ∈ m.ids⌝))) as %ls %lerr Hls
    · iframe #
      isplitl; rotate_left; · ipureintro; exact hAs
      imodintro; inext
      iunfold etcdLeaseLeasesSpec
      iexists [mg.id]
      isplitl
      · iapply BigSepL.bigSepL_cons.2
        iframe HQg
        iapply BigSepL.bigSepL_nil.2
        itrivial
      iintro %m %Hm
      ipureintro; exact Hm.2 mg.id (List.mem_singleton_self _)
    icases Hls with (⟨%Hlerr, %ml, %sl, #Hlsl, #Hsl, %Hin⟩ | %Hlfail)
    · subst Hlerr
      (try wp_auto)
      wp_apply (wp_listed ls sl ml.ids lv) $$ []
      · iframe #
      wp_if_destruct
      · -- 6. the last filler listed: `g1` is listed too
        (try wp_auto)
        wp_apply (wp_listed ls sl ml.ids mg.id) $$ []
        · iframe #
        rw [decide_eq_true Hin]
        (try wp_auto)
        wp_for_post
        iapply HΦ; itrivial
      · (try wp_auto)
        wp_apply time.wp_Sleep
        (try wp_auto)
        wp_for_post
        iframe
        iexists q + W64 1
        simp only [named]
        iframe
        ipureintro; exact incr_le q 60 Hq.1 Hlt (by decide)
    · cases lerr with
      | nil => exact absurd rfl Hlfail
      | ok ei => ?_
      (try wp_auto)
      wp_apply time.wp_Sleep
      (try wp_auto)
      wp_for_post
      iframe
      iexists q + W64 1
      simp only [named]
      iframe
      ipureintro; exact incr_le q 60 Hq.1 Hlt (by decide)
  · (try wp_auto)
    iapply HΦ; itrivial

end proof

end etcd_leasecatchup
end EtcdGrove
end Perennial
