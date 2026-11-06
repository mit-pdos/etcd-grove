/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/lib/cluster3/StartCluster.lean` (W4 of
`notes/watch-cut-plan.md`, 2026-10-22; package `partition`'s `startCluster` until 2026-11-05, at
linkv3p's configuration, with the clients). Lean-first (no Rocq counterpart).

The three peer URL slices and the initial cluster's map (from the configuration's fields); the
ghost state of the cluster and its members (`etcdstart.alloc3`, in the cluster's compaction mode,
the peers in `bootstrap`'s order, a permutation of the ids, the client's `etcdKV` at the first
member's names), each member's pure boot facts kept (`memberBoot`'s: its names, what `memberAt`
records); `StartMember` for each member, the thread token passed along (`memberServed`'s
`srvGoRes`), its watch server kept; the servers' slice; `StartBridge` for each member's client
address (the bridge owned, its address serving the member's, `forwards`) and the bridges' slice;
`clusterUp`. Every step's error ends with `ok = false`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartRes
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartCluster
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartBridge
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Alloc3
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Dir

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cluster3

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver
open etcdstart (httpURL commonPremises memberBoot)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Assumptions]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem StartCluster.wp_proof
    (wp_StartMember : StartMember.spec (GF := GF) (hG := hG))
    (wp_StartBridge : StartBridge.spec (GF := GF) (hG := hG)) :
    StartCluster.spec (GF := GF) (hG := hG) := by
  intro CS cfg N id₁ id₂ id₃ ps ctxs boot lg cmp lm Hcfg Hbf Hlg Htb Hrb48 HrbN HwbN Hck Haf Hbuq Hrf
    Hdbo Hms Hrun Hrev HlP
  -- (lease-mono3) a mode that grants leases: `alloc3` at it, `StartMember` at it, no `etcdKV`
  cases lm with
  | mono => sorry -- DRAFT lease-mono3
  | revocable => exact absurd rfl Hrev
  | none => ?_
  simp only [clusterUp_none]
  wp_start as ⟨Hstart, Htok, #Hprem⟩
  -- the members' start bundles (to `alloc3`) and the bridges' listen rights (to `StartBridge`)
  icases startRes_members cfg $$ Hstart with ⟨⟨Hs₁, Hs₂, Hs₃⟩, Hba₁, Hba₂, Hba₃⟩
  iunfold premises at Hprem
  icases Hprem with ⟨#Hb₁, #Hb₂, #Hb₃, #Hmarsh, #Hcom⟩
  -- `context`'s `closedchan`, from its package's facts
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  (try wp_auto)
  -- the peer URLs and the initial cluster's map, read-only from here on (D19r (F))
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %peer₁ ⟨Hpeer₁, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %peer₂ ⟨Hpeer₂, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %peer₃ ⟨Hpeer₃, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  wp_apply wp_map_make1 (K := GoString) (V := go_etcd_io.etcd.client.pkg.v3.types.URLs)
    as %pm Hpm
  wp_apply wp_mapInsert $$ Hpm as Hpm
  wp_apply wp_mapInsert $$ Hpm as Hpm
  wp_apply wp_mapInsert $$ Hpm as Hpm
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Hpeer₁ with #Hpeer₁
  imod ownSlice_persist _ _ _ $$ Hpeer₂ with #Hpeer₂
  imod ownSlice_persist _ _ _ $$ Hpeer₃ with #Hpeer₃
  imod ownMap_persist _ _ _ $$ Hpm with #Hpm
  -- the URLs in the forms `startMember` takes
  have hsl : ∀ p : Loc, slice.mk p (W64 (max (max (0 + 1) 0) 0)) (W64 (max (max (0 + 1) 0) 0)) =
      slice.mk p (W64 1) (W64 1) := fun _ => rfl
  simp only [hsl] at *
  ihave #Hq₁ : (slice.mk peer₁ (W64 1) (W64 1)) ↦*□ [httpURL cfg.Peer1'] $$ []
  · iExactEq Hpeer₁; rfl
  ihave #Hq₂ : (slice.mk peer₂ (W64 1) (W64 1)) ↦*□ [httpURL cfg.Peer2'] $$ []
  · iExactEq Hpeer₂; rfl
  ihave #Hq₃ : (slice.mk peer₃ (W64 1) (W64 1)) ↦*□ [httpURL cfg.Peer3'] $$ []
  · iExactEq Hpeer₃; rfl
  ihave #Hu₁ : (slice.mk peer₁ (W64 1) (W64 1)) ↦*□ initURLs3 cfg cfg.Name1' $$ []
  · iExactEq Hpeer₁; simp [initURLs3]; rfl
  ihave #Hu₂ : (slice.mk peer₂ (W64 1) (W64 1)) ↦*□ initURLs3 cfg cfg.Name2' $$ []
  · iExactEq Hpeer₂; simp [initURLs3, Ne.symm Hcfg.n12]; rfl
  ihave #Hu₃ : (slice.mk peer₃ (W64 1) (W64 1)) ↦*□ initURLs3 cfg cfg.Name3' $$ []
  · iExactEq Hpeer₃; simp [initURLs3, Ne.symm Hcfg.n13, Ne.symm Hcfg.n23]; rfl
  ihave #Hcm : pm ↦$□ GMap.insert cfg.Name3' (slice.mk peer₃ (W64 1) (W64 1))
      (GMap.insert cfg.Name2' (slice.mk peer₂ (W64 1) (W64 1))
        (GMap.insert cfg.Name1' (slice.mk peer₁ (W64 1) (W64 1)) ∅)) $$ []
  · iExactEq Hpm; rfl
  -- the ghost state of the cluster and its members (`etcdstart.alloc3`, the peers in `bootstrap`'s
  -- order; the client's `etcdKV` at the first member's names)
  -- (2026-10-24, rafthttp stage 6d) the directory well formed, its hosts the peer addresses
  have Hnz := etcdstart.id_nz id₁ id₂ id₃ Hbf.idLow Hbf.idLow0
  have Hdok : netDirOk (dir3 cfg id₁ id₂ id₃) :=
    dir3_ok cfg Hcfg id₁ id₂ id₃ (Hnz id₁ (by simp)) (Hnz id₂ (by simp)) (Hnz id₃ (by simp))
  have hblen0 : boot.length = 3 := by rw [Hbf.boot.1, Hbf.perm.length_eq]; rfl
  imod (etcdstart.alloc3 id₁ id₂ id₃ ps Hbf.perm ctxs boot Hbf.idLow Hbf.idLow0 Hbf.boot Hbf.cc Hbf.urls (dir3 cfg id₁ id₂ id₃)
      cfg.Peer1' cfg.Peer2' cfg.Peer3' Hdok.1 (dir3_host cfg id₁ id₂ id₃) (by omega) (by omega)
      cfg.Name1' cfg.Name2' cfg.Name3' (some cfg.Client1') (some cfg.Client2') (some cfg.Client3') cmp 0
      .none lease.runCfg_none (by decide))
      $$ Hmarsh Hs₁ Hs₂ Hs₃
    with ⟨%γ, %reg₁, %reg₂, %reg₃, %ρ₁, %ρ₂, %ρ₃, %E₁, %E₂, %E₃, %Φs, %γn, %Hal, Hmb₁, ⟨#Hsl₁, Hfr₁⟩, Hmb₂,
    ⟨#Hsl₂, Hfr₂⟩, Hmb₃, ⟨#Hsl₃, Hfr₃⟩, Hetcd⟩
  isimp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at Hetcd
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hlog₁, -, -, -, -, -, -, hst₂, hst₃, hcmp₁, hcret₁⟩ := Hal
  obtain ⟨hn12, hn13, hn23⟩ := etcdstart.id_ne id₁ id₂ id₃ Hbf.idLow Hbf.idLow0
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  -- the three members, each served
  iunfold memberBoot at Hmb₁
  icases Hmb₁ with ⟨%Hp₁, Hmb₁⟩
  ihave Hmb₁ : memberBoot { γ with reg := reg₁ } ctxs ρ₁ E₁ Φs id₁ cmp $$ [Hmb₁]
  · iunfold memberBoot; iframe; ipureintro; exact Hp₁
  wp_apply (wp_StartMember cfg N cfg.Name1' cfg.Peer1' cfg.Client1' (slice.mk peer₁ (W64 1) (W64 1)) pm lg
      (slice.mk peer₁ (W64 1) (W64 1)) (slice.mk peer₂ (W64 1) (W64 1))
      (slice.mk peer₃ (W64 1) (W64 1)) ps
      (LogEntry.toEntries boot 0) ctxs (dir3 cfg id₁ id₂ id₃) id₁ { γ with reg := reg₁ } ρ₁ E₁ Φs γn cmp .none
      Hcfg Htb Hrb48 HrbN HwbN hvs hrule hboot hblen hγn1 hγn2
      Hdok (by simp [dir3])
      (dir3_dirsOk cfg id₁ id₂ id₃ ps Hbf.perm) Hlg Hck Haf Hbuq Hrf Hdbo Hms (fun h => absurd rfl h)) $$ [Hfr₁ Htok Hmb₁] as %s₁ %err₁ Hr₁
  · iframe; iframe #
  icases Hr₁ with (⟨%Herr, Htok⟩ | ⟨%Herr, Hup₁⟩)
  · cases err₁ with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; ipureintro; rfl
  subst Herr
  wp_auto
  isimp only [memberServed_none] at Hup₁
  icases Hup₁ with ⟨%E₁', %γw₁, %cid₁, %mid₁, %HE₁, #Hreq₁, #Hrd₁, Hgo₁,
    Hctl₁, #HPut₁, #HRange₁, #HDel₁, #HTxn₁, #HCmp₁, ⟨%pw₁, %R₁, #Hws₁, %HR₁, #Hstr₁⟩, %Hnr₁⟩
  iunfold srvGoRes at Hgo₁
  icases Hgo₁ with ⟨-, Htok⟩
  iunfold memberBoot at Hmb₂
  icases Hmb₂ with ⟨%Hp₂, Hmb₂⟩
  ihave Hmb₂ : memberBoot { γ with reg := reg₂ } ctxs ρ₂ E₂ Φs id₂ cmp $$ [Hmb₂]
  · iunfold memberBoot; iframe; ipureintro; exact Hp₂
  wp_apply (wp_StartMember cfg N cfg.Name2' cfg.Peer2' cfg.Client2' (slice.mk peer₂ (W64 1) (W64 1)) pm lg
      (slice.mk peer₁ (W64 1) (W64 1)) (slice.mk peer₂ (W64 1) (W64 1))
      (slice.mk peer₃ (W64 1) (W64 1)) ps
      (LogEntry.toEntries boot 0) ctxs (dir3 cfg id₁ id₂ id₃) id₂ { γ with reg := reg₂ } ρ₂ E₂ Φs γn cmp .none
      Hcfg Htb Hrb48 HrbN HwbN hvs hrule hboot hblen hγn1 hγn2
      Hdok (by simp [dir3, Ne.symm hn12])
      (dir3_dirsOk cfg id₁ id₂ id₃ ps Hbf.perm) Hlg Hck Haf Hbuq Hrf Hdbo Hms (fun h => absurd rfl h))
    $$ [Hfr₂ Htok Hmb₂] as %s₂ %err₂ Hr₂
  · iframe; iframe #
  icases Hr₂ with (⟨%Herr, Htok⟩ | ⟨%Herr, Hup₂⟩)
  · cases err₂ with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; ipureintro; rfl
  subst Herr
  wp_auto
  isimp only [memberServed_none] at Hup₂
  icases Hup₂ with ⟨%E₂', %γw₂, %cid₂, %mid₂, %HE₂, #Hreq₂, #Hrd₂, Hgo₂,
    Hctl₂, #HPut₂, #HRange₂, #HDel₂, #HTxn₂, #HCmp₂, ⟨%pw₂, %R₂, #Hws₂, %HR₂, #Hstr₂⟩, %Hnr₂⟩
  iunfold srvGoRes at Hgo₂
  icases Hgo₂ with ⟨-, Htok⟩
  iunfold memberBoot at Hmb₃
  icases Hmb₃ with ⟨%Hp₃, Hmb₃⟩
  ihave Hmb₃ : memberBoot { γ with reg := reg₃ } ctxs ρ₃ E₃ Φs id₃ cmp $$ [Hmb₃]
  · iunfold memberBoot; iframe; ipureintro; exact Hp₃
  wp_apply (wp_StartMember cfg N cfg.Name3' cfg.Peer3' cfg.Client3' (slice.mk peer₃ (W64 1) (W64 1)) pm lg
      (slice.mk peer₁ (W64 1) (W64 1)) (slice.mk peer₂ (W64 1) (W64 1))
      (slice.mk peer₃ (W64 1) (W64 1)) ps
      (LogEntry.toEntries boot 0) ctxs (dir3 cfg id₁ id₂ id₃) id₃ { γ with reg := reg₃ } ρ₃ E₃ Φs γn cmp .none
      Hcfg Htb Hrb48 HrbN HwbN hvs hrule hboot hblen hγn1 hγn2
      Hdok (by simp [dir3, Ne.symm hn13, Ne.symm hn23])
      (dir3_dirsOk cfg id₁ id₂ id₃ ps Hbf.perm) Hlg Hck Haf Hbuq Hrf Hdbo Hms (fun h => absurd rfl h))
    $$ [Hfr₃ Htok Hmb₃] as %s₃ %err₃ Hr₃
  · iframe; iframe #
  icases Hr₃ with (⟨%Herr, Htok⟩ | ⟨%Herr, Hup₃⟩)
  · cases err₃ with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; ipureintro; rfl
  subst Herr
  wp_auto
  isimp only [memberServed_none] at Hup₃
  icases Hup₃ with ⟨%E₃', %γw₃, %cid₃, %mid₃, %HE₃, #Hreq₃, #Hrd₃, Hgo₃,
    Hctl₃, #HPut₃, #HRange₃, #HDel₃, #HTxn₃, #HCmp₃, ⟨%pw₃, %R₃, #Hws₃, %HR₃, #Hstr₃⟩, %Hnr₃⟩
  iunfold srvGoRes at Hgo₃
  icases Hgo₃ with ⟨-, Htok⟩
  iclear Hb₁ Hb₂ Hb₃ Hcom Hq₁ Hq₂ Hq₃ Hu₁ Hu₂ Hu₃ Hcm Hpeer₁ Hpeer₂ Hpeer₃ Hpm
  -- `srvs := []*etcdserver.EtcdServer{s1, s2, s3}`
  wp_apply wp_slice_literal (V := Loc) (l := [s₁, s₂, s₃])
  try (isplitr; (ipureintro; rfl))
  iintro %srvsp ⟨Hsrvs, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Hsrvs with #Hsrvs
  -- the three bridges, each to its member's client address
  wp_apply (wp_StartBridge cfg.Bridge1' cfg.Client1') $$ [Hba₁] as %br₁ %berr₁ Hbr₁
  · iframe
  icases Hbr₁ with (⟨%Hberr, Hob₁, #Hfw₁⟩ | %Hberr)
  rotate_left
  · cases berr₁ with
    | nil => exact absurd rfl Hberr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; ipureintro; rfl
  subst Hberr
  wp_auto
  wp_apply (wp_StartBridge cfg.Bridge2' cfg.Client2') $$ [Hba₂] as %br₂ %berr₂ Hbr₂
  · iframe
  icases Hbr₂ with (⟨%Hberr, Hob₂, #Hfw₂⟩ | %Hberr)
  rotate_left
  · cases berr₂ with
    | nil => exact absurd rfl Hberr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; ipureintro; rfl
  subst Hberr
  wp_auto
  wp_apply (wp_StartBridge cfg.Bridge3' cfg.Client3') $$ [Hba₃] as %br₃ %berr₃ Hbr₃
  · iframe
  icases Hbr₃ with (⟨%Hberr, Hob₃, #Hfw₃⟩ | %Hberr)
  rotate_left
  · cases berr₃ with
    | nil => exact absurd rfl Hberr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; ipureintro; rfl
  subst Hberr
  wp_auto
  -- `brs := []bridge.Bridge{br1, br2, br3}`
  wp_apply wp_slice_literal (V := GoInterface) (l := [br₁, br₂, br₃])
  try (isplitr; (ipureintro; rfl))
  iintro %brsp ⟨Hbrs, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  imod ownSlice_persist _ _ _ $$ Hbrs with #Hbrs
  (try wp_auto)
  iapply HΦ
  iright
  isplitr
  · ipureintro; rfl
  iframe Htok
  iexists γ, γn, ρ₁, ρ₂, ρ₃, E₁', E₂', E₃', cid₁, cid₂, cid₃, mid₁, mid₂, mid₃, R₁, R₂, R₃,
    s₁, s₂, s₃, br₁, br₂, br₃
  isimp only [clusterAt_none]
  iframe Hetcd Hob₁ Hob₂ Hob₃ Hctl₁ Hctl₂ Hctl₃
  -- (M2, the storage side, N1) each member's server in the cluster's mode: its stand-in's,
  -- through `envAgree`
  have off₁ : E₁'.γ.cm = cmp := (envAgree_mode E₁' E₁ HE₁.1).trans Hp₁.2.2.2.2.2.2.2.1
  have off₂ : E₂'.γ.cm = cmp := (envAgree_mode E₂' E₂ HE₂.1).trans Hp₂.2.2.2.2.2.2.2.1
  have off₃ : E₃'.γ.cm = cmp := (envAgree_mode E₃' E₃ HE₃.1).trans Hp₃.2.2.2.2.2.2.2.1
  obtain ⟨hr₁, hc₁, hch₁, hl₁, -⟩ := Hp₁
  obtain ⟨hr₂, hc₂, hch₂, hl₂, -⟩ := Hp₂
  obtain ⟨hr₃, hc₃, hch₃, hl₃, -⟩ := Hp₃
  iframe #
  isplitr
  · isimp only [memberAt_none]; iframe #; isplitr
    · ipureintro; exact Hnr₁
    isplitr
    · ipureintro; exact HR₁
    ipureintro; exact ⟨⟨reg₁, hr₁⟩, hc₁, hch₁, hl₁, off₁⟩
  isplitr
  · isimp only [memberAt_none]; iframe #; isplitr
    · ipureintro; exact Hnr₂
    isplitr
    · ipureintro; exact HR₂
    ipureintro; exact ⟨⟨reg₂, hr₂⟩, hc₂, hch₂, hl₂, off₂⟩
  isplitr
  · isimp only [memberAt_none]; iframe #; isplitr
    · ipureintro; exact Hnr₃
    isplitr
    · ipureintro; exact HR₃
    ipureintro; exact ⟨⟨reg₃, hr₃⟩, hc₃, hch₃, hl₃, off₃⟩
  ipureintro; exact ⟨hst₂, hst₃, hcmp₁, hcret₁⟩

end proof

end cluster3
end EtcdGrove
end Perennial
