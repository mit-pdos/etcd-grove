/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/linkv3p/startCluster.lean` (W4 of
`notes/watch-cut-plan.md`, 2026-10-22; `Main`'s proof's start until then). Lean-first (no Rocq
counterpart).

The three peer URL slices and the initial cluster's map; the ghost state of the cluster and its
members (`common.alloc3`, the ids in the names' order, the client's `etcdKV`
at the first member's names), each member's pure boot facts kept (`memberBoot`'s: its names, what
`memberAt` records); `startMember` for each member, the thread token passed along
(`memberServed`'s `srvGoRes`), its watch server kept; the servers' slice; `startBridge` for each
member's client address (the bridge owned, its address serving the member's, `forwards`) and the
bridges' slice; the endpoints' slice and `common.NewClients` of it for each client (linkv3p's `newClient` until 2026-10-23), at the watch
environment of the three members (`watchEnv`); the clients' slice and `clusterUp`. Every step's
error ends with `ok = false`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.startCluster
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.startMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.NewClients
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.startBridge
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Alloc3
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.Alloc

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver
open putget3 (httpURL commonPremises)
open common (memberBoot)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem startCluster.wp_proof
    (wp_startMember : startMember.spec (GF := GF) (hG := hG))
    (wp_startBridge : startBridge.spec (GF := GF) (hG := hG))
    (wp_NewClients : common.NewClients.spec (GF := GF) (hG := hG)) :
    startCluster.spec (GF := GF) (hG := hG) := by
  intro CS N id₁ id₂ id₃ ctxs boot lg pfx Hbf Hlg Htb Hrb48 HrbN Hck Haf Hbuq Hdbo Hms
  wp_start as ⟨Ha₁, Ha₂, Ha₃, Hc₁, Hc₂, Hc₃, Hba₁, Hba₂, Hba₃, Hf₁, Hf₂, Hf₃, Htok, #Hprem⟩
  iunfold premises at Hprem
  icases Hprem with ⟨#Hb₁, #Hb₂, #Hb₃, #Hmarsh, #Hcom⟩
  -- `context`'s `closedchan`, from its package's facts
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  (try wp_auto)
  simp only [github_com.mit_pdos.etcd_grove.examples.linkv3p.peerAddr1,
    github_com.mit_pdos.etcd_grove.examples.linkv3p.peerAddr2,
    github_com.mit_pdos.etcd_grove.examples.linkv3p.peerAddr3,
    github_com.mit_pdos.etcd_grove.examples.linkv3p.clientAddr1,
    github_com.mit_pdos.etcd_grove.examples.linkv3p.clientAddr2,
    github_com.mit_pdos.etcd_grove.examples.linkv3p.clientAddr3,
    github_com.mit_pdos.etcd_grove.examples.linkv3p.bridgeAddr1,
    github_com.mit_pdos.etcd_grove.examples.linkv3p.bridgeAddr2,
    github_com.mit_pdos.etcd_grove.examples.linkv3p.bridgeAddr3]
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
  ihave #Hq₁ : (slice.mk peer₁ (W64 1) (W64 1)) ↦*□ [httpURL peerAddr₁] $$ []
  · iExactEq Hpeer₁; rfl
  ihave #Hq₂ : (slice.mk peer₂ (W64 1) (W64 1)) ↦*□ [httpURL peerAddr₂] $$ []
  · iExactEq Hpeer₂; rfl
  ihave #Hq₃ : (slice.mk peer₃ (W64 1) (W64 1)) ↦*□ [httpURL peerAddr₃] $$ []
  · iExactEq Hpeer₃; rfl
  ihave #Hu₁ : (slice.mk peer₁ (W64 1) (W64 1)) ↦*□ initURLs3 name₁ $$ []
  · iExactEq Hpeer₁; simp [initURLs3]; rfl
  ihave #Hu₂ : (slice.mk peer₂ (W64 1) (W64 1)) ↦*□ initURLs3 name₂ $$ []
  · iExactEq Hpeer₂; simp [initURLs3]; rfl
  ihave #Hu₃ : (slice.mk peer₃ (W64 1) (W64 1)) ↦*□ initURLs3 name₃ $$ []
  · iExactEq Hpeer₃; simp [initURLs3]; rfl
  ihave #Hcm : pm ↦$□ GMap.insert name₃ (slice.mk peer₃ (W64 1) (W64 1))
      (GMap.insert name₂ (slice.mk peer₂ (W64 1) (W64 1))
        (GMap.insert name₁ (slice.mk peer₁ (W64 1) (W64 1)) ∅)) $$ []
  · iExactEq Hpm; rfl
  -- the ghost state of the cluster and its members (`common.alloc3`, in `bootstrap`'s order,
  -- which is the names'; the client's `etcdKV` at `linkv3p-1`'s names)
  -- (2026-10-24, rafthttp stage 6d) the directory well formed, its hosts the peer addresses
  have Hnz := common.id_nz id₁ id₂ id₃ Hbf.idLow Hbf.idLow0
  have Hdok : netDirOk (dir3 id₁ id₂ id₃) :=
    dir3_ok id₁ id₂ id₃ (Hnz id₁ (by simp)) (Hnz id₂ (by simp)) (Hnz id₃ (by simp))
  have hblen0 : boot.length = 3 := by rw [Hbf.boot.1]; rfl
  iunfold ids at Hmarsh
  imod (common.alloc3 id₁ id₂ id₃ ctxs boot Hbf.idLow Hbf.idLow0 Hbf.boot Hbf.cc (dir3 id₁ id₂ id₃)
      peerAddr₁ peerAddr₂ peerAddr₃ Hdok.1 (dir3_host id₁ id₂ id₃) (by omega) (by omega))
      $$ Hmarsh Hf₁ Hf₂ Hf₃
    with ⟨%γ, %reg₁, %reg₂, %reg₃, %ρ₁, %ρ₂, %ρ₃, %E₁, %E₂, %E₃, %Φs, %γn, %Hal, Hmb₁, ⟨#Hsl₁, Ho₁⟩, Hmb₂,
    ⟨#Hsl₂, Ho₂⟩, Hmb₃, ⟨#Hsl₃, Ho₃⟩, Hetcd⟩
  obtain ⟨hvs, hdyn, hboot, hγn1, hγn2, hlog₁, hst₂, hst₃, -⟩ := Hal
  obtain ⟨hn12, hn13, hn23⟩ := common.id_ne id₁ id₂ id₃ Hbf.idLow Hbf.idLow0
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  -- the three members, each served
  iunfold memberBoot at Hmb₁
  icases Hmb₁ with ⟨%Hp₁, Hmb₁⟩
  ihave Hmb₁ : memberBoot { γ with reg := reg₁ } ctxs ρ₁ E₁ Φs id₁ $$ [Hmb₁]
  · iunfold memberBoot; iframe; ipureintro; exact Hp₁
  wp_apply (wp_startMember N name₁ peerAddr₁ clientAddr₁ (slice.mk peer₁ (W64 1) (W64 1)) pm lg
      (slice.mk peer₁ (W64 1) (W64 1)) (slice.mk peer₂ (W64 1) (W64 1))
      (slice.mk peer₃ (W64 1) (W64 1)) (ids id₁ id₂ id₃)
      (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃) id₁ { γ with reg := reg₁ } ρ₁ E₁ Φs γn
      Htb Hrb48 HrbN hvs hdyn hboot hblen hγn1 hγn2
      Hdok (by simp [dir3]) Hlg Hck Haf Hbuq Hdbo Hms) $$ [Ha₁ Hc₁ Htok Hmb₁ Ho₁] as %s₁ %err₁ Hr₁
  · iframe; iframe #
  icases Hr₁ with (⟨%Herr, Htok⟩ | ⟨%Herr, Hup₁⟩)
  · cases err₁ with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; ipureintro; rfl
  subst Herr
  wp_auto
  iunfold memberServed at Hup₁
  icases Hup₁ with ⟨%E₁', %γw₁, %cid₁, %mid₁, %HE₁, #Hreq₁, #Hrd₁, Hgo₁,
    Hctl₁, #HPut₁, #HRange₁, #HDel₁, #HTxn₁, ⟨%pw₁, %R₁, #Hws₁, %HR₁, #Hstr₁⟩, %Hnr₁⟩
  iunfold srvGoRes at Hgo₁
  icases Hgo₁ with ⟨-, Htok⟩
  iunfold memberBoot at Hmb₂
  icases Hmb₂ with ⟨%Hp₂, Hmb₂⟩
  ihave Hmb₂ : memberBoot { γ with reg := reg₂ } ctxs ρ₂ E₂ Φs id₂ $$ [Hmb₂]
  · iunfold memberBoot; iframe; ipureintro; exact Hp₂
  wp_apply (wp_startMember N name₂ peerAddr₂ clientAddr₂ (slice.mk peer₂ (W64 1) (W64 1)) pm lg
      (slice.mk peer₁ (W64 1) (W64 1)) (slice.mk peer₂ (W64 1) (W64 1))
      (slice.mk peer₃ (W64 1) (W64 1)) (ids id₁ id₂ id₃)
      (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃) id₂ { γ with reg := reg₂ } ρ₂ E₂ Φs γn
      Htb Hrb48 HrbN hvs hdyn hboot hblen hγn1 hγn2
      Hdok (by simp [dir3, Ne.symm hn12]) Hlg Hck Haf Hbuq Hdbo Hms)
    $$ [Ha₂ Hc₂ Htok Hmb₂ Ho₂] as %s₂ %err₂ Hr₂
  · iframe; iframe #
  icases Hr₂ with (⟨%Herr, Htok⟩ | ⟨%Herr, Hup₂⟩)
  · cases err₂ with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; ipureintro; rfl
  subst Herr
  wp_auto
  iunfold memberServed at Hup₂
  icases Hup₂ with ⟨%E₂', %γw₂, %cid₂, %mid₂, %HE₂, #Hreq₂, #Hrd₂, Hgo₂,
    Hctl₂, #HPut₂, #HRange₂, #HDel₂, #HTxn₂, ⟨%pw₂, %R₂, #Hws₂, %HR₂, #Hstr₂⟩, %Hnr₂⟩
  iunfold srvGoRes at Hgo₂
  icases Hgo₂ with ⟨-, Htok⟩
  iunfold memberBoot at Hmb₃
  icases Hmb₃ with ⟨%Hp₃, Hmb₃⟩
  ihave Hmb₃ : memberBoot { γ with reg := reg₃ } ctxs ρ₃ E₃ Φs id₃ $$ [Hmb₃]
  · iunfold memberBoot; iframe; ipureintro; exact Hp₃
  wp_apply (wp_startMember N name₃ peerAddr₃ clientAddr₃ (slice.mk peer₃ (W64 1) (W64 1)) pm lg
      (slice.mk peer₁ (W64 1) (W64 1)) (slice.mk peer₂ (W64 1) (W64 1))
      (slice.mk peer₃ (W64 1) (W64 1)) (ids id₁ id₂ id₃)
      (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃) id₃ { γ with reg := reg₃ } ρ₃ E₃ Φs γn
      Htb Hrb48 HrbN hvs hdyn hboot hblen hγn1 hγn2
      Hdok (by simp [dir3, Ne.symm hn13, Ne.symm hn23]) Hlg Hck Haf Hbuq Hdbo Hms)
    $$ [Ha₃ Hc₃ Htok Hmb₃ Ho₃] as %s₃ %err₃ Hr₃
  · iframe; iframe #
  icases Hr₃ with (⟨%Herr, Htok⟩ | ⟨%Herr, Hup₃⟩)
  · cases err₃ with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; ipureintro; rfl
  subst Herr
  wp_auto
  iunfold memberServed at Hup₃
  icases Hup₃ with ⟨%E₃', %γw₃, %cid₃, %mid₃, %HE₃, #Hreq₃, #Hrd₃, Hgo₃,
    Hctl₃, #HPut₃, #HRange₃, #HDel₃, #HTxn₃, ⟨%pw₃, %R₃, #Hws₃, %HR₃, #Hstr₃⟩, %Hnr₃⟩
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
  wp_apply (wp_startBridge bridgeAddr₁ clientAddr₁) $$ [Hba₁] as %br₁ %berr₁ Hbr₁
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
  wp_apply (wp_startBridge bridgeAddr₂ clientAddr₂) $$ [Hba₂] as %br₂ %berr₂ Hbr₂
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
  wp_apply (wp_startBridge bridgeAddr₃ clientAddr₃) $$ [Hba₃] as %br₃ %berr₃ Hbr₃
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
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Hbrs with #Hbrs
  -- `eps := []string{bridgeAddr1, bridgeAddr2, bridgeAddr3}`: every client of every bridge
  -- (failover, 2026-10-21, D27)
  wp_apply wp_slice_literal (V := GoString) (l := [bridgeAddr₁, bridgeAddr₂, bridgeAddr₃])
  try (isplitr; (ipureintro; rfl))
  iintro %epsp ⟨Heps, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Heps with #Heps
  have hpl : plainEndpoints [bridgeAddr₁, bridgeAddr₂, bridgeAddr₃] := by
    refine ⟨by simp, fun e he => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at he
    rcases he with rfl | rfl | rfl <;> (unfold plainEndpoint; decide)
  wp_apply (wp_NewClients _ [bridgeAddr₁, bridgeAddr₂, bridgeAddr₃] lg
      (watchEnv R₁ R₂ R₃ ρ₁.rd pfx) (by omega) Hlg hpl) $$ [] as %cl₁ %cerr₁ Hcl₁
  · iframe #
  icases Hcl₁ with (Hok₁ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr₁ with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; ipureintro; rfl
  icases Hok₁ with ⟨%Hcerr, #Hnc₁⟩
  subst Hcerr
  wp_auto
  wp_apply (wp_NewClients _ [bridgeAddr₁, bridgeAddr₂, bridgeAddr₃] lg
      (watchEnv R₁ R₂ R₃ ρ₁.rd pfx) (by omega) Hlg hpl) $$ [] as %cl₂ %cerr₂ Hcl₂
  · iframe #
  icases Hcl₂ with (Hok₂ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr₂ with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; ipureintro; rfl
  icases Hok₂ with ⟨%Hcerr, #Hnc₂⟩
  subst Hcerr
  wp_auto
  wp_apply (wp_NewClients _ [bridgeAddr₁, bridgeAddr₂, bridgeAddr₃] lg
      (watchEnv R₁ R₂ R₃ ρ₁.rd pfx) (by omega) Hlg hpl) $$ [] as %cl₃ %cerr₃ Hcl₃
  · iframe #
  icases Hcl₃ with (Hok₃ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr₃ with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; ipureintro; rfl
  icases Hok₃ with ⟨%Hcerr, #Hnc₃⟩
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
  iexists γ, γn, ρ₁, ρ₂, ρ₃, E₁', E₂', E₃', cid₁, cid₂, cid₃, mid₁, mid₂, mid₃, R₁, R₂, R₃,
    s₁, s₂, s₃, cl₁, cl₂, cl₃, br₁, br₂, br₃
  iframe Hetcd Hob₁ Hob₂ Hob₃ Hctl₁ Hctl₂ Hctl₃
  obtain ⟨hr₁, -, hc₁, hch₁, hl₁, -⟩ := Hp₁
  obtain ⟨hr₂, -, hc₂, hch₂, hl₂, -⟩ := Hp₂
  obtain ⟨hr₃, -, hc₃, hch₃, hl₃, -⟩ := Hp₃
  iframe #
  isplitr
  · iunfold memberAt; iframe #; isplitr
    · ipureintro; exact Hnr₁
    isplitr
    · ipureintro; exact HR₁
    ipureintro; exact ⟨⟨reg₁, hr₁⟩, hc₁, hch₁, hl₁⟩
  isplitr
  · iunfold memberAt; iframe #; isplitr
    · ipureintro; exact Hnr₂
    isplitr
    · ipureintro; exact HR₂
    ipureintro; exact ⟨⟨reg₂, hr₂⟩, hc₂, hch₂, hl₂⟩
  isplitr
  · iunfold memberAt; iframe #; isplitr
    · ipureintro; exact Hnr₃
    isplitr
    · ipureintro; exact HR₃
    ipureintro; exact ⟨⟨reg₃, hr₃⟩, hc₃, hch₃, hl₃⟩
  ipureintro; exact ⟨hst₂, hst₃⟩

end proof

end linkv3p
end EtcdGrove
end Perennial
