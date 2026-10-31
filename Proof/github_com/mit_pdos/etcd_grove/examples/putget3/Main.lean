/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/putget3/Main.lean` (D21 stage M5,
2026-10-19). Lean-first (no Rocq counterpart).

The steps (over the examples' shared start since 2026-10-22, D33): the members' premises in the
shared start's form (`common.bootPremise_of`); the logger; the three peer URL slices and the
initial cluster's map (read-only from then on); the ghost state of the cluster and its members
(`common.alloc3`); `common.StartMember` for each member, the thread token passed from one to the
next out of the previous member's `srvGoRes` (each error returns `Main`); then putget's steps on
the first member: `common.Serve` at the client address with the ghost step `common.kv_served`,
`common.NewClient`, each call's context with the request timeout (`client.wp_WithTimeout_bg`,
as putget's since 2026-10-23), the client's invariant at the bootstrap log, `cli.Put`, `cli.Get`
and the check.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.putget3.Main
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.StartMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.Serve
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.NewClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Alloc3
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Served
public import Perennial.Spec.context.Background
public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace putget3

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.putget3.Assumptions]

/-- A host of the directory is one of the three peer addresses (2026-10-24, rafthttp stage 6d). -/
theorem dir3_host (id₁ id₂ id₃ id : w64) (h : GoString)
    (hm : go!"http://" ++ h ∈ dir3 id₁ id₂ id₃ id) : h = peerAddr₁ ∨ h = peerAddr₂ ∨ h = peerAddr₃ := by
  unfold dir3 at hm
  split at hm
  · left; simpa using hm
  split at hm
  · right; left; simpa using hm
  split at hm
  · right; right; simpa using hm
  · simp at hm

/-- **`Main`'s directory is well formed** (`netDirOk`, `NewServer`'s premise; rafthttp stage 6d):
no member `0`, each peer address one member's, plain `http://` URLs. -/
theorem dir3_ok (id₁ id₂ id₃ : w64) (ctxs : List (List w8)) (bl : List LogEntry)
    (Hbf : BootFacts id₁ id₂ id₃ ctxs bl) :
    netDirOk (dir3 id₁ id₂ id₃) := by
  obtain ⟨hn12, hn13, hn23⟩ := common.id_ne id₁ id₂ id₃ Hbf.idLow Hbf.idLow0
  have Hnz := common.id_nz id₁ id₂ id₃ Hbf.idLow Hbf.idLow0
  have h1 := Hnz id₁ (by simp); have h2 := Hnz id₂ (by simp); have h3 := Hnz id₃ (by simp)
  refine ⟨?_, ?_, ?_⟩
  · unfold dir3
    rw [if_neg (fun e => h1 (by rw [← e]; rfl)), if_neg (fun e => h2 (by rw [← e]; rfl)),
      if_neg (fun e => h3 (by rw [← e]; rfl))]
  · intro i j h hi hj
    unfold dir3 at hi hj
    split at hi <;> split at hj <;> (try split at hi) <;> (try split at hj) <;>
      (try split at hi) <;> (try split at hj) <;> simp_all <;> (try decide)
  · intro i s hs
    unfold dir3 at hs
    split at hs
    · simp at hs; subst hs; decide
    split at hs
    · simp at hs; subst hs; decide
    split at hs
    · simp at hs; subst hs; decide
    · simp at hs

set_option maxHeartbeats 1000000 in
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_StartMember : common.StartMember.spec (GF := GF) (hG := hG))
    (wp_Serve : common.Serve.spec (GF := GF) (hG := hG))
    (wp_NewClient : common.NewClient.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS CRE CEC N id₁ id₂ id₃ ctxs boot Hbf Htb Hrb48 HrbN Hck Haf Hbuq Hdbo Hms hAs
  wp_start as ⟨Ha₁, Ha₂, Ha₃, Hac, Hf₁, Hf₂, Hf₃, Htok, #Hprem⟩
  iunfold premises at Hprem
  icases Hprem with ⟨#Hb₁, #Hb₂, #Hb₃, #Hmarsh, #Hcom⟩
  -- `Main`'s premises in the shared start's form
  iunfold bootPremise at Hb₁
  iunfold bootPremise at Hb₂
  iunfold bootPremise at Hb₃
  ihave #Hc₁ := common.bootPremise_of N [id₁, id₂, id₃] (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
      go!"putget3" name₁
      (common.urls3 name₁ name₂ name₃ initURLs3 peerAddr₁ clientAddr₁) id₁ (cfgOk name₁)
      (urlsOk peerAddr₁ clientAddr₁) (fun _ h => h) (fun _ h => h) $$ Hb₁
  ihave #Hc₂ := common.bootPremise_of N [id₁, id₂, id₃] (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
      go!"putget3" name₂
      (common.urls3 name₁ name₂ name₃ initURLs3 peerAddr₂ clientAddr₂) id₂ (cfgOk name₂)
      (urlsOk peerAddr₂ clientAddr₂) (fun _ h => h) (fun _ h => h) $$ Hb₂
  ihave #Hc₃ := common.bootPremise_of N [id₁, id₂, id₃] (LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
      go!"putget3" name₃
      (common.urls3 name₁ name₂ name₃ initURLs3 peerAddr₃ clientAddr₃) id₃ (cfgOk name₃)
      (urlsOk peerAddr₃ clientAddr₃) (fun _ h => h) (fun _ h => h) $$ Hb₃
  ihave #Hcm' : common.commonPremises (GF := GF) $$ []
  · iunfold common.commonPremises; iunfold putget3.commonPremises at Hcom; iexact Hcom
  ihave #Hcom' := Hcom
  iunfold putget3.commonPremises at Hcom'
  icases Hcom' with ⟨-, -, -, -, -, #Hnrl⟩
  -- `context`'s `closedchan`, from its package's fact
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  -- the imports' package facts
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pv3 : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  (try wp_auto)
  simp only [github_com.mit_pdos.etcd_grove.examples.putget3.peerAddr1,
    github_com.mit_pdos.etcd_grove.examples.putget3.peerAddr2,
    github_com.mit_pdos.etcd_grove.examples.putget3.peerAddr3,
    github_com.mit_pdos.etcd_grove.examples.putget3.clientAddr,
    github_com.mit_pdos.etcd_grove.examples.putget3.clientAddr2,
    github_com.mit_pdos.etcd_grove.examples.putget3.clientAddr3]
  wp_apply wp_NewNop as %lg %Hlg
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
  ihave #Hsls : [∗map] k ↦ sl ∈ GMap.insert name₃ (slice.mk peer₃ (W64 1) (W64 1))
      (GMap.insert name₂ (slice.mk peer₂ (W64 1) (W64 1))
        (GMap.insert name₁ (slice.mk peer₁ (W64 1) (W64 1)) ∅)), sl ↦*□ initURLs3 k $$ []
  · iapply (BigSepM.bigSepM_insert (by
      rw [gmap_get?_eq, GMap.lookup_insert_ne _ _ (by decide : name₂ ≠ name₃),
        GMap.lookup_insert_ne _ _ (by decide : name₁ ≠ name₃)]; rfl)).2
    isplitr; · iexact Hu₃
    iapply (BigSepM.bigSepM_insert (by
      rw [gmap_get?_eq, GMap.lookup_insert_ne _ _ (by decide : name₁ ≠ name₂)]; rfl)).2
    isplitr; · iexact Hu₂
    iapply (BigSepM.bigSepM_insert (GMap.lookup_empty _)).2
    isplitr; · iexact Hu₁
    iapply BigSepM.bigSepM_empty.2; itrivial
  -- the ghost state of the cluster and its members (`alloc3`)
  have hblen0 : boot.length = 3 := by rw [Hbf.boot.1]; rfl
  imod (common.alloc3 id₁ id₂ id₃ ctxs boot Hbf.idLow Hbf.idLow0 Hbf.boot Hbf.cc
      (dir3 id₁ id₂ id₃) peerAddr₁ peerAddr₂ peerAddr₃ (dir3_ok id₁ id₂ id₃ ctxs boot Hbf).1
      (dir3_host id₁ id₂ id₃) (by omega) (by omega)) $$ Hmarsh Hf₁ Hf₂ Hf₃
    with ⟨%γ, %reg₁, %reg₂, %reg₃, %ρ₁, %ρ₂, %ρ₃, %E₁, %E₂, %E₃, %Φs, %γn, %Hal,
    Hmb₁, ⟨#Hnet₁, Hpo₁⟩, Hmb₂, ⟨#Hnet₂, Hpo₂⟩, Hmb₃, ⟨#Hnet₃, Hpo₃⟩, Hetcd⟩
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hlog₁, -⟩ := Hal
  obtain ⟨hn12, hn13, hn23⟩ := common.id_ne id₁ id₂ id₃ Hbf.idLow Hbf.idLow0
  have hd₁ : go!"http://" ++ peerAddr₁ ∈ dir3 id₁ id₂ id₃ id₁ := by simp [dir3]
  have hd₂ : go!"http://" ++ peerAddr₂ ∈ dir3 id₁ id₂ id₃ id₂ := by simp [dir3, hn12.symm]
  have hd₃ : go!"http://" ++ peerAddr₃ ∈ dir3 id₁ id₂ id₃ id₃ := by
    simp [dir3, hn13.symm, hn23.symm]
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  -- the three members (`StartMember`), the thread token passed along
  wp_apply (wp_StartMember N name₁ peerAddr₁ clientAddr₁ go!"putget3"
      (slice.mk peer₁ (W64 1) (W64 1)) pm lg
      (GMap.insert name₃ (slice.mk peer₃ (W64 1) (W64 1)) (GMap.insert name₂ (slice.mk peer₂ (W64 1) (W64 1))
        (GMap.insert name₁ (slice.mk peer₁ (W64 1) (W64 1)) ∅))) initURLs3
      (common.urls3 name₁ name₂ name₃ initURLs3 peerAddr₁ clientAddr₁) [id₁, id₂, id₃]
      (LogEntry.toEntries boot 0) ctxs
      (dir3 id₁ id₂ id₃) id₁ { γ with reg := reg₁ } ρ₁ E₁ Φs γn Htb Hrb48 HrbN
      hvs hrule hboot hblen hγn1 hγn2 (dir3_ok id₁ id₂ id₃ ctxs boot Hbf) hd₁ ⟨rfl, rfl, ⟨_, _, _, rfl⟩, rfl⟩ Hlg Hck Haf
      Hbuq Hdbo) $$ [Ha₁ Htok Hmb₁ Hpo₁] as %s₁ %err₁ Hr₁
  · iframe; iframe #
    iExactEq Hq₁; rfl
  icases Hr₁ with (⟨%Herr, Htok⟩ | ⟨%Herr, Hup₁⟩)
  · cases err₁ with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  iunfold common.memberUp at Hup₁
  icases Hup₁ with ⟨%E, %cfg, %γw, %HEc, #Hreq, #Hrd, Hgo, Hlg3, Hrslots, #Hwb, #Hsf, Hwpi, Hbemu,
    Hlts, Hlgs, Hrds, Hsts, Hbms, -, HWR⟩
  iunfold srvGoRes at Hgo
  icases Hgo with ⟨Hwgr, Htok⟩
  wp_apply (wp_StartMember N name₂ peerAddr₂ clientAddr₂ go!"putget3"
      (slice.mk peer₂ (W64 1) (W64 1)) pm lg
      (GMap.insert name₃ (slice.mk peer₃ (W64 1) (W64 1)) (GMap.insert name₂ (slice.mk peer₂ (W64 1) (W64 1))
        (GMap.insert name₁ (slice.mk peer₁ (W64 1) (W64 1)) ∅))) initURLs3
      (common.urls3 name₁ name₂ name₃ initURLs3 peerAddr₂ clientAddr₂) [id₁, id₂, id₃]
      (LogEntry.toEntries boot 0) ctxs
      (dir3 id₁ id₂ id₃) id₂ { γ with reg := reg₂ } ρ₂ E₂ Φs γn Htb Hrb48 HrbN
      hvs hrule hboot hblen hγn1 hγn2 (dir3_ok id₁ id₂ id₃ ctxs boot Hbf) hd₂ ⟨rfl, rfl, ⟨_, _, _, rfl⟩, rfl⟩ Hlg Hck Haf
      Hbuq Hdbo) $$ [Ha₂ Htok Hmb₂ Hpo₂] as %s₂ %err₂ Hr₂
  · iframe; iframe #
    iExactEq Hq₂; rfl
  icases Hr₂ with (⟨%Herr, Htok⟩ | ⟨%Herr, Hup₂⟩)
  · cases err₂ with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  iunfold common.memberUp at Hup₂
  icases Hup₂ with ⟨%E', %cfg', %γw', -, -, -, Hgo₂, -⟩
  iunfold srvGoRes at Hgo₂
  icases Hgo₂ with ⟨-, Htok⟩
  wp_apply (wp_StartMember N name₃ peerAddr₃ clientAddr₃ go!"putget3"
      (slice.mk peer₃ (W64 1) (W64 1)) pm lg
      (GMap.insert name₃ (slice.mk peer₃ (W64 1) (W64 1)) (GMap.insert name₂ (slice.mk peer₂ (W64 1) (W64 1))
        (GMap.insert name₁ (slice.mk peer₁ (W64 1) (W64 1)) ∅))) initURLs3
      (common.urls3 name₁ name₂ name₃ initURLs3 peerAddr₃ clientAddr₃) [id₁, id₂, id₃]
      (LogEntry.toEntries boot 0) ctxs
      (dir3 id₁ id₂ id₃) id₃ { γ with reg := reg₃ } ρ₃ E₃ Φs γn Htb Hrb48 HrbN
      hvs hrule hboot hblen hγn1 hγn2 (dir3_ok id₁ id₂ id₃ ctxs boot Hbf) hd₃ ⟨rfl, rfl, ⟨_, _, _, rfl⟩, rfl⟩ Hlg Hck Haf
      Hbuq Hdbo) $$ [Ha₃ Htok Hmb₃ Hpo₃] as %s₃ %err₃ Hr₃
  · iframe; iframe #
    iExactEq Hq₃; rfl
  icases Hr₃ with (⟨%Herr, Htok⟩ | ⟨%Herr, Hup₃⟩)
  · cases err₃ with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  iunfold common.memberUp at Hup₃
  icases Hup₃ with ⟨%E'', %cfg'', %γw'', -, -, -, Hgo₃, -⟩
  iunfold srvGoRes at Hgo₃
  icases Hgo₃ with ⟨-, Htok⟩
  ihave Hgo : srvGoRes s₁ $$ [Hwgr Htok]
  · iunfold srvGoRes; iframe
  obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HEc
  -- `Serve(s, clientAddr)`, with etcd's KV calls registered at the address
  haveI := Hms
  wp_apply (wp_Serve s₁ clientAddr₁ E { ρ₁ with wait := γw } ρ₁.rd cfg
      (fun cid mid _ => common.etcdKVAt clientAddr₁ E { ρ₁ with wait := γw } ρ₁.rd cid mid)
      (by rw [HElg]; exact Hlg) HEtr HEw Hms Hbuq)
    $$ [Hac Hlg3 Hbemu Hgo Hwpi HWR Hlts Hlgs Hrds Hsts Hrslots Hbms] as %serr Hs
  · iframe; iframe #
    iintro %gs %lis %cid %mid %R Hg
    iapply (common.kv_served s₁ E { ρ₁ with wait := γw } ρ₁.rd gs lis clientAddr₁ cid mid R Hrb48)
    iframe; iframe #
  icases Hs with (%Hserr | ⟨%Hserr, %cid, %mid, %R, #Hkv⟩)
  · cases serr with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hserr
  wp_auto
  ihave #Hregs := common.etcdKVAt_regs clientAddr₁ E { ρ₁ with wait := γw } ρ₁.rd cid mid
    rfl $$ Hkv
  -- `NewClient(clientAddr, lg)` (etcd's default client configuration)
  wp_apply (wp_NewClient clientAddr₁ lg
      (EtcdGrove.client.srvWEnv R clientAddr₁ [] null null [] null default) Hlg
      (by unfold plainEndpoint clientAddr₁; decide) Htb) as %cl %cerr Hcl
  icases Hcl with (⟨%Hcerr, #Hnc, -⟩ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hcerr
  wp_auto
  -- `pctx, pcancel := context.WithTimeout(context.Background(), common.RequestTimeout)`
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %pctx %pcd %pcancel ⟨#Hpcancel, #Hpctx, #Hpce, -⟩
  (try wp_auto)
  -- the client's invariant, the floor, no options
  rw [kvModelSt_boot _ (fun _ _ => True) _ _ (srvBootLogOk_of_BootLog _ _ _ Hbf.boot)]
  imod (client.putGetInv_alloc_log ρ₁.rd (kvModel ρ₁.rd.kv (bootEntries (LogEntry.toEntries boot 0))) go!"k" go!"v" ⊤)
    $$ Hetcd with ⟨%γf, #Hinv⟩
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
  -- `cli.Put(ctx, "k", "v")`
  wp_apply (client.client_Put_own cl clientAddr₁ _ E ρ₁.rd γf cid mid
      pctx pcd go!"k" go!"v" slice.nil []
      (opSizeOk_opPutModel (K := 1) (E := 0) (V := 1) (optsKeep_nil _ _ _) (by decide) (by decide)
        (by decide))) as %presp %perr Hput
  · iframe #
  -- `pcancel()`
  (try wp_auto)
  wp_apply Hpcancel
  icases Hput with (⟨%Hperr, -, #Hflag⟩ | %Hpfail)
  rotate_left
  · obtain ⟨Hperr, -⟩ := Hpfail
    cases perr with
    | nil => exact absurd rfl Hperr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hperr
  (try wp_auto)
  -- `gctx, gcancel := context.WithTimeout(context.Background(), common.RequestTimeout)`
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %gctx %gcd %gcancel ⟨#Hgcancel, #Hgctx, #Hgce, -⟩
  (try wp_auto)
  -- `cli.Get(gctx, "k")`
  imod monoNatLbOwn_0 (GF := GF) ρ₁.rd.committed with #Hc0
  wp_apply (client.client_Get_own cl clientAddr₁ _ E ρ₁.rd γf (W64 0) cid mid
      gctx gcd go!"k" go!"v" slice.nil []
      (opSizeOk_opGetModel (K := 1) (E := 0) (V := 0) (optsKeep_nil _ _ _) (by decide) (by decide))) as %gresp %gerr Hget
  · iframe #
    iunfold committedAtLeast
    iExactEq Hc0; rfl
  -- `gcancel()`
  (try wp_auto)
  wp_apply Hgcancel
  icases Hget with (⟨%Hgerr, %m, #Hm, %Hv⟩ | %Hgfail)
  rotate_left
  · obtain ⟨Hgerr, -⟩ := Hgfail
    cases gerr with
    | nil => exact absurd rfl Hgerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hgerr
  (try wp_auto)
  iunfold rangeRespMsg at Hm
  icases Hm with ⟨%Hnn, %h, %sl, %ps, #Hh, #Hhf, #Hkvf, #Hsl, #Hkvs, #Hmore, #Hcount⟩
  -- the reply's first key-value holds `v`
  obtain ⟨kv0, Hkv0, Hval0⟩ : ∃ kv0, m.kvs[0]? = some kv0 ∧ kv0.value = go!"v" := by
    cases h : m.kvs with
    | nil => simp [h] at Hv
    | cons x xs => simp [h] at Hv; exact ⟨x, rfl, Hv⟩
  iunfold txn.kvsIs at Hkvs
  icases Hkvs with ⟨%Hlen, #Hall⟩
  obtain ⟨p0, Hp0⟩ : ∃ p0, ps[0]? = some p0 := by
    have : 0 < ps.length := by
      rw [Hlen]
      cases h : m.kvs with
      | nil => simp [h] at Hkv0
      | cons x xs => simp
    exact ⟨ps[0], List.getElem?_eq_getElem this⟩
  ihave #Hkv := Hall $$ %0 %p0 %kv0 %Hp0 %Hkv0
  iunfold txn.kvIs at Hkv
  icases Hkv with ⟨%kSl, %vSl, -, -, -, -, -, #HvF, #HvS, -⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  have Hne : decide (sl.len = W64 0) = false := by
    rw [decide_eq_false_iff_not]
    intro h
    have hl := Hsll.1
    rw [h] at hl
    have : 0 < ps.length := List.length_pos_of_mem (List.mem_of_getElem? Hp0)
    rw [hl] at this
    exact absurd this (by decide)
  wp_auto
  simp only [Hne]
  wp_auto
  have Hbnd : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by
    have := Hsll.1
    have : 0 < ps.length := List.length_pos_of_mem (List.mem_of_getElem? Hp0)
    constructor <;> word
  simp only [Hbnd, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ DFrac.discard p0 Hbnd.1 $$ [Hsl] as -
  · iframe Hsl; ipureintro; exact Hp0
  wp_apply wp_bytes_to_string vSl kv0.value DFrac.discard $$ [HvS] as -
  · iframe #
  rw [Hval0]
  wp_auto
  iapply HΦ; itrivial

end proof

end putget3
end EtcdGrove
end Perennial
