/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/linkv3/Main.lean` (D20, D21, 2026-10-19;
over the examples' shared start since 2026-10-22, D33). Lean-first (no Rocq counterpart).

The cluster's start is putget3's `Main` (`Proof/.../putget3/Main.lean`, whose steps this follows
up to the client, at linkv3's configuration): the members' premises in the shared start's form;
the three peer URL slices and the initial cluster's map; the ghost state of the cluster and its
members (`common.alloc3`, in `bootstrap`'s order; the cluster's `etcdKV` moved to the first
member's names); `common.StartMember` for each member, the thread token passed along;
`common.Serve` at the first member's client address with the ghost step `grpcUp_noRefusal` (the
member refusal-free, D29) then `kv_served` (etcd's KV calls registered at the address);
`common.NewClient` (etcd's default configuration, so `clientWriteOnce`, D29). Then linkv's `Main`
(`Proof/.../linkv/Main.lean`): the instance's invariant at the cluster's start store
(`linkvInv_alloc_boot`: the bootstrap log changes no KV state) and `linkv.Check(cli, clients, ops,
0)`, which returns `Ok` (`timeout = 0`), so the panic on `Illegal` is not taken. Every step's error
ends `Main` with `Unknown`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv.Check
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.Boot
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.StartMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.Serve
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.NewClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Alloc3
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Served
public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver
open putget3 (httpURL ccOk commonPremises)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3.Assumptions]

set_option maxHeartbeats 1000000 in
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_StartMember : common.StartMember.spec (GF := GF) (hG := hG))
    (wp_Serve : common.Serve.spec (GF := GF) (hG := hG))
    (wp_NewClient : common.NewClient.spec (GF := GF) (hG := hG))
    (wp_Check : linkv.Check.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS ESL ESE N id₁ id₂ id₃ bootLog clients ops Hbf Htb Hrb48 HrbN Hck Haf Hbuq Hdbo Hms hAs
    H0 H31 Hops Hmul
  wp_start as ⟨Ha₁, Ha₂, Ha₃, Hac, Htok, #Hprem⟩
  iunfold premises at Hprem
  icases Hprem with ⟨#Hb₁, #Hb₂, #Hb₃, #Hcom⟩
  -- `Main`'s premises in the shared start's form
  iunfold bootPremise at Hb₁
  iunfold bootPremise at Hb₂
  iunfold bootPremise at Hb₃
  ihave #Hc₁ := common.bootPremise_of N (ids id₁ id₂ id₃) bootLog (dir3 id₁ id₂ id₃) go!"linkv3" name₁
      (common.urls3 name₁ name₂ name₃ initURLs3 peerAddr₁ clientAddr₁) id₁ (cfgOk name₁)
      (urlsOk peerAddr₁ clientAddr₁) (putget3.ccOk (ids id₁ id₂ id₃)) (fun _ h => h) (fun _ h => h) rfl $$ Hb₁
  ihave #Hc₂ := common.bootPremise_of N (ids id₁ id₂ id₃) bootLog (dir3 id₁ id₂ id₃) go!"linkv3" name₂
      (common.urls3 name₁ name₂ name₃ initURLs3 peerAddr₂ clientAddr₂) id₂ (cfgOk name₂)
      (urlsOk peerAddr₂ clientAddr₂) (putget3.ccOk (ids id₁ id₂ id₃)) (fun _ h => h) (fun _ h => h) rfl $$ Hb₂
  ihave #Hc₃ := common.bootPremise_of N (ids id₁ id₂ id₃) bootLog (dir3 id₁ id₂ id₃) go!"linkv3" name₃
      (common.urls3 name₁ name₂ name₃ initURLs3 peerAddr₃ clientAddr₃) id₃ (cfgOk name₃)
      (urlsOk peerAddr₃ clientAddr₃) (putget3.ccOk (ids id₁ id₂ id₃)) (fun _ h => h) (fun _ h => h) rfl $$ Hb₃
  ihave #Hcm' : common.commonPremises (GF := GF) $$ []
  · iunfold common.commonPremises; iunfold putget3.commonPremises at Hcom; iexact Hcom
  ihave #Hcom' := Hcom
  iunfold putget3.commonPremises at Hcom'
  icases Hcom' with ⟨-, -, -, -, -, -, #Hnrl⟩
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
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  (try wp_auto)
  simp only [github_com.mit_pdos.etcd_grove.examples.linkv3.peerAddr1,
    github_com.mit_pdos.etcd_grove.examples.linkv3.peerAddr2,
    github_com.mit_pdos.etcd_grove.examples.linkv3.peerAddr3,
    github_com.mit_pdos.etcd_grove.examples.linkv3.clientAddr,
    github_com.mit_pdos.etcd_grove.examples.linkv3.clientAddr2,
    github_com.mit_pdos.etcd_grove.examples.linkv3.clientAddr3]
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
  -- (in `bootstrap`'s order: `linkv3-2`, `-3`, `-1`; the client's `etcdKV` at `linkv3-1`'s names)
  imod (common.alloc3 putgetWorkload id₂ id₃ id₁ bootLog Hbf.idLow Hbf.idLow0 Hbf.boot
      (dir3 id₁ id₂ id₃) (by omega)) with ⟨%γ, %bud, %ρ₂, %ρ₃, %ρ₁, %E₂, %E₃, %E₁, %Φs, %γn, %Hal,
    Hmb₂, Hsl₂, Hmb₃, Hsl₃, Hmb₁, Hsl₁, Hetcd⟩
  obtain ⟨hcfg, hdyn, hcc, hboot, htr, htx, hγn1, hγn2, -, hwl₂, -, -, hst₁, hwl₁', -, hkv₁, -,
    hlog₁⟩ := Hal
  have hwl₁ : ρ₁.rd.kv.wl = putgetWorkload := by rw [hwl₁', hwl₂]
  -- the cluster's `etcdKV`, at the client's member's names
  ihave Hetcd : etcdKV ρ₁.rd.kv (kvStateOf (kvModel ρ₁.rd.kv (bootEntries bootLog))) $$ [Hetcd]
  · rw [etcdKV_congr ρ₁.rd.kv ρ₂.rd.kv hst₁, hkv₁]; iexact Hetcd
  obtain ⟨hn23, hn21, hn31⟩ := common.id_ne id₂ id₃ id₁ Hbf.idLow Hbf.idLow0
  have hd₁ : go!"http://" ++ peerAddr₁ ∈ dir3 id₁ id₂ id₃ id₁ := by simp [dir3]
  have hd₂ : go!"http://" ++ peerAddr₂ ∈ dir3 id₁ id₂ id₃ id₂ := by simp [dir3, hn21]
  have hd₃ : go!"http://" ++ peerAddr₃ ∈ dir3 id₁ id₂ id₃ id₃ := by
    simp [dir3, hn31, hn23.symm]
  have hblen : bootLog.length ≤ 2 ^ 60 := by rw [Hbf.boot.1]; simp
  -- the three members (`StartMember`), the thread token passed along
  wp_apply (wp_StartMember N name₁ peerAddr₁ clientAddr₁ go!"linkv3"
      (slice.mk peer₁ (W64 1) (W64 1)) pm lg
      (GMap.insert name₃ (slice.mk peer₃ (W64 1) (W64 1)) (GMap.insert name₂ (slice.mk peer₂ (W64 1) (W64 1))
        (GMap.insert name₁ (slice.mk peer₁ (W64 1) (W64 1)) ∅))) initURLs3
      (common.urls3 name₁ name₂ name₃ initURLs3 peerAddr₁ clientAddr₁) (ids id₁ id₂ id₃) bootLog
      (dir3 id₁ id₂ id₃) id₁ γ bud ρ₁ E₁ Φs γn putgetWorkload putgetWorkload_noGrant Htb Hrb48 HrbN
      hcfg hdyn hcc hboot htr htx hblen hγn1 hγn2 hd₁ ⟨rfl, rfl, ⟨_, _, _, rfl⟩, rfl⟩ Hlg Hck Haf
      Hbuq Hdbo) $$ [Ha₁ Htok Hmb₁ Hsl₁] as %s₁ %err₁ Hr₁
  · iframe; iframe #
    iExactEq Hq₁; rfl
  icases Hr₁ with (⟨%Herr, Htok⟩ | ⟨%Herr, Hup₁⟩)
  · cases err₁ with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Herr
  wp_auto
  iunfold common.memberUp at Hup₁
  icases Hup₁ with ⟨%E, %cfg, %γw, %HEc, #Hreq, #Hrd, Hgo, Hlg3, Hrslots, #Hwb, #Hsf, Hwpi, Hbemu,
    Hlts, Hlgs, Hrds, Hsts, Hbms, -, HWR⟩
  iunfold srvGoRes at Hgo
  icases Hgo with ⟨Hwgr, Htok⟩
  wp_apply (wp_StartMember N name₂ peerAddr₂ clientAddr₂ go!"linkv3"
      (slice.mk peer₂ (W64 1) (W64 1)) pm lg
      (GMap.insert name₃ (slice.mk peer₃ (W64 1) (W64 1)) (GMap.insert name₂ (slice.mk peer₂ (W64 1) (W64 1))
        (GMap.insert name₁ (slice.mk peer₁ (W64 1) (W64 1)) ∅))) initURLs3
      (common.urls3 name₁ name₂ name₃ initURLs3 peerAddr₂ clientAddr₂) (ids id₁ id₂ id₃) bootLog
      (dir3 id₁ id₂ id₃) id₂ γ bud ρ₂ E₂ Φs γn putgetWorkload putgetWorkload_noGrant Htb Hrb48 HrbN
      hcfg hdyn hcc hboot htr htx hblen hγn1 hγn2 hd₂ ⟨rfl, rfl, ⟨_, _, _, rfl⟩, rfl⟩ Hlg Hck Haf
      Hbuq Hdbo) $$ [Ha₂ Htok Hmb₂ Hsl₂] as %s₂ %err₂ Hr₂
  · iframe; iframe #
    iExactEq Hq₂; rfl
  icases Hr₂ with (⟨%Herr, Htok⟩ | ⟨%Herr, Hup₂⟩)
  · cases err₂ with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Herr
  wp_auto
  iunfold common.memberUp at Hup₂
  icases Hup₂ with ⟨%E', %cfg', %γw', -, -, -, Hgo₂, -⟩
  iunfold srvGoRes at Hgo₂
  icases Hgo₂ with ⟨-, Htok⟩
  wp_apply (wp_StartMember N name₃ peerAddr₃ clientAddr₃ go!"linkv3"
      (slice.mk peer₃ (W64 1) (W64 1)) pm lg
      (GMap.insert name₃ (slice.mk peer₃ (W64 1) (W64 1)) (GMap.insert name₂ (slice.mk peer₂ (W64 1) (W64 1))
        (GMap.insert name₁ (slice.mk peer₁ (W64 1) (W64 1)) ∅))) initURLs3
      (common.urls3 name₁ name₂ name₃ initURLs3 peerAddr₃ clientAddr₃) (ids id₁ id₂ id₃) bootLog
      (dir3 id₁ id₂ id₃) id₃ γ bud ρ₃ E₃ Φs γn putgetWorkload putgetWorkload_noGrant Htb Hrb48 HrbN
      hcfg hdyn hcc hboot htr htx hblen hγn1 hγn2 hd₃ ⟨rfl, rfl, ⟨_, _, _, rfl⟩, rfl⟩ Hlg Hck Haf
      Hbuq Hdbo) $$ [Ha₃ Htok Hmb₃ Hsl₃] as %s₃ %err₃ Hr₃
  · iframe; iframe #
    iExactEq Hq₃; rfl
  icases Hr₃ with (⟨%Herr, Htok⟩ | ⟨%Herr, Hup₃⟩)
  · cases err₃ with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
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
      (fun cid mid _ => iprop(common.etcdKVAt clientAddr₁ E { ρ₁ with wait := γw } ρ₁.rd cid mid ∗
        ⌜noRefusalAt clientAddr₁⌝))
      (by rw [HElg]; exact Hlg) HEtr HEw Hms Hbuq)
    $$ [Hac Hlg3 Hbemu Hgo Hwpi HWR Hlts Hlgs Hrds Hsts Hrslots Hbms] as %serr Hs
  · iframe; iframe #
    iintro %gs %lis %cid %mid %R Hg
    ihave ⟨Hg, %Hnr⟩ := common.grpcUp_noRefusal s₁ E { ρ₁ with wait := γw } ρ₁.rd gs lis
      clientAddr₁ cid mid R HEo $$ [Hg]
    · iframe; iframe #
    imod (common.kv_served s₁ E { ρ₁ with wait := γw } ρ₁.rd gs lis clientAddr₁ cid mid R Hrb48)
      $$ [Hg Hlts Hlgs Hrds Hsts Hrslots Hbms] with ⟨Hserv, #Hkv⟩
    · iframe; iframe #
    imodintro
    iframe Hserv Hkv
    ipureintro; exact Hnr
  icases Hs with (%Hserr | ⟨%Hserr, %cid, %mid, %R, #Hkv, %Hnr⟩)
  · cases serr with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hserr
  wp_auto
  iunfold common.etcdKVAt at Hkv
  icases Hkv with ⟨#HPut, #HRange, #HDel, #HTxn⟩
  -- `NewClient(clientAddr, lg)` (etcd's default client configuration)
  wp_apply (wp_NewClient clientAddr₁ lg
      (EtcdGrove.client.srvWEnv R clientAddr₁ [] null null [] null) Hlg
      (by unfold plainEndpoint clientAddr₁; decide) Htb) as %cl %cerr Hcl
  icases Hcl with (⟨%Hcerr, #Hnc⟩ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hcerr
  wp_auto
  -- (D29) a write sent at most once: the member is refusal-free
  ihave #Hwo : client.clientWriteOnce (GF := GF) cl [clientAddr₁] $$ []
  · iunfold client.clientWriteOnce; ipureintro
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at ha
    subst ha; exact Hnr
  -- the instance's invariant, at the server's start store (empty)
  imod (linkv.linkvInv_alloc_boot ρ₁.rd.kv hlog₁ (ccOk (ids id₁ id₂ id₃)) (ids id₁ id₂ id₃) bootLog
      Hbf.boot (by rw [hwl₁]; intro; trivial) ⊤) $$ Hetcd
    with ⟨%γl, #Hlinv, Hst⟩
  -- `Check(cli, clients, ops, 0)`
  wp_apply (wp_Check γl cl clientAddr₁ _ E ρ₁.rd cid mid clients ops (W64 0) hAs
      (by omega) H0 H31 Hops Hmul) $$ [Hst] as %r %Hr
  · iframe; iframe #
  obtain ⟨-, Hok⟩ := Hr
  have Hok : r = go!"Ok" := Hok (by decide)
  subst Hok
  wp_auto
  iapply HΦ; ipureintro; left; rfl

end proof

end linkv3
end EtcdGrove
end Perennial
