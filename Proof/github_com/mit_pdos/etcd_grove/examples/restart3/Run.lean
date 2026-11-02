/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/restart3/Run.lean` (the restart plan's R2,
2026-11-02). Lean-first (no Rocq counterpart).

putget3's `Main` proof (`putget3/Main.lean`) for `restart3`'s steps: the peer URLs and the initial
cluster's map; the ghost state of the cluster and its members (`common.alloc3`); `startMember` for
each member (`startMember.spec`), the first thread token passed from one to the next out of the
previous member's `srvGoRes`; member 1's gRPC API served (`serveClient`, with the ghost step
`common.kv_served`); a client of it (`common.NewClient`); the client's invariant for `k ↦ v2` at the
bootstrap log; the put of `k0` (`put.specOther`); member 3's leader and member id (`Leader`,
`MemberID`, from its request view); and `restartCheck` of member 2 or 3, with the second thread
token (their KV state's ghost variable member 1's, `alloc3`'s).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.restart3.Run
public import Spec.github_com.mit_pdos.etcd_grove.examples.restart3.startMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.restart3.serveClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.restart3.restartCheck
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.NewClient
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Leader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Alloc3
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Served
public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.restart3.Assumptions]

/-- A host of the directory is one of the three peer addresses (putget3's `dir3_host`). -/
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

/-- **`Run`'s directory is well formed** (putget3's `dir3_ok`). -/
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

/-- **A started server's leader and member-id fields** (what `Leader` and `MemberID` read), from
its request view. -/
theorem leadInv_memberID_of_req (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    isServerReq (GF := GF) s E ρ ⊢ srvLeadInv s ∗ ∃ mid : w64, srvMemberIDAddr s ↦□ mid := by
  iintro #Hreq
  iunfold isServerReq at Hreq
  icases Hreq with ⟨⟨%v, #Hv⟩, -⟩
  iunfold srvReqFieldsAt at Hv
  icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hmid, #Hlead, -⟩
  isplitl
  · iunfold srvLeadInv
    iunfold srvAtomicU64 at Hlead
    iexact Hlead
  · iexists v.memberID
    iexact Hmid

set_option maxHeartbeats 2000000 in
theorem Run.wp_proof
    (wp_startMember : startMember.spec (GF := GF) (hG := hG))
    (wp_serveClient : serveClient.spec (GF := GF) (hG := hG))
    (wp_NewClient : common.NewClient.spec (GF := GF) (hG := hG))
    (wp_putOther : put.specOther (GF := GF) (hG := hG))
    (wp_Leader : EtcdServer.Leader.spec (GF := GF) (hG := hG))
    (wp_MemberID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (wp_restartCheck : restartCheck.spec (GF := GF) (hG := hG)) :
    Run.spec (GF := GF) (hG := hG) := by
  intro CS CRE CEC lg N id₁ id₂ id₃ ctxs boot ThB RcB RcN Hlg Hp Hms hAs
  obtain ⟨Hbf, Hck, Haf, Hbuq, Hrf, Hdbo⟩ := Hp
  have Htb := ThreadBoundLe.le (GF := GF) (2 ^ 28)
  have Hrb48 := ReceiptBoundLe.le (GF := GF) (2 ^ 48)
  wp_start as Hres
  iunfold runRes at Hres
  icases Hres with ⟨Ha₁, Ha₂, Ha₃, Hac₁, Hac₂, Hac₃, Hf₁, Hf₂, Hf₃, Htok, Htok2, #Hprem⟩
  iunfold premises at Hprem
  icases Hprem with ⟨#Hb₁, #Hb₂, #Hb₃, #HbR₂, #HbR₃, #Hmarsh, #Hcom⟩
  ihave #Hcom' := Hcom
  iunfold common.commonPremises at Hcom'
  icases Hcom' with ⟨-, -, -, -, -, #Hnrl⟩
  -- `context`'s `closedchan`, from its package's fact
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  -- the imports' package facts
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pv3 : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pcom : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.common $$ []
  · iPkgInit
  (try wp_auto)
  simp only [github_com.mit_pdos.etcd_grove.examples.restart3.peerAddr1,
    github_com.mit_pdos.etcd_grove.examples.restart3.peerAddr2,
    github_com.mit_pdos.etcd_grove.examples.restart3.peerAddr3,
    github_com.mit_pdos.etcd_grove.examples.restart3.clientAddr1,
    github_com.mit_pdos.etcd_grove.examples.restart3.clientAddr2,
    github_com.mit_pdos.etcd_grove.examples.restart3.clientAddr3]
  -- the peer URLs and the initial cluster's map, read-only from here on
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
  have hsl : ∀ p : Loc, slice.mk p (W64 (max (max (0 + 1) 0) 0)) (W64 (max (max (0 + 1) 0) 0)) =
      slice.mk p (W64 1) (W64 1) := fun _ => rfl
  simp only [hsl] at *
  ihave #Hq₁ : (slice.mk peer₁ (W64 1) (W64 1)) ↦*□ [common.httpURL peerAddr₁] $$ []
  · iExactEq Hpeer₁; rfl
  ihave #Hq₂ : (slice.mk peer₂ (W64 1) (W64 1)) ↦*□ [common.httpURL peerAddr₂] $$ []
  · iExactEq Hpeer₂; rfl
  ihave #Hq₃ : (slice.mk peer₃ (W64 1) (W64 1)) ↦*□ [common.httpURL peerAddr₃] $$ []
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
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hlog₁, hst₂, hst₃, -⟩ := Hal
  obtain ⟨hn12, hn13, hn23⟩ := common.id_ne id₁ id₂ id₃ Hbf.idLow Hbf.idLow0
  have hd₁ : go!"http://" ++ peerAddr₁ ∈ dir3 id₁ id₂ id₃ id₁ := by simp [dir3]
  have hd₂ : go!"http://" ++ peerAddr₂ ∈ dir3 id₁ id₂ id₃ id₂ := by simp [dir3, hn12.symm]
  have hd₃ : go!"http://" ++ peerAddr₃ ∈ dir3 id₁ id₂ id₃ id₃ := by
    simp [dir3, hn13.symm, hn23.symm]
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  -- the three members (`startMember`), the thread token passed along
  wp_apply (wp_startMember N name₁ peerAddr₁ clientAddr₁ (slice.mk peer₁ (W64 1) (W64 1)) pm lg
      (GMap.insert name₃ (slice.mk peer₃ (W64 1) (W64 1)) (GMap.insert name₂ (slice.mk peer₂ (W64 1) (W64 1))
        (GMap.insert name₁ (slice.mk peer₁ (W64 1) (W64 1)) ∅))) initURLs3
      (urlsOk peerAddr₁ clientAddr₁) [id₁, id₂, id₃] (LogEntry.toEntries boot 0) ctxs
      (dir3 id₁ id₂ id₃) id₁ { γ with reg := reg₁ } ρ₁ E₁ Φs γn
      hvs hrule hboot hblen hγn1 hγn2 (dir3_ok id₁ id₂ id₃ ctxs boot Hbf) hd₁
      ⟨rfl, rfl, ⟨_, _, _, rfl⟩, rfl⟩ Hlg Hck Haf Hbuq Hdbo) $$ [Ha₁ Htok Hmb₁ Hpo₁]
    as %m₁ %err₁ Hr₁
  · iframe; iframe #
  icases Hr₁ with (⟨%Herr, Htok⟩ | ⟨%Herr, %s₁, %pl₁, Hup₁, Hst₁⟩)
  · cases err₁ with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  iunfold common.memberUp at Hup₁
  icases Hup₁ with ⟨%E, %cfg, %γw, %HEc, #Hreq, #Hrd, Hgo, Hlg3, Hrslots, #Hwb, #Hsf, Hbemu,
    Hlts, Hlgs, Hrds, Hsts, Hbms, -, HWR⟩
  iunfold srvGoRes at Hgo
  icases Hgo with ⟨Hwgr, Htok⟩
  wp_apply (wp_startMember N name₂ peerAddr₂ clientAddr₂ (slice.mk peer₂ (W64 1) (W64 1)) pm lg
      (GMap.insert name₃ (slice.mk peer₃ (W64 1) (W64 1)) (GMap.insert name₂ (slice.mk peer₂ (W64 1) (W64 1))
        (GMap.insert name₁ (slice.mk peer₁ (W64 1) (W64 1)) ∅))) initURLs3
      (urlsOk peerAddr₂ clientAddr₂) [id₁, id₂, id₃] (LogEntry.toEntries boot 0) ctxs
      (dir3 id₁ id₂ id₃) id₂ { γ with reg := reg₂ } ρ₂ E₂ Φs γn
      hvs hrule hboot hblen hγn1 hγn2 (dir3_ok id₁ id₂ id₃ ctxs boot Hbf) hd₂
      ⟨rfl, rfl, ⟨_, _, _, rfl⟩, rfl⟩ Hlg Hck Haf Hbuq Hdbo) $$ [Ha₂ Htok Hmb₂ Hpo₂]
    as %m₂ %err₂ Hr₂
  · iframe; iframe #
  icases Hr₂ with (⟨%Herr, Htok⟩ | ⟨%Herr, %s₂, %pl₂, Hup₂, Hst₂⟩)
  · cases err₂ with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  iunfold common.memberUp at Hup₂
  icases Hup₂ with ⟨%E₂', %cfg₂, %γw₂, -, #Hreq₂, -, Hgo₂, -⟩
  iunfold srvGoRes at Hgo₂
  icases Hgo₂ with ⟨-, Htok⟩
  wp_apply (wp_startMember N name₃ peerAddr₃ clientAddr₃ (slice.mk peer₃ (W64 1) (W64 1)) pm lg
      (GMap.insert name₃ (slice.mk peer₃ (W64 1) (W64 1)) (GMap.insert name₂ (slice.mk peer₂ (W64 1) (W64 1))
        (GMap.insert name₁ (slice.mk peer₁ (W64 1) (W64 1)) ∅))) initURLs3
      (urlsOk peerAddr₃ clientAddr₃) [id₁, id₂, id₃] (LogEntry.toEntries boot 0) ctxs
      (dir3 id₁ id₂ id₃) id₃ { γ with reg := reg₃ } ρ₃ E₃ Φs γn
      hvs hrule hboot hblen hγn1 hγn2 (dir3_ok id₁ id₂ id₃ ctxs boot Hbf) hd₃
      ⟨rfl, rfl, ⟨_, _, _, rfl⟩, rfl⟩ Hlg Hck Haf Hbuq Hdbo) $$ [Ha₃ Htok Hmb₃ Hpo₃]
    as %m₃ %err₃ Hr₃
  · iframe; iframe #
  icases Hr₃ with (⟨%Herr, Htok⟩ | ⟨%Herr, %s₃, %pl₃, Hup₃, Hst₃⟩)
  · cases err₃ with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  iunfold common.memberUp at Hup₃
  icases Hup₃ with ⟨%E₃', %cfg₃, %γw₃, -, #Hreq₃, -, Hgo₃, -⟩
  iunfold srvGoRes at Hgo₃
  icases Hgo₃ with ⟨-, Htok⟩
  ihave Hgo : srvGoRes s₁ $$ [Hwgr Htok]
  · iunfold srvGoRes; iframe
  obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HEc
  -- `serveClient(m1, clientAddr1)`, with etcd's KV calls registered at the address
  haveI := Hms
  iunfold memberStop at Hst₁
  icases Hst₁ with ⟨Hm₁, -, -, -⟩
  wp_apply (wp_serveClient m₁ s₁ pl₁ clientAddr₁ E { ρ₁ with wait := γw } ρ₁.rd cfg
      (fun cid mid _ => common.etcdKVAt clientAddr₁ E { ρ₁ with wait := γw } ρ₁.rd cid mid)
      (by rw [HElg]; exact Hlg) HEtr HEw Hms Hbuq)
    $$ [Hm₁ Hac₁ Hlg3 Hbemu Hgo HWR Hlts Hlgs Hrds Hsts Hrslots Hbms] as %serr ⟨-, Hs⟩
  · iframe; iframe #
    iintro %gs %lis %cid %mid %R Hg
    iapply (common.kv_served s₁ E { ρ₁ with wait := γw } ρ₁.rd gs lis clientAddr₁ cid mid R Hrb48
      Hrf rfl)
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
  -- `NewClient(clientAddr1, lg)` (etcd's default client configuration)
  wp_apply (wp_NewClient clientAddr₁ lg
      (EtcdGrove.client.srvWEnv R clientAddr₁ [] null null [] null default) Hlg
      (by unfold plainEndpoint clientAddr₁; decide) (by omega)) as %cl %cerr Hcl
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
  -- the client's invariant for `k ↦ v2`, at the bootstrap log
  rw [kvModelSt_boot _ (fun _ _ => True) _ _ (srvBootLogOk_of_BootLog _ _ _ Hbf.boot)]
  imod (client.putGetInv_alloc_log ρ₁.rd (kvModel ρ₁.rd.kv (bootEntries (LogEntry.toEntries boot 0)))
      go!"k" go!"v2" ⊤) $$ Hetcd with ⟨%γf, #Hinv⟩
  -- `put(cli, "k0", "v1")`: another key
  wp_apply (wp_putOther cl clientAddr₁ (EtcdGrove.client.srvWEnv R clientAddr₁ [] null null [] null default)
      E ρ₁.rd γf cid mid go!"k" go!"v2" go!"k0" go!"v1" (by decide)
      (opSizeOk_opPutModel (K := 2) (E := 0) (V := 2) (optsKeep_nil _ _ _) (by decide) (by decide)
        (by decide)) hAs) as %perr -
  · iframe; iframe #
  cases perr with
  | ok ei =>
    wp_auto
    iapply HΦ; itrivial
  | nil => ?_
  wp_auto
  -- `m3.s.Leader() == m3.s.MemberID()`
  ihave ⟨#Hlead₃, %mid₃, #Hmid₃⟩ := leadInv_memberID_of_req s₃ E₃' { ρ₃ with wait := γw₃ } $$ Hreq₃
  iunfold memberStop at Hst₃
  icases Hst₃ with ⟨Hm₃, Hsr₃, %Hli₃, Hcl₃⟩
  wp_auto
  wp_apply (wp_Leader s₃) as %l -
  · iframe #
  (try wp_auto)
  wp_apply (wp_MemberID s₃ mid₃)
  · iframe #
  (try wp_auto)
  wp_if_destruct
  · -- member 3 leads: member 2 stopped and started again
    wp_apply (wp_restartCheck cl clientAddr₁
        (EtcdGrove.client.srvWEnv R clientAddr₁ [] null null [] null default) E ρ₁.rd γf cid mid
        m₂ s₂ pl₂ E₂' { ρ₂ with wait := γw₂ } N name₂ peerAddr₂ clientAddr₂
        (slice.mk peer₂ (W64 1) (W64 1)) pm lg
        (GMap.insert name₃ (slice.mk peer₃ (W64 1) (W64 1)) (GMap.insert name₂ (slice.mk peer₂ (W64 1) (W64 1))
          (GMap.insert name₁ (slice.mk peer₁ (W64 1) (W64 1)) ∅))) initURLs3
        (urlsOk peerAddr₂ clientAddr₂) [id₁, id₂, id₃] (LogEntry.toEntries boot 0) ctxs
        (dir3 id₁ id₂ id₃) id₂ { γ with reg := reg₂ } γn hst₂
        hvs hrule hboot hblen hγn1 hγn2 (dir3_ok id₁ id₂ id₃ ctxs boot Hbf) hd₂
        ⟨rfl, rfl, ⟨_, _, _, rfl⟩, rfl⟩ (by unfold plainEndpoint clientAddr₂; decide) Hlg Hck Haf
        Hbuq Hrf Hdbo Hms hAs) $$ [Hst₂ Hac₂ Htok2]
    · iframe; iframe #
    iapply HΦ; itrivial
  · -- member 3 stopped and started again
    wp_apply (wp_restartCheck cl clientAddr₁
        (EtcdGrove.client.srvWEnv R clientAddr₁ [] null null [] null default) E ρ₁.rd γf cid mid
        m₃ s₃ pl₃ E₃' { ρ₃ with wait := γw₃ } N name₃ peerAddr₃ clientAddr₃
        (slice.mk peer₃ (W64 1) (W64 1)) pm lg
        (GMap.insert name₃ (slice.mk peer₃ (W64 1) (W64 1)) (GMap.insert name₂ (slice.mk peer₂ (W64 1) (W64 1))
          (GMap.insert name₁ (slice.mk peer₁ (W64 1) (W64 1)) ∅))) initURLs3
        (urlsOk peerAddr₃ clientAddr₃) [id₁, id₂, id₃] (LogEntry.toEntries boot 0) ctxs
        (dir3 id₁ id₂ id₃) id₃ { γ with reg := reg₃ } γn hst₃
        hvs hrule hboot hblen hγn1 hγn2 (dir3_ok id₁ id₂ id₃ ctxs boot Hbf) hd₃
        ⟨rfl, rfl, ⟨_, _, _, rfl⟩, rfl⟩ (by unfold plainEndpoint clientAddr₃; decide) Hlg Hck Haf
        Hbuq Hrf Hdbo Hms hAs) $$ [Hm₃ Hsr₃ Hcl₃ Hac₃ Htok2]
    · iframe; iframe #
      iunfold memberStop
      iframe
      ipureintro; exact Hli₃
    iapply HΦ; itrivial

end proof

end restart3
end EtcdGrove
end Perennial
