/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/restart/Run.lean` (the restart plan's R2,
2026-11-02). Lean-first (no Rocq counterpart).

putget3's `Main` proof (`putget3/Main.lean`) for `restart3`'s steps: the peer URLs and the initial
cluster's map; the ghost state of the cluster and its members (`etcdstart.alloc3`); `startMember` for
each member (`startMember.spec`), the first thread token passed from one to the next out of the
previous member's `srvGoRes`; member 1's gRPC API served (`serveClient`, with the ghost step
`etcdstart.kv_served`); a client of it (`etcdstart.NewClient`); the client's invariant for `k ↦ v2` at the
bootstrap log; the put of `k0` (`put.specOther`); member 3's leader and member id (`Leader`,
`MemberID`, from its request view); and `restartCheck` of member 2 or 3, with the second thread
token (their KV state's ghost variable member 1's, `alloc3`'s).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart.Run
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart.startMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart.serveClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart.restartCheck
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NewClient
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Leader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Alloc3
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Served
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
namespace etcd_restart

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart.Assumptions]

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

/-- **`Run`'s directory names the peers** (`rafthttp.bootCfg`, `NewServer`'s premise; 2026-11-03, the final
whole-`bootOk` review's M2): its members are the ids, which the peers permute. -/
theorem dir3_dirsOk (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (bl : List LogEntry)
    (Hbf : BootFacts id₁ id₂ id₃ ps ctxs bl) : rafthttp.bootCfg (dir3 id₁ id₂ id₃) ps := by
  refine rafthttp.bootCfg_of _ ps (fun f => ?_) (by rw [Hbf.perm.length_eq]; simp)
  rw [Hbf.perm.mem_iff]
  unfold dir3
  constructor
  · intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    by_cases h1 : f = id₁
    · exact Or.inl h1
    by_cases h2 : f = id₂
    · exact Or.inr (Or.inl h2)
    by_cases h3 : f = id₃
    · exact Or.inr (Or.inr h3)
    rw [if_neg h1, if_neg h2, if_neg h3] at h
    exact absurd rfl h
  · intro hm
    split
    · simp
    split
    · simp
    split
    · simp
    · simp_all

/-- **`Run`'s directory is well formed** (putget3's `dir3_ok`). -/
theorem dir3_ok (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (bl : List LogEntry)
    (Hbf : BootFacts id₁ id₂ id₃ ps ctxs bl) :
    netDirOk (dir3 id₁ id₂ id₃) := by
  obtain ⟨hn12, hn13, hn23⟩ := etcdstart.id_ne id₁ id₂ id₃ Hbf.idLow Hbf.idLow0
  have Hnz := etcdstart.id_nz id₁ id₂ id₃ Hbf.idLow Hbf.idLow0
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
    (wp_NewClient : etcdstart.NewClient.spec (GF := GF) (hG := hG))
    (wp_putOther : put.specOther (GF := GF) (hG := hG))
    (wp_Leader : EtcdServer.Leader.spec (GF := GF) (hG := hG))
    (wp_MemberID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (wp_restartCheck : restartCheck.spec (GF := GF) (hG := hG))
    (hne : mvcc.api.names_nonempty.law) (hRS : mvcc.api.mvccReaders_split.law (GF := GF)) :
    Run.spec (GF := GF) (hG := hG) := by
  intro CS CRE CEC lg N id₁ id₂ id₃ ps ctxs boot ThB RcB RcN HwbN Hp Hms hAs
  obtain ⟨Hbf, Hck, Haf, Hbuq, Hrf, Hdbo⟩ := Hp
  have Htb := ThreadBoundLe.le (GF := GF) (2 ^ 28)
  have Hrb48 := ReceiptBoundLe.le (GF := GF) (2 ^ 48)
  wp_start as ⟨#Hzlg, Hres⟩
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hzlg
  iunfold runRes at Hres
  icases Hres with ⟨Hs₁, Hs₂, Hs₃, Htok, Htok2, #Hprem⟩
  iunfold premises at Hprem
  icases Hprem with ⟨#Hb₁, #Hb₂, #Hb₃, #HbR₂, #HbR₃, #Hmarsh, #Hcom⟩
  ihave #Hcom' := Hcom
  iunfold etcdstart.commonPremises at Hcom'
  icases Hcom' with ⟨-, -, -, #Hnrl⟩
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
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  (try wp_auto)
  simp only [github_com.mit_pdos.etcd_grove.examples.etcd.restart.peerAddr1,
    github_com.mit_pdos.etcd_grove.examples.etcd.restart.peerAddr2,
    github_com.mit_pdos.etcd_grove.examples.etcd.restart.peerAddr3,
    github_com.mit_pdos.etcd_grove.examples.etcd.restart.clientAddr1,
    github_com.mit_pdos.etcd_grove.examples.etcd.restart.clientAddr2,
    github_com.mit_pdos.etcd_grove.examples.etcd.restart.clientAddr3]
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
  ihave #Hq₁ : (slice.mk peer₁ (W64 1) (W64 1)) ↦*□ [etcdstart.httpURL peerAddr₁] $$ []
  · iExactEq Hpeer₁; rfl
  ihave #Hq₂ : (slice.mk peer₂ (W64 1) (W64 1)) ↦*□ [etcdstart.httpURL peerAddr₂] $$ []
  · iExactEq Hpeer₂; rfl
  ihave #Hq₃ : (slice.mk peer₃ (W64 1) (W64 1)) ↦*□ [etcdstart.httpURL peerAddr₃] $$ []
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
  have hblen0 : boot.length = 3 := by rw [Hbf.boot.1, Hbf.perm.length_eq]; rfl
  imod (etcdstart.alloc3 hne id₁ id₂ id₃ ps Hbf.perm ctxs boot Hbf.idLow Hbf.idLow0 Hbf.boot Hbf.cc Hbf.urls
      (dir3 id₁ id₂ id₃) peerAddr₁ peerAddr₂ peerAddr₃ (dir3_ok id₁ id₂ id₃ ps ctxs boot Hbf).1
      (dir3_host id₁ id₂ id₃) (by omega) (by omega) name₁ name₂ name₃ (some clientAddr₁)
      (some clientAddr₂) (some clientAddr₃) .none lease.runCfg_none (by decide))
      $$ Hmarsh Hs₁ Hs₂ Hs₃
    with ⟨%γ, %reg₁, %reg₂, %reg₃, %ρ₁, %ρ₂, %ρ₃, %E₁, %E₂, %E₃, %Φs, %γn, %Hal,
    Hmb₁, ⟨#Hnet₁, Hfr₁⟩, Hmb₂, ⟨#Hnet₂, Hfr₂⟩, Hmb₃, ⟨#Hnet₃, Hfr₃⟩, Hetcd⟩
  -- (lease-mono3) the cluster at the mode `none`: the client's `etcdKV`
  isimp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at Hetcd
  -- the client addresses' listen rights, to `serveClient` and `restartCheck`
  icases etcdstart.memberFreshRes_client _ _ _ _ rfl $$ Hfr₁ with ⟨Hac₁, Hfr₁⟩
  icases etcdstart.memberFreshRes_client _ _ _ _ rfl $$ Hfr₂ with ⟨Hac₂, Hfr₂⟩
  icases etcdstart.memberFreshRes_client _ _ _ _ rfl $$ Hfr₃ with ⟨Hac₃, Hfr₃⟩
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hlog₁, hst₂, hst₃, -⟩ := Hal
  -- (R2c-4) members 2 and 3 out of compaction mode (their boot bundles'): their stops' scope
  icases etcdstart.memberBoot_cmp _ _ _ _ _ _ false $$ Hmb₂ with ⟨%hc₂, Hmb₂⟩
  icases etcdstart.memberBoot_cmp _ _ _ _ _ _ false $$ Hmb₃ with ⟨%hc₃, Hmb₃⟩
  obtain ⟨hn12, hn13, hn23⟩ := etcdstart.id_ne id₁ id₂ id₃ Hbf.idLow Hbf.idLow0
  have hd₁ : go!"http://" ++ peerAddr₁ ∈ dir3 id₁ id₂ id₃ id₁ := by simp [dir3]
  have hd₂ : go!"http://" ++ peerAddr₂ ∈ dir3 id₁ id₂ id₃ id₂ := by simp [dir3, hn12.symm]
  have hd₃ : go!"http://" ++ peerAddr₃ ∈ dir3 id₁ id₂ id₃ id₃ := by
    simp [dir3, hn13.symm, hn23.symm]
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  have hb3 : (LogEntry.toEntries boot 0).length ≤ 3 := by
    simp [LogEntry.toEntries, hblen0]
  -- the three members (`startMember`), the thread token passed along
  wp_apply (wp_startMember N name₁ peerAddr₁ clientAddr₁ (slice.mk peer₁ (W64 1) (W64 1)) pm lg
      (GMap.insert name₃ (slice.mk peer₃ (W64 1) (W64 1)) (GMap.insert name₂ (slice.mk peer₂ (W64 1) (W64 1))
        (GMap.insert name₁ (slice.mk peer₁ (W64 1) (W64 1)) ∅))) initURLs3
      (urlsOk peerAddr₁ clientAddr₁) ps (LogEntry.toEntries boot 0) ctxs
      (dir3 id₁ id₂ id₃) id₁ { γ with reg := reg₁ } ρ₁ E₁ Φs γn
      HwbN hvs hrule hboot hblen hγn1 hγn2 (dir3_ok id₁ id₂ id₃ ps ctxs boot Hbf) hd₁
        (dir3_dirsOk id₁ id₂ id₃ ps ctxs boot Hbf)
      ⟨rfl, rfl, ⟨_, _, _, rfl⟩, rfl⟩
      (etcdstart.utf8Keys_insert _ _ _ (by decide) (etcdstart.utf8Keys_insert _ _ _ (by decide)
        (etcdstart.utf8Keys_insert _ _ _ (by decide) etcdstart.utf8Keys_empty))) Hck Haf Hbuq Hdbo) $$ [Htok Hmb₁ Hfr₁]
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
  icases etcdstart.memberUp_served _ _ _ _ _ _ _ $$ Hup₁ with ⟨%E, %cfg, %γw, %HEc, #Hreq, #Hrd,
    #Hsf, Hgo, Hlg3, Hbemu, HWR, ⟨Hlts, Hlgs, Hrds, Hsts, Hrslots, Hbms⟩, -, -⟩
  iunfold srvGoRes at Hgo
  icases Hgo with ⟨Hwgr, Htok⟩
  wp_apply (wp_startMember N name₂ peerAddr₂ clientAddr₂ (slice.mk peer₂ (W64 1) (W64 1)) pm lg
      (GMap.insert name₃ (slice.mk peer₃ (W64 1) (W64 1)) (GMap.insert name₂ (slice.mk peer₂ (W64 1) (W64 1))
        (GMap.insert name₁ (slice.mk peer₁ (W64 1) (W64 1)) ∅))) initURLs3
      (urlsOk peerAddr₂ clientAddr₂) ps (LogEntry.toEntries boot 0) ctxs
      (dir3 id₁ id₂ id₃) id₂ { γ with reg := reg₂ } ρ₂ E₂ Φs γn
      HwbN hvs hrule hboot hblen hγn1 hγn2 (dir3_ok id₁ id₂ id₃ ps ctxs boot Hbf) hd₂
        (dir3_dirsOk id₁ id₂ id₃ ps ctxs boot Hbf)
      ⟨rfl, rfl, ⟨_, _, _, rfl⟩, rfl⟩
      (etcdstart.utf8Keys_insert _ _ _ (by decide) (etcdstart.utf8Keys_insert _ _ _ (by decide)
        (etcdstart.utf8Keys_insert _ _ _ (by decide) etcdstart.utf8Keys_empty))) Hck Haf Hbuq Hdbo) $$ [Htok Hmb₂ Hfr₂]
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
  -- (R2c-4) member 2 never serves: what its stop takes, out of its started bundle
  icases memberUp_stopRes hRS _ _ _ _ _ _ hc₂ $$ Hup₂ with ⟨⟨%E₂', %γw₂, #Hreq₂, Hgo₂⟩, Hsres₂⟩
  iunfold srvGoRes at Hgo₂
  icases Hgo₂ with ⟨-, Htok⟩
  wp_apply (wp_startMember N name₃ peerAddr₃ clientAddr₃ (slice.mk peer₃ (W64 1) (W64 1)) pm lg
      (GMap.insert name₃ (slice.mk peer₃ (W64 1) (W64 1)) (GMap.insert name₂ (slice.mk peer₂ (W64 1) (W64 1))
        (GMap.insert name₁ (slice.mk peer₁ (W64 1) (W64 1)) ∅))) initURLs3
      (urlsOk peerAddr₃ clientAddr₃) ps (LogEntry.toEntries boot 0) ctxs
      (dir3 id₁ id₂ id₃) id₃ { γ with reg := reg₃ } ρ₃ E₃ Φs γn
      HwbN hvs hrule hboot hblen hγn1 hγn2 (dir3_ok id₁ id₂ id₃ ps ctxs boot Hbf) hd₃
        (dir3_dirsOk id₁ id₂ id₃ ps ctxs boot Hbf)
      ⟨rfl, rfl, ⟨_, _, _, rfl⟩, rfl⟩
      (etcdstart.utf8Keys_insert _ _ _ (by decide) (etcdstart.utf8Keys_insert _ _ _ (by decide)
        (etcdstart.utf8Keys_insert _ _ _ (by decide) etcdstart.utf8Keys_empty))) Hck Haf Hbuq Hdbo) $$ [Htok Hmb₃ Hfr₃]
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
  icases memberUp_stopRes hRS _ _ _ _ _ _ hc₃ $$ Hup₃ with ⟨⟨%E₃', %γw₃, #Hreq₃, Hgo₃⟩, Hsres₃⟩
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
      (fun cid mid _ => etcdstart.etcdKVAt clientAddr₁ E { ρ₁ with wait := γw } ρ₁.rd cid mid)
      (by rw [HElg]; exact Hlg) HEtr HEw Hms Hbuq)
    $$ [Hm₁ Hac₁ Hlg3 Hbemu Hgo HWR Hlts Hlgs Hrds Hsts Hrslots Hbms] as %serr ⟨-, Hs⟩
  · iframe; iframe #
    iintro %gs %lis %cid %mid %R Hg
    iapply (etcdstart.kv_served s₁ E { ρ₁ with wait := γw } ρ₁.rd gs lis clientAddr₁ cid mid R Hrb48
      Hrf rfl)
    unfold etcdstart.kvServeStocks
    iframe; iframe #
  icases Hs with (%Hserr | ⟨%Hserr, %cid, %mid, %R, #Hkv⟩)
  · cases serr with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hserr
  wp_auto
  ihave #Hregs := etcdstart.etcdKVAt_regs clientAddr₁ E { ρ₁ with wait := γw } ρ₁.rd cid mid
    rfl $$ Hkv
  -- `NewClient(clientAddr1, lg)` (etcd's default client configuration)
  wp_apply (wp_NewClient clientAddr₁ lg
      (EtcdGrove.client.srvWEnv R (etcdstart.srvWOf R.E ρ₁.rd false) ρ₁.rd clientAddr₁ [] null null [] null default)
      (by unfold plainEndpoint clientAddr₁; decide) (by omega)) as %cl %cerr Hcl
  · iframe #
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
  wp_apply (wp_putOther cl clientAddr₁ (EtcdGrove.client.srvWEnv R (etcdstart.srvWOf R.E ρ₁.rd false) ρ₁.rd clientAddr₁ [] null null [] null default)
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
        (EtcdGrove.client.srvWEnv R (etcdstart.srvWOf R.E ρ₁.rd false) ρ₁.rd clientAddr₁ [] null null [] null default) E ρ₁.rd γf cid mid
        m₂ s₂ pl₂ ρ₂ N name₂ peerAddr₂ clientAddr₂
        (slice.mk peer₂ (W64 1) (W64 1)) pm lg
        (GMap.insert name₃ (slice.mk peer₃ (W64 1) (W64 1)) (GMap.insert name₂ (slice.mk peer₂ (W64 1) (W64 1))
          (GMap.insert name₁ (slice.mk peer₁ (W64 1) (W64 1)) ∅))) initURLs3
        (urlsOk peerAddr₂ clientAddr₂) ps (LogEntry.toEntries boot 0) ctxs
        (dir3 id₁ id₂ id₃) id₂ { γ with reg := reg₂ } γn HwbN hst₂
        hvs hrule hboot hblen hb3 hγn1 hγn2 (dir3_ok id₁ id₂ id₃ ps ctxs boot Hbf) hd₂
        (dir3_dirsOk id₁ id₂ id₃ ps ctxs boot Hbf)
        ⟨rfl, rfl, ⟨_, _, _, rfl⟩, rfl⟩ (by unfold plainEndpoint clientAddr₂; decide) Hck Haf
        Hbuq Hrf Hdbo Hms hAs) $$ [Hst₂ Hsres₂ Hac₂ Htok2]
    · iframe; iframe #
    iapply HΦ; itrivial
  · -- member 3 stopped and started again
    wp_apply (wp_restartCheck cl clientAddr₁
        (EtcdGrove.client.srvWEnv R (etcdstart.srvWOf R.E ρ₁.rd false) ρ₁.rd clientAddr₁ [] null null [] null default) E ρ₁.rd γf cid mid
        m₃ s₃ pl₃ ρ₃ N name₃ peerAddr₃ clientAddr₃
        (slice.mk peer₃ (W64 1) (W64 1)) pm lg
        (GMap.insert name₃ (slice.mk peer₃ (W64 1) (W64 1)) (GMap.insert name₂ (slice.mk peer₂ (W64 1) (W64 1))
          (GMap.insert name₁ (slice.mk peer₁ (W64 1) (W64 1)) ∅))) initURLs3
        (urlsOk peerAddr₃ clientAddr₃) ps (LogEntry.toEntries boot 0) ctxs
        (dir3 id₁ id₂ id₃) id₃ { γ with reg := reg₃ } γn HwbN hst₃
        hvs hrule hboot hblen hb3 hγn1 hγn2 (dir3_ok id₁ id₂ id₃ ps ctxs boot Hbf) hd₃
        (dir3_dirsOk id₁ id₂ id₃ ps ctxs boot Hbf)
        ⟨rfl, rfl, ⟨_, _, _, rfl⟩, rfl⟩ (by unfold plainEndpoint clientAddr₃; decide) Hck Haf
        Hbuq Hrf Hdbo Hms hAs) $$ [Hm₃ Hsr₃ Hcl₃ Hsres₃ Hac₃ Htok2]
    · iframe; iframe #
      iunfold memberStop
      iframe
      ipureintro; exact Hli₃
    iapply HΦ; itrivial

end proof

end etcd_restart
end EtcdGrove
end Perennial
