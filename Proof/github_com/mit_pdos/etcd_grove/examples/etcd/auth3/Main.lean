/-
`Main()` (`examples/etcd/auth3/auth3.go`; the auth3 Scope's A1, 2026-11-14): **proved**, over its
callees' specs. Lean-first (no Rocq counterpart).

The steps: putget3's start with auth on (the logger; the peer URL slices and the initial cluster's
map, read-only; the cluster's ghost state with auth on, `etcdstart.alloc3On`; the three members,
`startMember`, the thread token passed along, as putget3's `StartMember`s), the history invariant
over member 1's KV names (`akHist_alloc`, at the boot state, `stateHistOk_boot`), then authkv's run
on member 1 (`auth.Run`, its spec `etcd_auth.Run.spec`): its gRPC API at its client address (the
listen right from its fresh bundle), the client's view of the auth history at the start. Every error
returns `Failed`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.startMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Run
public import Spec.go_uber_org.zap.NewNop
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Alloc3On
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Hist

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_auth3

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.auth3.Assumptions]

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

/-- **`Main`'s directory is well formed** (putget3's `dir3_ok`). -/
theorem dir3_ok (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (bl : List LogEntry)
    (Hbf : etcd_putget3.BootFacts id₁ id₂ id₃ ps ctxs bl) :
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

/-- **`Main`'s directory names the peers** (putget3's `dir3_dirsOk`). -/
theorem dir3_dirsOk (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (bl : List LogEntry)
    (Hbf : etcd_putget3.BootFacts id₁ id₂ id₃ ps ctxs bl) : rafthttp.bootCfg (dir3 id₁ id₂ id₃) ps := by
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

/-- A started member's thread token, out of its `memberUpOn` (its `srvGoRes`), and back. -/
theorem memberUpOn_tok (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (id : w64) (γa : auth.AuthNames) :
    etcdstart.memberUpOn s ρ E₀ lg γn id γa ⊢
      threadTok ∗ (threadTok -∗ etcdstart.memberUpOn s ρ E₀ lg γn id γa) := by
  iintro H
  iunfold etcdstart.memberUpOn at H
  icases H with ⟨%E, %cfg, %γw, %HE, H1, H2, #H3, #H4, #H5, Hgo, H7, H8, #H9, #H10, H11, H12,
    #H13, #H14⟩
  iunfold srvGoRes at Hgo
  icases Hgo with ⟨Hwgr, Htok⟩
  iframe Htok
  iintro Htok
  iunfold etcdstart.memberUpOn
  iexists E, cfg, γw
  iframe
  iframe #
  isplitr
  · ipureintro; exact HE
  iunfold srvGoRes
  iframe

set_option maxHeartbeats 1000000 in
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_startMember : startMember.spec (GF := GF) (hG := hG))
    (wp_Run : etcd_auth.Run.spec (GF := GF) (hG := hG))
    (hne : mvcc.api.names_nonempty.law) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS ES FS RS CRE CEC N id₁ id₂ id₃ ps ctxs boot Hbf Htb HLv Hrb48 HrbN HwbN Haf Hbuq Hrf Hdbo
    Hms hAs
  wp_start as ⟨Hs₁, Hs₂, Hs₃, Htok, #Hprem⟩
  iunfold premises at Hprem
  icases Hprem with ⟨#Hb₁, #Hb₂, #Hb₃, #Hmarsh, #Hcom⟩
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  (try wp_auto)
  simp only [github_com.mit_pdos.etcd_grove.examples.etcd.auth3.peerAddr1,
    github_com.mit_pdos.etcd_grove.examples.etcd.auth3.peerAddr2,
    github_com.mit_pdos.etcd_grove.examples.etcd.auth3.peerAddr3,
    github_com.mit_pdos.etcd_grove.examples.etcd.auth3.clientAddr,
    github_com.mit_pdos.etcd_grove.examples.etcd.auth3.clientAddr2,
    github_com.mit_pdos.etcd_grove.examples.etcd.auth3.clientAddr3]
  wp_apply wp_NewNop as %lg #Hlgz
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hlgz
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
  -- the ghost state of the cluster and its members with auth on (`alloc3On`)
  have hblen0 : boot.length = 3 := by rw [Hbf.boot.1, Hbf.perm.length_eq]; rfl
  imod (etcdstart.alloc3On hne id₁ id₂ id₃ ps Hbf.perm ctxs boot Hbf.toBootCore
      (dir3 id₁ id₂ id₃) peerAddr₁ peerAddr₂ peerAddr₃ (dir3_ok id₁ id₂ id₃ ps ctxs boot Hbf).1
      (dir3_host id₁ id₂ id₃) (by omega) (by omega) name₁ name₂ name₃ (some clientAddr₁) none none)
      $$ Hmarsh Hs₁ Hs₂ Hs₃
    with ⟨%γ, %reg₁, %reg₂, %reg₃, %ρ₁, %ρ₂, %ρ₃, %E₁, %E₂, %E₃, %Φs, %γn, %Hal,
    Hmb₁, ⟨#Hnet₁, Hfr₁⟩, Hmb₂, ⟨#Hnet₂, Hfr₂⟩, Hmb₃, ⟨#Hnet₃, Hfr₃⟩, Hetcd, Hview⟩
  -- member 1's client address's listen right, out of its fresh bundle (to `Run`'s `Serve`)
  icases etcdstart.memberFreshRes_client _ _ _ _ rfl $$ Hfr₁ with ⟨Hac, Hfr₁⟩
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hc0₁, hlog₁⟩ := Hal
  -- the history invariant over member 1's KV names, at the boot state
  have hσ₀ : etcd_auth.stateHistOk (kvStateOf (kvModelOn ρ₁.rd.kv srvAuthSt0
      (bootEntries (LogEntry.toEntries boot 0)))) :=
    etcd_auth.stateHistOk_boot ρ₁.rd.kv srvAuthSt0 ps _
      (srvBootLogOk_of_BootLog _ _ _ Hbf.boot) hlog₁
  imod (etcd_auth.akHist_alloc ρ₁.rd.kv _ hσ₀) $$ Hetcd with #Hhist
  obtain ⟨hn12, hn13, hn23⟩ := etcdstart.id_ne id₁ id₂ id₃ Hbf.idLow Hbf.idLow0
  have hd₁ : go!"http://" ++ peerAddr₁ ∈ dir3 id₁ id₂ id₃ id₁ := by simp [dir3]
  have hd₂ : go!"http://" ++ peerAddr₂ ∈ dir3 id₁ id₂ id₃ id₂ := by simp [dir3, hn12.symm]
  have hd₃ : go!"http://" ++ peerAddr₃ ∈ dir3 id₁ id₂ id₃ id₃ := by
    simp [dir3, hn13.symm, hn23.symm]
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  -- the three members (`startMember`), the thread token passed along
  wp_apply (wp_startMember N name₁ peerAddr₁ clientAddr₁
      (slice.mk peer₁ (W64 1) (W64 1)) pm lg
      (GMap.insert name₃ (slice.mk peer₃ (W64 1) (W64 1)) (GMap.insert name₂ (slice.mk peer₂ (W64 1) (W64 1))
        (GMap.insert name₁ (slice.mk peer₁ (W64 1) (W64 1)) ∅))) initURLs3 ps
      (LogEntry.toEntries boot 0) ctxs
      (dir3 id₁ id₂ id₃) id₁ { γ with reg := reg₁ } ρ₁ E₁ Φs γn Htb Hrb48 HrbN HwbN
      hvs hrule hboot hblen hγn1 hγn2 (dir3_ok id₁ id₂ id₃ ps ctxs boot Hbf) hd₁
      (dir3_dirsOk id₁ id₂ id₃ ps ctxs boot Hbf) ⟨rfl, rfl, ⟨_, _, _, rfl⟩, rfl⟩
      (etcdstart.utf8Keys_insert _ _ _ (by decide) (etcdstart.utf8Keys_insert _ _ _ (by decide)
        (etcdstart.utf8Keys_insert _ _ _ (by decide) etcdstart.utf8Keys_empty))) Haf
      Hbuq Hdbo) $$ [Hfr₁ Htok Hmb₁] as %s₁ %err₁ Hr₁
  · iframe; iframe #
  icases Hr₁ with (⟨%Herr, Htok⟩ | ⟨%Herr, %γa, Hup₁⟩)
  · cases err₁ with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  subst Herr
  wp_auto
  icases memberUpOn_tok _ _ _ _ _ _ _ $$ Hup₁ with ⟨Htok, Hup₁⟩
  wp_apply (wp_startMember N name₂ peerAddr₂ clientAddr₂
      (slice.mk peer₂ (W64 1) (W64 1)) pm lg
      (GMap.insert name₃ (slice.mk peer₃ (W64 1) (W64 1)) (GMap.insert name₂ (slice.mk peer₂ (W64 1) (W64 1))
        (GMap.insert name₁ (slice.mk peer₁ (W64 1) (W64 1)) ∅))) initURLs3 ps
      (LogEntry.toEntries boot 0) ctxs
      (dir3 id₁ id₂ id₃) id₂ { γ with reg := reg₂ } ρ₂ E₂ Φs γn Htb Hrb48 HrbN HwbN
      hvs hrule hboot hblen hγn1 hγn2 (dir3_ok id₁ id₂ id₃ ps ctxs boot Hbf) hd₂
      (dir3_dirsOk id₁ id₂ id₃ ps ctxs boot Hbf) ⟨rfl, rfl, ⟨_, _, _, rfl⟩, rfl⟩
      (etcdstart.utf8Keys_insert _ _ _ (by decide) (etcdstart.utf8Keys_insert _ _ _ (by decide)
        (etcdstart.utf8Keys_insert _ _ _ (by decide) etcdstart.utf8Keys_empty))) Haf
      Hbuq Hdbo) $$ [Hfr₂ Htok Hmb₂] as %s₂ %err₂ Hr₂
  · iframe; iframe #
  icases Hr₂ with (⟨%Herr, Htok⟩ | ⟨%Herr, %γa₂, Hup₂⟩)
  · cases err₂ with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  subst Herr
  wp_auto
  icases memberUpOn_tok _ _ _ _ _ _ _ $$ Hup₂ with ⟨Htok, -⟩
  wp_apply (wp_startMember N name₃ peerAddr₃ clientAddr₃
      (slice.mk peer₃ (W64 1) (W64 1)) pm lg
      (GMap.insert name₃ (slice.mk peer₃ (W64 1) (W64 1)) (GMap.insert name₂ (slice.mk peer₂ (W64 1) (W64 1))
        (GMap.insert name₁ (slice.mk peer₁ (W64 1) (W64 1)) ∅))) initURLs3 ps
      (LogEntry.toEntries boot 0) ctxs
      (dir3 id₁ id₂ id₃) id₃ { γ with reg := reg₃ } ρ₃ E₃ Φs γn Htb Hrb48 HrbN HwbN
      hvs hrule hboot hblen hγn1 hγn2 (dir3_ok id₁ id₂ id₃ ps ctxs boot Hbf) hd₃
      (dir3_dirsOk id₁ id₂ id₃ ps ctxs boot Hbf) ⟨rfl, rfl, ⟨_, _, _, rfl⟩, rfl⟩
      (etcdstart.utf8Keys_insert _ _ _ (by decide) (etcdstart.utf8Keys_insert _ _ _ (by decide)
        (etcdstart.utf8Keys_insert _ _ _ (by decide) etcdstart.utf8Keys_empty))) Haf
      Hbuq Hdbo) $$ [Hfr₃ Htok Hmb₃] as %s₃ %err₃ Hr₃
  · iframe; iframe #
  icases Hr₃ with (⟨%Herr, Htok⟩ | ⟨%Herr, %γa₃, Hup₃⟩)
  · cases err₃ with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  subst Herr
  wp_auto
  icases memberUpOn_tok _ _ _ _ _ _ _ $$ Hup₃ with ⟨Htok, -⟩
  ihave Hup₁ := Hup₁ $$ Htok
  -- `auth.Run(s, clientAddr, lg)` on member 1
  wp_apply (wp_Run s₁ lg clientAddr₁ ρ₁ E₁ γn id₁ γa (by unfold plainEndpoint clientAddr₁; decide)
      Htb HLv Hrb48 Hbuq Hrf Hms hAs hc0₁ hlog₁) $$ [Hac Hup₁ Hview] as %r %Hr
  · iframe; iframe #
  iapply HΦ; ipureintro; exact Hr

end proof

end etcd_auth3
end EtcdGrove
end Perennial
