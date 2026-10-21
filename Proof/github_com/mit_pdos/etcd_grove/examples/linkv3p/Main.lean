/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/linkv3p/Main.lean` (the partition plan's
S3b, 2026-10-20). Lean-first (no Rocq counterpart).

linkv3's `Main` (`Proof/.../linkv3/Main.lean`) at linkv3p's configuration, with every member
served: the logger; the three peer URL slices and the initial cluster's map; the ghost state of
the cluster and its members (`cluster3_alloc`, the ids in the names' order, the client's `etcdKV`
at the first member's names); `startMember` for each member, the thread token passed along
(`memberServed`'s `srvGoRes`); the servers' slice; `startBridge` for each member's client address
(the thread token passed along; the bridge owned, and its address serving the member's,
`forwards`) and the bridges' slice (2026-10-21, `notes/client-cut-plan.md`); `newClient` to each
bridge (at a watch environment the clients never use); the partitioner forked on the schedule
(every member's `srvNetMember`, every bridge owned and not blackholed); the instance's invariant at the cluster's start store (linkvtxn's
`linkvInv_alloc_boot`, at the first member's names, the others' by `linkvInv_congr`), so each
client has linkvtxn's `Apply.spec`'s premises (`clientOk`: at its bridge's address, the member's
registrations through `isGrpcRpc_forwards`); `Check(clis, clients, ops, 0)`, which returns `Ok`
(`timeout = 0`), so the panic on `Illegal` is not taken. Every step's error ends `Main` with
`Unknown`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.startMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.newClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.partitioner
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.startBridge
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.Check
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Boot
public import Spec.go_uber_org.zap.NewNop

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver
open putget3 (httpURL ccOk commonPremises memberBoot id_ne)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

/-- **A watch environment for a client at `addr`** that never watches (`isNewClient`'s parameter,
which `clientv3.New` takes as the caller's choice; `isNewClient_watcher` would need its facts): the
member's apply environment and null for the rest. -/
def noWatch (E : apply.AEnv GF) (addr : GoString) : EtcdGrove.client.WEnv GF :=
  ⟨⟨null, E, null, ⟨E.γ, 0, 0, 0, 0⟩, W64 0, W64 0, null, W64 0⟩, addr, [], null, null, [], null⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_startMember : startMember.spec (GF := GF) (hG := hG))
    (wp_startBridge : startBridge.spec (GF := GF) (hG := hG))
    (wp_newClient : newClient.spec (GF := GF) (hG := hG))
    (wp_partitioner : partitioner.spec (GF := GF) (hG := hG))
    (wp_Check : Check.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS ESL ESE N id₁ id₂ id₃ bootLog clients ops sched steps Hbf Htb1 Hrb48 HrbN Hck Haf Hbuq
    Hnoc Hms hAs H0 H31 Hops Hmul
  have Htb : threadBound GF ≤ 2 ^ 31 := by omega
  wp_start as ⟨Ha₁, Ha₂, Ha₃, Hc₁, Hc₂, Hc₃, Hba₁, Hba₂, Hba₃, #Hsched, Htok, #Hprem⟩
  iunfold premises at Hprem
  icases Hprem with ⟨#Hb₁, #Hb₂, #Hb₃, #Hcom⟩
  -- `context`'s `closedchan`, from its package's facts
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  -- the imports' package facts
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
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
  -- the ghost state of the cluster and its members (`cluster3_alloc`, in `bootstrap`'s order,
  -- which is the names'; the client's `etcdKV` at `linkv3p-1`'s names)
  imod (cluster3_alloc id₁ id₂ id₃ bootLog Hbf (dir3 id₁ id₂ id₃) (by omega)) with ⟨%γ, %bud, %ρ₁,
    %ρ₂, %ρ₃, %E₁, %E₂, %E₃, %Φs, %γn, %Hal, Hmb₁, Hsl₁, Hmb₂, Hsl₂, Hmb₃, Hsl₃, Hetcd⟩
  obtain ⟨hcfg, hdyn, hcc, hboot, htr, hγn1, hγn2, hlog₁, hwl₁, hst₂, hwl₂, hst₃, hwl₃⟩ := Hal
  obtain ⟨hn12, hn13, hn23⟩ := id_ne id₁ id₂ id₃ bootLog Hbf
  have hblen : bootLog.length ≤ 2 ^ 60 := by rw [Hbf.boot.1]; simp
  -- the three members, each served
  wp_apply (wp_startMember N name₁ peerAddr₁ clientAddr₁ (slice.mk peer₁ (W64 1) (W64 1)) pm lg
      (slice.mk peer₁ (W64 1) (W64 1)) (slice.mk peer₂ (W64 1) (W64 1))
      (slice.mk peer₃ (W64 1) (W64 1)) (ids id₁ id₂ id₃) bootLog
      (dir3 id₁ id₂ id₃) id₁ γ bud ρ₁ E₁ Φs γn Htb Hrb48 HrbN hcfg hdyn hcc hboot htr hblen hγn1 hγn2
      (by simp [dir3]) Hlg Hck Haf Hbuq Hnoc Hms) $$ [Ha₁ Hc₁ Htok Hmb₁ Hsl₁] as %s₁ %err₁ Hr₁
  · iframe; iframe #
  icases Hr₁ with (⟨%Herr, Htok⟩ | ⟨%Herr, Hup₁⟩)
  · cases err₁ with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  iunfold memberServed at Hup₁
  icases Hup₁ with ⟨%E₁', %γw₁, %cid₁, %mid₁, %HE₁, #Hreq₁, #Hrd₁, Hgo₁,
    #Hnm₁, #HPut₁, #HRange₁, #HDel₁, #HTxn₁⟩
  iunfold srvGoRes at Hgo₁
  icases Hgo₁ with ⟨-, Htok⟩
  wp_apply (wp_startMember N name₂ peerAddr₂ clientAddr₂ (slice.mk peer₂ (W64 1) (W64 1)) pm lg
      (slice.mk peer₁ (W64 1) (W64 1)) (slice.mk peer₂ (W64 1) (W64 1))
      (slice.mk peer₃ (W64 1) (W64 1)) (ids id₁ id₂ id₃) bootLog
      (dir3 id₁ id₂ id₃) id₂ γ bud ρ₂ E₂ Φs γn Htb Hrb48 HrbN hcfg hdyn hcc hboot htr hblen hγn1 hγn2
      (by simp [dir3, Ne.symm hn12]) Hlg Hck Haf Hbuq Hnoc Hms)
    $$ [Ha₂ Hc₂ Htok Hmb₂ Hsl₂] as %s₂ %err₂ Hr₂
  · iframe; iframe #
  icases Hr₂ with (⟨%Herr, Htok⟩ | ⟨%Herr, Hup₂⟩)
  · cases err₂ with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  iunfold memberServed at Hup₂
  icases Hup₂ with ⟨%E₂', %γw₂, %cid₂, %mid₂, %HE₂, #Hreq₂, #Hrd₂, Hgo₂,
    #Hnm₂, #HPut₂, #HRange₂, #HDel₂, #HTxn₂⟩
  iunfold srvGoRes at Hgo₂
  icases Hgo₂ with ⟨-, Htok⟩
  wp_apply (wp_startMember N name₃ peerAddr₃ clientAddr₃ (slice.mk peer₃ (W64 1) (W64 1)) pm lg
      (slice.mk peer₁ (W64 1) (W64 1)) (slice.mk peer₂ (W64 1) (W64 1))
      (slice.mk peer₃ (W64 1) (W64 1)) (ids id₁ id₂ id₃) bootLog
      (dir3 id₁ id₂ id₃) id₃ γ bud ρ₃ E₃ Φs γn Htb Hrb48 HrbN hcfg hdyn hcc hboot htr hblen hγn1 hγn2
      (by simp [dir3, Ne.symm hn13, Ne.symm hn23]) Hlg Hck Haf Hbuq Hnoc Hms)
    $$ [Ha₃ Hc₃ Htok Hmb₃ Hsl₃] as %s₃ %err₃ Hr₃
  · iframe; iframe #
  icases Hr₃ with (⟨%Herr, Htok⟩ | ⟨%Herr, Hup₃⟩)
  · cases err₃ with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  iunfold memberServed at Hup₃
  icases Hup₃ with ⟨%E₃', %γw₃, %cid₃, %mid₃, %HE₃, #Hreq₃, #Hrd₃, Hgo₃,
    #Hnm₃, #HPut₃, #HRange₃, #HDel₃, #HTxn₃⟩
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
  wp_apply (wp_startBridge bridgeAddr₁ clientAddr₁ Htb1) $$ [Hba₁ Htok] as %br₁ %berr₁ ⟨Htok, Hbr₁⟩
  · iframe
  icases Hbr₁ with (⟨%Hberr, Hob₁, #Hfw₁⟩ | %Hberr)
  rotate_left
  · cases berr₁ with
    | nil => exact absurd rfl Hberr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hberr
  wp_auto
  wp_apply (wp_startBridge bridgeAddr₂ clientAddr₂ Htb1) $$ [Hba₂ Htok] as %br₂ %berr₂ ⟨Htok, Hbr₂⟩
  · iframe
  icases Hbr₂ with (⟨%Hberr, Hob₂, #Hfw₂⟩ | %Hberr)
  rotate_left
  · cases berr₂ with
    | nil => exact absurd rfl Hberr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hberr
  wp_auto
  wp_apply (wp_startBridge bridgeAddr₃ clientAddr₃ Htb1) $$ [Hba₃ Htok] as %br₃ %berr₃ ⟨Htok, Hbr₃⟩
  · iframe
  icases Hbr₃ with (⟨%Hberr, Hob₃, #Hfw₃⟩ | %Hberr)
  rotate_left
  · cases berr₃ with
    | nil => exact absurd rfl Hberr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hberr
  wp_auto
  -- `brs := []bridge.Bridge{br1, br2, br3}`
  wp_apply wp_slice_literal (V := GoInterface) (l := [br₁, br₂, br₃])
  try (isplitr; (ipureintro; rfl))
  iintro %brsp ⟨Hbrs, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Hbrs with #Hbrs
  -- the three clients, each to its bridge
  wp_apply (wp_newClient bridgeAddr₁ lg (noWatch E₁' bridgeAddr₁) Htb Hlg
      (by unfold plainEndpoint bridgeAddr₁; decide)) $$ [] as %cl₁ %cerr₁ Hcl₁
  icases Hcl₁ with (Hok₁ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr₁ with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  icases Hok₁ with ⟨%Hcerr, #Hnc₁, #Hone₁⟩
  subst Hcerr
  wp_auto
  wp_apply (wp_newClient bridgeAddr₂ lg (noWatch E₂' bridgeAddr₂) Htb Hlg
      (by unfold plainEndpoint bridgeAddr₂; decide)) $$ [] as %cl₂ %cerr₂ Hcl₂
  icases Hcl₂ with (Hok₂ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr₂ with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  icases Hok₂ with ⟨%Hcerr, #Hnc₂, #Hone₂⟩
  subst Hcerr
  wp_auto
  wp_apply (wp_newClient bridgeAddr₃ lg (noWatch E₃' bridgeAddr₃) Htb Hlg
      (by unfold plainEndpoint bridgeAddr₃; decide)) $$ [] as %cl₃ %cerr₃ Hcl₃
  icases Hcl₃ with (Hok₃ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr₃ with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  icases Hok₃ with ⟨%Hcerr, #Hnc₃, #Hone₃⟩
  subst Hcerr
  wp_auto
  -- `clis := []*clientv3.Client{cli1, cli2, cli3}`
  wp_apply wp_slice_literal (V := Loc) (l := [cl₁, cl₂, cl₃])
  try (isplitr; (ipureintro; rfl))
  iintro %clisp ⟨Hclis, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Hclis with #Hclis
  -- `go partitioner(srvs, brs, sched)`: every member's place in the network
  ihave #Hmem : ([∗list] s ∈ [s₁, s₂, s₃], ∃ id : w64, srvNetMember γn s id) $$ []
  · iapply (BigSepL.bigSepL_cons
      (Φ := fun _ s => iprop(∃ id : w64, srvNetMember (GF := GF) γn s id))).2
    isplitr
    · iexists id₁; iexact Hnm₁
    iapply (BigSepL.bigSepL_cons
      (Φ := fun _ s => iprop(∃ id : w64, srvNetMember (GF := GF) γn s id))).2
    isplitr
    · iexists id₂; iexact Hnm₂
    iapply (BigSepL.bigSepL_cons
      (Φ := fun _ s => iprop(∃ id : w64, srvNetMember (GF := GF) γn s id))).2
    isplitr
    · iexists id₃; iexact Hnm₃
    iapply BigSepL.bigSepL_nil.2
    itrivial
  -- every bridge owned, not blackholed
  ihave Hobs : ([∗list] br ∈ [br₁, br₂, br₃], ∃ addr : GoString, bridge.ownBridge br addr false)
    $$ [Hob₁ Hob₂ Hob₃]
  · iapply (BigSepL.bigSepL_cons
      (Φ := fun _ br => iprop(∃ addr : GoString, bridge.ownBridge (GF := GF) br addr false))).2
    isplitl [Hob₁]
    · iexists clientAddr₁; iexact Hob₁
    iapply (BigSepL.bigSepL_cons
      (Φ := fun _ br => iprop(∃ addr : GoString, bridge.ownBridge (GF := GF) br addr false))).2
    isplitl [Hob₂]
    · iexists clientAddr₂; iexact Hob₂
    iapply (BigSepL.bigSepL_cons
      (Φ := fun _ br => iprop(∃ addr : GoString, bridge.ownBridge (GF := GF) br addr false))).2
    isplitl [Hob₃]
    · iexists clientAddr₃; iexact Hob₃
    iapply BigSepL.bigSepL_nil.2
    itrivial
  wp_apply wp_fork $$ [Hobs]
  · wp_apply (wp_partitioner γn _ _ sched [s₁, s₂, s₃] [br₁, br₂, br₃] steps) $$ [Hobs]
    all_goals (try (iframe #))
    all_goals (try iframe)
    ipureintro; exact isPanic_intoVal ()
  (try wp_auto)
  -- the instance's invariant, at the cluster's start store (empty), for every member's names
  imod (linkvtxn.linkvInv_alloc_boot ρ₁.rd.kv hlog₁ (ccOk (ids id₁ id₂ id₃)) (ids id₁ id₂ id₃)
      bootLog Hbf.boot (by rw [hwl₁]; intro; trivial) ⊤) $$ Hetcd
    with ⟨%γl, #Hlinv, Hst⟩
  ihave #Hlinv₂ : linkvtxn.linkvInv γl ρ₂.rd.kv $$ []
  · rw [linkvInv_congr γl ρ₂.rd.kv ρ₁.rd.kv hst₂ hwl₂]; iexact Hlinv
  ihave #Hlinv₃ : linkvtxn.linkvInv γl ρ₃.rd.kv $$ []
  · rw [linkvInv_congr γl ρ₃.rd.kv ρ₁.rd.kv hst₃ hwl₃]; iexact Hlinv
  ihave #Hok : ([∗list] cl ∈ [cl₁, cl₂, cl₃], clientOk γl cl) $$ []
  · iapply (BigSepL.bigSepL_cons (Φ := fun _ cl => clientOk (GF := GF) γl cl)).2
    isplitr
    · iunfold clientOk
      iexists bridgeAddr₁, noWatch E₁' bridgeAddr₁, E₁', ρ₁.rd, cid₁, mid₁
      iframe #
      isplitr
      · iapply isGrpcRpc_forwards $$ [Hfw₁ HPut₁]; iframe #
      isplitr
      · iapply isGrpcRpc_forwards $$ [Hfw₁ HRange₁]; iframe #
      isplitr
      · iapply isGrpcRpc_forwards $$ [Hfw₁ HDel₁]; iframe #
      iapply isGrpcRpc_forwards $$ [Hfw₁ HTxn₁]; iframe #
    iapply (BigSepL.bigSepL_cons (Φ := fun _ cl => clientOk (GF := GF) γl cl)).2
    isplitr
    · iunfold clientOk
      iexists bridgeAddr₂, noWatch E₂' bridgeAddr₂, E₂', ρ₂.rd, cid₂, mid₂
      iframe #
      isplitr
      · iapply isGrpcRpc_forwards $$ [Hfw₂ HPut₂]; iframe #
      isplitr
      · iapply isGrpcRpc_forwards $$ [Hfw₂ HRange₂]; iframe #
      isplitr
      · iapply isGrpcRpc_forwards $$ [Hfw₂ HDel₂]; iframe #
      iapply isGrpcRpc_forwards $$ [Hfw₂ HTxn₂]; iframe #
    iapply (BigSepL.bigSepL_cons (Φ := fun _ cl => clientOk (GF := GF) γl cl)).2
    isplitr
    · iunfold clientOk
      iexists bridgeAddr₃, noWatch E₃' bridgeAddr₃, E₃', ρ₃.rd, cid₃, mid₃
      iframe #
      isplitr
      · iapply isGrpcRpc_forwards $$ [Hfw₃ HPut₃]; iframe #
      isplitr
      · iapply isGrpcRpc_forwards $$ [Hfw₃ HRange₃]; iframe #
      isplitr
      · iapply isGrpcRpc_forwards $$ [Hfw₃ HDel₃]; iframe #
      iapply isGrpcRpc_forwards $$ [Hfw₃ HTxn₃]; iframe #
    iapply BigSepL.bigSepL_nil.2
    itrivial
  -- `Check(clis, clients, ops, 0)`
  wp_apply (wp_Check γl _ [cl₁, cl₂, cl₃] clients ops (W64 0) hAs (by omega) (by simp) H0 H31 Hops
      Hmul) $$ [Hst] as %r %Hr
  · iframe; iframe #
  obtain ⟨-, Hok⟩ := Hr
  have Hok : r = go!"Ok" := Hok (by decide)
  subst Hok
  wp_auto
  iapply HΦ; ipureintro; left; rfl

end proof

end linkv3p
end EtcdGrove
end Perennial
