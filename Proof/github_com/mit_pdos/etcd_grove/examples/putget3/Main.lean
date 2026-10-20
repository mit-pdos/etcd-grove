/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/putget3/Main.lean` (D21 stage M5,
2026-10-19). Lean-first (no Rocq counterpart).

The steps: the logger; the three peer URL slices and the initial cluster's map (read-only from
then on); the ghost state of the cluster and its members (`putget3_alloc`); `startMember` for each
member (`startMember.spec`), the thread token passed from one to the next out of the previous
member's `srvGoRes` (each error returns `Main`); then putget's steps on the first member:
`v3rpc.Server`, `Listen` at the client address, the ghost step `etcd_kv_started`, `go
gs.Serve(l)`, `clientv3.New`, `context.Background()`, the client's invariant at the bootstrap log,
`cli.Put`, `cli.Get` and the check.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.putget3.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.putget3.startMember
public import Spec.go_uber_org.zap.NewNop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Server
public import Spec.net.Listen
public import Spec.google_golang_org.grpc.Server__Serve
public import Spec.go_etcd_io.etcd.client.v3.New
public import Perennial.Spec.context.Background
public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV

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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.putget3.Assumptions]

omit package_sem in
/-- `client.grpcCfgOk_of_started` with the logger's premise inside (putget's). -/
theorem grpcCfgOk_of_started' [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    [go_etcd_io.etcd.server.v3.etcdserver.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (tos : List GoInterface) :
    ⌜cfg.Logger' ≠ null⌝ ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ srvServeFacts s E cfg ∗
        srvWatchBuilt s E ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.eofVar ∗ v3rpc.runsNoRequireLeader ∗
        cfg.TracerOptions' ↦*□ tos ⊢
      ∃ C : v3rpc.GrpcCfg GF, v3rpc.grpcCfgOk s C ∗
        ⌜C.A = v3rpc.srvKVAns s E ρ γr (W64 0) [] .none ∧ C.E = E⌝ := by
  iintro ⟨%hlg, H⟩
  iapply (client.grpcCfgOk_of_started s E ρ γr cfg tos hlg) $$ H

set_option maxHeartbeats 1000000 in
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_startMember : startMember.spec (GF := GF) (hG := hG))
    (wp_Server : v3rpc.Server.spec (GF := GF) (hG := hG))
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Serve : grpc.Server.Serve.spec (GF := GF) (hG := hG))
    (wp_New : clientv3.New.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS N id₁ id₂ id₃ bootLog Hbf HEof HCc Htb Hrb48 HrbN Hck Haf Hbuq Hms hAs
  wp_start as ⟨Ha₁, Ha₂, Ha₃, Hac, Htok, #Hprem⟩
  iunfold premises at Hprem
  icases Hprem with ⟨#Hb₁, #Hb₂, #Hb₃, #Hcom⟩
  ihave #Hcom' := Hcom
  iunfold commonPremises at Hcom'
  icases Hcom' with ⟨-, -, -, -, -, -, #Hnrl⟩
  -- `io.EOF` and `context`'s `closedchan`, from their packages' facts (the named Props)
  ihave #Heof : v3rpc.eofVar (GF := GF) $$ []
  · unfold EofFromIoInit at HEof
    iapply HEof
    iPkgInit
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · unfold ClosedchanFromContextInit at HCc
    iapply HCc
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
  -- the ghost state of the cluster and its members (`putget3_alloc`)
  imod (putget3_alloc id₁ id₂ id₃ bootLog Hbf (by omega)) with ⟨%γ, %bud, %ρ₁, %ρ₂, %ρ₃, %E₁, %E₂,
    %E₃, %Φs, %γn, %Hal, Hmb₁, Hsl₁, Hmb₂, Hsl₂, Hmb₃, Hsl₃, Hetcd⟩
  obtain ⟨hcfg, hdyn, hcc, hboot, htr, htx, hγn1, hγn2⟩ := Hal
  have hblen : bootLog.length ≤ 2 ^ 60 := by rw [Hbf.boot.1]; simp
  -- the three members
  wp_apply (wp_startMember N name₁ peerAddr₁ clientAddr₁ (slice.mk peer₁ (W64 1) (W64 1)) pm lg
      (slice.mk peer₁ (W64 1) (W64 1)) (slice.mk peer₂ (W64 1) (W64 1))
      (slice.mk peer₃ (W64 1) (W64 1)) [id₁, id₂, id₃] bootLog
      (dir3 id₁ id₂ id₃) id₁ γ bud ρ₁ E₁ Φs γn Htb Hrb48 HrbN hcfg hdyn hcc hboot htr htx hblen hγn1 hγn2
      (by simp [dir3]) Hlg Hck Haf Hbuq) $$ [Ha₁ Htok Hmb₁ Hsl₁] as %s₁ %err₁ Hr₁
  · iframe; iframe #
  icases Hr₁ with (⟨%Herr, Htok⟩ | ⟨%Herr, Hup₁⟩)
  · cases err₁ with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  iunfold memberUp at Hup₁
  icases Hup₁ with ⟨%E, %cfg, %γw, %HEc, #Hreq, #Hrd, Hgo, Hlg3, Hrslots, #Hwb, #Hsf, Hwpi, Hbemu,
    Hlts, Hlgs, Hrds, Hsts, Hbms⟩
  iunfold srvGoRes at Hgo
  icases Hgo with ⟨Hwgr, Htok⟩
  wp_apply (wp_startMember N name₂ peerAddr₂ clientAddr₂ (slice.mk peer₂ (W64 1) (W64 1)) pm lg
      (slice.mk peer₁ (W64 1) (W64 1)) (slice.mk peer₂ (W64 1) (W64 1))
      (slice.mk peer₃ (W64 1) (W64 1)) [id₁, id₂, id₃] bootLog
      (dir3 id₁ id₂ id₃) id₂ γ bud ρ₂ E₂ Φs γn Htb Hrb48 HrbN hcfg hdyn hcc hboot htr htx hblen hγn1 hγn2
      (by simp [dir3, (id_ne id₁ id₂ id₃ bootLog Hbf).1.symm]) Hlg Hck Haf Hbuq)
    $$ [Ha₂ Htok Hmb₂ Hsl₂] as %s₂ %err₂ Hr₂
  · iframe; iframe #
  icases Hr₂ with (⟨%Herr, Htok⟩ | ⟨%Herr, Hup₂⟩)
  · cases err₂ with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  iunfold memberUp at Hup₂
  icases Hup₂ with ⟨%E', %cfg', %γw', -, -, -, Hgo', -⟩
  iunfold srvGoRes at Hgo'
  icases Hgo' with ⟨-, Htok⟩
  wp_apply (wp_startMember N name₃ peerAddr₃ clientAddr₃ (slice.mk peer₃ (W64 1) (W64 1)) pm lg
      (slice.mk peer₁ (W64 1) (W64 1)) (slice.mk peer₂ (W64 1) (W64 1))
      (slice.mk peer₃ (W64 1) (W64 1)) [id₁, id₂, id₃] bootLog
      (dir3 id₁ id₂ id₃) id₃ γ bud ρ₃ E₃ Φs γn Htb Hrb48 HrbN hcfg hdyn hcc hboot htr htx hblen hγn1 hγn2
      (by simp [dir3, (id_ne id₁ id₂ id₃ bootLog Hbf).2.1.symm,
        (id_ne id₁ id₂ id₃ bootLog Hbf).2.2.symm]) Hlg Hck Haf Hbuq)
    $$ [Ha₃ Htok Hmb₃ Hsl₃] as %s₃ %err₃ Hr₃
  · iframe; iframe #
  icases Hr₃ with (⟨%Herr, Htok⟩ | ⟨%Herr, Hup₃⟩)
  · cases err₃ with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  iunfold memberUp at Hup₃
  icases Hup₃ with ⟨%E'', %cfg'', %γw'', -, -, -, Hgo'', -⟩
  iunfold srvGoRes at Hgo''
  icases Hgo'' with ⟨-, Htok⟩
  ihave Hgo : srvGoRes s₁ $$ [Hwgr Htok]
  · iunfold srvGoRes; iframe
  obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HEc
  iclear Hb₁ Hb₂ Hb₃ Hcom Hq₁ Hq₂ Hq₃ Hu₁ Hu₂ Hu₃ Hcm Hpeer₁ Hpeer₂ Hpeer₃ Hpm
  -- `v3rpc.Server(s, nil, nil)`: its configuration from `NewServer`'s and `Start`'s
  ihave ⟨%C, #Hgc, %HC⟩ : ∃ C : v3rpc.GrpcCfg GF, v3rpc.grpcCfgOk s₁ C ∗
      ⌜C.A = v3rpc.srvKVAns s₁ E { ρ₁ with wait := γw } ρ₁.rd (W64 0) [] .none ∧ C.E = E⌝ $$ []
  · iapply (grpcCfgOk_of_started' s₁ E { ρ₁ with wait := γw } ρ₁.rd cfg [])
    iframe #
    isplitr
    · ipureintro; rw [HElg]; exact Hlg
    rw [HEtr]
    iapply ownSlice_nil
  wp_apply (wp_Server Hms s₁ C _ slice.nil [] Hbuq) $$ [Hlg3 Hbemu Hgo Hwpi]
    as %gs ⟨%q, %p, %pw, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %cid, %mid, %R, %d',
      Hgsn, %Hregs, #Hq, #Hkvs, #Hws, %HR, #Hil, #Him, #Hiu, #Hims, #His, Hlg4, Hbemu2, Hgo2,
      Hwpi2⟩
  · iframe; iframe #
    isplitr
    · ipureintro; rw [HEw]; simp
    isplitr
    · iapply ownSlice_nil
    ipureintro; intro v hv; cases hv
  -- `net.Listen("tcp", clientAddr)`
  wp_apply (wp_Listen go!"tcp" clientAddr₁) $$ [Hac] as %lis %lerr Hlis
  · iframe; ipureintro; rfl
  icases Hlis with (⟨%Hlerr, Hlis⟩ | %Hlerr)
  rotate_left
  · cases lerr with
    | nil => exact absurd rfl Hlerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hlerr
  wp_auto
  -- the ghost step between `Listen` and `go gs.Serve(l)`: etcd's KV specs at the address
  haveI := Hms
  icases replicate_take2 _ _ (by omega) $$ Hlts with ⟨-, -, Hlts⟩
  icases replicate_take2 _ _ (by omega) $$ Hrds with ⟨-, -, Hrds⟩
  ihave Hslots := client.etcdGrpcSlots_of_started s₁ E ρ₁.rd 1 (64 - 2) 64
      (Int.toNat sync.rwmutex.actualMaxReaders) 64 (by omega) (by omega)
      (by have := sync.actualMaxReaders_ge_2; omega) (by omega)
      $$ [Hlts Hlgs Hrds Hsts Hrslots Hbms]
  · iframe
  ihave #Hkva := client.kvServerAt_of_is p s₁ C.A cid mid C.n $$ Hkvs
  rw [HC.1]
  imod (client.etcd_kv_started clientAddr₁ gs q p s₁ lis E { ρ₁ with wait := γw } ρ₁.rd
      cid mid C.n il im iu ims is svcs regs sregs 1 Hregs.1)
    $$ [Hgsn Hlis Hslots] with ⟨Hserv, -, #HPut, #HRange, -, -⟩
  · iframe Hgsn Hlis Hslots
    iframe Pv3 Psrv Hreq Hrd Hkva Hq Hil Him Hiu
    iintro !>
    imodintro
    iunfold idCred
    ipureintro; exact Hrb48
  -- `go gs.Serve(l)`
  wp_apply wp_fork $$ [Hserv]
  · wp_apply (wp_Serve gs lis) $$ [$Hserv] as %serr -
    ipureintro; exact isPanic_intoVal serr
  -- `clientv3.New(Config{Endpoints: {clientAddr}, Logger: lg})`
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %eps ⟨Heps, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Heps with #Heps
  wp_apply (wp_New _ clientAddr₁
      ⟨R, clientAddr₁, [], null, null, [], null⟩) $$ [] as %cl %cerr Hcl
  · iframe #
    iunfold clientCfgOk
    simp only
    iframe #
    isplitr
    · isplitr
      · iapply ownSlice_nil
      ipureintro
      refine ⟨?_, ?_⟩
      · unfold plainEndpoint clientAddr₁; decide
      · simp [Hlg]
    ipureintro; exact Htb
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
  -- `ctx := context.Background()`
  wp_apply wp_Background
  imod client.background_ctx (GF := GF) hAs with ⟨%cd, #Hctx, #Hce⟩
  (try wp_auto)
  -- the client's invariant, the floor, no options
  imod (client.putGetInv_alloc_log ρ₁.rd (kvModel ρ₁.rd.kv (bootEntries bootLog)) go!"k" go!"v" ⊤)
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
      context.backgroundCtxVal cd go!"k" go!"v" slice.nil []) as %presp %perr Hput
  · iframe #
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
  -- `cli.Get(ctx, "k")`
  imod monoNatLbOwn_0 (GF := GF) ρ₁.rd.committed with #Hc0
  wp_apply (client.client_Get_own cl clientAddr₁ _ E ρ₁.rd γf (W64 0) cid mid
      context.backgroundCtxVal cd go!"k" go!"v" slice.nil []) as %gresp %gerr Hget
  · iframe #
    iunfold committedAtLeast
    iExactEq Hc0; rfl
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
