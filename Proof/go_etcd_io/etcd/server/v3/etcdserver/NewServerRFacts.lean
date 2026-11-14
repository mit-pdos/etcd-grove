/-
**The restart construction's sub-facts** (restart S6 B2, 2026-11-14): the lemmas `NewServer.wp_proofR`
(`NewServerR.lean`) uses that no other proof provides yet, each stated here so that the main proof
stays a copy of `NewServer.wp_proofG`'s with the boot steps replaced. Lean-first.

STATUS: being written; the lemmas marked `sorry` are open (the handoff's list,
`notes/restart-s56-handoff.md`, "B2 proof").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuiltRestart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ImageLeases
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthSrv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The restarted names' compaction revision of a log is the stopped one's. -/
theorem restartNames_crevOf {ρ ρ' : ReqNames} (h : restartNames ρ ρ') (A : List EntryModel) :
    crevOf ρ'.rd.kv A = crevOf ρ.rd.kv A := by
  obtain ⟨-, h2, h3, -⟩ := h.2.1
  unfold crevOf; rw [h2, h3]

/-- The leased rest image reads only the KV names' start values (`c0`, `ch0`): the restarted names'
is the stopped one's. -/
theorem restartNames_bkRestAtL {ρ ρ' : ReqNames} (h : restartNames ρ ρ') (b : List EntryM)
    (L : List EntryModel) (D : backend.Data) :
    bkRestAtL ρ'.rd.kv b L D ↔ bkRestAtL ρ.rd.kv b L D := by
  obtain ⟨-, h2, h3, -⟩ := h.2.1
  unfold bkRestAtL kvLeases; rw [h2, h3]

/-- (The restarted lessor's requested TTLs) **`tableReq` of a table is at most the records' TTLs**,
for records whose ids are the table's (`imageLeasesAt_recs`'s facts): `NewLessor.spec`'s premise at
`reqOf := tableReq T`. -/
theorem tableReq_le_recs (T : LeaseTable) (recs : List (w64 × w64 × w64)) (hn : T.ids.Nodup)
    (hperm : (recs.map (·.1)).Perm T.ids)
    (hge : ∀ x ∈ recs, ∀ p ∈ T, p.1 = x.1 → sint.Z p.2 ≤ sint.Z x.2.1) :
    ∀ x ∈ recs, sint.Z (tableReq T x.1) ≤ sint.Z x.2.1 := by
  intro x hx
  have hm : x.1 ∈ T.ids := hperm.subset (List.mem_map.2 ⟨x, hx, rfl⟩)
  obtain ⟨p, hp, hp1⟩ := List.mem_map.1 hm
  rw [← hp1, tableReq_of_mem hn hp]
  exact hge x hx p hp hp1

/-- (The restarted lessor's guard) **A cluster that grants no lease has an empty applied table**:
the image's lease bucket holds no record unless `lg`. OPEN (from the KV invariant: with
`lg = false` no committed `LeaseGrant` takes effect). -/
theorem restart_noGrant (γr : ReadNames) (A : List EntryModel) (hpre : γr.raft.pre = []) :
    ⊢ kvInv (GF := GF) γr.raft γr.kv -∗ srvRaftLogInv γr.raft -∗ srvRLogLb γr.raft A ={⊤}=∗
      ⌜γr.kv.lg = false → (appliedTable γr A).ids = []⌝ := by
  sorry

/-- (Probe P5; the restart contract's clause (G)) **The members' peer URLs at a committed log are the
boot log's**: no committed conf change adds a member (every `AddNode` names a present id) and the
attribute updates keep peer URLs (`withAttrs`). OPEN: the phase-2 invariant of `RestConf.lean`
(the `members` bucket exactly the encodings of `r.mem`, peer URLs `memBoot`'s). -/
theorem restart_peerURLs (γ : ServerRaftNames) (γk : KVNames) (A : List EntryModel)
    (hpre : γ.pre = []) :
    ⊢ kvInv (GF := GF) γ γk -∗ srvRaftLogInv γ -∗ srvRLogLb γ A ={⊤}=∗
      ⌜∀ f, ((restModel (W64 0) γ.raft.boot A).mem.lookup f).map apply.MemberM.peerURLs =
        ((memBoot γ.raft.boot).lookup f).map apply.MemberM.peerURLs⌝ := by
  sorry

open srvApi mvcc.api in
/-- (The restart's store invariant; `srvApi.bootStore_holds`' restart form) **The store invariant at
the image's state**: the fresh store-state names moved to the image's history `kvModel A` and
compaction revision `c` (the history extends the boot's `[[], []]`), its witness the committed `A`,
its permit `c`'s, its receipt `New`'s. -/
theorem restartStore_holds (Hp : mvcc.api.persistent.law (GF := GF)) (kv : GoInterface)
    (γ : MvccName) (γr : ReadNames) (γs : KVSNames) (A : List EntryModel) (c : Int)
    (h0 : ([[], []] : mvcc.Log) <+: kvModel γr.kv A)
    (hk : mvcc.LogPutsLe etcdKeyMax (kvModel γr.kv A)) (hc : γr.kv.cmp = false → c = -1) :
    isMvcc (GF := GF) kv γ ∗ mvccState γ (stAt (kvModel γr.kv A) c) ∗ newServerStoreFreshA γs ∗
      srvRLogLb γr.raft A ∗ (⌜c = -1⌝ ∨ kvCmpPermit γr.kv c) ∗ ⧖ (mvcc.logCh (kvModel γr.kv A))
      ={⊤}=∗ kvStoreInv kv γ γr false γs ∗ wSt γs (kvModel γr.kv A) c ∗ crOwn γs c := by
  haveI := Hp.1 kv γ
  rw [kvStoreInv_eq]
  iintro ⟨#Hm, Hs, Hf, #Hlb, #Hcp, #Hr⟩
  iunfold newServerStoreFreshA at Hf
  icases Hf with ⟨Hst, Hcr, Hsl, Hnl⟩
  imod (ghostVar_update (kvModel γr.kv A, (none : Option (List mvcc.Change))) γs.st _) $$ Hst with Hst
  imod (ghostVar_update c γs.cr _) $$ Hcr with Hcr
  imod (monoListAuthOwn_update (kvModel γr.kv A) h0) $$ Hsl with ⟨Hsl, -⟩
  imod (monoListAuthOwn_update (kvModel γr.kv A) h0) $$ Hnl with ⟨Hnl, -⟩
  ihave ⟨Hst, Hw1⟩ := (ghostVar_split_half γs.st 1 _).1 $$ Hst
  ihave ⟨Hcr, Hq⟩ := (ghostVar_split_half γs.cr 1 _).1 $$ Hcr
  ihave ⟨Hw2, Hc⟩ := (ghostVar_split_half γs.cr (1 : Qp).half _).1 $$ Hq
  ihave #Hnx : kvNx γr false (kvModel γr.kv A) $$ []
  · iunfold kvNx
    iexists A
    iframe Hlb
    ipureintro; rw [kvModelM_false]; exact ⟨rfl, hk⟩
  imod inv_alloc kvsN ⊤ iprop(∃ σ : MvccState, mvccState γ σ ∗
    ghostVar γs.st (1 : Qp).half (σ.log, σ.pending) ∗ ghostVar γs.cr (1 : Qp).half σ.crev ∗
    monoListAuthOwn γs.slog 1 σ.log ∗ monoListAuthOwn γs.nlog 1 σ.notifiedLog ∗
    kvNx γr false σ.log ∗ kvNx γr false σ.notifiedLog ∗ ⧖ (mvcc.logCh σ.notifiedLog) ∗ crevOk γr σ.crev)
    $$ [Hs Hst Hcr Hsl Hnl] with #Hinv
  · inext
    iexists (stAt (kvModel γr.kv A) c)
    simp only [show (stAt (kvModel γr.kv A) c).log = kvModel γr.kv A from rfl,
      show (stAt (kvModel γr.kv A) c).crev = c from rfl,
      show (stAt (kvModel γr.kv A) c).pending = none from rfl,
      show (stAt (kvModel γr.kv A) c).notifiedLog = kvModel γr.kv A from rfl]
    iframe Hs Hst Hcr Hsl Hnl Hnx Hr
    iunfold crevOk
    iframe Hcp
    ipureintro; exact hc
  imodintro
  iunfold kvStoreInvG
  iunfold wSt
  iunfold crOwn
  iframe Hm Hinv Hw1 Hw2 Hc

open backend go_etcd_io.etcd.server.v3.storage in
/-- (Probe P7) **The image's auth buckets are a first start's leftovers**: `auth` at `authBoot`,
`authUsers` and `authRoles` empty, at every committed log (`restModel_keep`). -/
theorem imageRestAt_auth (γk : KVNames) (bootLog : List EntryM) (i : w64)
    (L : List EntryModel) (D : Data) (h : imageRestAt γk bootLog i L D) :
    (D.lookup go!"auth").getD ∅ = authBoot ∧ (D.lookup go!"authUsers").getD ∅ = ∅ ∧
      (D.lookup go!"authRoles").getD ∅ = ∅ := by
  obtain ⟨-, -, f, -, hb⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;>
  (rw [hb _ (by decide), restLeasesWith_lookup_other _ _ _ _ (by decide),
    restModel_keep _ _ _ _ (by decide) (by decide) (by decide)]
   simp [restBoot, restBootBk])

open backend go_etcd_io.etcd.server.v3.storage in
/-- (Probe P7) **The image's alarm bucket is empty**, at every committed log. -/
theorem imageRestAt_alarm (γk : KVNames) (bootLog : List EntryM) (i : w64)
    (L : List EntryModel) (D : Data) (h : imageRestAt γk bootLog i L D) :
    (D.lookup go!"alarm").getD ∅ = ∅ := by
  obtain ⟨-, -, f, -, hb⟩ := h
  rw [hb go!"alarm" (by decide), restLeasesWith_lookup_other _ _ _ _ (by decide),
    restModel_keep _ _ _ _ (by decide) (by decide) (by decide)]
  simp [restBoot, restBootBk]

end lemmas

section kit
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]
variable [auth_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]
open go_etcd_io.etcd.server.v3

/-- (Restart S6 B2) **`authStoreKit` with the auth bucket a restart finds**: as `authStoreKit` (its body
copied), the auth bucket empty (a first start) or at `authBoot` (a restart: what a first start
leaves), as `NewAuthStore`'s axiom takes it since HS1 (restart S5). Only the mode `off`'s is built
(`authStoreKitR_off`). Follow-up (proof cleanup): widen `authStoreKit` itself and drop this copy. -/
def authStoreKitR (M : auth.AuthMode) (tp : GoInterface) : IProp GF :=
  iprop(∃ K : IProp GF, K ∗ □ ∀ (lg : Loc) (ab : GoInterface) (abl : Loc)
      (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp) (r : GMap GoString backend.BktData) (cost : w64),
    {{ K ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ zapLoggerOk lg ∗
        ⌜tp ≠ GoInterface.nil⌝ ∗ ⌜authRecordsFit⌝ ∗ ⌜ab = authBkIface abl⌝ ∗
        structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"be" abl ↦□
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            #d.be : GoInterface) ∗
        structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"lg" abl ↦□ lg ∗
        backend.isBackend d.γB d.P W Pk d.be ∗ backend.bOpen d.γB qo ∗
        backend.plHook d.γB func.nil ∗ ownToks d.γB.wb 2 ∗ backend.rbOwnIn d.γB authBkts r ∗
        authKitIn M d ∗
        ⌜((r.lookup go!"auth").getD ∅ = ∅ ∨ (r.lookup go!"auth").getD ∅ = authBoot) ∧
          (r.lookup go!"authUsers").getD ∅ = ∅ ∧ (r.lookup go!"authRoles").getD ∅ = ∅⌝ ∗
        -- (2026-11-02, the backend-auth-split stage) the auth buckets in the backend's table, as
        -- `NewAuthStore`'s axiom now takes them
        ⌜d.P.has mvcc.authBI ∧ d.P.has mvcc.authUsersBI ∧ d.P.has mvcc.authRolesBI⌝ }}
      (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.NewAuthStore)) (Val #lg))
        (Val #ab)) (Val #tp)) (Val #cost))
    {{ (st : GoInterface), RET #st; backend.bOpen d.γB qo ∗ backend.plHook d.γB func.nil ∗
        authKitOut M d r ∗
        ∃ (RD : IProp GF) (stl : Loc), ⌜st = auth.authIface stl⌝ ∗ authBeOn stl d.be ∗
        authRdSupply RD ∗
        -- (auth-schema-fix S1 option A) the request side once the token provider is ready (`start`
        -- fires `auth.tpReady`)
        □ (auth.tpReady M -∗ isReqAuth st RD) ∗
        authApplyOkM M stl RD ∗ authStoreLatestM M st RD stl ∗ authStoreLbM M st RD ∗
        authPublishM M stl ∗
        -- (E3zb) with auth on, the request side bound to the request context's token
        □ (⌜M.isOn = true⌝ → auth.tpReady M -∗ isReqAuthBound st RD M) ∗
        authApplyResPre M stl (auth.bump auth.bootState) d RD ∗ authCapM M stl ∗
        -- (R-D1, 2026-11-04) the store abandoned on `NewServer`'s error path
        authAbandonM M stl d RD ∗
        -- (D22 J1a, 2026-10-26) in the mode `off`, the store's `Recover` on a new backend
        -- (`NewAuthStore`'s axiom's `authRecoverOk`)
        □ (⌜M = auth.AuthMode.off⌝ → authRecoverOk stl) ∗
        -- (R2b-3d stage 5b, 2026-11-05) in the mode `off`, the store's `Close` (`NewAuthStore`'s
        -- axiom's `authCloseOk`), for `Cleanup`
        □ (⌜M = auth.AuthMode.off⌝ → authCloseOk stl) ∗
        -- (the auth-on snapshot plan's decision 8) in the mode `on`, its snapshot clause
        authSnapKitM M stl RD ∗
        -- (authkv's Main, 2026-10-30) with auth on, the store's cost field, read-only
        -- (`BcryptCost()`'s; `newAuthStore_on`'s); (C1's A4, 2026-10-31) and its `Authenticate`
        -- side (`authnStoreOk`, of its invariant: `authnStoreOk_of_authInv`)
        □ (⌜M.isOn = true⌝ →
          (∃ c : w64, structFieldRef go_etcd_io.etcd.server.v3.auth.authStore go!"bcryptCost" stl ↦□ c) ∗
          authnStoreOk st RD) }})


/-- `authStoreKitR` in the mode `off`, of `NewAuthStore`'s axiom (`authStoreKit_off`'s proof). -/
theorem authStoreKitR_off (h30 : auth.NewAuthStore.spec (GF := GF) (hG := hG)) (tp : GoInterface) :
    ⊢ authStoreKitR (GF := GF) .off tp := by
  iunfold authStoreKitR
  iexists iprop(True)
  isplitr
  · itrivial
  iintro !> %lg %ab %abl %d %W %Pk %qo %r %cost %Φ !> ⟨-, #Hpkg, #Hlg, %Htp, %Hfit, %Hab, #Habbe,
    #Hablg, #HB, Ho, Hh, Hwb, Hrb, -, %Hr, %Hhas⟩ HΦ
  -- (the auth-on snapshot plan's Prove step) the axiom at the auth buckets, idle
  ihave Hrb := backend.rbOwnIn_part _ _ _ $$ Hrb
  iapply (h30 lg ab tp cost abl d W Pk qo authBkts r (fun _ h => h) Hhas.1 Hhas.2.1
    Hhas.2.2) $$ [Ho Hh Hwb Hrb]
  · iframe Hpkg Habbe Hablg HB Ho Hh Hwb Hrb
    isplitr
    · iapply zapLoggerOk_orNil; iexact Hlg
    ipureintro; exact ⟨Htp, Hfit, Hab, Hr.1, Hr.2⟩
  iintro !> %st ⟨Ho, Hh, Hr, %RD, %stl, %Hst, Hbe, Hsl, #Hreq, #Hok, #HauR, #HauC⟩
  iapply HΦ
  iframe Ho Hh
  isplitl [Hr]
  · simp only [authKitOut]; iexact Hr
  have hR : backend.authRdN - 1 ≤ Int.toNat sync.rwmutex.actualMaxReaders := by
    rw [sync.rwmutex.actualMaxReaders_unseal]; unfold backend.authRdN; decide
  icases replicate_takeN _ (backend.authRdN - 1) _ hR $$ Hsl with ⟨Hsl, -⟩
  ihave Hsl : authRdSupply RD $$ [Hsl]
  · unfold authRdSupply; iexact Hsl
  iexists RD, stl
  iframe Hbe Hsl
  isplitr
  · ipureintro; exact Hst
  isplitr
  · iintro !> -; iexact Hreq
  isplitr
  · iExactEq Hok; rfl
  isplitr
  · unfold authStoreLatestM; itrivial
  isplitr
  · unfold authStoreLbM; itrivial
  isplitr
  · unfold authPublishM; itrivial
  isplitr
  · iintro !> %h; exact absurd h (by decide)
  isplitr
  · unfold authApplyResPre
    itrivial
  isplitr
  · unfold authCapM; itrivial
  isplitr
  · iunfold authAbandonM
    iintro !> %_st _ _
    unfold authOpenM
    imodintro; itrivial
  isplitr
  · iintro !> -
    iexact HauR
  isplitr
  · iintro !> -
    iexact HauC
  isplitr
  · unfold authSnapKitM; itrivial
  iintro !> %h; exact absurd h (by decide)


end kit

end EtcdGrove
end Perennial
