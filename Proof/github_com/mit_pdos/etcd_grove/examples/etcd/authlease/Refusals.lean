/-
**authlease's refusals** (auth-lease S4, item 9; what `run` hands the checks): the caller's premises of
`noAuth` and `foreign` (no lease check passes for the principal: the auth state fixed after the set-up,
`akAuthFixed`, and the cell's lessor-side facts, `Holds.lean`), and the updates of the refused writes
under the cell (u's leased put of `a/x` with `Lz` and its revocation of `Lz`; the revocations of `Lu` by
`v`, the client with no token and the one with the invalid token), each refuted at its grant
(`akGrantedL_of_writeGrantG`, `not_akGrantedL_lease`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Holds
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.LeaseAttempts

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authlease

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic Iris.Std go_etcd_io.etcd.server.v3.etcdserver client etcd_auth

section pure
variable [GooseExts]

/-- u and v are no admins at `setupSt`. -/
theorem not_adminOk_setupSt (r : Nat) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (hu : info.Username' = go!"u" ∨ info.Username' = go!"v") :
    ¬ auth.adminOk (setupSt r) (some (auth.authInfoM info)) := by
  intro hadm
  rcases hadm with hen | ⟨a', u', ha, -, hus, hroot⟩
  · simp [setupSt] at hen
  cases ha
  simp only [auth.authInfoM] at hus
  rcases hu with hu' | hv
  · rw [hu', setupSt_users_u] at hus; cases hus; exact not_isRoot_u hroot
  · rw [hv, setupSt_users_v] at hus; cases hus; exact not_isRoot_v hroot

/-- u may not read a key outside `[a, b)`, v no key, at `setupSt`. -/
theorem not_permitted_setupSt (r : Nat) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (k : GoString)
    (hk : k ≠ []) (hu : (info.Username' = go!"u" ∧ ¬ inRangeK k) ∨ info.Username' = go!"v") :
    ¬ auth.permitted (setupSt r) (auth.authInfoM info) k [] .read := by
  have hs : auth.reqShape k [] := ⟨hk, Or.inl rfl⟩
  intro hp
  rcases hp with hen | ⟨-, u', hus, hc⟩
  · simp [setupSt] at hen
  simp only [auth.authInfoM] at hus
  rcases hu with ⟨hu', hnk⟩ | hv
  · rw [hu', setupSt_users_u] at hus; cases hus
    rcases hc with hroot | hc
    · exact not_isRoot_u hroot
    · have := hc hs
      simp only [auth.covers, if_pos rfl, auth.coversPoint, userPerms_u, List.mem_singleton,
        exists_eq_left] at this
      exact hnk ((permR_covers _ k).1 this)
  · rw [hv, setupSt_users_v] at hus; cases hus
    rcases hc with hroot | hc
    · exact not_isRoot_v hroot
    · have := hc hs
      simp [auth.covers, auth.coversPoint, userPerms_v] at this

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **An auth state no older than the fixed one is a `setupSt`** (`akAuthFixed`'s, at the full mask). -/
theorem fixed_state (γa : auth.AuthNames) (ρ : ReqNames) (Lset : List EntryModel) (n m : Nat)
    (st : auth.AuthState) (hm : n ≤ m) :
    akAuthFixed (GF := GF) γa ρ Lset n ∗ auth.authStateAt γa m st ={⊤}=∗ ⌜∃ r, st = setupSt r⌝ := by
  iintro ⟨#Hf, #Hst⟩
  iunfold akAuthFixed at Hf
  icases Hf with ⟨-, #Hfx, -⟩
  have hmask : authTieReadMask ⊆ (⊤ : CoPset) ∧ n ≤ m := ⟨fun _ _ => CoPset.mem_full, hm⟩
  iapply Hfx $$ %⊤ %m %st %hmask Hst

/-- **The principal of a lease check of `who`** (`principalBoundT` at an attempt's token): `who`, for u
and v; the TLS fallback is off. -/
theorem princ_who (s : Loc) (γa : auth.AuthNames) (who : GoString) (tok : Option GoString)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    v3rpc.principalBoundT (GF := GF) s (.on γa) tok info ∗ akTokSeen γa who tok ∗
      □ (srvTLSId s -∗ False) ⊢ ⌜info.Username' = who ∧ (who = go!"u" ∨ who = go!"v")⌝ := by
  iintro ⟨#Hb, #Ht, #Htls⟩
  unfold v3rpc.principalBoundT
  icases Hb with (⟨%token, %Htok, #Hok⟩ | #Hs)
  · unfold auth.tokOk
    iunfold akTokSeen at Ht
    icases Ht with (%Hn | ⟨%t, %Ht', #Hall⟩)
    · rw [Hn] at Htok; cases Htok
    · rw [Ht'] at Htok
      cases Htok
      iapply Hall $$ %info.Username' Hok
  · iexfalso; iapply Htls $$ Hs

/-- **No lease check passes for the client with no token or the invalid one** (`noAuth`'s premise):
auth is enabled at every state no older than the fixed one, and no user is bound to their tokens. -/
theorem noAuth_refutes (s : Loc) (E : apply.AEnv GF) (γa : auth.AuthNames) (ρ : ReqNames)
    (Lset : List EntryModel) (n : Nat) (who : GoString) (hγa : E.authMode = .on γa)
    (hwho : who = go!"anon" ∨ who = go!"bad") :
    akAuthFixed (GF := GF) γa ρ Lset n ∗ □ (srvTLSId s -∗ False) ⊢
      □ (∀ (tok : Option GoString) (K : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF),
          akTokSeen γa who tok -∗ v3rpc.leaseCheckT s E tok n K ={⊤}=∗ False) := by
  have hon : E.authOn = true := by unfold apply.AEnv.authOn; rw [hγa]; rfl
  iintro ⟨#Hf, #Htls⟩ !> %tok %K #Hs Hck
  iunfold v3rpc.leaseCheckT at Hck
  rw [hγa]
  icases Hck with (Hen | ⟨%info, #Hpb, -⟩)
  · unfold auth.enabledVerdictFrom
    icases Hen with ⟨%j, %st, #Hst, %Hj⟩
    imod (fixed_state γa ρ Lset n j st Hj.1) $$ [Hf Hst] with %Hr
    · iframe #
    obtain ⟨r, hr⟩ := Hr
    subst hr
    simp [setupSt] at Hj
  · ihave #Hpb' := Hpb $$ %hon
    ihave %Hw := princ_who s γa who tok info $$ [Hpb' Hs Htls]
    · iframe #
    exfalso
    rcases hwho with rfl | rfl <;> rcases Hw.2 with h | h <;> exact absurd h (by decide)

/-- **`foreign`'s refutation of a passed lease check over a held lease** (u against `Lz`, v against
`Lu`): auth enabled, the principal no admin, and its keys verdict over the held lease refuted
(`holds_refutes_keys`), at the main thread's unpermitted revocation `γc.a`. -/
theorem foreign_check_refuted (s : Loc) (E : apply.AEnv GF) (γa : auth.AuthNames) (ρ : ReqNames)
    (Lset : List EntryModel) (n : Nat) (who : GoString) (γc : CellNames) (γl : GName) (m : Nat)
    (id : w64) (k : GoString) (tok : Option GoString)
    (K : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF) (hγa : E.authMode = .on γa) (hk : k ≠ [])
    (hwho : (who = go!"u" ∧ ¬ inRangeK k) ∨ who = go!"v") :
    akAuthFixed (GF := GF) γa ρ Lset n ∗ □ (srvTLSId s -∗ False) ∗ akTokSeen γa who tok ∗
      □ (∀ info, K info -∗ leaseKeysVerdictFrom E.authMode n info γl m id .read) ∗
      holdsFrom γc γl m id k ∗ v3rpc.leaseCheckT s E tok n K ∗
      monoNatAuthOwn γc.a (1 : Qp).half 0 ={⊤}=∗ False := by
  have hon : E.authOn = true := by unfold apply.AEnv.authOn; rw [hγa]; rfl
  iintro ⟨#Hf, #Htls, #Hs, #HK, #Hh, Hck, Ham⟩
  iunfold v3rpc.leaseCheckT at Hck
  icases Hck with (Hen | ⟨%info, #Hpb, Hv⟩)
  · rw [hγa]
    unfold auth.enabledVerdictFrom
    icases Hen with ⟨%j, %st, #Hst, %Hj⟩
    imod (fixed_state γa ρ Lset n j st Hj.1) $$ [Hf Hst] with %Hr
    · iframe #
    obtain ⟨r, hr⟩ := Hr
    subst hr
    simp [setupSt] at Hj
  ihave #Hpb' := Hpb $$ %hon
  rw [hγa] at *
  ihave %Hw := princ_who s γa who tok info $$ [Hpb' Hs Htls]
  · iframe #
  have hu : info.Username' = go!"u" ∨ info.Username' = go!"v" := by
    rcases Hw.2 with h | h
    · left; rw [Hw.1, h]
    · right; rw [Hw.1, h]
  icases Hv with (Had | HKi)
  · iunfold adminVerdictFrom at Had
    unfold auth.adminVerdictFrom
    icases Had with ⟨%i, %st, #Hst, %Hi⟩
    imod (fixed_state γa ρ Lset n i st Hi.1) $$ [Hf Hst] with %Hr
    · iframe #
    obtain ⟨r, hr⟩ := Hr
    subst hr
    exact absurd (Hi.2 rfl) (not_adminOk_setupSt r info hu)
  ihave Hkv := HK $$ %info HKi
  rw [hγa]
  iapply (holds_refutes_keys γc γl m id k (.on γa) n info)
  iframe Hh Hkv Ham
  iintro !> Hp
  unfold auth.permVerdictFrom
  icases Hp with ⟨⟨%i, %st, #Hst, %Hi⟩, -, -⟩
  imod (fixed_state γa ρ Lset n i st Hi.1) $$ [Hf Hst] with %Hr
  · iframe #
  obtain ⟨r, hr⟩ := Hr
  subst hr
  have hu' : (info.Username' = go!"u" ∧ ¬ inRangeK k) ∨ info.Username' = go!"v" := by
    rcases hwho with ⟨rfl, hnk⟩ | rfl
    · exact Or.inl ⟨Hw.1, hnk⟩
    · exact Or.inr Hw.1
  exact absurd (Hi.2 rfl) (not_permitted_setupSt r info k hk hu')

/-- `holdsFrom` from a later index on. -/
theorem holdsFrom_mono (γc : CellNames) (γl : GName) (m i : Nat) (id : w64) (k : GoString) (hmi : m ≤ i) :
    holdsFrom (GF := GF) γc γl m id k ⊢ holdsFrom γc γl i id k := by
  iintro #Hh
  iunfold holdsFrom at Hh
  iunfold holdsFrom
  iintro !> %j %σl %hj Ha Ham
  iapply Hh $$ %j %σl %(Nat.le_trans hmi hj) Ha Ham

/-- **`foreign`'s two lessor-side premises** (see `foreign.spec`), at `R` the main thread's unpermitted
revocation: the keys verdict of a passed `TimeToLive` over the held lease, and a passed listing (which
lists the held lease, `holds_listed`), are refuted. -/
theorem foreign_reads_refuted (s : Loc) (E : apply.AEnv GF) (γa : auth.AuthNames) (ρ : ReqNames)
    (Lset : List EntryModel) (n : Nat) (who : GoString) (γc : CellNames) (γl : GName) (m : Nat)
    (id : w64) (k : GoString) (hγa : E.authMode = .on γa) (hk : k ≠ [])
    (hwho : (who = go!"u" ∧ ¬ inRangeK k) ∨ who = go!"v") :
    akAuthFixed (GF := GF) γa ρ Lset n ∗ □ (srvTLSId s -∗ False) ∗ holdsFrom γc γl m id k ⊢
      □ (∀ tok : Option GoString, akTokSeen γa who tok -∗
          v3rpc.leaseCheckT s E tok n (fun info => leaseKeysVerdictFrom E.authMode n info γl m id .read) -∗
          monoNatAuthOwn γc.a (1 : Qp).half 0 ={⊤}=∗ False) ∗
      □ (∀ (tok : Option GoString) (i : Nat) (ids : List w64), ⌜m ≤ i⌝ -∗ akTokSeen γa who tok -∗
          lease.leaseIdsAt γl i ids -∗
          v3rpc.leaseCheckT s E tok n (fun info => iprop([∗list] id' ∈ ids,
            leaseKeysVerdictFrom E.authMode n info γl i id' .read)) -∗
          monoNatAuthOwn γc.a (1 : Qp).half 0 ={⊤}=∗ False) := by
  iintro ⟨#Hf, #Htls, #Hh⟩
  isplitl
  · iintro !> %tok #Hs Hck Ham
    iapply (foreign_check_refuted s E γa ρ Lset n who γc γl m id k tok _ hγa hk hwho)
    iframe Hf Htls Hs Hh Hck Ham
    iintro !> %info H
    iexact H
  · iintro !> %tok %i %ids %hmi #Hs #Hids Hck Ham
    imod (holds_listed γc γl m i id k ids hmi) $$ [Hh Hids Ham] with ⟨Ham, %Hin⟩
    · iframe #; iframe
    ihave #Hhi := holdsFrom_mono γc γl m i id k hmi $$ Hh
    iapply (foreign_check_refuted s E γa ρ Lset n who γc γl i id k tok _ hγa hk hwho)
    iframe Hf Htls Hs Hhi Hck Ham
    iintro !> %info Hall
    iapply (BigSepL.bigSepL_mem Hin) $$ Hall

/-- **A grant of a write naming a held lease, refuted** (`akGrantedL_of_writeGrantG`,
`not_akGrantedL_lease`): the request `rq` of `who`'s checks the lease `L` holding `k`, which `who` may
not write. -/
theorem grantG_refuted (s : Loc) (E : apply.AEnv GF) (γa : auth.AuthNames) (ρ : ReqNames)
    (Lset : List EntryModel) (n : Nat) (who : GoString) (tok : Option GoString) (rq : apply.IRRModel)
    (σ : KVState) (k : GoString) (L : w64) (hγa : E.authMode = .on γa)
    (hk : leaseOf k σ.kvs = some L) (hL : L ≠ W64 0)
    (hwho : who = go!"anon" ∨ who = go!"bad" ∨ who = go!"v" ∨ (who = go!"u" ∧ ¬ inRangeK k))
    (hrq : ∀ r (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (hm : apply.HeaderModel),
      leaseGrantedM (setupSt r) I (apply.withHeader rq hm) →
        leaseOk (setupSt r) ⟨hm.username, hm.authRevision⟩ I L) :
    akAuthFixed (GF := GF) γa ρ Lset n ∗ akTokSeen γa who tok ∗ □ (srvTLSId s -∗ False) ∗
      writeGrantG ρ.kv srvAuthSt0 (v3rpc.hdrBoundT s E.authMode tok) rq Lset σ ={cellM}=∗ False := by
  iintro ⟨#Hf, #Hs, #Htls, Hw⟩
  imod (akGrantedL_of_writeGrantG s E γa ρ Lset n who tok rq σ cellM hγa authHistN_cellM) $$ [Hf Hs Htls] Hw
    with %Hg
  · iframe #
  exact absurd Hg (not_akGrantedL_lease who σ rq k L hk hL hwho (fun r hm h => hrq r _ hm h))

/-- **A client update of `who`'s, refuted at every state the cell holds** (`cell_refusedAu`): `op`'s
grant is `rq`'s, which checks the lease `L`, held on `k` at those states. -/
theorem refused_update (s : Loc) (E : apply.AEnv GF) (γa : auth.AuthNames) (ρ : ReqNames)
    (Lset : List EntryModel) (n : Nat) (who : GoString) (γc : CellNames) (op : KVOp) (rq : apply.IRRModel)
    (k : GoString) (L : w64) (pre : List w64) (ps0 : List Nat) (Q : KVState → IProp GF)
    (hγa : E.authMode = .on γa)
    (hop : ∀ tok L₀ σ, v3rpc.opGrantT (GF := GF) s E ρ tok op L₀ σ =
      writeGrantG ρ.kv srvAuthSt0 (v3rpc.hdrBoundT s E.authMode tok) rq L₀ σ)
    (hcell : ∀ σ ids ps gs d, CellOk σ ids ps gs d → pre <+: ids → ps0.length ≤ ps.length →
      leaseOf k σ.kvs = some L ∧ L ≠ W64 0)
    (hwho : who = go!"anon" ∨ who = go!"bad" ∨ who = go!"v" ∨ (who = go!"u" ∧ ¬ inRangeK k))
    (hrq : ∀ r (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (hm : apply.HeaderModel),
      leaseGrantedM (setupSt r) I (apply.withHeader rq hm) →
        leaseOk (setupSt r) ⟨hm.username, hm.authRevision⟩ I L) :
    cellInv ρ.kv γc ∗ monoListLbOwn γc.ids pre ∗ monoListLbOwn γc.ps ps0 ∗
      akAuthFixed (GF := GF) γa ρ Lset n ∗ □ (srvTLSId s -∗ False) ⊢
      □ ∀ (conn : Loc) (ctx : GoInterface), attemptTokOk conn (akTokP γa who) -∗
        ⌜metadata.outgoingOf ctx = akOut who⌝ -∗ clientOpAuOn s E ρ conn ctx op Q := by
  iintro ⟨#Hinv, #Hi0, #Hp0, #Hf, #Htls⟩ !> %conn %ctx #Htk %hout
  iunfold clientOpAuOn
  iexists Lset
  isplitr
  · iunfold akAuthFixed at Hf
    icases Hf with ⟨-, -, #Hl, -⟩
    iexact Hl
  ihave #Hau := cell_refusedAu ρ.kv γc op (clientGrant s E ρ conn ctx op Lset) Q $$ []
  · isplitl []
    · iexact Hinv
    iintro !> %σ %ids %ps %gs %d %HS Hids Ha HG
    ihave %Hpre := ids_of_lb γc ids pre $$ Hids Hi0
    iunfold cellAuth at Ha
    icases Ha with ⟨Hp, -, -, -⟩
    ihave %Hps := len_of_lb γc ps ps0 $$ Hp Hp0
    obtain ⟨hk, hL⟩ := hcell σ ids ps gs d HS Hpre Hps
    iunfold clientGrant at HG
    icases HG with ⟨%md, %Hmd, HG⟩
    rw [hop]
    ihave #Hs := akTokSeen_attempt γa who conn md
      (by unfold clientAttemptMd at Hmd; rw [hout] at Hmd; exact Hmd) $$ Htk
    iapply (grantG_refuted s E γa ρ Lset n who _ rq σ k L hγa hk hL hwho hrq)
    iframe #; iframe
  iexact Hau

/-- **A revocation of `Lu` of `who`'s** (`v`, the client with no token, the invalid one) **under the
cell** (`cell_revokeLuAu`): refuted while `a/lease` holds `Lu`, a no-op after u's revocation; it tells
`revoked`. -/
theorem revokeLu_update (s : Loc) (E : apply.AEnv GF) (γa : auth.AuthNames) (ρ : ReqNames)
    (Lset : List EntryModel) (n : Nat) (who : GoString) (γc : CellNames) (Lz Lu : w64) (ps0 : List Nat)
    (h3 : 3 ≤ ps0.length) (hLu : Lu ≠ W64 0) (hγa : E.authMode = .on γa)
    (hwho : who = go!"anon" ∨ who = go!"bad" ∨ who = go!"v") :
    cellInv ρ.kv γc ∗ monoListLbOwn γc.ids [Lz, Lu] ∗ monoListLbOwn γc.ps ps0 ∗
      akAuthFixed (GF := GF) γa ρ Lset n ∗ □ (srvTLSId s -∗ False) ⊢
      □ ∀ (conn : Loc) (ctx : GoInterface), attemptTokOk conn (akTokP γa who) -∗
        ⌜metadata.outgoingOf ctx = akOut who⌝ -∗ clientOpAuOn s E ρ conn ctx (.leaseRevoke Lu) (revoked γc) := by
  iintro ⟨#Hinv, #Hi0, #Hp0, #Hf, #Htls⟩ !> %conn %ctx #Htk %hout
  iunfold clientOpAuOn
  iexists Lset
  isplitr
  · iunfold akAuthFixed at Hf
    icases Hf with ⟨-, -, #Hl, -⟩
    iexact Hl
  ihave #Hau := cell_revokeLuAu ρ.kv γc Lz Lu ps0 h3
    (clientGrant s E ρ conn ctx (.leaseRevoke Lu) Lset) $$ []
  rotate_left
  · iexact Hau
  iframe Hinv Hi0 Hp0
  iintro !> %σ %ha HG
  iunfold clientGrant at HG
  icases HG with ⟨%md, %Hmd, HG⟩
  ihave #Hs := akTokSeen_attempt γa who conn md
      (by unfold clientAttemptMd at Hmd; rw [hout] at Hmd; exact Hmd) $$ Htk
  iapply (grantG_refuted s E γa ρ Lset n who _ (irrLeaseRevoke Lu) σ aK Lu hγa ha hLu
    (by rcases hwho with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h)))
    (fun r I hm h => leaseGranted_revoke r I Lu hm h))
  iframe #
  iunfold v3rpc.opGrantT at HG
  iexact HG

end defs

end etcd_authlease
end EtcdGrove
end Perennial
