/-
**The principal of `Work`'s requests** (`notes/authkv-main-plan.md`, "Proving the stubs", layer 1;
2026-10-30). Lean-first (no Rocq counterpart).

`Work(cli, who)` sends with the context `reqCtx(who)` (and its watch with a timeout context, `bad`'s
with `badtoken` appended): its outgoing metadata is none, or for `bad` the one token `badtoken`
(`akOut`). An attempt of `cli`'s connection then carries (`attemptTokOk` at `akTokP γa who`) a token
issued to `who` (`u`, `v`), or the outgoing metadata's token: none, or `badtoken`, issued to no one
(`akTokSeen`). A header or auth info the server binds to such a token (`hdrBoundT`, `infoBoundT`)
names the empty user or, for `u` and `v`, `who` (`akUser`), the TLS fallback being off.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.WorkEnv
public import Proof.go_etcd_io.etcd.client.v3.StreamKey

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver client

/-- **The outgoing metadata of `who`'s requests**: none, or for `bad` the one token `badtoken`. -/
def akOut [GooseExts] (who : GoString) : GrpcMd :=
  if who = go!"bad" then metadata.mdAdd none go!"token" badToken else none

/-- **The user a request of `who` can be bound to**: the empty one, or for `u` and `v`, `who`. -/
def akUser (who user : GoString) : Prop :=
  user = (zeroValDef : GoString) ∨ (user = who ∧ (who = go!"u" ∨ who = go!"v"))

/-- Metadata whose `token` values are `[badtoken]` carries `badtoken`, as grpc delivers it. -/
theorem mdTokenOf_mdNorm_bad [GooseExts] (m : GrpcMd)
    (h : metadata.mdVals m go!"token" = [badToken]) :
    auth.mdTokenOf (metadata.mdNorm m) = some badToken := by
  cases m with
  | none => simp [metadata.mdVals] at h
  | some f =>
    simp only [metadata.mdVals, Option.bind_some] at h
    cases hf : f go!"token" with
    | none => rw [hf] at h; simp at h
    | some vs =>
      rw [hf] at h
      simp only [Option.getD_some] at h
      subst h
      simp only [auth.mdTokenOf, metadata.mdNorm, Option.map_some, hf, trimPrefix_badToken]

section tok
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The token an attempt of `who` carries** (persistent): none, or one every issuance of which
is to `who`, a user of the program (`u` or `v`). -/
def akTokSeen (γa : auth.AuthNames) (who : GoString) (tok : Option GoString) : IProp GF :=
  iprop(⌜tok = none⌝ ∨ ∃ t : GoString, ⌜tok = some t⌝ ∗
    □ (∀ u', auth.tokIssued γa t u' -∗ ⌜u' = who ∧ (who = go!"u" ∨ who = go!"v")⌝))

instance akTokSeen_persistent (γa : auth.AuthNames) (who : GoString) (tok : Option GoString) :
    Persistent (akTokSeen (GF := GF) γa who tok) := by
  unfold akTokSeen; infer_instance

/-- **An issued token has no `"Bearer "` prefix.** OPEN (2026-10-30): true of Go (the simple
provider's prefix is `genTokenPrefix`'s 16 letters, so a token has no space), but the model's shape
(`auth.tokShape`, `auth.authnCtx`'s prefix) does not record it: a `sorry` until the auth package's
shape does (`notes/authkv-main-plan.md`, "Proving the stubs"). -/
theorem tokIssued_trim (γa : auth.AuthNames) (t u : GoString) :
    auth.tokIssued (GF := GF) γa t u ⊢ ⌜strings.trimPrefix t go!"Bearer " = t⌝ := by
  sorry

/-- **The token of an attempt of `who`**, from the connection's token fact's two cases: a token
meeting `akTokP γa who` (issued to `who`, for `u` and `v`; none for the others), or the token of
outgoing metadata `m` that has none, or for `bad` the one value `badtoken`. -/
theorem akTokSeen_of (γa : auth.AuthNames) (who : GoString) (m : GrpcMd) (tok : Option GoString)
    (hm : m = none ∨ (who = go!"bad" ∧ metadata.mdVals m go!"token" = [badToken])) :
    ((∃ t, ⌜tok = some (strings.trimPrefix t go!"Bearer ")⌝ ∗ □ akTokP (GF := GF) γa who t) ∨
      ⌜tok = auth.mdTokenOf (metadata.mdNorm m)⌝) ⊢ akTokSeen γa who tok := by
  iintro (⟨%t, %Ht, #HP⟩ | %Ht)
  · unfold akTokP
    by_cases hw : who = go!"u" ∨ who = go!"v"
    · simp only [if_pos hw]
      ihave %Htr := tokIssued_trim γa t who $$ HP
      rw [Htr] at Ht
      iunfold akTokSeen
      iright
      iexists t
      isplitl []
      · ipureintro; exact Ht
      iintro !> %u' Hu
      ihave %Hag := auth.tokIssued_agree γa t u' who $$ [Hu]
      · iframe Hu HP
      ipureintro; exact ⟨Hag, hw⟩
    · simp only [if_neg hw]
      icases HP with ⟨⟩
  · rcases hm with rfl | ⟨-, hv⟩
    · iunfold akTokSeen
      ileft
      ipureintro
      rw [Ht]; rfl
    · rw [mdTokenOf_mdNorm_bad m hv] at Ht
      iunfold akTokSeen
      iright
      iexists badToken
      isplitl []
      · ipureintro; exact Ht
      iintro !> %u' Hu
      iexfalso
      iapply (tokIssued_badToken (GF := GF) γa u')
      iexact Hu

/-- `akOut`'s metadata is none, or `bad`'s one token. -/
theorem akOut_cases (who : GoString) :
    akOut who = none ∨ (who = go!"bad" ∧ metadata.mdVals (akOut who) go!"token" = [badToken]) := by
  unfold akOut
  split
  · right
    refine ⟨by assumption, ?_⟩
    rw [metadata.mdVals_mdAdd]; rfl
  · left; rfl

/-- **The token of an attempt of `who`'s client** with a context of outgoing metadata
`akOut who`. -/
theorem akTokSeen_attempt (γa : auth.AuthNames) (who : GoString) (conn : Loc) (md : GrpcMd)
    (hmd : clientAttemptMdOf conn (akOut who) md) :
    attemptTokOk (GF := GF) conn (akTokP γa who) ⊢ akTokSeen γa who (auth.mdTokenOf md) := by
  iintro #Ht
  unfold attemptTokOk
  ihave Hc := Ht $$ %(akOut who) %md %hmd
  iapply (akTokSeen_of γa who (akOut who) _ (akOut_cases who)) $$ Hc

/-- **The token of `who`'s watch stream**: the stream's metadata has the stream key of `who`'s
watch context (`akOut who`), so it is none or `bad`'s one token (`streamKeyOf_none`,
`streamKeyOf_single`). -/
theorem akOut_streamKey (who : GoString) (m : GrpcMd)
    (hk : streamKeyOf m = streamKeyOf (akOut who)) :
    m = none ∨ (who = go!"bad" ∧ metadata.mdVals m go!"token" = [badToken]) := by
  unfold akOut at hk
  split at hk
  · right
    refine ⟨by assumption, ?_⟩
    refine streamKeyOf_single m go!"token" badToken ?_ ?_ ?_ hk
    · unfold metadata.lowerKey; decide
    · decide
    · decide
  · left; exact streamKeyOf_none m hk

/-- **The user of a request of `who`** (a header bound to an attempt's token, `hdrBoundT`): the
empty one, or for `u` and `v`, `who`; the TLS fallback is off. -/
theorem akUser_hdr (s : Loc) (γa : auth.AuthNames) (who : GoString) (tok : Option GoString)
    (hm : apply.HeaderModel) :
    v3rpc.hdrBoundT (GF := GF) s (.on γa) tok hm ∗ akTokSeen γa who tok ∗ □ (srvTLSId s -∗ False) ⊢
      ⌜akUser who hm.username⌝ := by
  iintro ⟨#Hb, #Ht, #Htls⟩
  unfold v3rpc.hdrBoundT
  icases Hb with (%H0 | (⟨%token, %Htok, #Hok⟩ | #Hs))
  · ipureintro; exact Or.inl H0
  · unfold auth.tokOk
    iunfold akTokSeen at Ht
    icases Ht with (%Hn | ⟨%t, %Ht', #Hall⟩)
    · rw [Hn] at Htok; cases Htok
    · rw [Ht'] at Htok
      cases Htok
      ihave %H := Hall $$ %hm.username Hok
      ipureintro; exact Or.inr H
  · iexfalso; iapply Htls $$ Hs

/-- **The user of a read of `who`** (an auth info bound to an attempt's token, `infoBoundT`). -/
theorem akUser_info (s : Loc) (γa : auth.AuthNames) (who : GoString) (tok : Option GoString)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) :
    v3rpc.infoBoundT (GF := GF) s (.on γa) tok info ∗ akTokSeen γa who tok ∗
      □ (srvTLSId s -∗ False) ⊢ ⌜akUser who info.Username'⌝ := by
  iintro ⟨#Hb, #Ht, #Htls⟩
  unfold v3rpc.infoBoundT
  icases Hb with (%H0 | (⟨%token, %Htok, #Hok⟩ | #Hs))
  · ipureintro; exact Or.inl H0
  · unfold auth.tokOk
    iunfold akTokSeen at Ht
    icases Ht with (%Hn | ⟨%t, %Ht', #Hall⟩)
    · rw [Hn] at Htok; cases Htok
    · rw [Ht'] at Htok
      cases Htok
      ihave %H := Hall $$ %info.Username' Hok
      ipureintro; exact Or.inr H
  · iexfalso; iapply Htls $$ Hs

end tok

/-! ## A write's grant at `setupSt` -/

section pure
variable [GooseExts]

/-- No request has the empty user at `setupSt`. -/
theorem setupSt_users_empty (rev : Nat) :
    (setupSt rev).users !! (zeroValDef : GoString) = none := by
  simp [setupSt, zeroValDef]

/-- **A granted request of `who`'s principal at `setupSt`**: each point permission it needs on a
non-empty key is one `who` holds (`permittedK`). -/
theorem kvGranted_setupSt_point (r : Nat) (rq : apply.IRRModel) (who k : GoString) (op : auth.PermType)
    (hg : kvGranted (setupSt r) rq) (hu : akUser who (apply.principalOf rq).Username')
    (hx : ((k, [], op) : apply.Perm3) ∈ reqPerms rq) (hk : k ≠ []) : permittedK who k := by
  rcases hg _ hx with hen | ⟨hrev, -, u', hu', hc⟩
  · simp [setupSt] at hen
  · simp only [auth.authInfoM] at hrev hu' hc
    rcases hu with h0 | ⟨hw, hw'⟩
    · rw [h0, setupSt_users_empty] at hu'; cases hu'
    · rw [hw] at hu'
      exact (granted_setupSt_iff r _ op who k hrev hk hw').1 ⟨hrev, u', hu', hc.imp id fun h _ => h⟩

/-- **The write's grant the history admits**: the stamped request of `rq` granted at some
`setupSt`, its user one of `who`'s. -/
def akGranted (who : GoString) (rq : apply.IRRModel) : Prop :=
  ∃ r hm, kvGranted (setupSt r) (apply.withHeader rq hm) ∧ akUser who hm.username

/-- **A write operation's grant** (`opGrantT`'s request: a put's, a delete's, some wire
transaction's of a transaction). -/
def akOpGranted (who : GoString) : KVOp → Prop
  | .put o => akGranted who (irrPut o)
  | .deleteRange o => akGranted who (irrDeleteRange o)
  | .txn t => ∃ tw : txn.TxnModelW, tw.toModel = t ∧ akGranted who (irrTxn tw)
  | _ => True

/-- A granted request's point permissions on non-empty keys are `who`'s. -/
theorem akGranted_point (who : GoString) (rq : apply.IRRModel) (k : GoString) (op : auth.PermType)
    (hg : akGranted who rq) (hx : ((k, [], op) : apply.Perm3) ∈ reqPerms rq) (hk : k ≠ []) : permittedK who k := by
  obtain ⟨r, hm, hg, hu⟩ := hg
  exact kvGranted_setupSt_point r _ who k op hg (by rw [principalOf_withHeader]; exact hu)
    (by rw [reqPerms_withHeader]; exact hx) hk

end pure

section grant
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- The auth history's namespace is inside the history invariant's updates' mask. -/
theorem authHistN_akMask : (↑authHistN : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑akHistN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff]
  exact ⟨⟨⟨CoPset.mem_full, fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩⟩,
    fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩⟩,
    fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩⟩

/-- **A grant at an attempt of `who`'s** (`writeGrantG` at the set-up's log `Lset`, its header
bound to a token `akTokSeen` admits) **is at `setupSt`**: the grant's log extends `Lset`, so its auth
state is `setupSt` (`akAuthFixed_write`), and the header's user is one of `who`'s
(`akUser_hdr`). -/
theorem akGranted_of_writeGrantG (s : Loc) (E : apply.AEnv GF) (γa : auth.AuthNames)
    (ρ : ReqNames) (Lset : List EntryModel) (n : Nat) (who : GoString) (tok : Option GoString)
    (rq : apply.IRRModel) (σ : KVState) (Em : CoPset) (hγa : E.authMode = .on γa)
    (hE : ↑authHistN ⊆ Em) :
    akAuthFixed (GF := GF) γa ρ Lset n ∗ akTokSeen γa who tok ∗ □ (srvTLSId s -∗ False) ⊢
      writeGrantG ρ.kv srvAuthSt0 (v3rpc.hdrBoundT s E.authMode tok) rq Lset σ ={Em}=∗
        ⌜akGranted who rq⌝ := by
  rw [hγa]
  iintro ⟨#Hf, #Hseen, #Htls⟩ Hw
  unfold writeGrantG
  icases Hw with ⟨%hm, %L, #Hb, #Hlb, %Hp⟩
  obtain ⟨hL, hgr, -⟩ := Hp
  imod (akAuthFixed_write γa ρ Lset n L Em hE hL) $$ Hf Hlb with %Hr
  obtain ⟨r, hr⟩ := Hr
  ihave %Hu := akUser_hdr s γa who tok hm $$ [Hb Hseen Htls]
  · iframe Hb Hseen Htls
  imodintro
  ipureintro
  exact ⟨r, hm, by rw [← hr]; exact (grantedAt_iff _ _ _ _).1 hgr, Hu⟩

/-- **A write of `who`'s, told its grant, was granted at `setupSt`** (layer 2): the grant
(`clientGrant` at the set-up's log `Lset`) of an attempt of a context with `who`'s outgoing
metadata (`akTokSeen_attempt`, `akGranted_of_writeGrantG`). -/
theorem akOpGranted_of_grant (s : Loc) (E : apply.AEnv GF) (γa : auth.AuthNames) (ρ : ReqNames)
    (Lset : List EntryModel) (n : Nat) (who : GoString) (conn : Loc) (ctx : GoInterface)
    (op : KVOp) (σ : KVState) (Em : CoPset) (hγa : E.authMode = .on γa)
    (hout : metadata.outgoingOf ctx = akOut who) (hE : ↑authHistN ⊆ Em) :
    akAuthFixed (GF := GF) γa ρ Lset n ∗ attemptTokOk conn (akTokP γa who) ∗
      □ (srvTLSId s -∗ False) ⊢
      client.clientGrant s E ρ conn ctx op Lset σ ={Em}=∗ ⌜akOpGranted who op⌝ := by
  iintro ⟨#Hf, #Hat, #Htls⟩ Hg
  unfold client.clientGrant
  icases Hg with ⟨%md, %Hmd, Hg⟩
  have Hmd' : clientAttemptMdOf conn (akOut who) md := by rw [← hout]; exact Hmd
  ihave #Hseen := akTokSeen_attempt γa who conn md Hmd' $$ Hat
  cases op with
  | put o =>
    simp only [v3rpc.opGrantT, akOpGranted]
    iapply (akGranted_of_writeGrantG s E γa ρ Lset n who _ _ σ Em hγa hE) $$ [] Hg
    iframe Hf Hseen Htls
  | deleteRange o =>
    simp only [v3rpc.opGrantT, akOpGranted]
    iapply (akGranted_of_writeGrantG s E γa ρ Lset n who _ _ σ Em hγa hE) $$ [] Hg
    iframe Hf Hseen Htls
  | txn t =>
    simp only [v3rpc.opGrantT, akOpGranted]
    icases Hg with ⟨%tw, %Htw, Hg⟩
    imod (akGranted_of_writeGrantG s E γa ρ Lset n who _ _ σ Em hγa hE) $$ [] Hg with %H
    · iframe Hf Hseen Htls
    imodintro; ipureintro; exact ⟨tw, Htw, H⟩
  | _ => imodintro; ipureintro; simp [akOpGranted]

end grant

end authkv
end EtcdGrove
end Perennial
