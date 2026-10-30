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

end authkv
end EtcdGrove
end Perennial
