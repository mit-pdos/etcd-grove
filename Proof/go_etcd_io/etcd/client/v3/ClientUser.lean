/-
**C1: a user client's attempts carry its user's token** (the auth plan's C1, 2026-10-28;
`notes/c1-plan.md`). Lean-first (no Rocq counterpart).

A client built with a user name dials with its token bundle's per-RPC credentials, whose tokens
are `""` or meet `P` (`tokenBundleInv`, `tokMdOk`); grpc sends each attempt the credentials'
metadata before the context's (`grpcAttemptMd`), so the token the handler sees (`auth.mdTokenOf`,
what the server's `AuthInfoFromCtx` reads) is one meeting `P`, trimmed of `"Bearer "`, or, when
the bundle holds none, the context's own (`clientAttempt_tok`). With `P` the server's issue to the
user (`auth.tokIssued γa · u`) that is C1, `userClientAt`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.KVServiceOn
public import Proof.go_etcd_io.etcd.client.v3.InvClientAuth

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-! ## The token of an attempt's metadata, from its two keys -/

/-- `auth.mdTokenOf` reads the keys `token` and `authorization` only. -/
theorem auth.mdTokenOf_eq [GooseExts] (md : GrpcMd) :
    auth.mdTokenOf md =
      match mdGet md go!"token" with
      | some (v :: _) => some (strings.trimPrefix v go!"Bearer ")
      | some [] => none
      | none =>
        match mdGet md go!"authorization" with
        | some (v :: _) => some (strings.trimPrefix v go!"Bearer ")
        | _ => none := by
  cases md <;> rfl

theorem auth.mdTokenOf_congr [GooseExts] (md md' : GrpcMd)
    (ht : mdGet md go!"token" = mdGet md' go!"token")
    (ha : mdGet md go!"authorization" = mdGet md' go!"authorization") :
    auth.mdTokenOf md = auth.mdTokenOf md' := by
  rw [auth.mdTokenOf_eq, auth.mdTokenOf_eq, ht, ha]

theorem grpcReservedKey_token : ¬ grpcReservedKey go!"token" := by
  unfold grpcReservedKey; decide

theorem grpcReservedKey_authorization : ¬ grpcReservedKey go!"authorization" := by
  unfold grpcReservedKey; decide

theorem mdGet_mdSet_ne (md : GrpcMd) (k k' : GoString) (vs : List GoString) (h : k' ≠ k) :
    mdGet (metadata.mdSet md k vs) k' = mdGet md k' := by
  unfold mdGet metadata.mdSet
  simp [h]

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **C1** (the auth plan's C1; E2f's `userAttemptOk` over the attempt's metadata): the handler
of every attempt of a call with the context `ctx` on the connection `conn` sees a token issued to
`u` at the member's names `γa` (trimmed of `"Bearer "`, as the server reads it), or the context's
own (the bundle held none yet, or `Authenticate` answered that auth is off). -/
def userClientAt (conn : Loc) (γa : auth.AuthNames) (u : GoString) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterface) (md : GrpcMd), ⌜clientAttemptMd conn ctx md⌝ -∗
    (∃ t, ⌜auth.mdTokenOf md = some (strings.trimPrefix t go!"Bearer ")⌝ ∗
      auth.tokIssued (GF := GF) γa t u) ∨
    ⌜auth.mdTokenOf md = auth.mdTokenOf (metadata.outgoingOf ctx)⌝)

instance userClientAt_persistent (conn : Loc) (γa : auth.AuthNames) (u : GoString) :
    Persistent (userClientAt (GF := GF) conn γa u) := by
  unfold userClientAt; infer_instance

/-- **An attempt's token** on a connection whose credentials' tokens meet `P` (`connTokOk`): one
meeting `P`, trimmed, or the context's own. -/
theorem clientAttempt_tok (conn : Loc) (P : GoString → IProp GF) (ctx : GoInterface)
    (md : GrpcMd) (h : clientAttemptMd conn ctx md) :
    connTokOk conn P ⊢
      (∃ t, ⌜auth.mdTokenOf md = some (strings.trimPrefix t go!"Bearer ")⌝ ∗ □ P t) ∨
      ⌜auth.mdTokenOf md = auth.mdTokenOf (metadata.outgoingOf ctx)⌝ := by
  obtain ⟨c, v, hc, cm, hy, hmd⟩ := h
  have hot : ∀ k, k ≠ go!"client-api-version" →
      mdGet (metadata.outgoingOf c) k = mdGet (metadata.outgoingOf ctx) k := by
    intro k hk; rw [hc]; exact mdGet_mdSet_ne _ _ _ _ hk
  have htok := hmd _ grpcReservedKey_token
  have hauth := hmd _ grpcReservedKey_authorization
  unfold mdMergeAt at htok hauth
  rw [hot _ (by decide)] at htok
  rw [hot _ (by decide)] at hauth
  unfold connTokOk
  iintro #H
  ihave #Hq := H $$ %cm %hy
  unfold tokMdOk
  icases Hq with ⟨%hoth, (%hnone | ⟨%t, %ht, #Hp⟩)⟩
  · iright
    ipureintro
    apply auth.mdTokenOf_congr
    · rw [htok, hnone]
    · rw [hauth, hoth _ (by decide)]
  · ileft
    iexists t
    iframe Hp
    ipureintro
    rw [auth.mdTokenOf_eq, htok, ht]
    cases mdGet (metadata.outgoingOf ctx) go!"token" <;> rfl

/-- C1 from a connection whose credentials' tokens are issued to `u` at `γa`. -/
theorem userClientAt_of (conn : Loc) (γa : auth.AuthNames) (u : GoString) :
    connTokOk (GF := GF) conn (fun t => auth.tokIssued γa t u) ⊢ userClientAt conn γa u := by
  iintro #H
  unfold userClientAt
  iintro !> %ctx %md %h
  icases clientAttempt_tok conn _ ctx md h $$ H with (⟨%t, %ht, #Hp⟩ | %he)
  · ileft
    iexists t
    iframe Hp
    ipureintro; exact ht
  · iright; ipureintro; exact he

/-- **C1 for a client `New` built with the user name `u`** (at `clientAuthPre`'s `P` the tokens
`Authenticate` issues to `u`, `authTokReg_of`): its `KV` over a connection whose attempts carry a
token issued to `u` or the context's own. -/
theorem clientTokAt_user (cl : Loc) (eps : List GoString) (γa : auth.AuthNames) (u : GoString) :
    clientTokAt (GF := GF) cl eps (fun t => auth.tokIssued γa t u) ⊢
      ∃ api conn : Loc,
        structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api :
            GoInterface) ∗
        kvObjAtC api conn eps ∗ userClientAt conn γa u := by
  unfold clientTokAt
  iintro ⟨%api, %conn, #Hkv, #Hobj, #Htok⟩
  iexists api, conn
  iframe Hkv Hobj
  iapply userClientAt_of
  iexact Htok

end defs

end EtcdGrove
end Perennial
