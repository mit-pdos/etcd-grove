/-
**The principals of authkv's requests: the client's auth side as a contract** (the auth plan's
E2b, 2026-10-25; `notes/decisions.md`, "E2b of the auth plan", which states the contract in
full). Lean-first (no Rocq counterpart).

`Main`'s check attributes a write to the principal whose key it is (`x/<who>/...`), so its proof
needs to know which principal the server sees for each request a client sends: the server's
`AuthInfoFromCtx` reads the token in the request's incoming metadata, and the client puts it
there. The clientv3 side of auth is out of the verified code (D-AU6), so what it does is a
contract with four parts (C1-C4 in the decision): a client built with a user name sends with each
attempt no token or one the server issued to that user (`tokIssued`; it got it from
`Authenticate`, whose server side S5 proved); a client with no user name adds no token, so an
attempt carries its caller's outgoing metadata only; `metadata.AppendToOutgoingContext(ctx,
"token", t)` adds `t`; and gRPC delivers an attempt's outgoing metadata as the handler's incoming
metadata.

**The contract over the contexts' metadata** (the auth plan's E2f, 2026-10-25): the four parts
as statements over a request context's incoming metadata (`metadata.incomingOf`, what the
server's `AuthInfoFromCtx` reads, `auth.ctxTokenOf`) and a call's outgoing metadata
(`metadata.outgoingOf`):
- C1 (`userAttemptOk`): the handler context of an attempt of a client built with the user name
  `u` carries no token or one issued to `u` (`auth.tokIssued`);
- C2 and C4 (`deliversOutgoing`): the handler context of an attempt of a client with no user name
  carries its caller's outgoing metadata, as it is;
- C3 is the spec `metadata.AppendToOutgoingContext.spec` (a trust-boundary axiom: grpc's
  `metadata` is names-only), which `reqCtx`'s proof uses: the bad principal's context has the
  outgoing token values of its timeout context with `badtoken` appended.
The bad principal's request is then unbound (`badCtx_unbound`): a handler context delivering
outgoing metadata whose only token value is `badtoken` gives the server's `AuthInfoFromCtx` no
auth info in the mode `on γa`. That the timeout context `reqCtx` starts from has no outgoing
metadata is the trust-boundary spec `context.WithTimeoutBackgroundMd.spec` (5b, 2026-10-29; true
of Go: only grpc stores under its metadata key; Perennial's context model does not describe values
at other keys, `ContextDesc.Values` unused), which `SetUp` uses; `reqCtx`'s spec does not yet.

What this file proves besides is the one fact of the contract about a token rather than a client: the
bad principal's token (`badToken`, `"badtoken"`) is not one the simple provider makes
(`simpleTok_ne_badToken`): every token its `assign` issues is `<prefix>.<raft index>`
(`auth.simpleTok`), which has a dot. Every token issued in the server's mode has the simple
provider's shape (`auth.tokIssued_shape`, the auth plan's E2c), so the bad token was issued to no
one (`tokIssued_badToken`), and the bad principal's requests have no principal (`ctxBound`'s `null`
case, refused: `granted_rev0`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Model
public import Proof.go_etcd_io.etcd.server.v3.auth.Tokens
public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth
public import Proof.google_golang_org.grpc.metadata.Outgoing

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProofMode

/-- The token the bad principal sends (`authkv.go`'s `badToken`). -/
abbrev badToken : GoString := go!"badtoken"

/-- **The bad token is not one the simple provider makes**: every token of `simpleTok` has a dot
(`.`, byte `46`), and `badtoken` has none. -/
theorem simpleTok_ne_badToken (pre : GoString) (idx : w64) : auth.simpleTok pre idx ≠ badToken := by
  intro h
  have hmem : (46 : w8) ∈ auth.simpleTok pre idx := by
    simp [auth.simpleTok]
  rw [h] at hmem
  revert hmem
  decide

/-- **The bad token was issued to no one** (E2c): an issued token has the simple provider's shape
(`auth.tokIssued_shape`). -/
theorem tokIssued_badToken {GF : BundledGFunctors} [AllG GF] (γa : auth.AuthNames) (u : GoString) :
    auth.tokIssued (GF := GF) γa badToken u ⊢ False := by
  iintro H
  ihave %Hsh := auth.tokIssued_shape γa badToken u $$ H
  obtain ⟨pre, idx, h, -⟩ := Hsh
  exact absurd h.symm (simpleTok_ne_badToken pre idx)

/-! ## The contract over the contexts' metadata (C1, C2, C4) -/

section contract
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **C1**: the handler context `h` of an attempt of a client built with the user name `u`
carries no token, or one issued to `u` at the auth names `γa` of the member it reached. -/
def userAttemptOk (γa : auth.AuthNames) (u : GoString) (h : GoInterface) : IProp GF :=
  iprop(⌜auth.ctxTokenOf h = none⌝ ∨
    ∃ t : GoString, ⌜auth.ctxTokenOf h = some t⌝ ∗ auth.tokIssued γa t u)

/-- **C2 and C4**: the handler context `h` of an attempt of a client with no user name, called
with the context `c`, carries `c`'s outgoing metadata as its incoming metadata. -/
def deliversOutgoing (c h : GoInterface) : Prop :=
  metadata.incomingOf h = metadata.outgoingOf c

end contract

theorem trimPrefix_badToken : strings.trimPrefix badToken go!"Bearer " = badToken := by
  unfold strings.trimPrefix; decide

/-- The token of a handler context delivering outgoing metadata whose token values are
`[badtoken]`. -/
theorem ctxTokenOf_bad [GooseExts] (c h : GoInterface) (hd : deliversOutgoing c h)
    (ht : metadata.mdVals (metadata.outgoingOf c) go!"token" = [badToken]) :
    auth.ctxTokenOf h = some badToken := by
  unfold auth.ctxTokenOf
  rw [hd]
  unfold metadata.mdVals at ht
  cases ho : metadata.outgoingOf c with
  | none => rw [ho] at ht; simp at ht
  | some md =>
    rw [ho] at ht
    simp only [Option.bind_some] at ht
    cases hm : md go!"token" with
    | none => rw [hm] at ht; simp at ht
    | some vs =>
      rw [hm] at ht
      simp only [Option.getD_some] at ht
      subst ht
      simp only [hm, trimPrefix_badToken]

section bound
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The bad principal's request has no principal** (C2, C4 and E2c's facts): the auth info the
server's `AuthInfoFromCtx` gives for a handler context delivering outgoing metadata whose token
values are `[badtoken]` is `nil`, in the mode `on γa`. -/
theorem badCtx_unbound (γa : auth.AuthNames) (c h : GoInterface) (a : Loc)
    (hd : deliversOutgoing c h)
    (ht : metadata.mdVals (metadata.outgoingOf c) go!"token" = [badToken]) :
    auth.ctxBound (GF := GF) (.on γa) h a ⊢ ⌜a = null⌝ := by
  iintro H
  unfold auth.ctxBound
  icases H with (%Ha | ⟨%t, %Ht, Hb⟩)
  · ipureintro; exact Ha
  · rw [ctxTokenOf_bad c h hd ht] at Ht
    cases Ht
    unfold auth.infoBound
    icases Hb with ⟨-, %u, -, Hu⟩
    simp only [auth.tokOk]
    iexfalso
    iapply (tokIssued_badToken (GF := GF) γa u)
    iexact Hu

end bound

end authkv
end EtcdGrove
end Perennial
