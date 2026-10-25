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

What this file proves is the one fact of the contract about a token rather than a client: the
bad principal's token (`badToken`, `"badtoken"`) is not one the simple provider makes
(`simpleTok_ne_badToken`): every token its `assign` issues is `<prefix>.<raft index>`
(`auth.simpleTok`), which has a dot. With the invariant that every token issued in the server's
mode is the simple provider's (a fact E2a's `NewAuthStore` will have to state: the right to issue
a token, `authnCtx`'s `freshOk`, is only ever given for a `simpleTok`), the bad principal's
requests have no principal (`ctxBound`'s `null` case, refused: `granted_rev0`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Model
public import Proof.go_etcd_io.etcd.server.v3.auth.Tokens

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

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

end authkv
end EtcdGrove
end Perennial
