/-
**The auth applier's verdicts in the model's terms** (the auth plan's E2s, 2026-10-26;
`notes/decisions.md`, "E2s of the auth plan"). The auth applier's KV methods on the apply thread
decide their outcome at the latest state one checked permission at a time (`apply.authOutL`,
`apply.granted1`, `apply/AuthApplyLatest*.lean`); the model decides a KV entry at once
(`kvGranted`, `KVAuthModel.lean`). The two agree on the request's own permissions
(`reqPerms`): `kvGranted` is, by definition since E2v, each of the request's permissions granted
(`granted1_of_kvGranted`, `kvGranted_of_granted1`), so a request needing none (a transaction
without comparisons or operations) is granted, as the code applies it unchecked.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVAuthModel
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthLatest

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

section pure
variable [GooseExts]

/-- **A granted request's permissions are each granted.** -/
theorem granted1_of_kvGranted (st : auth.AuthState) (rq : apply.IRRModel) (x : apply.Perm3)
    (hx : x ∈ reqPerms rq) (h : kvGranted st rq) :
    apply.granted1 st (auth.authInfoM (apply.principalOf rq)) x :=
  h x hx

/-- **A request whose permissions are each granted is granted** (none at all included). -/
theorem kvGranted_of_granted1 (st : auth.AuthState) (rq : apply.IRRModel)
    (h : ∀ x ∈ reqPerms rq, apply.granted1 st (auth.authInfoM (apply.principalOf rq)) x) :
    kvGranted st rq :=
  h

/-- **The checks' verdict at the latest state is the model's**: for checked permissions that are
the request's own (`L = reqPerms rq`), a pass is `kvGranted` at the latest state and
a refusal its negation. -/
theorem kvGranted_of_passedL (γa : auth.AuthNames) (hs : List auth.AuthState) (stl : auth.AuthState)
    (hl : hs.getLast? = some stl) (rq : apply.IRRModel)
    (h : apply.passedL (.on γa) hs (auth.authInfoM (apply.principalOf rq)) (reqPerms rq)) :
    kvGranted stl rq :=
  kvGranted_of_granted1 stl rq (h stl hl)

theorem not_kvGranted_of_refusedL (γa : auth.AuthNames) (hs : List auth.AuthState)
    (stl : auth.AuthState) (hl : hs.getLast? = some stl) (rq : apply.IRRModel) (L : List apply.Perm3)
    (hL : ∀ x ∈ L, x ∈ reqPerms rq)
    (h : apply.refusedL (.on γa) hs (auth.authInfoM (apply.principalOf rq)) L) :
    ¬ kvGranted stl rq := by
  intro hg
  obtain ⟨x, hx, hn⟩ := h stl hl
  exact hn (granted1_of_kvGranted stl rq x (hL x hx) hg)

end pure

end EtcdGrove
end Perennial
