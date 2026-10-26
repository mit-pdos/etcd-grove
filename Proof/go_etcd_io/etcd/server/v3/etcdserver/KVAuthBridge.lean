/-
**The auth applier's verdicts in the model's terms** (the auth plan's E2s, 2026-10-26;
`notes/decisions.md`, "E2s of the auth plan"). The auth applier's KV methods on the apply thread
decide their outcome at the latest state one checked permission at a time (`apply.authOutL`,
`apply.granted1`, `apply/AuthApplyLatest*.lean`); the model decides a KV entry at once
(`kvGranted`, `KVAuthModel.lean`). The two agree on the request's own permissions
(`reqPerms`): each permission of a granted request is granted (`granted1_of_kvGranted`), and a
request whose permissions are each granted is granted when it needs at least one
(`kvGranted_of_granted1`). With none (a transaction without comparisons or operations) the checks
pass while `kvGranted` asks the principal's revision and user: the model would refuse what the
code applies (both keep the log: such a transaction writes nothing).
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
variable [ext : FfiSyntax]

/-- **A granted request's permissions are each granted.** -/
theorem granted1_of_kvGranted (st : auth.AuthState) (rq : apply.IRRModel) (x : apply.Perm3)
    (hx : x ∈ reqPerms rq) (h : kvGranted st rq) :
    apply.granted1 st (auth.authInfoM (apply.principalOf rq)) x := by
  unfold apply.granted1
  rcases h with hd | ⟨h0, hr, u, hu, hc⟩
  · exact Or.inl hd
  · refine Or.inr ⟨h0, hr, u, hu, ?_⟩
    rcases hc with hroot | hcov
    · exact Or.inl hroot
    · exact Or.inr (hcov x hx)

/-- **A request whose permissions, at least one, are each granted is granted.** -/
theorem kvGranted_of_granted1 (st : auth.AuthState) (rq : apply.IRRModel)
    (hne : reqPerms rq ≠ [])
    (h : ∀ x ∈ reqPerms rq, apply.granted1 st (auth.authInfoM (apply.principalOf rq)) x) :
    kvGranted st rq := by
  obtain ⟨x0, hx0⟩ := List.exists_mem_of_ne_nil _ hne
  unfold apply.granted1 at h
  unfold kvGranted
  by_cases hen : st.enabled = false
  · exact Or.inl hen
  · rcases h x0 hx0 with hd | ⟨h0, hr, u, hu, hc0⟩
    · exact absurd hd hen
    · refine Or.inr ⟨h0, hr, u, hu, ?_⟩
      by_cases hroot : auth.isRoot u
      · exact Or.inl hroot
      · refine Or.inr fun x hx => ?_
        rcases h x hx with hd | ⟨-, -, u', hu', hc⟩
        · exact absurd hd hen
        · rw [hu] at hu'; cases hu'
          rcases hc with hr' | hcov
          · exact absurd hr' hroot
          · exact hcov

/-- **The checks' verdict at the latest state is the model's**: for checked permissions that are
the request's own (`L = reqPerms rq`, at least one), a pass is `kvGranted` at the latest state and
a refusal its negation. -/
theorem kvGranted_of_passedL (γa : auth.AuthNames) (hs : List auth.AuthState) (stl : auth.AuthState)
    (hl : hs.getLast? = some stl) (rq : apply.IRRModel) (hne : reqPerms rq ≠ [])
    (h : apply.passedL (.on γa) hs (auth.authInfoM (apply.principalOf rq)) (reqPerms rq)) :
    kvGranted stl rq :=
  kvGranted_of_granted1 stl rq hne (h stl hl)

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
