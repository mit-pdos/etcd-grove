/-
**`grantIds`/`grantRest` over `apply.Apply`'s outcome** (the lease-grant stage, 2026-11-02;
`notes/lease-grant-plan.md`, "Design of the server chain", 2.0 and 2.10, and its Freeze,
amendment (B)): `grantIdsA rq v3 out L`, `grantRestA t rq v3 out r` are `grantIds`/`grantRest`
(`apply/Chain.lean`) of a dispatched request's outcome, the identity for any other `ApplyOut`, for
`Apply.spec`'s post. The rest of the grant's pure vocabulary is in `apply/RestLease.lean`
(`restGrantT`, `grantIdsOk`, `restLeasesWith`) and `apply/Chain.lean` (`grantGoes`, `grantIds`,
`grantRest`), where the triples need it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvUber
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.RestLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

/-- `grantIds` over `apply.Apply`'s outcome: a dispatched request's. -/
def grantIdsA (rq : IRRModel) (v3 : Bool) (out : ApplyOut) (L : List w64) : List w64 :=
  match out with
  | .dispatched o _ => grantIds rq v3 o L
  | _ => L

/-- `grantRest` over `apply.Apply`'s outcome: a dispatched request's. -/
def grantRestA (t : w64) (rq : IRRModel) (v3 : Bool) (out : ApplyOut) (r : RestM) : RestM :=
  match out with
  | .dispatched o _ => grantRest t rq v3 o r
  | _ => r

/-- `grantOutOk` over `apply.Apply`'s outcome: a dispatched request's (amendment (C)); vacuous for
any other `ApplyOut`. -/
def grantOutOkA (c : Chain) (rq : IRRModel) (v3 : Bool) (T : List w64) (out : ApplyOut) : Prop :=
  match out with
  | .dispatched o _ => grantOutOk c rq v3 T o
  | _ => True

/-- `revokeIds` over `apply.Apply`'s outcome (the lease-expiry plan's X7): a dispatched request's. -/
def revokeIdsA (rq : IRRModel) (v3 : Bool) (out : ApplyOut) (L : List w64) : List w64 :=
  match out with
  | .dispatched o _ => revokeIds rq v3 o L
  | _ => L

/-- `revokeRest` over `apply.Apply`'s outcome: a dispatched request's. -/
def revokeRestA (T : List w64) (rq : IRRModel) (v3 : Bool) (out : ApplyOut) (r : RestM) : RestM :=
  match out with
  | .dispatched o _ => revokeRest T rq v3 o r
  | _ => r

theorem revokeIdsA_nonRevoke (rq : IRRModel) (v3 : Bool) (out : ApplyOut) (L : List w64)
    (h : dispatchKind rq ≠ .leaseRevoke) : revokeIdsA rq v3 out L = L := by
  unfold revokeIdsA; split
  · exact revokeIds_nonRevoke _ _ _ _ h
  · rfl

theorem revokeRestA_nonRevoke (T : List w64) (rq : IRRModel) (v3 : Bool) (out : ApplyOut)
    (r : RestM) (h : dispatchKind rq ≠ .leaseRevoke) : revokeRestA T rq v3 out r = r := by
  unfold revokeRestA; split
  · exact revokeRest_nonRevoke _ _ _ _ _ h
  · rfl

theorem revokeIdsA_not_dispatched (rq : IRRModel) (v3 : Bool) (out : ApplyOut) (L : List w64)
    (h : ∀ o sk, out ≠ .dispatched o sk) : revokeIdsA rq v3 out L = L := by
  cases out with
  | dispatched o sk => exact absurd rfl (h o sk)
  | _ => rfl

theorem revokeRestA_not_dispatched (T : List w64) (rq : IRRModel) (v3 : Bool) (out : ApplyOut)
    (r : RestM) (h : ∀ o sk, out ≠ .dispatched o sk) : revokeRestA T rq v3 out r = r := by
  cases out with
  | dispatched o sk => exact absurd rfl (h o sk)
  | _ => rfl

theorem grantIdsA_not_dispatched (rq : IRRModel) (v3 : Bool) (out : ApplyOut) (L : List w64)
    (h : ∀ o sk, out ≠ .dispatched o sk) : grantIdsA rq v3 out L = L := by
  cases out with
  | dispatched o sk => exact absurd rfl (h o sk)
  | _ => rfl

theorem grantRestA_not_dispatched (t : w64) (rq : IRRModel) (v3 : Bool) (out : ApplyOut) (r : RestM)
    (h : ∀ o sk, out ≠ .dispatched o sk) : grantRestA t rq v3 out r = r := by
  cases out with
  | dispatched o sk => exact absurd rfl (h o sk)
  | _ => rfl

theorem grantIdsA_nonGrant (rq : IRRModel) (v3 : Bool) (out : ApplyOut) (L : List w64)
    (h : dispatchKind rq ≠ .leaseGrant) : grantIdsA rq v3 out L = L := by
  unfold grantIdsA; split
  · exact grantIds_nonGrant _ _ _ _ h
  · rfl

theorem grantRestA_nonGrant (t : w64) (rq : IRRModel) (v3 : Bool) (out : ApplyOut) (r : RestM)
    (h : dispatchKind rq ≠ .leaseGrant) : grantRestA t rq v3 out r = r := by
  unfold grantRestA; split
  · exact grantRest_nonGrant _ _ _ _ _ h
  · rfl

/-- **The record a grant puts, in the leased image** (`srvRest_applyG`): the rest after the
outcome of the image of `T` at `f` is the image of the ids after it at some `f'` (a grant applied
puts a record of an id not in `T`, by `grantOutOk`). -/
theorem grantRestA_leases (c : Chain) (t : w64) (rq : IRRModel) (v3 : Bool) (out : ApplyOut)
    (f : w64 → w64) (T : List w64) (R : RestM) (hgo : grantOutOkA c rq v3 T out) :
    ∃ f' : w64 → w64, grantRestA t rq v3 out (restLeasesWith f T R) =
      restLeasesWith f' (grantIdsA rq v3 out T) R := by
  cases out with
  | skipped => exact ⟨f, rfl⟩
  | rejected => exact ⟨f, rfl⟩
  | dispatched o sk =>
    simp only [grantRestA, grantIdsA, grantOutOkA] at hgo ⊢
    by_cases hc : dispatchKind rq = .leaseGrant ∧ v3 = true
    · cases hgl : rq.leaseGrant with
      | none => exact ⟨f, by rw [grantRest_none _ _ _ _ _ hgl, grantIds_none _ _ _ _ hgl]⟩
      | some g =>
        obtain ⟨hk, hv⟩ := hc
        subst hv
        cases o with
        | rejected e => exact ⟨f, by rw [grantRest_rejected, grantIds_rejected]⟩
        | applied l ns =>
          have hok := (hgo hk rfl g hgl).1 ⟨l, ns, rfl⟩
          refine ⟨updFn f g.id t, ?_⟩
          rw [grantRest_applied _ _ g _ _ _ hk hgl, grantIds_applied _ g _ _ _ hk hgl]
          exact restLeasesWith_snoc f T g.id t R hok.2.2.2
    · refine ⟨f, ?_⟩
      unfold grantRest grantIds
      rw [if_neg hc, if_neg hc]

theorem grantIdsA_none (rq : IRRModel) (v3 : Bool) (out : ApplyOut) (L : List w64)
    (h : rq.leaseGrant = none) : grantIdsA rq v3 out L = L := by
  unfold grantIdsA; split
  · exact grantIds_none _ _ _ _ h
  · rfl

theorem grantRestA_none (t : w64) (rq : IRRModel) (v3 : Bool) (out : ApplyOut) (r : RestM)
    (h : rq.leaseGrant = none) : grantRestA t rq v3 out r = r := by
  unfold grantRestA; split
  · exact grantRest_none _ _ _ _ _ h
  · rfl

end apply
end EtcdGrove
end Perennial
