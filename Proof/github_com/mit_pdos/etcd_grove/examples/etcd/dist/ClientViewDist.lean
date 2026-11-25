/-
**DRAFTS of the lease calls' interim contracts at the cluster view** (`notes/etcd-dist-plan.md` §18.4; #50,
the etcd_safe lead, 2026-11-25). Lean-first (no Rocq counterpart).

STATEMENTS ONLY: definitions, no axiom, no proof, no `sorry`. Nothing imports this file. The four that read
the view's lessor names (`Lease_Grant_dist`, `Lease_GrantLive_dist`, `Lease_LeasesGranted_dist`,
`Lease_LeasesLive_dist`) wait for the Prove item P-L1 (`NewServer` taking the lessor's name from the start,
§18.3); the two view-free ones are etcd-grove-03's (`etcd-safe-n9b`), re-indexed by the view, waiting for that
branch. The KV calls' contracts were adopted on 2026-11-25 (O1 option B) as the interim axioms of
`KVPutDist.lean`, `KVGetDist.lean`, `KVDeleteDist.lean`, `KVCompactDist.lean`, `TxnCommitDist.lean`.

At adoption each draft moves to its own Spec/Proof pair, gets an `axiom`-skill review, and joins the
etcd_safe packet.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.S2Interim
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Proof.go_etcd_io.etcd.client.v3.InvClientNew
public import Proof.go_etcd_io.etcd.client.v3.InvLease
public import Proof.go_etcd_io.etcd.client.v3.InvLeaseGrant
public import Proof.go_etcd_io.etcd.client.v3.InvLeaseRead

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace view

open Iris Iris.BI Net client go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

/-! ## The lease calls (one endpoint: `LeaseLeases` is a member-local read) -/

section lease
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- What every lease draft takes of the client: `New`'s client `cl` of the one endpoint `ep` (no
proxy), its `Lease` field the `*lessor` `lp`, `ep` serving member `mid` of `Γ`. -/
def leaseClientAt [π : NetProtoGS] (cl lp : Loc) (ep : GoString)
    (V : WEnv GF) (Γ : DistView) (mid : w64) : IProp GF :=
  iprop(isNewClient cl [ep] V ∗ clientNoProxy cl ∗
    clientF cl go!"Lease" ↦□
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty) #lp : GoInterface) ∗
    etcdAddrAt (Gg := hG.goose_globalGS) ep Γ mid)

/-- **DRAFT `Lease_Grant_dist`: `(*lessor).Grant(ctx, ttl)` at member `mid`, monotone lease mode**
(mirrors `lessor.Grant.spec` at `etcdLeaseGrantSpec γl`, i.e. `etcdLeaseGrantSpecW`, `γl := Γ.ls mid`;
`etcdReached` dropped: no workload reads it). Reads the lessor name: an axiom only after P-L1. -/
abbrev Lease_Grant_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (ttl : w64),
  Γ.kv.lm = .mono →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      leaseClientAt cl lp ep V Γ mid ∗ ctxOk ctx cd ∗ ctxErrClient ctx cd }}
    (App (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Grant"))
      (Val #(GoInterface.ok ctx))) (Val #ttl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ m : LeaseGrantRespM,
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"ID" resp ↦□ m.id ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"TTL" resp ↦□ m.ttl ∗
        ⌜m.id ≠ W64 0⌝ ∗ ∃ i : Nat, lease.leaseGrantedAt (Γ.ls mid) i m.id) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- **DRAFT `Lease_GrantLive_dist`: `(*lessor).Grant(ctx, ttl)` at member `mid`, revocable lease
mode** (mirrors `lessor.Grant.spec` at `etcdLeaseGrantSpecLive γl`, i.e. `etcdLeaseGrantSpecLiveW`;
clientv3's `Grant` sends `ID = 0`, the filter's request). After P-L1 only. -/
abbrev Lease_GrantLive_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (ttl : w64),
  Γ.kv.lm = .revocable →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      leaseClientAt cl lp ep V Γ mid ∗ ctxOk ctx cd ∗ ctxErrClient ctx cd }}
    (App (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Grant"))
      (Val #(GoInterface.ok ctx))) (Val #ttl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ m : LeaseGrantRespM,
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"ID" resp ↦□ m.id ∗
        structFieldRef go_etcd_io.etcd.client.v3.LeaseGrantResponse go!"TTL" resp ↦□ m.ttl ∗
        ⌜m.id ≠ W64 0⌝ ∗ ∃ (i : Nat) (l : Loc),
          lease.leaseLiveFrom (Γ.ls mid) i m.id l ∗ lease.leaseReqIs (Γ.ls mid) m.id ttl) ∨
      ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- **DRAFT `Lease_LeasesGranted_dist`: `(*lessor).Leases(ctx)` at member `mid`, monotone mode**
(mirrors `lessor.Leases.spec` at `etcdLeaseLeasesSpec γl`, i.e. `etcdLeaseLeasesSpecW`): the caller's
grants `G` at this member's lessor are all listed, no id twice. After P-L1 only. -/
abbrev Lease_LeasesGranted_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (G : List w64),
  Γ.kv.lm = .mono →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      leaseClientAt cl lp ep V Γ mid ∗ ctxOk ctx cd ∗ ctxErrClient ctx cd ∗
      [∗list] id ∈ G, ∃ i : Nat, lease.leaseGrantedAt (Γ.ls mid) i id }}
    (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Leases"))
      (Val #(GoInterface.ok ctx)))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (ids : List w64) (sl : GoSlice),
          structFieldRef go_etcd_io.etcd.client.v3.LeaseLeasesResponse go!"Leases" resp ↦□ sl ∗
          sl ↦* (ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id))) ∗
          ⌜ids.Nodup ∧ ∀ id ∈ G, id ∈ ids⌝) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- **DRAFT `Lease_LeasesLive_dist`: `(*lessor).Leases(ctx)` at member `mid`, revocable mode**
(mirrors `lessor.Leases.spec` at `etcdLeaseLeasesSpecLive γl`, i.e. `etcdLeaseLeasesSpecLiveW`): the
caller's lower bound `n` of the member's lessor history; the listing is the ids of a snapshot at an
index `≥ n` (`leaseIdsAt`, no id twice). After P-L1 only. -/
abbrev Lease_LeasesLive_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (n : Nat),
  Γ.kv.lm = .revocable →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      leaseClientAt cl lp ep V Γ mid ∗ ctxOk ctx cd ∗ ctxErrClient ctx cd ∗
      lease.lessorLb (Γ.ls mid) n }}
    (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Leases"))
      (Val #(GoInterface.ok ctx)))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (ids : List w64) (sl : GoSlice) (j : Nat),
          structFieldRef go_etcd_io.etcd.client.v3.LeaseLeasesResponse go!"Leases" resp ↦□ sl ∗
          sl ↦* (ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id))) ∗
          ⌜n ≤ j⌝ ∗ lease.leaseIdsAt (Γ.ls mid) j ids) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- **`Client_LeaseLeases_dist` (etcd-grove-03's draft, `etcd-safe-n9b` b0076abbbe) re-indexed by the
view**: the body unchanged but for `etcdAddrAt ep γE mid` → `etcdAddrAt ep Γ mid` (inside
`leaseClientAt`) and `levelTok 0` threaded (see §18.7). View-free (`etcdLeaseLeasesSpecAnyW`): any lease
mode. -/
abbrev Client_LeaseLeases_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      leaseClientAt cl lp ep V Γ mid ∗ ctxOk ci cd ∗ ctxErrClient ci cd }}
    (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Leases"))
      (Val #(GoInterface.ok ci)))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (ids : List w64) (sl : GoSlice),
          structFieldRef go_etcd_io.etcd.client.v3.LeaseLeasesResponse go!"Leases" resp ↦□ sl ∗
          sl ↦* (ids.map (fun id => (go_etcd_io.etcd.client.v3.LeaseStatus.mk id))) ∗ ⌜ids.Nodup⌝) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

/-- **`Client_LeaseTimeToLive_dist` (etcd-grove-03's draft) re-indexed by the view**, as
`Client_LeaseLeases_dist` above. View-free (`etcdLeaseTTLSpecW`), the call without options. -/
abbrev Client_LeaseTimeToLive_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (cl lp : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗
      leaseClientAt cl lp ep V Γ mid ∗ ctxOk ci cd ∗ ctxErrClient ci cd }}
    (App (App (App (Val (lp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!!
        go!"TimeToLive")) (Val #(GoInterface.ok ci))) (Val #id)) (Val #slice.nil))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); levelTok 0 ∗
      ((⌜err = GoInterface.nil⌝ ∗
          structFieldRef go_etcd_io.etcd.client.v3.LeaseTimeToLiveResponse go!"ID" resp ↦□ id) ∨
        ⌜err ≠ GoInterface.nil ∧ resp = null⌝) }}

end lease

end view
end etcd_dist
end EtcdGrove
end Perennial
