/-
**The server's lease requests in either auth mode** (auth-lease S3b, `notes/auth-lease-s3b-draft.md`
§2, §4.2, §4.3): what `EtcdServer.LeaseGrant`/`LeaseRevoke` need and give at the environment's auth
mode. Off, nothing (the off KV invariant owns the whole state where the cluster grants or revokes, no
client is told); on, the client's update fired at the commit (a KV write's, `kvAu1G … writeGrantG`,
F3 of the S3a Draft) and, on success, its result at the state the committed prefix before the entry
reached.

- `leaseGrantPermitM`, `leaseRevokePermitM`: the permits (on, the update; a grant's at whichever id
  the member fixes, `∀ id`), with their laws (`_false`, `_true`, `_mono`) and the proposal they make
  (`…_reqPropOk`, through `reqPropOkOn`'s write form, `reqPropOkM_true_writeL`).
- `leaseGrantResM`, `leaseRevokeResM`: the success's results (on, the header bound to the context,
  the entry committed after the prefix `L` with the auth state after it published, `pubAfterM`, and
  the client's result; a revocation's also granted there, `grantedAt`), with their laws.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReqOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseRevoke

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

theorem irrLeaseGrant_kind (id ttl : w64) : apply.dispatchKind (irrLeaseGrant id ttl) = .leaseGrant := by
  simp [apply.dispatchKind, irrLeaseGrant, apply.irrEmpty]

/-- **A revocable-mode grant's write grant tells its update the id is fresh** (auth-lease S4, the
thaw of 2026-11-18): no key had the lease `id` at any revision up to the state `σ` it fires at. -/
theorem writeGrantG_grant_fresh (γk : KVNames) (st₀ : auth.AuthState) (Gb : apply.HeaderModel → IProp GF)
    (id ttl : w64) (L₀ : List EntryModel) (σ : KVState) (hrev : γk.lm = .revocable) :
    writeGrantG (GF := GF) γk st₀ Gb (irrLeaseGrant id ttl) L₀ σ ⊢
      ⌜∀ r ≤ σ.rev, ∀ kv ∈ (σ.at r).kvs, kv.lease ≠ W64 0 → kv.lease ≠ id⌝ := by
  unfold writeGrantG
  iintro ⟨%hm, %L, -, -, %Hp⟩
  ipureintro
  refine Hp.2.2.2 id ?_
  unfold rqRevGrantId
  simp only [hrev, irrLeaseGrant_kind, and_self, ↓reduceIte]
  rfl

theorem irrLeaseRevoke_kind (id : w64) : apply.dispatchKind (irrLeaseRevoke id) = .leaseRevoke := by
  simp [apply.dispatchKind, irrLeaseRevoke, apply.irrEmpty]

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **What `LeaseGrant` of TTL `ttl` needs, in the auth mode `on`**: off nothing (the off `kvInv`
holds the whole state where the cluster grants, no client); on, its client's update at whichever id
the member fixes (`∀ id`: the generated id is not known to the caller), told its grant at the
caller's binding `Gb` and its lower bound `L₀` of the requested log (`writeGrantG`). -/
def leaseGrantPermitM (on : Bool) (γ : ServerRaftNames) (γk : KVNames) (Gb : apply.HeaderModel → IProp GF)
    (ttl : w64) (Q : w64 → KVState → IProp GF) : IProp GF :=
  match on with
  | false => iprop(True)
  | true => iprop(∀ id : w64, ∃ L₀ : List EntryModel, srvReqLogLb γ L₀ ∗
      kvAu1G γk (kvOpStep (.leaseGrant id ttl)) (writeGrantG γk srvAuthSt0 Gb (irrLeaseGrant id ttl) L₀) (Q id))

/-- **What `LeaseRevoke` of the lease `id` needs, in the auth mode `on`** (`leaseGrantPermitM`'s). -/
def leaseRevokePermitM (on : Bool) (γ : ServerRaftNames) (γk : KVNames) (Gb : apply.HeaderModel → IProp GF)
    (id : w64) (Q : KVState → IProp GF) : IProp GF :=
  match on with
  | false => iprop(True)
  | true => iprop(∃ L₀ : List EntryModel, srvReqLogLb γ L₀ ∗
      kvAu1G γk (kvOpStep (.leaseRevoke id)) (writeGrantG γk srvAuthSt0 Gb (irrLeaseRevoke id) L₀) Q)

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]


theorem leaseGrantPermitM_false (γ : ServerRaftNames) (γk : KVNames) (Gb : apply.HeaderModel → IProp GF)
    (ttl : w64) (Q : w64 → KVState → IProp GF) : ⊢ leaseGrantPermitM (GF := GF) false γ γk Gb ttl Q := by
  unfold leaseGrantPermitM; istart; itrivial

theorem leaseRevokePermitM_false (γ : ServerRaftNames) (γk : KVNames) (Gb : apply.HeaderModel → IProp GF)
    (id : w64) (Q : KVState → IProp GF) : ⊢ leaseRevokePermitM (GF := GF) false γ γk Gb id Q := by
  unfold leaseRevokePermitM; istart; itrivial

theorem leaseGrantPermitM_true (γ : ServerRaftNames) (γk : KVNames) (Gb : apply.HeaderModel → IProp GF)
    (ttl : w64) (Q : w64 → KVState → IProp GF) :
    leaseGrantPermitM (GF := GF) true γ γk Gb ttl Q ⊣⊢ ∀ id : w64, ∃ L₀ : List EntryModel,
      srvReqLogLb γ L₀ ∗
      kvAu1G γk (kvOpStep (.leaseGrant id ttl)) (writeGrantG γk srvAuthSt0 Gb (irrLeaseGrant id ttl) L₀) (Q id) :=
  .rfl

theorem leaseRevokePermitM_true (γ : ServerRaftNames) (γk : KVNames) (Gb : apply.HeaderModel → IProp GF)
    (id : w64) (Q : KVState → IProp GF) :
    leaseRevokePermitM (GF := GF) true γ γk Gb id Q ⊣⊢ ∃ L₀ : List EntryModel, srvReqLogLb γ L₀ ∗
      kvAu1G γk (kvOpStep (.leaseRevoke id)) (writeGrantG γk srvAuthSt0 Gb (irrLeaseRevoke id) L₀) Q :=
  .rfl

/-- A grant's permit made at a binding `Gb` serves a caller whose binding `Gb'` gives `Gb`. -/
theorem leaseGrantPermitM_mono (on : Bool) (γ : ServerRaftNames) (γk : KVNames)
    (Gb Gb' : apply.HeaderModel → IProp GF) (ttl : w64) (Q : w64 → KVState → IProp GF)
    (hb : ∀ hm, Gb' hm ⊢ Gb hm) :
    leaseGrantPermitM (GF := GF) on γ γk Gb ttl Q ⊢ leaseGrantPermitM on γ γk Gb' ttl Q := by
  cases on
  · unfold leaseGrantPermitM; iintro -; itrivial
  unfold leaseGrantPermitM
  iintro H %id
  icases H $$ %id with ⟨%L₀, #HL₀, Hau⟩
  iexists L₀
  iframe HL₀
  iapply kvAu1G_mono γk _ _ (writeGrantG γk srvAuthSt0 Gb' (irrLeaseGrant id ttl) L₀) (Q id)
    (fun σ => writeGrantG_mono γk srvAuthSt0 Gb Gb' _ L₀ σ hb) $$ Hau

/-- `leaseGrantPermitM_mono` for a revocation. -/
theorem leaseRevokePermitM_mono (on : Bool) (γ : ServerRaftNames) (γk : KVNames)
    (Gb Gb' : apply.HeaderModel → IProp GF) (id : w64) (Q : KVState → IProp GF)
    (hb : ∀ hm, Gb' hm ⊢ Gb hm) :
    leaseRevokePermitM (GF := GF) on γ γk Gb id Q ⊢ leaseRevokePermitM on γ γk Gb' id Q := by
  cases on
  · unfold leaseRevokePermitM; iintro -; itrivial
  unfold leaseRevokePermitM
  iintro ⟨%L₀, #HL₀, Hau⟩
  iexists L₀
  iframe HL₀
  iapply kvAu1G_mono γk _ _ (writeGrantG γk srvAuthSt0 Gb' (irrLeaseRevoke id) L₀) Q
    (fun σ => writeGrantG_mono γk srvAuthSt0 Gb Gb' _ L₀ σ hb) $$ Hau

open Iris.ProofMode in
/-- `leaseGrantPermitM_mono` under a persistent hypothesis `P` (O2's monotonicity laws, 2026-11-23). -/
theorem leaseGrantPermitM_mono_with (on : Bool) (γ : ServerRaftNames) (γk : KVNames)
    (Gb Gb' : apply.HeaderModel → IProp GF) (ttl : w64) (Q : w64 → KVState → IProp GF)
    (P : IProp GF) [Persistent P] (hb : ∀ hm, P ∗ Gb' hm ⊢ Gb hm) :
    P ∗ leaseGrantPermitM (GF := GF) on γ γk Gb ttl Q ⊢ leaseGrantPermitM on γ γk Gb' ttl Q := by
  cases on
  · unfold leaseGrantPermitM; iintro -; itrivial
  unfold leaseGrantPermitM
  iintro ⟨#HP, H⟩ %id
  icases H $$ %id with ⟨%L₀, #HL₀, Hau⟩
  iexists L₀
  iframe HL₀
  iapply kvAu1G_mono_with γk _ _ (writeGrantG γk srvAuthSt0 Gb' (irrLeaseGrant id ttl) L₀) (Q id) P
    (fun σ => writeGrantG_mono_with γk srvAuthSt0 Gb Gb' _ L₀ σ P hb) $$ [Hau]
  iframe HP Hau

open Iris.ProofMode in
/-- `leaseRevokePermitM_mono` under a persistent hypothesis `P`. -/
theorem leaseRevokePermitM_mono_with (on : Bool) (γ : ServerRaftNames) (γk : KVNames)
    (Gb Gb' : apply.HeaderModel → IProp GF) (id : w64) (Q : KVState → IProp GF)
    (P : IProp GF) [Persistent P] (hb : ∀ hm, P ∗ Gb' hm ⊢ Gb hm) :
    P ∗ leaseRevokePermitM (GF := GF) on γ γk Gb id Q ⊢ leaseRevokePermitM on γ γk Gb' id Q := by
  cases on
  · unfold leaseRevokePermitM; iintro -; itrivial
  unfold leaseRevokePermitM
  iintro ⟨#HP, %L₀, #HL₀, Hau⟩
  iexists L₀
  iframe HL₀
  iapply kvAu1G_mono_with γk _ _ (writeGrantG γk srvAuthSt0 Gb' (irrLeaseRevoke id) L₀) Q P
    (fun σ => writeGrantG_mono_with γk srvAuthSt0 Gb Gb' _ L₀ σ P hb) $$ [Hau]
  iframe HP Hau

/-- **A grant's result in the mode `on`** at the header `hm` the server stamps and the committed
log `L` before its entry: `grantedRes` of the stamped request (always granted, `grantedAt_grant`). -/
def grantQhOn (γk : KVNames) (id ttl : w64) (γc : GName) (Q : w64 → KVState → IProp GF)
    (hm : apply.HeaderModel) (L : List EntryModel) : IProp GF :=
  grantedRes γk srvAuthSt0 (apply.withHeader (irrLeaseGrant id ttl) hm) γc (Q id) L

/-- **A revocation's result in the mode `on`** (`grantQhOn`'s). -/
def revokeQhOn (γk : KVNames) (id : w64) (γc : GName) (Q : KVState → IProp GF)
    (hm : apply.HeaderModel) (L : List EntryModel) : IProp GF :=
  grantedRes γk srvAuthSt0 (apply.withHeader (irrLeaseRevoke id) hm) γc Q L

/-- **A grant's update is its proposal in the mode `on`**, at the id the member fixed, with the
id's claim right (`grantIdOwn`, the off proposal's). -/
theorem leaseGrantPermit_reqPropOk (γ : ServerRaftNames) (γk : KVNames)
    (Gb Gb' : apply.HeaderModel → IProp GF) (id ttl : w64) (Q : w64 → KVState → IProp GF) (γc : GName)
    (hb : ∀ hm, Gb' hm ⊢ Gb hm) (hg : grantPropOk γk.lm (irrLeaseGrant id ttl)) :
    (∃ L₀ : List EntryModel, srvReqLogLb γ L₀ ∗
      kvAu1G γk (kvOpStep (.leaseGrant id ttl)) (writeGrantG γk srvAuthSt0 Gb (irrLeaseGrant id ttl) L₀) (Q id)) ∗
      grantIdOwn γk (irrLeaseGrant id ttl) ⊢
      reqPropOkM (GF := GF) true γ γk Gb' (irrLeaseGrant id ttl) (grantQhOn γk id ttl γc Q) := by
  iintro ⟨⟨%L₀, #HL₀, Hau⟩, Hgo⟩
  ihave Hau := kvAu1G_mono γk _ _ (writeGrantG γk srvAuthSt0 Gb' (irrLeaseGrant id ttl) L₀) (Q id)
    (fun σ => writeGrantG_mono γk srvAuthSt0 Gb Gb' _ L₀ σ hb) $$ Hau
  have hk := irrLeaseGrant_kind id ttl
  have hop : reqKVOp (irrLeaseGrant id ttl) = some (.leaseGrant id ttl) := by
    unfold reqKVOp; rw [hk]; rfl
  have hz : irrNoZeroEnd (irrLeaseGrant id ttl) := by
    refine ⟨?_, ?_, ?_⟩ <;> intro _ h <;> simp [irrLeaseGrant, apply.irrEmpty] at h
  have ha : kvShapeAll (irrLeaseGrant id ttl) := by
    intro x hx; unfold reqPerms at hx; rw [hk] at hx; simp at hx
  have hq : grantQhOn (GF := GF) γk id ttl γc Q =
      fun hm => grantedRes γk srvAuthSt0 (apply.withHeader (irrLeaseGrant id ttl) hm) γc (Q id) := rfl
  rw [hq]
  iapply reqPropOkM_true_writeL γ γk Gb' (irrLeaseGrant id ttl) (.leaseGrant id ttl) (Q id) γc L₀
    (Or.inr (Or.inl hg)) hop hz (rqShape_grant _ _ hg) ha $$ [$HL₀ $Hau $Hgo]

/-- **A revocation's permit is its proposal in the mode `on`.** -/
theorem leaseRevokePermit_reqPropOk (γ : ServerRaftNames) (γk : KVNames)
    (Gb Gb' : apply.HeaderModel → IProp GF) (id : w64) (Q : KVState → IProp GF) (γc : GName)
    (hb : ∀ hm, Gb' hm ⊢ Gb hm) (hr : revokePropOk γk.lm (irrLeaseRevoke id)) :
    leaseRevokePermitM (GF := GF) true γ γk Gb id Q ⊢
      reqPropOkM true γ γk Gb' (irrLeaseRevoke id) (revokeQhOn γk id γc Q) := by
  unfold leaseRevokePermitM
  iintro ⟨%L₀, #HL₀, Hau⟩
  ihave Hau := kvAu1G_mono γk _ _ (writeGrantG γk srvAuthSt0 Gb' (irrLeaseRevoke id) L₀) Q
    (fun σ => writeGrantG_mono γk srvAuthSt0 Gb Gb' _ L₀ σ hb) $$ Hau
  have hk := irrLeaseRevoke_kind id
  have hop : reqKVOp (irrLeaseRevoke id) = some (.leaseRevoke id) := by
    unfold reqKVOp; rw [hk]; rfl
  have hz : irrNoZeroEnd (irrLeaseRevoke id) := by
    refine ⟨?_, ?_, ?_⟩ <;> intro _ h <;> simp [irrLeaseRevoke, apply.irrEmpty] at h
  have ha : kvShapeAll (irrLeaseRevoke id) := by
    intro x hx; unfold reqPerms at hx; rw [hk] at hx; simp at hx
  have hq : revokeQhOn (GF := GF) γk id γc Q =
      fun hm => grantedRes γk srvAuthSt0 (apply.withHeader (irrLeaseRevoke id) hm) γc Q := rfl
  rw [hq]
  ihave Hgo := grantIdOwn_nonGrant (GF := GF) γk (irrLeaseRevoke id) (by rw [hk]; decide)
  iapply reqPropOkM_true_writeL γ γk Gb' (irrLeaseRevoke id) (.leaseRevoke id) Q γc L₀
    (Or.inr (Or.inr hr)) hop hz (rqShape_revoke _ _ hr) ha $$ [$HL₀ $Hau $Hgo]

/-- **A grant's success, in the auth mode `on`**: off nothing; on, for the lease `id` the response
names (`ID`), the header `hm` the server stamped bound to the context, the grant of `id` stamped with
`hm` committed right after the prefix `L` with the auth state after it published (`pubAfterM`), and
the client's result `Q id` at the state of `L`. -/
def leaseGrantResM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (ttl : w64) (resp : Loc) (Q : w64 → KVState → IProp GF) : IProp GF :=
  match on with
  | false => iprop(True)
  | true => iprop(∃ (id : w64) (hm : apply.HeaderModel) (L : List EntryModel),
      structFieldRef etcdserverpb.LeaseGrantResponse go!"ID" resp ↦□ id ∗
      hdrBoundM true s E tok hm ∗
      pubAfterM true E ρ (apply.withHeader (irrLeaseGrant id ttl) hm) L ∗
      Q id (kvStateOf (kvModelOn ρ.kv srvAuthSt0 L) (kvLeasesOn ρ.kv srvAuthSt0 L)))

/-- **A revocation's success, in the auth mode `on`** (`leaseGrantResM`'s, and the revocation granted
at `L`, `grantedAt`: the auth layer let it through). -/
def leaseRevokeResM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (id : w64) (Q : KVState → IProp GF) : IProp GF :=
  match on with
  | false => iprop(True)
  | true => iprop(∃ (hm : apply.HeaderModel) (L : List EntryModel),
      hdrBoundM true s E tok hm ∗
      ⌜grantedAt ρ.kv srvAuthSt0 (apply.withHeader (irrLeaseRevoke id) hm) L⌝ ∗
      pubAfterM true E ρ (apply.withHeader (irrLeaseRevoke id) hm) L ∗
      Q (kvStateOf (kvModelOn ρ.kv srvAuthSt0 L) (kvLeasesOn ρ.kv srvAuthSt0 L)))

theorem leaseGrantResM_false (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (ttl : w64) (resp : Loc) (Q : w64 → KVState → IProp GF) :
    leaseGrantResM (GF := GF) false s E ρ tok ttl resp Q ⊣⊢ iprop(True) := .rfl

theorem leaseRevokeResM_false (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (id : w64) (Q : KVState → IProp GF) :
    leaseRevokeResM (GF := GF) false s E ρ tok id Q ⊣⊢ iprop(True) := .rfl

theorem leaseGrantResM_true (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (ttl : w64) (resp : Loc) (Q : w64 → KVState → IProp GF) :
    leaseGrantResM (GF := GF) true s E ρ tok ttl resp Q ⊣⊢
      ∃ (id : w64) (hm : apply.HeaderModel) (L : List EntryModel),
        structFieldRef etcdserverpb.LeaseGrantResponse go!"ID" resp ↦□ id ∗
        hdrBoundM true s E tok hm ∗
        pubAfterM true E ρ (apply.withHeader (irrLeaseGrant id ttl) hm) L ∗
        Q id (kvStateOf (kvModelOn ρ.kv srvAuthSt0 L) (kvLeasesOn ρ.kv srvAuthSt0 L)) := .rfl

theorem leaseRevokeResM_true (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (id : w64) (Q : KVState → IProp GF) :
    leaseRevokeResM (GF := GF) true s E ρ tok id Q ⊣⊢
      ∃ (hm : apply.HeaderModel) (L : List EntryModel),
        hdrBoundM true s E tok hm ∗
        ⌜grantedAt ρ.kv srvAuthSt0 (apply.withHeader (irrLeaseRevoke id) hm) L⌝ ∗
        pubAfterM true E ρ (apply.withHeader (irrLeaseRevoke id) hm) L ∗
        Q (kvStateOf (kvModelOn ρ.kv srvAuthSt0 L) (kvLeasesOn ρ.kv srvAuthSt0 L)) := .rfl

/-- **The server's grant response at the lease `id`** (`leaseGrantedResp` with its `ID` named). -/
def leaseGrantedRespAt (E : apply.AEnv GF) (resp : Loc) (reqTTL id : w64) : IProp GF :=
  iprop(∃ (ttl : w64) (e : GoString) (i : Nat) (h : Loc) (rv : w64),
    structFieldRef etcdserverpb.LeaseGrantResponse go!"Header" resp ↦□ h ∗
    structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ rv ∗ ⌜rv ≠ W64 0⌝ ∗
    srvRevLb E (sint.Z rv) ∗
    txn.respHdrOwn (structFieldRef etcdserverpb.LeaseGrantResponse go!"Header" resp) ∗
    structFieldRef etcdserverpb.LeaseGrantResponse go!"ID" resp ↦□ id ∗ ⌜id ≠ W64 0⌝ ∗
    structFieldRef etcdserverpb.LeaseGrantResponse go!"TTL" resp ↦□ ttl ∗
    structFieldRef etcdserverpb.LeaseGrantResponse go!"Error" resp ↦□ e ∗
    ∃ l : Loc, lease.leaseLiveFrom (mvcc.api.mvccLeases E.γ) i id l ∗ lease.leaseReqIs (mvcc.api.mvccLeases E.γ) id reqTTL)

theorem leaseGrantedResp_iff_at (E : apply.AEnv GF) (resp : Loc) (reqTTL : w64) :
    leaseGrantedResp (GF := GF) E resp reqTTL ⊣⊢ ∃ id : w64, leaseGrantedRespAt E resp reqTTL id := by
  unfold leaseGrantedResp leaseGrantedRespAt
  constructor
  · iintro ⟨%id, %ttl, %e, %i, %h, %rv, H⟩
    iexists id, ttl, e, i, h, rv; iexact H
  · iintro ⟨%id, %ttl, %e, %i, %h, %rv, H⟩
    iexists id, ttl, e, i, h, rv; iexact H

/-- **The response's lease is the update's** (review r2 S1'): a grant's success at auth on names one
id, the response's `ID`, for which the lessor's history has the lease and the client's update fired. -/
theorem leaseGrantResM_true_id (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (ttl : w64) (resp : Loc) (Q : w64 → KVState → IProp GF) :
    leaseGrantedResp E resp ttl ∗ leaseGrantResM (GF := GF) true s E ρ tok ttl resp Q ⊢
      ∃ (id : w64) (hm : apply.HeaderModel) (L : List EntryModel), leaseGrantedRespAt E resp ttl id ∗
        hdrBoundM true s E tok hm ∗
        pubAfterM true E ρ (apply.withHeader (irrLeaseGrant id ttl) hm) L ∗
        Q id (kvStateOf (kvModelOn ρ.kv srvAuthSt0 L) (kvLeasesOn ρ.kv srvAuthSt0 L)) := by
  unfold leaseGrantResM
  iintro ⟨Hr, ⟨%id, %hm, %L, #Hid, #Hb, #Hp, HQ⟩⟩
  ihave ⟨%id', Hr⟩ := (leaseGrantedResp_iff_at E resp ttl).1 $$ Hr
  iunfold leaseGrantedRespAt at Hr
  icases Hr with ⟨%t, %e, %i, %h, %rv, #Hh, #Hrv, %Hrv0, #Hlb, Hown, #Hid', %Hid0, #Ht, #He, %l, #Hl, #Hq⟩
  icombine Hid Hid' gives %Heq
  subst Heq
  iexists id, hm, L
  iframe Hb Hp HQ
  iunfold leaseGrantedRespAt
  iexists t, e, i, h, rv
  iframe Hh Hrv Hlb Hown Hid Ht He
  isplitr
  · ipureintro; exact Hrv0
  isplitr
  · ipureintro; exact Hid0
  iexists l; iframe Hl Hq

end defs

end EtcdGrove
end Perennial
