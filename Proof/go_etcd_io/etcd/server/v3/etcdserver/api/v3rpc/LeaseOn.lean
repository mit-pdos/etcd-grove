/-
**The server's lease contracts in the auth mode** (auth-lease S3c, decision D6/C5′, 2026-11-15; Draft
`notes/auth-lease-s3c-draft.md` §7.1): `lessorGrantOkGM on`, `lessorGrantOkM on`, `lessorRevokeOkM on`,
`raftLessorM on`, the server's lease methods as the Lease service's handlers call them (`InvLease.lean`
has the requests and the answers), with the client's update: the
caller binds `Q` and hands the server's permit (`leaseGrantPermitM`/`leaseRevokePermitM`, at the request
context's token, `hdrBoundT`), and a success gives the client's result at the token
(`leaseGrantResT`/`leaseRevokeResT`, the server's `leaseGrantResM`/`leaseRevokeResM` unfolded at it).
With auth off the permit and the result are `True`. (Auth-lease S4, the C5′ merge, D5, 2026-11-16: the
auth-off contracts `lessorGrantOkG`, `lessorGrantOk`, `lessorRevokeOk`, `raftLessor` that stood beside
these, and their `_false` bridges, are deleted; their users take these at `E.authOn` with auth off.) Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvLease
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKVOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseReqOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvLeaseKeepAlive

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

end defs

section defsHF
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **A grant's client result at a token** (`leaseGrantResM` at `true`, its header bound to the token
`tok`, `hdrBoundT`): with auth on, the lease `id` granted at a published log `L` of the request, and
the client's result `Q id` at the model's state after it. `True` off. -/
def leaseGrantResT (on : Bool) (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (ttl id : w64) (Q : w64 → KVState → IProp GF) : IProp GF :=
  iprop(⌜on = true⌝ → ∃ (hm : apply.HeaderModel) (L : List EntryModel), hdrBoundT T E.authMode tok hm ∗
      pubAfterM on E ρ (apply.withHeader (irrLeaseGrant id ttl) hm) L ∗
      Q id (kvStateOf (kvModelOn ρ.kv srvAuthSt0 L) (kvLeasesOn ρ.kv srvAuthSt0 L)))

/-- **A revocation's client result at a token** (`leaseRevokeResM` at `true`): `leaseGrantResT`'s,
with the revocation granted at `L` (`grantedAt`). `True` off. -/
def leaseRevokeResT (on : Bool) (T : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (id : w64) (Q : KVState → IProp GF) : IProp GF :=
  iprop(⌜on = true⌝ → ∃ (hm : apply.HeaderModel) (L : List EntryModel), hdrBoundT T E.authMode tok hm ∗
      ⌜grantedAt ρ.kv srvAuthSt0 (apply.withHeader (irrLeaseRevoke id) hm) L⌝ ∗
      pubAfterM on E ρ (apply.withHeader (irrLeaseRevoke id) hm) L ∗
      Q (kvStateOf (kvModelOn ρ.kv srvAuthSt0 L) (kvLeasesOn ρ.kv srvAuthSt0 L)))

end defsHF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]


/-- **The server's `LeaseGrant` in the auth mode `on`, with a success fact `G`** (the lease-grant plan's
amendment (F2)): with the run's resource `S`, a gRPC run's context and the decoded request (its `TTL`
read-only, its `ID` owned), the caller's `Q` and permit, the answer `leaseGrantAns` and, on success, the
response's `ID` with `G` of it and the caller's result `leaseGrantResT`. The request filter `R` (the
lease-expiry plan's E3, 2026-11-04; `True` by default): the requests the contract covers, by their
`(TTL, ID)`; in the revocable lease mode those with `ID = 0` only (`EtcdServer.LeaseGrant.spec`'s
premise there). `G` takes the request `m` before the id (E3/R5: the live fact `grantLiveG` bounds the
lease's TTL by the request's). At the token `tok` the request context carries (`auth.ctxToken`, gated
by the mode; perheap C1a, 2026-11-18: until then the pure `auth.ctxTokenOf ci`). -/
def lessorGrantOkGM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF)
    (G : w64 × w64 → w64 → IProp GF) (R : w64 × w64 → Prop := fun _ => True) : IProp GF :=
  iprop(∀ (ci : GoInterfaceOk) (tok : Option GoString) (cd : context.ContextDesc (IProp GF)) (r : Loc)
      (m : w64 × w64) (Q : w64 → KVState → IProp GF) (n : Nat),
    {{ S ∗ auth.authPubLbM E.authMode n ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗
        □ (⌜on = true⌝ → auth.ctxToken (GoInterface.ok ci) tok) ∗ leaseGrantReqIs r m ∗
        leaseGrantReqIdOwn r m.2 ∗ ⌜R m⌝ ∗
        leaseGrantPermitM on ρ.raft ρ.kv (hdrBoundT (srvTLSId s) E.authMode tok) m.1 Q }}
      (App (App (Val (srvM s go!"LeaseGrant")) (Val #(GoInterface.ok ci))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); S ∗ leaseGrantAns E resp err ∗
        (⌜err ≠ GoInterface.nil⌝ ∨ ∃ id : w64,
          structFieldRef etcdserverpb.LeaseGrantResponse go!"ID" resp ↦□ id ∗ G m id ∗
          leaseGrantResT on (srvTLSId s) E ρ tok m.1 id Q ∗
          leaseCheckFrom (srvTLSId s) E tok n (fun _ => iprop(True))) }})

instance lessorGrantOkGM_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (S : IProp GF) (G : w64 × w64 → w64 → IProp GF) (R : w64 × w64 → Prop) :
    Persistent (lessorGrantOkGM on s E ρ S G R) := by
  unfold lessorGrantOkGM; infer_instance

/-- **The server's `LeaseGrant` in the auth mode `on`, at no success fact.** -/
def lessorGrantOkM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF) : IProp GF :=
  lessorGrantOkGM on s E ρ S (fun _ _ => iprop(True))

/-- **The server's `LeaseRevoke` in the auth mode `on`**: the answer `leaseRevokeAns` and, on success,
the caller's result `leaseRevokeResT`, at the token `tok` the request context carries (as
`lessorGrantOkGM`). -/
def lessorRevokeOkM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF) : IProp GF :=
  iprop(∀ (ci : GoInterfaceOk) (tok : Option GoString) (cd : context.ContextDesc (IProp GF)) (r : Loc)
      (id : w64) (Q : KVState → IProp GF) (n : Nat),
    {{ S ∗ auth.authPubLbM E.authMode n ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗
        □ (⌜on = true⌝ → auth.ctxToken (GoInterface.ok ci) tok) ∗ leaseRevokeReqIs r id ∗
        leaseRevokePermitM on ρ.raft ρ.kv (hdrBoundT (srvTLSId s) E.authMode tok) id Q }}
      (App (App (Val (srvM s go!"LeaseRevoke")) (Val #(GoInterface.ok ci))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); S ∗ leaseRevokeAns E resp err ∗
        (⌜err ≠ GoInterface.nil⌝ ∨ (leaseRevokeResT on (srvTLSId s) E ρ tok id Q ∗
          leaseCheckFrom (srvTLSId s) E tok n (fun _ => iprop(True)))) }})

instance lessorGrantOkM_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (S : IProp GF) : Persistent (lessorGrantOkM on s E ρ S) := by
  unfold lessorGrantOkM; infer_instance

instance lessorRevokeOkM_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (S : IProp GF) : Persistent (lessorRevokeOkM on s E ρ S) := by
  unfold lessorRevokeOkM; infer_instance

/-- **The server `s` as the Lease service's handlers call it, in the auth mode `on`** (persistent): its
`LeaseGrant` and `LeaseRevoke`, with the run's resource `S`, answering at the server's model of the apply
environment `E`. -/
def raftLessorM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF) : IProp GF :=
  iprop(lessorGrantOkM on s E ρ S ∗ lessorRevokeOkM on s E ρ S)

instance raftLessorM_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (S : IProp GF) : Persistent (raftLessorM on s E ρ S) := by
  unfold raftLessorM; infer_instance

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

open Iris.ProofMode

theorem leaseGrantResT_false (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (ttl id : w64) (Q : w64 → KVState → IProp GF) : ⊢ leaseGrantResT (GF := GF) false (srvTLSId s) E ρ tok ttl id Q := by
  unfold leaseGrantResT; iintro %h; cases h

theorem leaseRevokeResT_false (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (id : w64) (Q : KVState → IProp GF) : ⊢ leaseRevokeResT (GF := GF) false (srvTLSId s) E ρ tok id Q := by
  unfold leaseRevokeResT; iintro %h; cases h

/-- **A grant's result with auth on, at the request context's token** (the server's `leaseGrantResM
true` gives the response's `ID` and `leaseGrantResT` at it, by `hdrBoundM_tok`). -/
theorem leaseGrantResT_true (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (ttl : w64) (resp : Loc) (Q : w64 → KVState → IProp GF) :
    leaseGrantResM (GF := GF) true s E ρ tok ttl resp Q ⊢
      ∃ id : w64, structFieldRef etcdserverpb.LeaseGrantResponse go!"ID" resp ↦□ id ∗
        leaseGrantResT true (srvTLSId s) E ρ tok ttl id Q := by
  unfold leaseGrantResM leaseGrantResT
  iintro ⟨%id, %hm, %L, #Hid, #Hb, Hp, HQ⟩
  iexists id
  iframe Hid
  iintro -
  iexists hm, L
  iframe Hp HQ
  iapply hdrBoundM_tok s E tok hm $$ Hb

/-- **A revocation's result with auth on, at the request context's token.** -/
theorem leaseRevokeResT_true (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (id : w64) (Q : KVState → IProp GF) :
    leaseRevokeResM (GF := GF) true s E ρ tok id Q ⊢
      leaseRevokeResT true (srvTLSId s) E ρ tok id Q := by
  unfold leaseRevokeResM leaseRevokeResT
  iintro ⟨%hm, %L, #Hb, %Hg, Hp, HQ⟩ -
  iexists hm, L
  iframe Hp HQ
  isplitl
  · iapply hdrBoundM_tok s E tok hm $$ Hb
  ipureintro; exact Hg

/-- **`raftLessorM`'s grant conjunct, at no success fact** (`lessorGrantOkM`'s unfolding). -/
theorem raftLessorM_grantG (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF) :
    raftLessorM (GF := GF) on s E ρ S ⊢ lessorGrantOkGM on s E ρ S (fun _ _ => iprop(True)) := by
  unfold raftLessorM lessorGrantOkM
  iintro ⟨#HG, -⟩
  iexact HG

/-- **`raftLessorM`'s revocation conjunct.** -/
theorem raftLessorM_revoke (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF) :
    raftLessorM (GF := GF) on s E ρ S ⊢ lessorRevokeOkM on s E ρ S := by
  unfold raftLessorM
  iintro ⟨-, #HR⟩
  iexact HR

/-- **The grant contract in the mode is monotone in its success fact and its filter**
(the lease-expiry plan's X2/E3). -/
theorem lessorGrantOkGM_mono (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF)
    (G G' : w64 × w64 → w64 → IProp GF) (R R' : w64 × w64 → Prop) (hR : ∀ m, R' m → R m) :
    □ (∀ (m : w64 × w64) (id : w64), G m id -∗ G' m id) ∗ lessorGrantOkGM on s E ρ S G R ⊢
      lessorGrantOkGM on s E ρ S G' R' := by
  iintro ⟨#HGG, #HL⟩
  unfold lessorGrantOkGM
  iintro %ci %tok %cd %r %m %Q %n !> %Φ ⟨HS0, Hn, Hctx, Hrc, #Htk, Hreq, Hid, %HR', Hp⟩ HΦ
  wp_apply HL $$ %ci %tok %cd %r %m %Q %n [HS0 Hn Hctx Hrc Hreq Hid Hp] as %resp %err ⟨HSr, Hans, Hg⟩
  · iframe; iframe #; ipureintro; exact hR m HR'
  iapply HΦ
  iframe HSr Hans
  icases Hg with (%Hne | ⟨%id, #Hid, Hg, Hres, Hck⟩)
  · ileft; ipureintro; exact Hne
  iright
  iexists id
  iframe Hid Hres Hck
  iapply HGG $$ %m %id Hg

section monoT
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

open Iris.ProofMode in
/-- `leaseGrantResT` is monotone in the TLS fact (O2, 2026-11-23). -/
theorem leaseGrantResT_mono (on : Bool) (T1 T2 : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (tok : Option GoString) (ttl id : w64) (Q : w64 → KVState → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ leaseGrantResT on T1 E ρ tok ttl id Q ⊢ leaseGrantResT on T2 E ρ tok ttl id Q := by
  unfold leaseGrantResT
  iintro ⟨#HT, H⟩ %h
  icases H $$ %h with ⟨%hm, %L, Hb, Hp, HQ⟩
  iexists hm, L
  iframe Hp HQ
  iapply hdrBoundT_mono T1 T2
  iframe HT Hb

open Iris.ProofMode in
/-- `leaseRevokeResT` is monotone in the TLS fact. -/
theorem leaseRevokeResT_mono (on : Bool) (T1 T2 : IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (tok : Option GoString) (id : w64) (Q : KVState → IProp GF) :
    iprop(□ (T1 -∗ T2)) ∗ leaseRevokeResT on T1 E ρ tok id Q ⊢ leaseRevokeResT on T2 E ρ tok id Q := by
  unfold leaseRevokeResT
  iintro ⟨#HT, H⟩ %h
  icases H $$ %h with ⟨%hm, %L, Hb, %hg, Hp, HQ⟩
  iexists hm, L
  isplitl [Hb]
  · iapply hdrBoundT_mono T1 T2
    iframe HT Hb
  isplitr
  · ipureintro; exact hg
  iframe Hp HQ

end monoT

end lemmas

end v3rpc
end EtcdGrove
end Perennial
