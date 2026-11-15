/-
**The server's lease contracts in the auth mode** (auth-lease S3c, decision D6/C5′, 2026-11-15; Draft
`notes/auth-lease-s3c-draft.md` §7.1): `lessorGrantOkGM on`, `lessorGrantOkM on`, `lessorRevokeOkM on`,
`raftLessorM on`, the contracts of `InvLease.lean` (`lessorGrantOkG`, `lessorGrantOk`, `lessorRevokeOk`,
`raftLessor`, which stay as the auth-off contracts: their `_false` laws) with the client's update: the
caller binds `Q` and hands the server's permit (`leaseGrantPermitM`/`leaseRevokePermitM`, at the request
context's token, `hdrBoundT`), and a success gives the client's result at the token
(`leaseGrantResT`/`leaseRevokeResT`, the server's `leaseGrantResM`/`leaseRevokeResM` unfolded at it).
With auth off the permit and the result are `True`. The pair (today's contracts, these) is recorded
for the cleanup stage (`etc/mode-allow.txt`, `pair`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvLease
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKVOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseReqOn

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

/-- **A grant's client result at a token** (`leaseGrantResM` at `true`, its header bound to the token
`tok`, `hdrBoundT`): with auth on, the lease `id` granted at a published log `L` of the request, and
the client's result `Q id` at the model's state after it. `True` off. -/
def leaseGrantResT (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (ttl id : w64) (Q : w64 → KVState → IProp GF) : IProp GF :=
  iprop(⌜on = true⌝ → ∃ (hm : apply.HeaderModel) (L : List EntryModel), hdrBoundT s E.authMode tok hm ∗
      pubAfterM on E ρ (apply.withHeader (irrLeaseGrant id ttl) hm) L ∗
      Q id (kvStateOf (kvModelOn ρ.kv srvAuthSt0 L) (kvLeasesOn ρ.kv srvAuthSt0 L)))

/-- **A revocation's client result at a token** (`leaseRevokeResM` at `true`): `leaseGrantResT`'s,
with the revocation granted at `L` (`grantedAt`). `True` off. -/
def leaseRevokeResT (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (id : w64) (Q : KVState → IProp GF) : IProp GF :=
  iprop(⌜on = true⌝ → ∃ (hm : apply.HeaderModel) (L : List EntryModel), hdrBoundT s E.authMode tok hm ∗
      ⌜grantedAt ρ.kv srvAuthSt0 (apply.withHeader (irrLeaseRevoke id) hm) L⌝ ∗
      pubAfterM on E ρ (apply.withHeader (irrLeaseRevoke id) hm) L ∗
      Q (kvStateOf (kvModelOn ρ.kv srvAuthSt0 L) (kvLeasesOn ρ.kv srvAuthSt0 L)))

/-- **The server's `LeaseGrant` in the auth mode `on`** (`lessorGrantOkG`'s, with the client's update:
the caller's `Q` and permit, a success's result `leaseGrantResT`). -/
def lessorGrantOkGM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF)
    (G : w64 × w64 → w64 → IProp GF) (R : w64 × w64 → Prop := fun _ => True) : IProp GF :=
  iprop(∀ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (m : w64 × w64)
      (Q : w64 → KVState → IProp GF),
    {{ S ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ leaseGrantReqIs r m ∗ leaseGrantReqIdOwn r m.2 ∗ ⌜R m⌝ ∗
        leaseGrantPermitM on ρ.raft ρ.kv (hdrBoundT s E.authMode (auth.ctxTokenOf (GoInterface.ok ci))) m.1 Q }}
      (App (App (Val (srvM s go!"LeaseGrant")) (Val #(GoInterface.ok ci))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); S ∗ leaseGrantAns E resp err ∗
        (⌜err ≠ GoInterface.nil⌝ ∨ ∃ id : w64,
          structFieldRef etcdserverpb.LeaseGrantResponse go!"ID" resp ↦□ id ∗ G m id ∗
          leaseGrantResT on s E ρ (auth.ctxTokenOf (GoInterface.ok ci)) m.1 id Q) }})

instance lessorGrantOkGM_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (S : IProp GF) (G : w64 × w64 → w64 → IProp GF) (R : w64 × w64 → Prop) :
    Persistent (lessorGrantOkGM on s E ρ S G R) := by
  unfold lessorGrantOkGM; infer_instance

/-- **The server's `LeaseGrant` in the auth mode `on`, at no success fact.** -/
def lessorGrantOkM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF) : IProp GF :=
  lessorGrantOkGM on s E ρ S (fun _ _ => iprop(True))

/-- **The server's `LeaseRevoke` in the auth mode `on`** (`lessorRevokeOk`'s, with the client's
update). -/
def lessorRevokeOkM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF) : IProp GF :=
  iprop(∀ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (id : w64)
      (Q : KVState → IProp GF),
    {{ S ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ leaseRevokeReqIs r id ∗
        leaseRevokePermitM on ρ.raft ρ.kv (hdrBoundT s E.authMode (auth.ctxTokenOf (GoInterface.ok ci))) id Q }}
      (App (App (Val (srvM s go!"LeaseRevoke")) (Val #(GoInterface.ok ci))) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); S ∗ leaseRevokeAns E resp err ∗
        (⌜err ≠ GoInterface.nil⌝ ∨ leaseRevokeResT on s E ρ (auth.ctxTokenOf (GoInterface.ok ci)) id Q) }})

instance lessorGrantOkM_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (S : IProp GF) : Persistent (lessorGrantOkM on s E ρ S) := by
  unfold lessorGrantOkM; infer_instance

instance lessorRevokeOkM_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (S : IProp GF) : Persistent (lessorRevokeOkM on s E ρ S) := by
  unfold lessorRevokeOkM; infer_instance

/-- **The server `s` as the Lease service's handlers call it, in the auth mode `on`** (`raftLessor`'s). -/
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
    (ttl id : w64) (Q : w64 → KVState → IProp GF) : ⊢ leaseGrantResT (GF := GF) false s E ρ tok ttl id Q := by
  unfold leaseGrantResT; iintro %h; cases h

theorem leaseRevokeResT_false (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (tok : Option GoString)
    (id : w64) (Q : KVState → IProp GF) : ⊢ leaseRevokeResT (GF := GF) false s E ρ tok id Q := by
  unfold leaseRevokeResT; iintro %h; cases h

/-- **A grant's result with auth on, at the request context's token** (the server's `leaseGrantResM
true` gives the response's `ID` and `leaseGrantResT` at it, by `hdrBoundM_tok`). -/
theorem leaseGrantResT_true (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (ttl : w64) (resp : Loc) (Q : w64 → KVState → IProp GF) :
    leaseGrantResM (GF := GF) true s E ρ ctx ttl resp Q ⊢
      ∃ id : w64, structFieldRef etcdserverpb.LeaseGrantResponse go!"ID" resp ↦□ id ∗
        leaseGrantResT true s E ρ (auth.ctxTokenOf (GoInterface.ok ctx)) ttl id Q := by
  unfold leaseGrantResM leaseGrantResT
  iintro ⟨%id, %hm, %L, #Hid, #Hb, Hp, HQ⟩
  iexists id
  iframe Hid
  iintro -
  iexists hm, L
  iframe Hp HQ
  iapply hdrBoundM_tok s E (GoInterface.ok ctx) hm $$ Hb

/-- **A revocation's result with auth on, at the request context's token.** -/
theorem leaseRevokeResT_true (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (id : w64) (Q : KVState → IProp GF) :
    leaseRevokeResM (GF := GF) true s E ρ ctx id Q ⊢
      leaseRevokeResT true s E ρ (auth.ctxTokenOf (GoInterface.ok ctx)) id Q := by
  unfold leaseRevokeResM leaseRevokeResT
  iintro ⟨%hm, %L, #Hb, %Hg, Hp, HQ⟩ -
  iexists hm, L
  iframe Hp HQ
  isplitl
  · iapply hdrBoundM_tok s E (GoInterface.ok ctx) hm $$ Hb
  ipureintro; exact Hg

/-- **The grant contract in the mode, off, is `lessorGrantOkG`** (C5′'s bridge). -/
theorem lessorGrantOkGM_false (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF)
    (G : w64 × w64 → w64 → IProp GF) (R : w64 × w64 → Prop) :
    lessorGrantOkGM (GF := GF) false s E ρ S G R ⊣⊢ lessorGrantOkG s E S G R := by
  constructor
  · iintro #H
    unfold lessorGrantOkG
    iintro %ci %cd %r %m !> %Φ ⟨HS, Hctx, Hrc, Hreq, Hid, %HR⟩ HΦ
    iunfold lessorGrantOkGM at H
    wp_apply H $$ %ci %cd %r %m %(fun _ _ => iprop(True)) [HS Hctx Hrc Hreq Hid] as %resp %err ⟨HS, Hans, Hg⟩
    · iframe
      isplitr
      · ipureintro; exact HR
      iapply leaseGrantPermitM_false
    iapply HΦ
    iframe HS Hans
    icases Hg with (%Hne | ⟨%id, #Hid', Hg, -⟩)
    · ileft; ipureintro; exact Hne
    iright; iexists id; iframe Hid' Hg
  · iintro #H
    unfold lessorGrantOkGM
    iintro %ci %cd %r %m %Q !> %Φ ⟨HS, Hctx, Hrc, Hreq, Hid, %HR, -⟩ HΦ
    iunfold lessorGrantOkG at H
    wp_apply H $$ %ci %cd %r %m [HS Hctx Hrc Hreq Hid] as %resp %err ⟨HS, Hans, Hg⟩
    · iframe; ipureintro; exact HR
    iapply HΦ
    iframe HS Hans
    icases Hg with (%Hne | ⟨%id, #Hid', Hg⟩)
    · ileft; ipureintro; exact Hne
    iright; iexists id; iframe Hid' Hg
    iapply leaseGrantResT_false

/-- **The revocation contract in the mode, off, is `lessorRevokeOk`** (C5′'s bridge). -/
theorem lessorRevokeOkM_false (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF) :
    lessorRevokeOkM (GF := GF) false s E ρ S ⊣⊢ lessorRevokeOk s E S := by
  constructor
  · iintro #H
    unfold lessorRevokeOk
    iintro %ci %cd %r %id !> %Φ ⟨HS, Hctx, Hrc, Hreq⟩ HΦ
    iunfold lessorRevokeOkM at H
    wp_apply H $$ %ci %cd %r %id %(fun _ => iprop(True)) [HS Hctx Hrc Hreq] as %resp %err ⟨HS, Hans, -⟩
    · iframe
      iapply leaseRevokePermitM_false
    iapply HΦ
    iframe HS Hans
  · iintro #H
    unfold lessorRevokeOkM
    iintro %ci %cd %r %id %Q !> %Φ ⟨HS, Hctx, Hrc, Hreq, -⟩ HΦ
    iunfold lessorRevokeOk at H
    wp_apply H $$ %ci %cd %r %id [HS Hctx Hrc Hreq] as %resp %err ⟨HS, Hans⟩
    · iframe
    iapply HΦ
    iframe HS Hans
    iright
    iapply leaseRevokeResT_false

theorem lessorGrantOkM_false (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF) :
    lessorGrantOkM (GF := GF) false s E ρ S ⊣⊢ lessorGrantOk s E S := by
  unfold lessorGrantOkM
  refine (lessorGrantOkGM_false s E ρ S _ _).trans ?_
  constructor
  · iintro #H
    unfold lessorGrantOk
    iintro %ci %cd %r %m !> %Φ ⟨HS, Hctx, Hrc, Hreq, Hid⟩ HΦ
    iunfold lessorGrantOkG at H
    wp_apply H $$ %ci %cd %r %m [HS Hctx Hrc Hreq Hid] as %resp %err ⟨HS, Hans, -⟩
    · iframe
    iapply HΦ
    iframe HS Hans
  · iintro #H
    iapply lessorGrantOkG_true s E S $$ H

theorem raftLessorM_false (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF) :
    raftLessorM (GF := GF) false s E ρ S ⊣⊢ raftLessor s E S := by
  unfold raftLessorM raftLessor
  exact sep_congr (lessorGrantOkM_false s E ρ S) (lessorRevokeOkM_false s E ρ S)

/-- **The grant contract in the mode is monotone in its success fact and its filter**
(`lessorGrantOkG_mono`'s). -/
theorem lessorGrantOkGM_mono (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF)
    (G G' : w64 × w64 → w64 → IProp GF) (R R' : w64 × w64 → Prop) (hR : ∀ m, R' m → R m) :
    □ (∀ (m : w64 × w64) (id : w64), G m id -∗ G' m id) ∗ lessorGrantOkGM on s E ρ S G R ⊢
      lessorGrantOkGM on s E ρ S G' R' := by
  iintro ⟨#HGG, #HL⟩
  unfold lessorGrantOkGM
  iintro %ci %cd %r %m %Q !> %Φ ⟨HS0, Hctx, Hrc, Hreq, Hid, %HR', Hp⟩ HΦ
  wp_apply HL $$ %ci %cd %r %m %Q [HS0 Hctx Hrc Hreq Hid Hp] as %resp %err ⟨HSr, Hans, Hg⟩
  · iframe; ipureintro; exact hR m HR'
  iapply HΦ
  iframe HSr Hans
  icases Hg with (%Hne | ⟨%id, #Hid, Hg, Hres⟩)
  · ileft; ipureintro; exact Hne
  iright
  iexists id
  iframe Hid Hres
  iapply HGG $$ %m %id Hg

end lemmas

end v3rpc
end EtcdGrove
end Perennial
