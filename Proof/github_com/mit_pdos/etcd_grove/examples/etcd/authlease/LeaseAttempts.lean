/-
**The authlease checks' lease calls, at their attempts** (auth-lease S4, item 9; `noAuth`, `foreign`).
Lean-first (no Rocq counterpart).

The attempt preconditions (`attemptPre`) of `Grant`, `Revoke`, `TimeToLive` and `Leases` at the Lease
service's metadata specs with auth on, for a client whose attempts carry a token of `who`'s
(`attemptTokOk … (akTokP γa who)`) on a context of `reqCtx(who)`'s metadata (`akOut who`): every reply
carries a passed lease check at the token of one of the attempts (`akTokSeen`). The `…_refuted` forms
take the caller's refutation of every such check (`noAuth`'s premise) and ask for nothing of the reply
(`False`); the `…_seen` forms hand the check to the reply (`foreign`'s, refuted with the caller's
resource after the call). Also the lease options' slices (`leaseOptsAt`) of no option and of one.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Env
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.WorkCalls

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authlease

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver client etcd_auth

section opts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- No lease option. -/
theorem leaseOptsAt_nil : ⊢ leaseOptsAt (GF := GF) slice.nil [] := by
  iunfold leaseOptsAt
  iexists ([] : List GoFunc)
  isplitl
  · iapply ownSlice_nil
  isplitl
  · ipureintro; rfl
  imodintro
  iintro %i %f %g %Hf %Hg
  simp at Hf

/-- One lease option. -/
theorem leaseOptsAt_one (sl : GoSlice) (f : GoFunc) (g : Bool → Bool) :
    sl ↦*□ [f] ∗ leaseOptSpec (GF := GF) f g ⊢ leaseOptsAt sl [g] := by
  iintro ⟨#Hsl, #Hf⟩
  iunfold leaseOptsAt
  iexists [f]
  iframe Hsl
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %i %f' %g' %Hf' %Hg'
  rcases i with _ | i
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hf' Hg'; subst Hf' Hg'; iexact Hf
  · simp at Hf'

end opts

section attempts
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Assumptions]

/-- **The token an attempt of `who`'s call carries** (`akTokSeen_attempt` at `reqCtx`'s context). -/
theorem akTokSeen_md (γa : auth.AuthNames) (who : GoString) (conn : Loc) (c : GrpcMd) (md : GrpcMd)
    (hout : c = akOut who) (hmd : clientAttemptMd conn c md) :
    attemptTokOk (GF := GF) conn (akTokP γa who) ⊢ akTokSeen γa who (auth.mdTokenOf md) :=
  akTokSeen_attempt γa who conn md (by unfold clientAttemptMd at hmd; rw [hout] at hmd; exact hmd)

/-- `Grant(ttl)`'s attempts, refuted. -/
theorem grant_attempt_refuted (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γl : GName)
    (γa : auth.AuthNames) (who : GoString) (conn : Loc) (c : GrpcMd) (n : Nat) (ttl : w64)
    (Q : w64 → KVState → IProp GF) (Φ : LeaseGrantRespM → IProp GF)
    (hout : c = akOut who) :
    attemptTokOk conn (akTokP γa who) ∗ auth.authPubLbM E.authMode n ∗
      □ (∀ (tok : Option GoString) (K : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF) m,
          akTokSeen γa who tok -∗ leaseCheckFrom (srvTLSId s) E tok n K -∗ Φ m) ∗
      □ (∀ id : w64, clientOpAuOn s E ρ conn c (.leaseGrant id ttl) (Q id)) ⊢
    □ ▷ attemptPre conn c (etcdLeaseGrantSpecOn (srvTLSId s) E ρ γl) (ttl, W64 0) Φ := by
  iintro ⟨#Htok, #Hn, #Hno, #Hau⟩
  imodintro
  inext
  unfold attemptPre
  iintro %md %Hmd
  unfold etcdLeaseGrantSpecOn etcdLeaseGrantSpecOnW
  isplitr
  · iintro !> %_; itrivial
  isplitr
  · ipureintro; rfl
  iexists n
  iframe Hn
  iexists Q
  isplitr
  · cases hon : E.authOn
    · iapply leaseGrantPermitM_false
    · simp only [leaseGrantPermitM]
      iintro %id
      ihave Hau1 := Hau $$ %id
      ihave H := clientOpAuOn_attempt s E ρ conn c md _ (Q id) Hmd $$ Hau1
      iapply kvOpAuOn_leaseGrant $$ H
  iintro %m %_ #_ _ _ #Hck
  ihave #Hs := akTokSeen_md γa who conn c md hout Hmd $$ Htok
  iapply Hno $$ %_ %_ %m Hs Hck

/-- `Revoke(id)`'s attempts, with the caller's update `Q` and the reply's result. -/
theorem revoke_attempt (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc) (c : GrpcMd)
    (n : Nat) (id : w64) (Q : KVState → IProp GF) (Φ : LeaseRevokeRespM → IProp GF) :
    auth.authPubLbM E.authMode n ∗ □ clientOpAuOn s E ρ conn c (.leaseRevoke id) Q ∗
      □ (∀ (md : GrpcMd) (m : LeaseRevokeRespM), ⌜clientAttemptMd conn c md⌝ -∗
          v3rpc.leaseRevokeResT E.authOn (srvTLSId s) E ρ (auth.mdTokenOf md) id Q -∗
          leaseCheckFrom (srvTLSId s) E (auth.mdTokenOf md) n (fun _ => iprop(True)) -∗ Φ m) ⊢
    □ ▷ attemptPre conn c (etcdLeaseRevokeSpecOn (srvTLSId s) E ρ) id Φ := by
  iintro ⟨#Hn, #Hau, #HΦ⟩
  imodintro
  inext
  unfold attemptPre
  iintro %md %Hmd
  unfold etcdLeaseRevokeSpecOn etcdLeaseRevokeSpecOnW
  isplitr
  · iintro !> %_; itrivial
  iexists n
  iframe Hn
  iexists Q
  isplitr
  · cases hon : E.authOn
    · iapply leaseRevokePermitM_false
    · simp only [leaseRevokePermitM]
      ihave H := clientOpAuOn_attempt s E ρ conn c md _ Q Hmd $$ Hau
      iapply kvOpAuOn_leaseRevoke $$ H
  iintro %m #_ Hres #Hck
  iapply HΦ $$ %md %m %Hmd Hres Hck

/-- `Revoke(id)`'s attempts, refuted. -/
theorem revoke_attempt_refuted (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γa : auth.AuthNames)
    (who : GoString) (conn : Loc) (c : GrpcMd) (n : Nat) (id : w64) (Q : KVState → IProp GF)
    (Φ : LeaseRevokeRespM → IProp GF)
    (hout : c = akOut who) :
    attemptTokOk conn (akTokP γa who) ∗ auth.authPubLbM E.authMode n ∗
      □ (∀ (tok : Option GoString) (K : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF) m,
          akTokSeen γa who tok -∗ leaseCheckFrom (srvTLSId s) E tok n K -∗ Φ m) ∗
      □ clientOpAuOn s E ρ conn c (.leaseRevoke id) Q ⊢
    □ ▷ attemptPre conn c (etcdLeaseRevokeSpecOn (srvTLSId s) E ρ) id Φ := by
  iintro ⟨#Htok, #Hn, #Hno, #Hau⟩
  imodintro
  inext
  unfold attemptPre
  iintro %md %Hmd
  unfold etcdLeaseRevokeSpecOn etcdLeaseRevokeSpecOnW
  isplitr
  · iintro !> %_; itrivial
  iexists n
  iframe Hn
  iexists Q
  isplitr
  · cases hon : E.authOn
    · iapply leaseRevokePermitM_false
    · simp only [leaseRevokePermitM]
      ihave H := clientOpAuOn_attempt s E ρ conn c md _ Q Hmd $$ Hau
      iapply kvOpAuOn_leaseRevoke $$ H
  iintro %m #_ - #Hck
  ihave #Hs := akTokSeen_md γa who conn c md hout Hmd $$ Htok
  iapply Hno $$ %_ %_ %m Hs Hck

/-- `TimeToLive(req)`'s attempts, the reply's check at the token of one of them handed to `Φ`. -/
theorem ttl_attempt_seen (s : Loc) (E : apply.AEnv GF) (γl : GName) (γa : auth.AuthNames)
    (who : GoString) (conn : Loc) (c : GrpcMd) (n m : Nat) (req : w64 × Bool)
    (Φ : LeaseTTLRespM → IProp GF) (hout : c = akOut who) :
    attemptTokOk conn (akTokP γa who) ∗ auth.authPubLbM E.authMode n ∗ lease.lessorLb γl m ∗
      □ (∀ (r : LeaseTTLRespM) (tok : Option GoString), akTokSeen γa who tok -∗
          leaseCheckFrom (srvTLSId s) E tok n (fun info => if req.2 then
            leaseKeysVerdictFrom E.authMode n info γl m req.1 .read else iprop(True)) -∗ Φ r) ⊢
    □ ▷ attemptPre conn c (etcdLeaseTTLSpecMd (srvTLSId s) (leaseTTLRow s γl) E γl) req Φ := by
  iintro ⟨#Htok, #Hn, #Hm, #HΦ⟩
  imodintro
  inext
  unfold attemptPre
  iintro %md %Hmd
  unfold etcdLeaseTTLSpecMd etcdLeaseTTLSpecMdW
  isplitr
  · iintro !> %_; itrivial
  iexists n
  iexists m
  iframe Hn Hm
  iintro %r %_ - Hck
  ihave #Hs := akTokSeen_md γa who conn c md hout Hmd $$ Htok
  iapply HΦ $$ %r %(auth.mdTokenOf md) Hs Hck

/-- `TimeToLive(req)`'s attempts, refuted. -/
theorem ttl_attempt_refuted (s : Loc) (E : apply.AEnv GF) (γl : GName) (γa : auth.AuthNames)
    (who : GoString) (conn : Loc) (c : GrpcMd) (n m : Nat) (req : w64 × Bool)
    (Φ : LeaseTTLRespM → IProp GF)
    (hout : c = akOut who) :
    attemptTokOk conn (akTokP γa who) ∗ auth.authPubLbM E.authMode n ∗ lease.lessorLb γl m ∗
      □ (∀ (tok : Option GoString) (K : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF) m,
          akTokSeen γa who tok -∗ leaseCheckFrom (srvTLSId s) E tok n K -∗ Φ m) ⊢
    □ ▷ attemptPre conn c (etcdLeaseTTLSpecMd (srvTLSId s) (leaseTTLRow s γl) E γl) req Φ := by
  iintro ⟨#Htok, #Hn, #Hm, #Hno⟩
  imodintro
  inext
  unfold attemptPre
  iintro %md %Hmd
  unfold etcdLeaseTTLSpecMd etcdLeaseTTLSpecMdW
  isplitr
  · iintro !> %_; itrivial
  iexists n
  iexists m
  iframe Hn Hm
  iintro %r %_ - Hck
  ihave #Hs := akTokSeen_md γa who conn c md hout Hmd $$ Htok
  iapply Hno $$ %_ %_ %r Hs Hck

/-- `Leases()`'s attempts, the listing and the reply's check at the token of one of them handed to
`Φ`. -/
theorem leases_attempt_seen (s : Loc) (E : apply.AEnv GF) (γl : GName) (γa : auth.AuthNames)
    (who : GoString) (conn : Loc) (c : GrpcMd) (n m : Nat) (Φ : LeaseLeasesRespM → IProp GF)
    (hout : c = akOut who) :
    attemptTokOk conn (akTokP γa who) ∗ auth.authPubLbM E.authMode n ∗ lease.lessorLb γl m ∗
      □ (∀ (r : LeaseLeasesRespM) (tok : Option GoString) (i : Nat), ⌜m ≤ i⌝ -∗ akTokSeen γa who tok -∗
          lease.leaseIdsAt γl i r.ids -∗
          leaseCheckFrom (srvTLSId s) E tok n (fun info => iprop([∗list] id ∈ r.ids,
            leaseKeysVerdictFrom E.authMode n info γl i id .read)) -∗ Φ r) ⊢
    □ ▷ attemptPre conn c (etcdLeaseLeasesSpecMd (srvTLSId s) E γl) () Φ := by
  iintro ⟨#Htok, #Hn, #Hm, #HΦ⟩
  imodintro
  inext
  unfold attemptPre
  iintro %md %Hmd
  unfold etcdLeaseLeasesSpecMd etcdLeaseLeasesSpecMdW
  isplitr
  · iintro !> %_; itrivial
  iexists n
  iexists m
  iframe Hn Hm
  iintro %r %_ ⟨%i, %hi, Hids, Hck⟩
  ihave #Hs := akTokSeen_md γa who conn c md hout Hmd $$ Htok
  iapply HΦ $$ %r %(auth.mdTokenOf md) %i %hi Hs Hids Hck

/-- `Leases()`'s attempts, refuted. -/
theorem leases_attempt_refuted (s : Loc) (E : apply.AEnv GF) (γl : GName) (γa : auth.AuthNames)
    (who : GoString) (conn : Loc) (c : GrpcMd) (n m : Nat)
    (Φ : LeaseLeasesRespM → IProp GF)
    (hout : c = akOut who) :
    attemptTokOk conn (akTokP γa who) ∗ auth.authPubLbM E.authMode n ∗ lease.lessorLb γl m ∗
      □ (∀ (tok : Option GoString) (K : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF) m,
          akTokSeen γa who tok -∗ leaseCheckFrom (srvTLSId s) E tok n K -∗ Φ m) ⊢
    □ ▷ attemptPre conn c (etcdLeaseLeasesSpecMd (srvTLSId s) E γl) () Φ := by
  iintro ⟨#Htok, #Hn, #Hm, #Hno⟩
  imodintro
  inext
  unfold attemptPre
  iintro %md %Hmd
  unfold etcdLeaseLeasesSpecMd etcdLeaseLeasesSpecMdW
  isplitr
  · iintro !> %_; itrivial
  iexists n
  iexists m
  iframe Hn Hm
  iintro %r %_ ⟨%i, -, -, Hck⟩
  ihave #Hs := akTokSeen_md γa who conn c md hout Hmd $$ Htok
  iapply Hno $$ %_ %_ %r Hs Hck

end attempts

end etcd_authlease
end EtcdGrove
end Perennial
