/-
**The authlease checks' lease calls, at their attempts** (auth-lease S4, item 9; `noAuth`, `foreign`).
Lean-first (no Rocq counterpart).

Here the part the multi-machine theorem reuses: the token an attempt carries (`akTokSeen_md`) and the
lease options' slices (`leaseOptsAt`) of no option and of one. The attempt preconditions themselves
(the `…_refuted` and `…_seen` forms below) stay in `authlease/LeaseAttempts.lean`: they take the
authlease package's `Assumptions`.

The attempt preconditions (`attemptPre`) of `Grant`, `Revoke`, `TimeToLive` and `Leases` at the Lease
service's metadata specs with auth on, for a client whose attempts carry a token of `who`'s
(`attemptTokOk … (akTokP γa who)`) on a context of `reqCtx(who)`'s metadata (`akOut who`): every reply
carries a passed lease check at the token of one of the attempts (`akTokSeen`). The `…_refuted` forms
take the caller's refutation of every such check (`noAuth`'s premise) and ask for nothing of the reply
(`False`); the `…_seen` forms hand the check to the reply (`foreign`'s, refuted with the caller's
resource after the call). Also the lease options' slices (`leaseOptsAt`) of no option and of one.

Moved here from the authlease example's `authlease/LeaseAttempts.lean` (2026-11-27): the multi-machine theorem
reuses it (names and namespace `etcd_authlease` unchanged).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseEnv
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

/-- **The token an attempt of `who`'s call carries** (`akTokSeen_attempt` at `reqCtx`'s context). -/
theorem akTokSeen_md (γa : auth.AuthNames) (who : GoString) (conn : Loc) (c : GrpcMd) (md : GrpcMd)
    (hout : c = akOut who) :
    clientAttemptMd conn c md ⊢
      attemptTokOk (GF := GF) conn (akTokP γa who) -∗ akTokSeen γa who (auth.mdTokenOf md) := by
  subst hout
  exact akTokSeen_attempt γa who conn md

end attempts

end etcd_authlease
end EtcdGrove
end Perennial
