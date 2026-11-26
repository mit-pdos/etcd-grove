/-
The vocabulary of the lease workloads of `examples/etcd/dist/client` (#50 N9b, 2026-11-25;
`notes/etcd-dist-n9b.md`). Lean-first (no Rocq counterpart).

Re-indexed by the cluster view (O1, option B, `notes/etcd-dist-plan.md` §18; the lead's drafts
`ClientViewDist.lean`): `Γ` is the view.

- `leaseMember Γ a`: what a lease workload's orchestrator holds of the member at `a`: a valid address
  (`Net.addrOk`, `deployment.WellFormed`'s) that serves etcd's table for some member of `Γ`
  (`etcdAddrAt`), with its lessor name's slot.
- `memberCli cl ep V Γ mid`: `New`'s client `cl` of the one endpoint `ep` (no proxy), `ep` serving member
  `mid` of `Γ`; `leaseClientV_of_memberCli`: the lease drafts' `leaseClientV` from it.
- `lessorAbsentStays_dist.law`: at a member of the view, a lease absent from the lessor's history after it was
  there stays absent (leaseexpiryN's `lease.lessorAt_absent_stays`, whose `lessorRdInv` is the member's heap);
  proved (`law_holds`) from the start's heap-free slot `lease.lessorSlot (Γ.ls mid)` (F2, 2026-11-26).
- `clientCoreAt_of_new`: what `Client.Close` reads of a client, from `New`'s result.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.S2Interim
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClientViewDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseGrantDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseGrantLiveDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseLeasesGrantedDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.LeaseLeasesLiveDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClientLeaseLeasesDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClientLeaseTTLDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AddrPlain
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Proof.go_etcd_io.etcd.client.v3.InvClientNew
public import Proof.go_etcd_io.etcd.client.v3.InvRetry
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorSlot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client
open etcd_dist.view

section member
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- **The member at `a`, as a lease workload's orchestrator holds it** (persistent): `a` is a valid
address and serves etcd's table for some member `mid` of the view `Γ`, whose lessor name `Γ.ls mid` has
the start's slot (`lease.lessorSlot`, P-L1: the member's `NewLessor` makes its lessor there). -/
def leaseMember (Γ : DistView) (a : GoString) : IProp GF :=
  iprop(⌜Net.addrOk a = true⌝ ∗ ∃ mid : w64, etcdAddrAt a Γ mid ∗ lease.lessorSlot (Γ.ls mid))

instance leaseMember_persistent (Γ : DistView) (a : GoString) :
    Persistent (leaseMember Γ a) := by
  unfold leaseMember; infer_instance

end member

section core
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **What `Client.Close` reads of a client, from `New`'s result**: `retryClientOk` gives it non-nil
with its logger, `clientKVAt` its connection and call options, `clientNoProxy` its configuration. -/
theorem clientCoreAt_of_new [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (cl : Loc) (eps : List GoString) (V : WEnv GF) :
    isNewClient cl eps V ∗ clientNoProxy cl ⊢ clientCoreAt cl := by
  iintro ⟨#Hnc, #Hnp⟩
  iunfold isNewClient at Hnc
  icases Hnc with ⟨#Hkv, #Hrc, -⟩
  iunfold clientKVAt at Hkv
  icases Hkv with ⟨%Hnn, %conn, %sl, #Hconn, -, #Hco, -⟩
  iunfold retryClientOk at Hrc
  icases Hrc with ⟨-, #Hlg, -⟩
  iunfold clientNoProxy at Hnp
  icases Hnp with ⟨%cfg, %n, -, #Hcfg, -⟩
  iunfold clientCoreAt
  iframe Hlg
  isplitr
  · ipureintro; exact Hnn
  isplitr
  · iexists conn; iexact Hconn
  isplitr
  · iexists sl; iexact Hco
  iexists cfg; iexact Hcfg

end core

section view
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`New`'s client of one member of the view** (persistent): `cl` is `New`'s client of the one endpoint
`ep`, dialing with no proxy, and `ep` serves member `mid` of `Γ`, whose lessor name has the start's slot. -/
def memberCli [π : NetProtoGS] (cl : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView)
    (mid : w64) : IProp GF :=
  iprop(isNewClient cl [ep] V ∗ clientNoProxy cl ∗ etcdAddrAt (Gg := hG.goose_globalGS) ep Γ mid ∗
    lease.lessorSlot (Γ.ls mid))

instance memberCli_persistent [π : NetProtoGS] (cl : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView)
    (mid : w64) : Persistent (memberCli cl ep V Γ mid) := by
  unfold memberCli; infer_instance

instance leaseClientAt_persistent [π : NetProtoGS] (cl lp : Loc)
    (ep : GoString) (V : WEnv GF) (Γ : DistView) (mid : w64) :
    Persistent (leaseClientAt cl lp ep V Γ mid) := by
  unfold leaseClientAt; infer_instance

/-- **The lease drafts' client fact from `memberCli`**: the client's `Lease` field (`New`'s). -/
theorem leaseClientV_of_memberCli [π : NetProtoGS] (cl : Loc) (ep : GoString) (V : WEnv GF) (Γ : DistView)
    (mid : w64) :
    memberCli cl ep V Γ mid ⊢ ∃ lp : Loc, leaseClientAt cl lp ep V Γ mid := by
  iintro #Hmc
  iunfold memberCli at Hmc
  icases Hmc with ⟨#Hnc, #Hnp, #Haddr, -⟩
  ihave #Hnc' := Hnc
  iunfold isNewClient at Hnc'
  icases Hnc' with ⟨-, -, -, -, ⟨%lp, #Hlf, -⟩, -⟩
  iexists lp
  iunfold leaseClientAt
  iframe #

/-- **A lease absent from member `mid`'s lessor history after it was there stays absent** (F2, 2026-11-26:
a theorem, `lessorAbsentStays_dist.law_holds`, over the heap-free slot; `notes/specs-only/ledger.md`, "2026-11-26:
`lessorAbsentStays_dist.law`"): from the start's slot of the member's lessor name `Γ.ls mid`
(`lease.lessorSlot`) and three snapshots of its history at `i ≤ k ≤ j`, the lease `id` in the first and not
in the second, it is not in the third. The single-process form is `lease.lessorAt_absent_stays`, over the
lessor's reader invariant `lessorRdInv`, which holds the member's heap; the slot gives that invariant at the
member's slot (`lease.lessorHistOk`), which a client at another machine can hold. It spends a later credit
(the slot is an invariant whose published law is not timeless). -/
abbrev lessorAbsentStays_dist.law : Prop :=
  ∀ (Γ : DistView) (mid : w64) (i k j : Nat) (σ ρ τ : lease.LSnap) (id : w64),
  (σ.1.lookup id).isSome → i ≤ k → ρ.1.lookup id = none → k ≤ j →
  £ 1 ∗ lease.lessorSlot (GF := GF) (Γ.ls mid) ∗ lease.lessorAt (Γ.ls mid) i σ ∗ lease.lessorAt (Γ.ls mid) k ρ ∗
      lease.lessorAt (Γ.ls mid) j τ ⊢
    |={⊤}=> ⌜τ.1.lookup id = none⌝

theorem lessorAbsentStays_dist.law_holds : lessorAbsentStays_dist.law (GF := GF) (hG := hG) :=
  fun Γ mid i k j σ ρ τ id hσ hik hρ hkj =>
    lease.lessorSlot_absent_stays (Γ.ls mid) i k j σ ρ τ id hσ hik hρ hkj

end view

end etcd_dist_client
end EtcdGrove
end Perennial
