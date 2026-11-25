/-
The vocabulary of the lease workloads of `examples/etcd/dist/client` (#50 N9b, 2026-11-25;
`notes/etcd-dist-n9b.md`). Lean-first (no Rocq counterpart).

- `leaseMember a`: what a lease workload's orchestrator holds of the member at `a`: a valid address
  (`Net.addrOk`, `deployment.WellFormed`'s) that serves etcd's table for some member (`etcdAddrAt`).
- `clientCoreAt_of_new`: what `Client.Close` reads of a client, from `New`'s result.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.S2Interim
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AddrPlain
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Proof.go_etcd_io.etcd.client.v3.InvClientNew
public import Proof.go_etcd_io.etcd.client.v3.InvRetry

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client

section member
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- **The member at `a`, as a lease workload's orchestrator holds it** (persistent): `a` is a valid
address and serves etcd's table for some member. -/
def leaseMember (a : GoString) : IProp GF :=
  iprop(⌜Net.addrOk a = true⌝ ∗ ∃ (γE : GName) (mid : w64), etcd_dist.etcdAddrAt a γE mid)

instance leaseMember_persistent (a : GoString) : Persistent (leaseMember (GF := GF) a) := by
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

end etcd_dist_client
end EtcdGrove
end Perennial
