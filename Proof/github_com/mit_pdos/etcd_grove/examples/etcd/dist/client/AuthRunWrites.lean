/-
**The dist auth workload's writes** (F7 stage S10; `Work.wp_proof_dist`'s updates): the dist `akWriteAu`
(`Proof/.../examples/lib/authwork/WorkCalls.lean`). Every write of a principal `P` (bound to users of `who`'s) sends
the update `akHist_writeAu` at the view's grant `opGrantD`: the grant, after the frozen set-up, is granted at
`setupSt` (`akGrantedL_of_writeGrantGD`), so the write is one `who` is granted (`akOpGranted`), which the history
admits (`hop`); the update tells that grant, which a refused write's caller refutes. Lean-first.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthRunDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthLeaseRefusals

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client go_etcd_io.etcd.server.v3.etcdserver
open etcd_dist etcd_dist.authd etcd_authlease

section writes
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **A view grant after the frozen set-up is a grant of `who`'s** (`akOpGranted`; the dist
`akOpGranted_of_grant`): each write's request through `akGrantedL_of_writeGrantGD`. -/
theorem akOpGranted_of_grantD (γk : KVNames) (γz : GName) (hs : List auth.AuthState)
    (Lset L₀ : List EntryModel) (r : Nat) (P : Option GoString) (who : GoString) (op : KVOp)
    (σ : KVState) (Em : CoPset) (hE : ↑authHistN ⊆ Em) (hpre : Lset <+: L₀)
    (hadm : admStates γk srvAuthSt0 Lset = hs) (hst : srvAuthAtLog γk srvAuthSt0 Lset = etcd_auth.setupSt r)
    (hPw : ∀ u, userOk P u → etcd_auth.akUser who u) :
    authHistFrozen (GF := GF) γk γz hs ⊢ opGrantD γk P op L₀ σ ={Em}=∗ ⌜etcd_auth.akOpGranted who op⌝ := by
  have hL : ∀ rq, akGrantedL who σ rq → etcd_auth.akGranted who rq :=
    fun _ ⟨r, hm, hg, hu⟩ => ⟨r, hm, hg.1, hu⟩
  iintro #Hz HG
  cases op with
  | put o =>
    iunfold opGrantD at HG
    imod (akGrantedL_of_writeGrantGD γk γz hs Lset L₀ r P who _ σ Em hE hpre hadm hst hPw) $$ Hz HG with %Hg
    imodintro; ipureintro; exact hL _ Hg
  | deleteRange o =>
    iunfold opGrantD at HG
    imod (akGrantedL_of_writeGrantGD γk γz hs Lset L₀ r P who _ σ Em hE hpre hadm hst hPw) $$ Hz HG with %Hg
    imodintro; ipureintro; exact hL _ Hg
  | txn t =>
    iunfold opGrantD at HG
    icases HG with ⟨%tw, %htw, HG⟩
    imod (akGrantedL_of_writeGrantGD γk γz hs Lset L₀ r P who _ σ Em hE hpre hadm hst hPw) $$ Hz HG with %Hg
    imodintro; ipureintro; exact ⟨tw, htw, hL _ Hg⟩
  | range o => imodintro; ipureintro; trivial
  | leaseGrant id ttl => imodintro; ipureintro; trivial
  | leaseRevoke id => imodintro; ipureintro; trivial

/-- **The update a write of `P`'s sends** (the dist `akWriteAu`): `akHist_writeAu` at the view's grant, read
at `setupSt` (`akOpGranted_of_grantD`); its result, the write granted to `who`. `hop`: a granted write is one
the history admits. -/
theorem akWriteAuD (γk : KVNames) (γz : GName) (hs : List auth.AuthState)
    (Lset L₀ : List EntryModel) (r : Nat) (P : Option GoString) (who : GoString) (op : KVOp)
    (hpre : Lset <+: L₀) (hadm : admStates γk srvAuthSt0 Lset = hs)
    (hst : srvAuthAtLog γk srvAuthSt0 Lset = etcd_auth.setupSt r)
    (hPw : ∀ u, userOk P u → etcd_auth.akUser who u)
    (hop : etcd_auth.akOpGranted who op → etcd_auth.opHistOk op) :
    etcd_auth.akHistInv (GF := GF) γk ∗ authHistFrozen γk γz hs ⊢
      writeAuD γk P op L₀ (fun _ => iprop(⌜etcd_auth.akOpGranted who op⌝)) := by
  iintro ⟨#Hinv, #Hz⟩
  ihave #Hw := etcd_auth.akHist_writeAu γk op (opGrantD γk P op L₀)
    (fun _ => iprop(⌜etcd_auth.akOpGranted who op⌝)) $$ [Hinv]
  · iframe Hinv
    iintro !> %σ Hg
    imod (akOpGranted_of_grantD γk γz hs Lset L₀ r P who op σ _ etcd_auth.authHistN_akMask hpre hadm hst hPw)
      $$ Hz Hg with %Hok
    imodintro
    isplitl []
    · ipureintro; exact hop Hok
    · ipureintro; exact Hok
  iunfold writeAuD
  imodintro
  iexact Hw

end writes

end etcd_dist_client
end EtcdGrove
end Perennial
