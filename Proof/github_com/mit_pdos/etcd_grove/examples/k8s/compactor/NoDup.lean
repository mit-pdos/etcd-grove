/-
**The compactor example's store writes no key twice in a revision** (Q1 (b), 2026-11-04): the
member's fact for watches (`mvcc.noDupKeys`, the arm of the create token's `watchNoDup` for a
compacting store), as `compactwatch`'s `noDupKeys_of_rounds`: the invariant's read update
(`oneChangeAu`: each revision has at most one change, `OneChange`) fires at every watched log
(`srvKVCoreM_fire`, from the member's KV facts), at a committed log it is a prefix of
(`oneChangePerKey_of_one`). Lean-first.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Aus
public import Proof.go_etcd_io.etcd.client.v3.WatchFire

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_compactor

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
theorem noDupKeys_of_one [go_etcd_io.raft.v3.Assumptions] [go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (V : client.WEnv GF) (γ : KVNames) (hst : γ.st = V.kst) :
    client.srvKVFacts V ∗ kvReadAu γ (fun σ => iprop(⌜OneChange σ⌝)) ⊢
      mvcc.noDupKeys V.R.E.γ := by
  iintro ⟨#Hkf, #Hau⟩
  iunfold client.srvKVFacts at Hkf
  icases Hkf with ⟨%on, %γr, #Hinvs, #H00, %Hkr, -⟩
  iunfold mvcc.noDupKeys
  iintro !> %log #Hev
  iunfold mvcc.evLog at Hev
  icases Hev with ⟨#Hs, #Hc⟩
  ihave #Hs' := Hs
  iunfold mvcc.idxSealed at Hs'
  icases Hs' with ⟨-, %Hwf, -⟩
  iunfold kvReadAu at Hau
  iunfold kvAu at Hau
  imod (srvKVCoreM_fire on V.R.E γr γ (by rw [hst, Hkr.1]) Hkr.2.1 log
      (fun σ => iprop(⌜OneChange σ⌝))) $$ Hinvs H00 Hs Hc Hau with ⟨%C, #HQ, %Hp⟩
  icases HQ with %Hov
  imodintro
  ipureintro
  exact oneChangePerKey_of_one log C Hov Hp Hwf.1

end proof

end k8s_compactor
end EtcdGrove
end Perennial
