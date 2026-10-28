/-
**The rest buckets after `applySnapshot`** (D22 receiver epochs, S8d, step 5 of
`srvSnapApplied_of_walk`, `notes/snapshot-s8-plan.md`): `srvRest` at the snapshot's environment and
entries `A'`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyNames

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Step 5: the rest buckets at the snapshot's entries** `A'`.

Brief for the prover: `unfold srvRest`, `simp only [snapE_RO]` (or `rfl`-`show`), unfold
`srvRestOwnH srvRestOwn srvObjsOn`, rewrite with `hA'.1` and `hA'.2` (`restModel …`'s `.bk` and
`.mem`; `simp only at` first if a projection of a literal record shows up), `hγB` for the tracked
buckets' names, and frame the hypotheses. -/
theorem snap_srvRest (E : apply.AEnv GF) (γ' : ApplyNames) (TM' : MetaCI → IProp GF) (ci : Loc)
    (p' : mvcc.PhysNames) (g : GoFunc) (γB : backend.BNames) (d' : mvcc.KBReal) (γr : ReadNames)
    (al ast lp cl : Loc) (bk : GMap GoString backend.BktData) (memI : GMap w64 apply.MemberM)
    (A' : List EntryModel) (hγB : d'.γB = γB)
    (hA' : (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).bk = bk ∧
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem = memI) :
    backend.rbOwn d'.γB bk ∗ membership.clusterMem cl memI ∗
      alarmBeOn al d'.be ∗ authBeOn ast d'.be ∗ clusterBeOn cl d'.be ∗ lease.lessorBeOn lp d'.be ⊢
    srvRest (snapE E γ' TM' ci p' g γB al ast lp cl d'.be) γr A' := by
  subst hγB
  unfold srvRest
  rw [snapE_RO]
  unfold srvRestOwnH srvRestOwn srvObjsOn
  rw [hA'.1, hA'.2]
  iintro ⟨H1, H2, H3, H4, H5, H6⟩
  iframe

end proof
end EtcdGrove
end Perennial
