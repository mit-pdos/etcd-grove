/-
The vocabulary of the dist auth workload's orchestrator (`RunAuth`, `examples/etcd/dist/client/auth.go`; F7 stage
S6, `notes/etcd-dist-f7.md`, "Handoff RA-1"). Lean-first (no Rocq counterpart).

`akDistEnv addrs Γ γR`: what the orchestrator hands each principal's machine with its call (`remotePrincipals`,
the principal service's request; persistent): after the set-up froze the cluster's auth history at `hs` (a
committed prefix `Lset`, auth state `setupSt r`), the KV invariant at `Γ.kv`, the history invariant
`etcd_auth.akHistInv Γ.kv` (the client half of `etcdKV Γ.kv`: every write a principal makes keeps it), the frozen
history, `Lset`'s lower bound, every endpoint's floor above `Lset` (the barriers': `watchFloorsD`), and the
view's tie `γR.raft.log = Γ.kv.rlog` (every `On_dist` contract's premise; added in S9). Auth.Work's
dist proof needs exactly these: each write's update under `akHistInv` (`akHist_writeAu`), each refusal at the
frozen state (`authFloorD_frozen`, `watchCheckedD_c_refuted`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.AuthWatchRefusal
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.authwork.Hist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.WatchClientDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.authwork.RootWatch

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client go_etcd_io.etcd.server.v3.etcdserver
open etcd_dist etcd_dist.authd

section pure
variable [GooseExts]

/-- Root's watch `Watch("", WithPrefix(), WithRev(1))`: `WatchOn_dist`'s request premise. -/
theorem watch_all_okD :
    (opWatchModel ([] : GoString) [withPrefixM, withRevM (W64 1)]).isRangeWatchP (W64 1) = true ∧
      ¬ opWatchPanics ([] : GoString) [withPrefixM, withRevM (W64 1)] ∧ 1 ≤ sint.Z (W64 1) ∧
      watchSizeOk (opWatchModel ([] : GoString) [withPrefixM, withRevM (W64 1)]) := by
  refine ⟨?_, etcd_auth.watch_all_ok.2, by decide, ?_⟩
  · simp [opWatchModel, op_simps, OpFull.isRangeWatchP]
  · unfold watchSizeOk
    simp [opWatchModel, op_simps]

/-- u's watch `Watch("a", WithRange("b"), WithRev(1))`: `WatchOn_dist`'s request premise. -/
theorem watch_ab_okD :
    (opWatchModel etcd_auth.lo [withRangeM etcd_auth.hi, withRevM (W64 1)]).isRangeWatchP (W64 1) = true ∧
      ¬ opWatchPanics etcd_auth.lo [withRangeM etcd_auth.hi, withRevM (W64 1)] ∧ 1 ≤ sint.Z (W64 1) ∧
      watchSizeOk (opWatchModel etcd_auth.lo [withRangeM etcd_auth.hi, withRevM (W64 1)]) := by
  refine ⟨?_, etcd_auth.watch_ab_ok.1.2, by decide, ?_⟩
  · simp [opWatchModel, op_simps, OpFull.isRangeWatchP]
  · unfold watchSizeOk
    simp [opWatchModel, op_simps]

/-- A principal's watch `Watch("c/", WithPrefix(), WithRev(1))`: `WatchOn_dist`'s request premise. -/
theorem watch_c_okD :
    (opWatchModel go!"c/" [withPrefixM, withRevM (W64 1)]).isRangeWatchP (W64 1) = true ∧
      ¬ opWatchPanics go!"c/" [withPrefixM, withRevM (W64 1)] ∧ 1 ≤ sint.Z (W64 1) ∧
      watchSizeOk (opWatchModel go!"c/" [withPrefixM, withRevM (W64 1)]) := by
  refine ⟨?_, etcd_auth.watch_c_ok.1.2, by decide, ?_⟩
  · simp [opWatchModel, op_simps, OpFull.isRangeWatchP]
  · unfold watchSizeOk
    simp [opWatchModel, op_simps]
    decide

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **The principals' environment** (see the file header). -/
def akDistEnv [NetProtoGS] (addrs : List GoString) (Γ : DistView) (γR : ServerRaftNames) : IProp GF :=
  iprop(∃ (γz : GName) (hs : List auth.AuthState) (Lset : List EntryModel) (r : Nat),
    kvInvOn γR Γ.kv srvAuthSt0 ∗ etcd_auth.akHistInv Γ.kv ∗ authHistFrozen Γ.kv γz hs ∗
    srvReqLogLb γR Lset ∗ watchFloorsD addrs Γ γR Lset ∗
    ⌜admStates Γ.kv srvAuthSt0 Lset = hs ∧ srvAuthAtLog Γ.kv srvAuthSt0 Lset = etcd_auth.setupSt r ∧
      γR.raft.log = Γ.kv.rlog⌝)

instance akDistEnv_persistent [NetProtoGS] (addrs : List GoString) (Γ : DistView) (γR : ServerRaftNames) :
    Persistent (akDistEnv (GF := GF) addrs Γ γR) := by
  unfold akDistEnv; infer_instance

/-- **A write the history admits, under the history invariant, is an auth-on write update** (its grant
ignored: `akHist_writeAu` at `G := opGrantD …`). -/
theorem akHist_writeAuD (γk : KVNames) (P : Option GoString) (op : KVOp) (L₀ : List EntryModel)
    (hop : etcd_auth.opHistOk op) :
    etcd_auth.akHistInv (GF := GF) γk ⊢ writeAuD γk P op L₀ (fun _ => iprop(True)) := by
  iintro #Hinv
  ihave #Hau := etcd_auth.akHist_writeAu γk op (opGrantD γk P op L₀) (fun _ => iprop(True)) $$ [Hinv]
  · isplitl []
    · iexact Hinv
    · iintro !> %σ -
      imodintro
      isplitl []
      · ipureintro; exact hop
      · itrivial
  iunfold writeAuD
  imodintro
  iexact Hau

/-- A user client of one endpoint is a watch client of it. -/
theorem watchClient_of_userCli [π : NetProtoGS] (cl : Loc) (a : GoString) (V : WEnv GF)
    (cfg : go_etcd_io.etcd.client.v3.Config) (Γ : DistView) :
    userCli cl a V cfg ∗ membersAt (Gg := hG.goose_globalGS) [a] Γ ⊢
      ∃ w : Loc, watchClientAt cl w [a] V Γ := by
  iintro ⟨#Hu, #Hms⟩
  iunfold userCli at Hu
  icases Hu with ⟨#Hnc, #Hnp, -, -⟩
  iapply watchClient_of_new cl [a] V Γ
  iframe #

/-- **`watchFloorsD` narrows to one of its endpoints** (a principal's client is at one: `Work.spec_dist`). -/
theorem watchFloorsD_of_mem [NetProtoGS] (addrs : List GoString) (Γ : DistView) (γR : ServerRaftNames)
    (L₀ : List EntryModel) (a : GoString) (ha : a ∈ addrs) :
    watchFloorsD (GF := GF) addrs Γ γR L₀ ⊢ watchFloorsD [a] Γ γR L₀ := by
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp ha
  unfold watchFloorsD
  refine (BigSepL.bigSepL_lookup (PROP := IProp GF) (List.getElem?_eq_some_iff.mpr ⟨hi, hget⟩)).trans ?_
  exact (BigSepL.bigSepL_singleton (PROP := IProp GF)
    (Φ := fun _ a => iprop(∃ (mid : w64) (m : Nat),
      etcdAddrAt (Gg := hG.goose_globalGS) a Γ mid ∗ authFloorD Γ γR mid L₀ m))).2

/-- **What a principal's client at `a ∈ addrs` takes from the principals' environment** (`Work.spec_dist`'s
proof): a committed prefix `L₀` (the set-up's) with its lower bound, the floors at `a` above it, the view's
tie, and the refusal of every checked create of its watch of `[c/, c0)` (`watchCheckedD_c_refuted`). -/
theorem akDistEnv_watch [NetProtoGS] (addrs : List GoString) (Γ : DistView) (γR : ServerRaftNames)
    (a : GoString) (ha : a ∈ addrs) (P : Option GoString)
    (hP : P = none ∨ P = some go!"u" ∨ P = some go!"v") :
    akDistEnv (GF := GF) addrs Γ γR ⊢ ∃ L₀ : List EntryModel, ⌜γR.raft.log = Γ.kv.rlog⌝ ∗
      srvReqLogLb γR L₀ ∗ watchFloorsD [a] Γ γR L₀ ∗
      □ (∀ E : CoPset, ⌜authTieReadMask ⊆ E⌝ -∗
        watchCheckedD [a] Γ γR P L₀ go!"c/" go!"c0" ={E}=∗ False) := by
  iintro #H
  iunfold akDistEnv at H
  icases H with ⟨%γz, %hs, %Lset, %r, #Hinv, -, #Hfz, #HL, #Hfl, %Hset⟩
  obtain ⟨hadm, hst, htie⟩ := Hset
  ihave #Hfa := watchFloorsD_of_mem addrs Γ γR Lset a ha $$ Hfl
  iexists Lset
  isplitr
  · ipureintro; exact htie
  iframe #
  iintro !> %E %hE #Hw
  iapply (watchCheckedD_c_refuted [a] Γ γR P Lset Lset γz hs r (List.prefix_refl _) hadm hst hP E hE)
    $$ Hinv Hfz Hw

end defs

end etcd_dist_client
end EtcdGrove
end Perennial
