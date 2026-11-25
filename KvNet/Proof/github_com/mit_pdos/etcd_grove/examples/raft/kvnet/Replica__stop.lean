/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/Replica__stop.lean`. Lean-first
(no Rocq counterpart; kvdurable's `Replica.stop` proof with its `crash`'s last `dmu` section, 2026-11-24,
G5).

`stopc` closed with the closer's token; `run`'s half of `nodeRunning` received on `runDone` (with its
claim on the pending batch, dropped: the start resource does not need it), `tickDone`'s nothing, the
snapshotter's half on `snapDone`; `node.Stop` with the whole of `nodeRunning`, which gives the vacancy
armed at the node's arm, the generation's (`nodeArm_agree` with `isReplica`'s `#Harm`). Then `dmu` is
taken and never released: its invariant's file handle, call permission and writer's half
(`kdWriter ph.fl S o`) come out, and the file invariant, opened with the crash token (`notCrashed`
refutes its crashed side) and a later credit, gives `fileHolds γ S (kdFileVal o)` (the writer's halves
agree: the file is outside a write's window, at `S`). That is `kvStart` at the generation's names.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Replica__stop
public import KvNet.Spec.go_etcd_io.raft.v3.node__Stop
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.DefsLaws
public import Perennial.GooseLang.NotCrashed

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

theorem Replica.stop.wp_proof (wp_Stop : node.Stop.spec (GF := GF) (hG := hG)) :
    Replica.stop.spec (GF := GF) (hG := hG) := by
  intro γ vs dir id r
  wp_start as Hs
  iunfold repStopper at Hs
  icases Hs with ⟨%n, %st, %sts, %sq, %ρ, #HR, Hpend, Hrd, Htd, Hsd⟩
  ihave #HR' := HR
  iunfold isReplicaR at HR'
  iNamed HR'
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Htt : □ (True : IProp GF) $$ []
  · imodintro; itrivial
  try wp_auto
  wp_apply wp_broadcast_chan_close ρ.stopc ρ.sc iprop(True) $$ [$Hpend $Htt] as -
  try wp_auto
  wp_apply wp_handoff_receive ρ.rd ρ.rdc (fun _ => iprop(nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half ∗
      ∃ v : Option GName × RaftState, ghostVar ρ.ph.ph (1 : Qp).half v))
    iprop(True) iprop(False) false $$ [$HrdH $Hrd] as %u %ok ⟨-, Hgot⟩
  unfold handoffGot
  ihave ⟨Hrun1, -⟩ : iprop(nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half ∗
      ∃ v : Option GName × RaftState, ghostVar ρ.ph.ph (1 : Qp).half v) $$ [Hgot]
  · cases ok with
    | true => simp only [Bool.false_eq_true, ↓reduceIte]; icases Hgot with ⟨$, -⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hgot with ⟨-, Hf⟩
      iexfalso; iexact Hf
  try wp_auto
  wp_apply wp_handoff_receive ρ.td ρ.tdc (fun _ => iprop(True)) iprop(True) iprop(False) false
    $$ [$HtdH $Htd] as %u' %ok' -
  try wp_auto
  wp_apply wp_handoff_receive ρ.sd ρ.sdc (fun _ => nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half)
    iprop(True) iprop(False) false $$ [$HsdH $Hsd] as %u'' %ok'' ⟨-, Hgot2⟩
  unfold handoffGot
  ihave Hrun2 : nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half $$ [Hgot2]
  · cases ok'' with
    | true => simp only [Bool.false_eq_true, ↓reduceIte]; icases Hgot2 with ⟨$, -⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hgot2 with ⟨-, Hf⟩
      iexfalso; iexact Hf
  ihave Hrun : nodeRunning n γ.r.cluster kdRaftN ((1 : Qp).half + (1 : Qp).half) $$ [Hrun1 Hrun2]
  · iapply (nodeRunning_fractional n γ.r.cluster kdRaftN).fractional _ _ |>.2
    iframe Hrun1 Hrun2
  rw [Qp.half_add_half]
  try wp_auto
  wp_apply (lc := 1) wp_Stop n γ.r.cluster kdRaftN id $$ [$Hraft $HisNode $Hrun] as ⟨-, %x, Hvac, #Harm'⟩
  ihave %Hx := nodeArm_agree n γ.r.cluster x ρ.ph.fl.x $$ Harm' Harm
  subst Hx
  -- `dmu`, never released: the writer, the handle and the call permission out of its invariant
  try wp_auto
  wp_apply +noauto sync.Mutex.wp_Lock _ _ $$ [$Hdmu] as ⟨-, HI⟩
  iunfold kdDmuInv at HI
  iNamed HI
  icases Hlive with ⟨%S, %o, %pz, Hwr, -, -, -, -⟩
  icases Hcpm with ⟨%qc, Hcpm⟩
  -- the file invariant, with the crash token: the writer's halves agree, the file holds `S`
  iapply wp_ncfupd _ _ rfl
  iintro Hnc
  iunfold kdFileInvK at HfInv
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ HfInv with ⟨Hb, Hclose⟩
  imod lc_fupd_elim_later $$ Hlc1 Hb with Hb
  iunfold kdFileBody at Hb
  icases Hb with ⟨%S0, %s0, %pb0, Hds, Hwv, Hb⟩
  iunfold kdWriter at Hwr
  ihave %Hag := ghostVar_agree ρ.ph.fl.wr _ _ _ _ $$ Hwr Hwv
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl, rfl⟩ := Hag
  icases Hb with (⟨HrS, Hfs⟩ | ⟨Hcr, -⟩)
  rotate_left
  · iexfalso; iapply notCrashed_crashed $$ Hnc Hcr
  iunfold kdFileState at Hfs
  icases Hfs with ⟨#Hfh, -⟩
  imod Hclose $$ [Hds Hwv HrS] with -
  · inext
    iunfold kdFileBody
    iexists S, ⟨kdFileVal o, none⟩, none
    iframe Hds Hwv
    ileft
    iframe HrS
    iunfold kdFileState
    isplitr
    · iexact Hfh
    ipureintro; rfl
  imodintro
  iframe Hnc
  try wp_auto
  iapply HΦ
  iexists ρ.ph.fl, qc
  iunfold kvStart
  iexists S, kdFileVal o
  iframe Hcl Hos HosS Hdi Hdh Hcpm Hwr Hfh Hvac
  isplitr
  · iunfold kdFileInvK; iexact HfInv
  ipureintro
  exact ⟨Hdf.1, Hdf.2, Hidr.1, Hidr.2⟩

end proof

end raft_kvnet
end EtcdGrove
end Perennial
