/-
`NewServer(cfg)` on a data directory a crash left: `NewServer.wp_proofC`, the proof of
`NewServer.specC` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/NewServerCrash.lean`; etcd-dist D6, T4,
2026-11-24, `notes/etcd-dist-d6.md` §4). **WIP: one labeled `sorry`, not linked.**

Over `NewServer.specRAt` (`NewServerRAt.lean`: the graceful restart's proof `NewServer.wp_proofRG`,
`bootstrap`'s contract at the image), taken as a callee. Two cases on the image (`srvCrashImageAt_disk`):

* the image is a graceful one (`σ.b ≤ i ≤ σ.commit`, `bootLen ≤ i`, the stored `confState` the index's):
  **proved**. The crash image is then turned into the graceful one (the vacancy armed,
  `wal.stopImage`), and the crash contract at it, with the WAL's read facts the image carries, is the
  restart contract's instance (`bootstrapAtR_of_crash`).
* otherwise: **`sorry` (WIP)**. Since T10's restatement of `srvCrashImageAt` (2026-11-25) this case
  holds, beside the one below, the received-snapshot window (`i < σ.b`, `snapRowB2`: `bootstrap`'s
  `.snap.db` recovery, the contract's second case), a backend index inside the bootstrap batch
  (`i < bootLen`) and a stored `confState` one conf change ahead (`confRowW`). The case
  `σ.commit < i` (the backend ahead of the WAL's commit, which a power loss can leave): Not an instance of the graceful proof: raft restarts at the WAL's commit, below the
  backend's log `A` (`|A| = i`), and the graceful restart's construction needs `|A| ≤ σ.commit`
  throughout: `NodeStartSpecR`'s premise and `rnBootPre`'s (`bootstrappedRaft.newRaftNode.spec` at
  `.restart`), `replaySeed_facts` (the replayed terms read from the WAL's entries up to `|A|`, which
  may be past the WAL's last index), and `isRaftNode`'s restart data `rnRestartOk`
  (`snap0 ≤ |a0| ≤ commit0`), whose `|a0| ≤ commit0` the running server uses in `raftNode.start`
  (`rnRestartOk_a0_le`: the stop's image, `rnStopImage`) and in the apply thread's snapshot window
  (`rnRestartOk_winAbove`: a `Ready`'s snapshot above the backend's log). The last is false after a
  crash: a leader's snapshot at an index in `(σ.last, i]` is restorable by raft (its entry not in the
  restarted log) and the apply thread installs it (`applySnapshot` checks only `> appliedi`), so the
  backend goes back to that index. `notes/etcd-dist-d6.md` §4 (T4) has the plan.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerRAt

@[expose] public section

set_option linter.unusedSectionVars false

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

/-- **`NewServer(cfg)` on a crash image** (`NewServer.specC`), over the restart at one image
(`NewServer.specRAt`). WIP: the case `σ.commit < i` is `sorry` (see the file header). -/
theorem NewServer.wp_proofC (hRAt : NewServer.specRAt (GF := GF) (hG := hG)) :
    NewServer.specC (GF := GF) (hG := hG) := by
  intro cfg U γ id ρ ρo E₀ N Φs γn dir m S σ i A D mb M HρRaft HrN Hrule Hnsm Hc0 Hch0 Hlog0 Hkcmp Hcbl
    Hmrb Hmto Hcb Hcmp0 HNx0 Hbnd Hrb HrbN Hboot Hpfx HΦs Hfgp Hdirok HpU HfU HfC Hrnc Hdirs Hlbc Hbco Hfnc
    Hdwd Hbwb
  letI : MemStorReg GF := ⟨γ.reg⟩
  iintro %Φ Hpre HΦ
  iNamed Hpre
  imod srvCrashImageAt_disk γ ρo id cfg.DataDir' S σ i A D mb M ⊤ $$ Himg with
    (⟨Himg, %Hw, HcT⟩ | ⟨Himg, %hng⟩)
  · have h' := hRAt cfg U γ id ρ ρo E₀ N Φs γn dir m S σ i A D mb M HρRaft HrN Hrule Hnsm Hc0 Hch0
      Hlog0 Hkcmp Hcbl Hmrb Hmto Hcb Hcmp0 HNx0 Hbnd Hrb HrbN Hboot Hpfx HΦs Hfgp Hdirok HpU HfU HfC Hrnc
      Hdirs Hlbc Hbco Hfnc Hdwd Hbwb
    ihave #HbootR := bootstrapAtR_of_crash cfg U γ id N dir σ i A D M Hw $$ HbootC
    icases HcT with ⟨HcT, HsK⟩
    iapply h' $$ [-HΦ HcT HsK]
    · iframe
      iframe %Hγn
      iframe %Haufit
      iframe %Hbuq
      iframe %Hdisk
      iframe %Hmmap
      iframe #
    inext
    iintro %srv %err Hq
    iapply HΦ
    iframe HcT HsK Hq
  · -- WIP (etcd-dist D6 T4): the image not a graceful one; see the file header.
    sorry

end proof

end EtcdGrove
end Perennial
