/-
Lean-first (no Rocq counterpart).

# Certifying a snapshot the replica takes (2026-10-29, kvreconf's `maybeSnapshot`)

The applier at the committed prefix `ap` (`repOwn`) encodes its maps (`encodeState`): the bytes are
`ap`'s replicated state (`kvr_snapOk_of`). `kvr_snap_make` records the snapshot in the store's
registry (`kvrSnapInv`, `snapshotCert_make`: its lists well formed by `Membership.Valid.snapListsOk'`,
the configuration `confAt` reached and below `2^61` ids, `repOwn`'s), and gives the `snapshotValid`
that `MemoryStorage.CreateSnapshot` takes (`J.SV` of `kvrJ`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Defs
public import Proof.go_etcd_io.raft.v3.ConfchangeApi

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The encoding of the applier's maps is its prefix's state. -/
theorem kvr_snapOk_of [GooseExts] (ap : List LogEntry) (K A : GMap (List w8) (List w8))
    (kvs ops : List (List w8 × List w8)) (Hk : KVsOf K kvs) (Ho : KVsOf A ops)
    (Hval : ∀ k, (K !! k).getD [] = kvFold (logHist ap) k) (HA : AppliedOk A (logHist ap)) :
    kvSnapOk ap (encState kvs ops) := by
  refine ⟨kvs, ops, rfl, Hk.1, Ho.1, ?_, ?_⟩
  · intro k; rw [Hk.2 k]; exact Hval k
  · have : (fun o => ops.lookup o) = (fun d => A !! d) := funext Ho.2
    rw [this]; exact HA

theorem kvrSnapN_raftN : (↑kvrRaftN : CoPset) ⊆ ⊤ \ ↑kvrSnapN :=
  mask_ndot_ne' nroot "kvreconf_raft" "kvreconf_snaps" (by decide)

section make
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [StorageModel GF] [AllG GF]

/-- **Certifying the applier's snapshot** at the committed prefix `ap` (its length `i`, its last
term `t`), the configuration `cs` denoting `m` there, the data `d` its state. -/
theorem kvr_snap_make (γr : RNames) (vs : List w64) (ap : List LogEntry) (i t : w64)
    (d : List w8) (m : Membership) (cs : ConfStateM) (sv0 : SnapshotM)
    (Hlen : ap.length = uint.nat i) (Hpos : 0 < uint.Z i) (Hi : uint.Z i < 2 ^ 61)
    (Hlast : Option.map LogEntry.term ap.getLast? = some t)
    (Hcs : confStateIs cs m) (Hsz : GMap.size m.ids < 2 ^ 61) (Hd : kvSnapOk ap d) :
    ⊢ kvrCluster (GF := GF) γr vs -∗ isCommittedLogLb γr.cluster ap -∗
      confAt γr.cluster ap.length m ={⊤}=∗
      snapshotValid γr.cluster (memSnapCreated sv0 i t (some cs) d) := by
  iintro #Hcl #Hl #Ha
  ihave %Hv := confAt_valid γr.cluster ap.length m $$ Ha
  ihave %Hr := confAt_restorable γr.cluster ap.length m $$ Ha
  have Hok : SnapListsOk ⟨⟨t, i⟩, cs.lists, m.autoLeave, d⟩ :=
    Membership.Valid.snapListsOk' Hv Hr Hcs Hsz Hi
  unfold kvrCluster
  icases Hcl with ⟨#Hc, -, -, #Hinv, -⟩
  unfold kvrSnapInv
  iinv Hinv with Hb Hclose
  icases Hb with ⟨%S, >Hown, HS⟩
  imod snapshotCert_make γr.cluster kvrRaftN (⊤ \ ↑kvrSnapN) ap i t d m cs S kvrSnapN_raftN
      Hlen Hlast Hok Hcs $$ Hc Hl Ha Hown with ⟨Hown, #Hcert⟩
  imod Hclose $$ [Hown HS] with -
  · inext
    iexists S ++ [⟨ap.length, m, d⟩]
    iframe Hown
    iapply (BigSepL.bigSepL_snoc (Φ := fun _ s => kvrSnapRecOk (GF := GF) γr s)).2
    iframe HS
    unfold kvrSnapRecOk
    iexists ap
    iframe Hl Ha
    ipureintro
    exact ⟨rfl, Hd, Hsz⟩
  imodintro
  iapply snapshotCert_valid γr.cluster kvrRaftN (memSnapCreated sv0 i t (some cs) d) Hpos Hi
  iframe Hc
  have Hal : cs.AutoLeave' = m.autoLeave := Hcs.2.2.2.2
  simp only [snapTrip, snapId, memSnapCreated, Option.getD_some, Hal]
  iexact Hcert

end make

end kvreconf
end EtcdGrove
end Perennial
