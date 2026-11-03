/-
Lean-first (no Rocq counterpart).

# Certifying a snapshot the replica takes (2026-11-01, durability stage II (f))

kvreconf's `SnapMake` (`kvr_snap_make`) at kvdurable's registry (`kdSnapInv`, in `kdCluster`), its
proof kvreconf's: the applier's snapshot at the committed prefix `ap` recorded in the store's
registry, and its `snapshotValid` (what `MemoryStorage.CreateSnapshot` takes, `J.SV` of `kdJ`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.DefsLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.SnapMake

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- kvdurable's codec (`Codec.lean`, a copy of kvreconf's) is kvreconf's. -/
theorem encKVs_eq [GooseExts] (kvs : List (List w8 × List w8)) : encKVs kvs = kvreconf.encKVs kvs := by
  induction kvs with
  | nil => rfl
  | cons p r ih => simp only [encKVs, kvreconf.encKVs, ih, putB, kvreconf.putB]

theorem encState_eq [GooseExts] (kvs ops : List (List w8 × List w8)) :
    encState kvs ops = kvreconf.encState kvs ops := by
  simp only [encState, kvreconf.encState, encMap, kvreconf.encMap, encKVs_eq]

theorem KVsOf_eq [GooseExts] (K : GMap (List w8) (List w8)) (kvs : List (List w8 × List w8)) :
    KVsOf K kvs → kvreconf.KVsOf K kvs := by
  intro h; exact h

section make
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

theorem kdSnapN_raftN : (↑kdRaftN : CoPset) ⊆ ⊤ \ ↑kdSnapN :=
  mask_ndot_ne' nroot "kvdurable_raft" "kvdurable_snaps" (by decide)

/-- **Certifying the applier's snapshot** at the committed prefix `ap` (its length `i`, its last
term `t`), the configuration `cs` denoting `m` there, the data `d` its state. -/
theorem kd_snap_make (γ : KdNames) (vs : List w64) (ap : List LogEntry) (i t : w64)
    (d : List w8) (m : Membership) (cs : ConfStateM) (sv0 : SnapshotM)
    (Hlen : ap.length = uint.nat i) (Hpos : 0 < uint.Z i) (Hi : uint.Z i < 2 ^ 61)
    (Hlast : Option.map LogEntry.term ap.getLast? = some t)
    (Hcs : confStateIs cs m) (Hsz : GMap.size m.ids < 2 ^ 61) (Hd : kvreconf.kvSnapOk ap d) :
    ⊢ kdCluster (GF := GF) γ vs -∗ isCommittedLogLb γ.r.cluster ap -∗
      confAt γ.r.cluster ap.length m ={⊤}=∗
      snapshotValid γ.r.cluster (memSnapCreated sv0 i t (some cs) d) := by
  iintro #Hcl #Hl #Ha
  ihave %Hv := confAt_valid γ.r.cluster ap.length m $$ Ha
  ihave %Hr := confAt_restorable γ.r.cluster ap.length m $$ Ha
  have Hok : SnapListsOk ⟨⟨t, i⟩, cs.lists, m.autoLeave, d⟩ :=
    Membership.Valid.snapListsOk' Hv Hr Hcs Hsz Hi
  unfold kdCluster
  icases Hcl with ⟨#Hc, -, -, #Hinv, -, -⟩
  unfold kdSnapInv
  iinv Hinv with Hb Hclose
  icases Hb with ⟨%S, >Hown, HS⟩
  imod snapshotCert_make γ.r.cluster kdRaftN (⊤ \ ↑kdSnapN) ap i t d m cs S kdSnapN_raftN
      Hlen Hlast Hok Hcs $$ Hc Hl Ha Hown with ⟨Hown, #Hcert⟩
  imod Hclose $$ [Hown HS] with -
  · inext
    iexists S ++ [⟨ap.length, m, d⟩]
    iframe Hown
    iapply (BigSepL.bigSepL_snoc (Φ := fun _ s => kdSnapRecOk (GF := GF) γ s)).2
    iframe HS
    unfold kdSnapRecOk
    iexists ap
    iframe Hl Ha
    ipureintro
    exact ⟨rfl, Hd, Hsz⟩
  imodintro
  iapply snapshotCert_valid γ.r.cluster kdRaftN (memSnapCreated sv0 i t (some cs) d) Hpos Hi
  iframe Hc
  have Hal : cs.AutoLeave' = m.autoLeave := Hcs.2.2.2.2
  simp only [snapTrip, snapId, memSnapCreated, Option.getD_some, Hal]
  iexact Hcert

end make

end kvdurable
end EtcdGrove
end Perennial
