/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E: **raft's durable state at the disk
after a synchronous write** (`StorageHolds`, `loopRestB2`'s, `restartRaft`'s): from the disk at the
loop head's durable state, a `Ready`'s write without a snapshot (`saveW`, from `base0`) leaves the disk
at the `Ready`'s durable state (`readyDurable`); the write's commit at least the disk's (commits only
grow: `AntSim.commit_reachD`) keeps the lowest restart commit (`wcommit`) below the disk's. The
etcdserver WAL's `walSave_holds`, without snapshots.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Phases
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Report
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessReportB2
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Mono

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **The disk after a synchronous write holds the `Ready`'s durable state**: from the disk `dk` at the
durable state `D` (`StorageHolds`), the write of the hard state `oh` (none: the disk's) and the entries
`es` (`saveW`, continuing the log: `SaveOk`) at the `Ready`'s hard state `H` (`oh`'s, or the disk's)
leaves the disk at `readyDurable D H none es`, given the write's commit at least the disk's. -/
theorem storageHolds_saveW (D : RaftState) (dk : AntSim.DurW) (H : HardStateM)
    (oh : Option HardStateM) (es : List EntryM)
    (h0 : StorageHolds D (diskContents dk))
    (hoh : oh.getD (HardStateM.mk dk.term dk.vote dk.commit) = H)
    (hok : SaveOk dk es)
    (hc : uint.Z dk.commit ≤ uint.Z H.Commit') :
    StorageHolds (readyDurable D H none es) (diskContents (saveW dk oh es)) := by
  obtain ⟨hb, ht, he, hT, hV, -, hw, -, -, -⟩ := h0
  simp only [diskContents, base0, StorContents.commit] at hb ht he hT hV hw
  have hbz : uint.Z D.base.index' = 0 := by
    have : uint.Z (W64 0) = 0 := rfl
    have : 0 ≤ uint.Z D.base.index' := Int.natCast_nonneg _
    omega
  have hbi : D.base.index' = W64 0 := by
    apply BitVec.eq_of_toNat_eq
    have : uint.Z D.base.index' = ((D.base.index').toNat : Int) := rfl
    have : (D.base.index').toNat = 0 := by omega
    simpa using this
  have hents : dk.log = D.ents := by
    rw [he]; unfold RaftState.entsFrom; rw [hbz]; simp
  have hterm : ∀ l : List EntryM, plogTermAt D.base l (W64 0) = some D.base.term' := by
    intro l; unfold plogTermAt
    have : uint.Z (W64 0) = 0 := rfl
    rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega)), ite_eq_left_iff.mpr (fun h => absurd (by omega) h)]
  have hbt : D.base.term' = W64 0 := by
    rw [hterm] at ht; exact Option.some.inj ht
  have hz : uint.Z (W64 0) = 0 := rfl
  have hzn : uint.nat (W64 0) = 0 := rfl
  have hfrom : ∀ S : RaftState, S.entsFrom base0 = S.ents := by
    intro S; unfold RaftState.entsFrom base0; simp only [hz]; simp
  cases es with
  | nil =>
    have hsave : saveW dk oh [] = ⟨H.Term', H.Vote', H.Commit', dk.log⟩ :=
      saveW_ready dk oh [] H _ hoh (fun _ => rfl) (fun _ h => by simp at h)
    rw [hsave]
    unfold StorageHolds readyDurable RaftState.next
    simp only [Option.map_none, diskContents, StorContents.b, StorContents.commit,
      Option.isSome_none, Bool.false_or, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ite_false]
    refine ⟨by unfold base0; omega, by unfold base0; rw [hterm, hbt], ?_, trivial, trivial,
      by show uint.nat (W64 0) ≤ _; omega, ?_, Nat.le_refl _, by simp, ?_⟩
    · rw [hfrom]; simpa [appendEnts] using hents
    · have : uint.nat D.wcommit ≤ uint.nat dk.commit := hw
      have : uint.nat dk.commit ≤ uint.nat H.Commit' := by
        have h1 : uint.Z dk.commit = (uint.nat dk.commit : Int) := rfl
        have h2 : uint.Z H.Commit' = (uint.nat H.Commit' : Int) := rfl
        omega
      omega
    · exact fun h => h hbi
  | cons e0 t =>
    have hsave : saveW dk oh (e0 :: t) =
        ⟨H.Term', H.Vote', H.Commit', dk.log.take (uint.nat e0.Index' - 1) ++ e0 :: t⟩ :=
      saveW_ready dk oh _ H _ hoh (fun h => by simp at h)
        (fun e h => by simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at h; subst h; rfl)
    rw [hsave]
    have h1 := (hok e0 (by simp)).1
    have hi : uint.Z e0.Index' = (uint.nat e0.Index' : Int) := rfl
    unfold StorageHolds readyDurable RaftState.next
    simp only [Option.map_none, diskContents, StorContents.b, StorContents.commit,
      Option.isSome_none, Bool.false_or, List.isEmpty_cons, Bool.not_false, ite_true]
    refine ⟨by unfold base0; omega, by unfold base0; rw [hterm, hbt], ?_, trivial, trivial,
      by show uint.nat (W64 0) ≤ _; omega, Nat.le_refl _, Nat.le_refl _, by simp, fun h => absurd hbi h⟩
    rw [hfrom]
    simp only [appendEnts, plogTruncateAppend, hbz]
    have hd : ((0 : Int) + 1 - uint.Z e0.Index').toNat = 0 := by omega
    rw [hd, List.drop_zero]
    have hk : (uint.Z e0.Index' - 0 - 1).toNat = uint.nat e0.Index' - 1 := by omega
    show _ = List.take (uint.Z e0.Index' - 0 - 1).toNat D.ents ++ e0 :: t
    rw [hk, hents]

/-- **`storageHolds_saveW` at an iteration** (`loopRestB2`'s facts at `rs₂` after the write): from the
loop head's disk at the loop head's durable state, the `Ready`'s write (`oh` the disk's hard state or the
`Ready`'s, as `phsNext`) leaves the disk at the `Ready`'s durable state (`rs₂.dur`), its term within the
ceiling, given the `Ready`'s commit at least the disk's (`AntSim.commit_reachD`) and its term within the
ceiling (`rawNode_term_tc`). -/
theorem DrainIterB1.holds_saveW (γ : AntNames) (j : Fin γ.R.N) (I : DrainIterB1) (oh : Option HardStateM)
    (hok : I.OkB2 γ j) (h0 : StorageHolds I.rs.dur (diskContents I.v.dur))
    (hoh : oh.getD (HardStateM.mk I.v.dur.term I.v.dur.vote I.v.dur.commit) = phsNext I.rs.phs I.h)
    (hsv : SaveOk I.v.dur I.es) (hc : uint.Z I.v.dur.commit ≤ uint.Z I.r.p.commit)
    (htc : uint.Z I.r.p.term ≤ uint.Z I.rs.tc) :
    StorageHolds I.rs₂.dur (diskContents (saveW I.v.dur oh I.es)) ∧
      uint.Z I.rs₂.dur.term ≤ uint.Z I.rs₂.tc := by
  have hph : phsNext I.rs.phs I.h = HardStateM.mk I.r.p.term I.r.p.vote I.r.p.commit :=
    hok.2.2.2.2.1.2.1
  refine ⟨storageHolds_saveW I.rs.dur I.v.dur _ oh I.es h0 hoh hsv (by rw [hph]; exact hc), ?_⟩
  show uint.Z (phsNext I.rs.phs I.h).Term' ≤ uint.Z I.rs.tc
  rw [hph]; exact htc

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **The disk's commit is at most the `Ready`'s** (`AntSim.commit_reachD` in the run's invariant): at a
view with no `mem` record and no split write, reached from the sent lists' lower bounds. -/
theorem commit_peekB2 (h_vu : view_update.law (GF := GF)) (msk : AntSim.SimMask)
    (hmsk : msk ≤ AntSim.mskB2) (c : Loc) (γ : AntNamesB2) (j : Fin γ.R.N) (q : Qp)
    (v : AntSim.NodeView) (r₁ : RState) (net₀ : List Msg) (xnet₀ : List XMsg)
    {Adm : List EntryM → CCState → Prop}
    (hinm : ∀ S V net xnet, AntSim.AntSimD γ.R γ.dec S V net xnet → AntSim.InMask msk γ.R net xnet)
    (hm : v.mems = []) (hparts : v.parts = [])
    (hreach : AntSim.ReachIn msk γ.R γ.dec Adm net₀ xnet₀ j v r₁) :
    antClusterB2 (GF := GF) c γ ∗ sentLb γ.toAntNames net₀ ∗ xsentLb γ.toAntNames xnet₀ ∗
        viewFrag γ.toAntNames j v ∗ runLive γ q ⊢
      |={⊤}=> ⌜uint.Z v.dur.commit ≤ uint.Z r₁.p.commit⌝ ∗ viewFrag γ.toAntNames j v ∗ runLive γ q := by
  iintro ⟨#Hc, #Hlb, #Hxlb, Hv, Hl⟩
  ihave #Hc' := Hc
  iunfold antClusterB2 at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, -, -, -, -, -, -, -, -, -, -, -, #Hinv, %Hrf, -⟩
  iunfold sentLb at Hlb
  iunfold xsentLb at Hxlb
  iinv Hinv with >Hi Hclose
  iunfold antInvB2 at Hi
  icases Hi with (Hi | Hover)
  · iunfold antOpenB2 at Hi
    icases Hi with ⟨%evs, %S, %V, %net, %xnet, %G, Hstr, Hviews, Hnet, Hxnet, %Hpure, #HF⟩
    ihave %Hpre := mono_list_auth_lb_valid (GF := GF) γ.sent 1 net net₀ $$ Hnet Hlb
    ihave %Hxpre := mono_list_auth_lb_valid (GF := GF) γ.xsent 1 xnet xnet₀ $$ Hxnet Hxlb
    imod h_vu (⊤ \ ↑antN) γ.toAntNames j V v v $$ [Hv Hviews] with ⟨%HVj, Hv, Hviews⟩
    · iframe Hv Hviews
    rw [setV_self_s HVj]
    have hA := Hpure.1.2.1
    have hcm := AntSim.commit_reachD hmsk (hinm S V net xnet hA) hA.2.2.1
      (by rw [← HVj]; exact hA.2.2.2.2 j) hm hparts (hreach.mono Hpre.2 Hxpre.2)
    imod Hclose $$ [Hstr Hviews Hnet Hxnet] with -
    · inext
      iunfold antInvB2
      ileft
      iunfold antOpenB2
      iexists evs, S, V, net, xnet, G
      iframe Hstr Hviews Hnet Hxnet HF
      ipureintro; exact Hpure
    imodintro
    iframe Hv Hl
    ipureintro; exact hcm
  · iexfalso
    iapply runLive_excl γ q
    iframe Hl Hover

/-- **An alive node's view holds no `mem` record** (synchronous storage, no batching: `QueueView` over
empty queues and no item). -/
theorem nodeMemB2_mems_nil (γ : AntNamesB2) (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView)
    (x : CrashNames) (g : Nat) (phs : HardStateM) (dur D : RaftState)
    (has : γ.mode.Async' = false) (hbt : γ.mode.Batch' = false) :
    nodeMemB2 (GF := GF) γ j n v x g phs dur D false none ⊢
      ⌜v.mems = []⌝ ∗ nodeMemB2 γ j n v x g phs dur D false none := by
  unfold nodeMemB2
  iintro ⟨%items, %mhs, %rhs, %wip, %aip, %wsl, %asl, %wls, %als, %jobs, %ajobs, %ow, %oa, %hm', %rh,
    H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, Hm, H13, H14, H15, H16, H17, H18, H19, H20, H21, H22,
    %Hp⟩
  have hmn : v.mems = [] := by
    obtain ⟨h1, -, -, -, -, h6, -, h8⟩ := Hp
    obtain ⟨rfl, rfl, -, -⟩ := h8 has
    have hi := h6 hbt
    subst hi
    have hq := (h1 rfl).1
    simp at hq
    exact hq
  isplitr
  · ipureintro; exact hmn
  iexists items, mhs, rhs, wip, aip, wsl, asl, wls, als, jobs, ajobs, ow, oa, hm', rh
  iframe H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 Hm H13 H14 H15 H16 H17 H18 H19 H20 H21 H22
  ipureintro; exact Hp

end proof

end AntHarness
end EtcdGrove
end Perennial
