/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E (the synchronous `node.drain`):
**`nodeOwnB2HD`'s loop phase opened and closed** (`DrainB1Loop`'s `nodeOwn_loop_open` over B2's
vocabulary):
- `nodeOwnB2HD_dead_read`: the kill flag `n.dead` read out of any phase and put back (`drain`'s
  `!n.dead` loop guard);
- `nodeOwnB2HD_loop_open` / `nodeOwnB2HD_loop_close`: the alive `.loop` phase (no job held) as the
  `RawNode`, the raft ghost pieces a `Ready` moves (the generation view, the durable ghost, the slot)
  and the rest (`loopRestB2`);
- `loopRestB2_dead`: the kill flag of `loopRestB2` (alive) read out and put back.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Phases

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **The kill flag read** (any phase, any job held): `n.dead` out, and back. -/
theorem nodeOwnB2HD_dead_read (c : Loc) (γ : AntNamesB2) (j : Fin γ.R.N) (n : Loc)
    (v : AntSim.NodeView) (ph : Phase) (hole : Option WorkHole) (dead : Bool) :
    nodeOwnB2HD (GF := GF) c γ j n v ph hole dead ⊢
      n.[H.node, go!"dead"] ↦ dead ∗
        (n.[H.node, go!"dead"] ↦ dead -∗ nodeOwnB2HD c γ j n v ph hole dead) := by
  unfold nodeOwnB2HD killOwn
  iintro ⟨%d, %rn, %ms, %hsl, %cl, %csl, %role, %applied, %fuse, %dk, #Hd, Hrn, Hms, Hrole, Hhs,
    Hcause, Happ, Hconf, ⟨Hdead, Hfuse⟩, Hrest⟩
  iframe Hdead
  iintro Hdead
  iexists d, rn, ms, hsl, cl, csl, role, applied, fuse, dk
  iframe Hd Hrn Hms Hrole Hhs Hcause Happ Hconf Hdead Hfuse Hrest

/-- **`nodeOwnB2HD`'s alive loop phase opened** (no job held): the `RawNode` at the record `rs`, the
generation view, the durable ghost at `D`, the slot (free, or async storage), the loop head's facts,
and the rest (`loopRestB2`, `n.hs` at `hsl`). -/
theorem nodeOwnB2HD_loop_open (c : Loc) (γ : AntNamesB2) (j : Fin γ.R.N) (n : Loc)
    (v : AntSim.NodeView) (net₀ : List Msg) (xnet₀ : List XMsg) (r₁ : RState) (xs₁ : List XMsg) :
    nodeOwnB2HD (GF := GF) c γ j n v (.loop net₀ xnet₀ r₁ xs₁) none false ⊢
      ∃ (rn : Loc) (rs : RNState) (qs : List Msg) (ip : Nat) (x : CrashNames) (g : Nat)
        (D : RaftState) (hsl : Loc),
        n.[H.node, go!"rn"] ↦ rn ∗ rawNode γ.raft.raftNames γ.R.md rn (AntSim.nodeId j) rs r₁ qs ip ∗
        genView γ.raft.raftNames (AntSim.nodeId j) x 1 g ∗
        ownDurGhost γ.raft.raftNames (AntSim.nodeId j) D ∗
        (⌜γ.mode.Async' = true⌝ ∨ slotFree γ.raft.raftNames (AntSim.nodeId j) g) ∗
        ⌜RsViewB2 γ.mode rs v ∧ AntSim.Reach γ.R γ.dec (AdmFold γ.dec γ.R.c0) net₀ xnet₀ j v r₁ ∧
          (γ.mode.Async' = false → qs = [] ∧ ip = lcpLen v.r.p.log r₁.p.log) ∧ ByOkB2 v.byE ∧
          ViewNormal v ∧ rs.k = γ.R.k j⌝ ∗
        loopRestB2 γ j n v net₀ xnet₀ rs x g D hsl := by
  unfold nodeOwnB2HD
  simp only [Bool.false_eq_true, ite_false]
  iintro ⟨%d, %rn, %ms, %hsl, %cl, %csl, %role, %applied, %fuse, %dk, #Hd, Hrn, Hms, Hrole, Hhs,
    Hcause, Happ, Hconf, Hkill, Hv, Hdisk, %Hvd, %si, %rs, %qs, %ip, %r, %x, %g, %D, %hn, Hstor,
    %Hsto, Hraw, Hgv, Hdur, Htlb, Hbud, %HD, Hmem, #Hhsro, Hslot, %Hrv, #Hcs, Hrq, %Hc0, %Hph,
    #Hlb, #Hxlb, Hco⟩
  obtain ⟨rfl, hR, hsync, hby⟩ := Hph
  iexists rn, rs, qs, ip, x, g, D, hsl
  iframe Hrn Hraw Hgv Hdur Hslot
  isplitr
  · ipureintro
    exact ⟨Hrv.1, hR, fun h => ⟨(hsync h).1, (hsync h).2.1⟩, hby, Hvd.1, Hrv.2.2.2.2⟩
  iunfold loopRestB2
  iexists d, ms, cl, csl, role, applied, fuse, dk, si, hn
  iframe Hd Hms Hrole Hhs Hcause Happ Hconf Hkill Hv Hdisk Hstor Htlb Hbud Hmem Hhsro Hcs Hrq Hlb
    Hxlb Hco
  ipureintro
  exact ⟨⟨Hvd.1, Hvd.2.1, fun h => (Hvd.2.2 h).2⟩, Hsto, HD,
    ⟨Hrv.2.1, Hrv.2.2.1, Hrv.2.2.2.1, Hrv.2.2.2.2, fun h => (hsync h).2.2⟩, Hc0⟩

/-- **`nodeOwnB2HD`'s alive loop phase closed** (`nodeOwnB2HD_loop_open`'s converse). -/
theorem nodeOwnB2HD_loop_close (c : Loc) (γ : AntNamesB2) (j : Fin γ.R.N) (n : Loc)
    (v : AntSim.NodeView) (net₀ : List Msg) (xnet₀ : List XMsg) (r₁ : RState) (xs₁ : List XMsg)
    (rn : Loc) (rs : RNState) (qs : List Msg) (ip : Nat) (x : CrashNames) (g : Nat) (D : RaftState)
    (hsl : Loc)
    (hrv : RsViewB2 γ.mode rs v)
    (hR : AntSim.Reach γ.R γ.dec (AdmFold γ.dec γ.R.c0) net₀ xnet₀ j v r₁)
    (hsync : γ.mode.Async' = false → qs = [] ∧ ip = lcpLen v.r.p.log r₁.p.log)
    (hby : ByOkB2 v.byE) :
    n.[H.node, go!"rn"] ↦ rn ∗ rawNode γ.raft.raftNames γ.R.md rn (AntSim.nodeId j) rs r₁ qs ip ∗
        genView γ.raft.raftNames (AntSim.nodeId j) x 1 g ∗
        ownDurGhost γ.raft.raftNames (AntSim.nodeId j) D ∗
        (⌜γ.mode.Async' = true⌝ ∨ slotFree γ.raft.raftNames (AntSim.nodeId j) g) ∗
        loopRestB2 γ j n v net₀ xnet₀ rs x g D hsl ⊢
      nodeOwnB2HD (GF := GF) c γ j n v (.loop net₀ xnet₀ r₁ xs₁) none false := by
  iintro ⟨Hrn, Hraw, Hgv, Hdur, Hslot, Hrest⟩
  iunfold loopRestB2 at Hrest
  icases Hrest with ⟨%d, %ms, %cl, %csl, %role, %applied, %fuse, %dk, %si, %hn, #Hd, Hms, Hrole,
    Hhs, Hcause, Happ, Hconf, Hkill, Hv, Hdisk, %Hvd, Hstor, %Hsto, Htlb, Hbud, %HD, Hmem, #Hhsro,
    %Hpv, #Hcs, Hrq, %Hc0, #Hlb, #Hxlb, Hco⟩
  unfold nodeOwnB2HD
  simp only [Bool.false_eq_true, ite_false]
  iexists d, rn, ms, hsl, cl, csl, role, applied, fuse, dk
  iframe Hd Hrn Hms Hrole Hhs Hcause Happ Hconf Hkill Hv Hdisk
  isplitr
  · ipureintro
    exact ⟨Hvd.1, Hvd.2.1, fun h => ⟨trivial, Hvd.2.2 h⟩⟩
  iexists si, rs, qs, ip, r₁, x, g, D, hn
  iframe Hstor Hraw Hgv Hdur Htlb Hbud Hmem Hhsro Hslot Hcs Hrq Hlb Hxlb Hco
  ipureintro
  exact ⟨Hsto, HD, ⟨hrv, Hpv.1, Hpv.2.1, Hpv.2.2.1, Hpv.2.2.2.1⟩, Hc0,
    ⟨rfl, hR, fun h => ⟨(hsync h).1, (hsync h).2, Hpv.2.2.2.2 h⟩, hby⟩⟩

/-- **The kill flag of `loopRestB2`** (alive): read out and put back. -/
theorem loopRestB2_dead (γ : AntNamesB2) (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView)
    (net₀ : List Msg) (xnet₀ : List XMsg) (rs : RNState) (x : CrashNames) (g : Nat) (D : RaftState)
    (hsl : Loc) :
    loopRestB2 (GF := GF) γ j n v net₀ xnet₀ rs x g D hsl ⊢
      n.[H.node, go!"dead"] ↦ false ∗
        (n.[H.node, go!"dead"] ↦ false -∗ loopRestB2 γ j n v net₀ xnet₀ rs x g D hsl) := by
  unfold loopRestB2 killOwn
  iintro ⟨%d, %ms, %cl, %csl, %role, %applied, %fuse, %dk, %si, %hn, #Hd, Hms, Hrole, Hhs, Hcause,
    Happ, Hconf, ⟨Hdead, Hfuse⟩, Hrest⟩
  iframe Hdead
  iintro Hdead
  iexists d, ms, cl, csl, role, applied, fuse, dk, si, hn
  iframe Hd Hms Hrole Hhs Hcause Happ Hconf Hdead Hfuse Hrest

/-- **A run write job on a node killed**: what holds alive holds dead (`writeJobMade`'s dead arm is
a disjunct). -/
theorem writeJobMade_kill (γ : AntNamesB2) (j : Fin γ.R.N) (l : Loc) (w : WJob) (D : RaftState) :
    writeJobMade (GF := GF) γ j l w D false ⊢ writeJobMade γ j l w D true := by
  unfold writeJobMade
  iintro ⟨Hobj, H⟩
  iframe Hobj
  icases H with (H | %H)
  · ileft; iexact H
  · exact absurd H.1 Bool.false_ne_true

/-- **The bookkeeping of a node killed** (`nodeMemB2`'s kill index set): the enter promises' chain is
no longer kept, a run write job's promise may be unfired. -/
theorem nodeMemB2_kill (γ : AntNamesB2) (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView)
    (x : CrashNames) (g : Nat) (phs : HardStateM) (dur D : RaftState) (hole : Option WorkHole) :
    nodeMemB2 (GF := GF) γ j n v x g phs dur D false hole ⊢ nodeMemB2 γ j n v x g phs dur D true hole := by
  unfold nodeMemB2
  iintro ⟨%items, %mhs, %rhs, %wip, %aip, %wsl, %asl, %wls, %als, %jobs, %ajobs, %ow, %oa, %hm, %rh,
    H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, Hm, H13, H14, H15, H16, H17, H18, H19, H20, H21, H22,
    %Hp⟩
  iexists items, mhs, rhs, wip, aip, wsl, asl, wls, als, jobs, ajobs, ow, oa, hm, rh
  iframe H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22
  isplitl [Hm]
  · cases ow with
    | none => iexact Hm
    | some w =>
      by_cases hf : WorkHole.wFresh hole = true
      · simp only [hf, ite_true]; iexact Hm
      · simp only [hf, Bool.false_eq_true, ite_false]
        iapply writeJobMade_kill; iexact Hm
  · ipureintro
    obtain ⟨h1, -, h3⟩ := Hp
    exact ⟨h1, fun h => absurd h (by decide), h3⟩

/-- **A dead node drained** (`nodeOwnB2HD … .drained none true` from its pieces): its fields, the kill
flag set, the view frozen at `v` (normal, the disk against it), its storage, its `RawNode` at any
record, raft's ghost pieces (the durable ghost at the disk), its bookkeeping dead. -/
theorem nodeOwnB2HD_dead_intro (c : Loc) (γ : AntNamesB2) (j : Fin γ.R.N) (n : Loc)
    (v : AntSim.NodeView) (d rn ms hsl cl csl : Loc) (role : GoString) (applied fuse : w64)
    (dk : AntSim.DurW) (si : Loc) (rs : RNState) (qs : List Msg) (ip : Nat) (r : RState)
    (x : CrashNames) (g : Nat) (D : RaftState) (hn : HardStateM)
    (hvn : ViewNormal v) (hdr : DiskRel v dk) (hre : γ.mode.Restarts' = true)
    (hsto : rs.storage = interface.ok ⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage.ty, #si⟩)
    (hD : StorageHolds D (diskContents dk) ∧ uint.Z D.term ≤ uint.Z rs.tc) :
    n.[H.node, go!"disk"] ↦□ d ∗ n.[H.node, go!"rn"] ↦ rn ∗ n.[H.node, go!"store"] ↦ ms ∗
      n.[H.node, go!"role"] ↦ role ∗ n.[H.node, go!"hs"] ↦ hsl ∗ n.[H.node, go!"cause"] ↦ cl ∗
      n.[H.node, go!"applied"] ↦ applied ∗ n.[H.node, go!"conf"] ↦ csl ∗ killOwn n true fuse ∗
      viewFrag γ.toAntNames j v ∗ diskOwn d dk ∗
      nodeStor si ms ((List.range γ.R.K).map fun (i : Nat) => W64 ((i : Int) + 1)) hn ∗
      rawNode γ.raft.raftNames γ.R.md rn (AntSim.nodeId j) rs r qs ip ∗
      genView γ.raft.raftNames (AntSim.nodeId j) x 1 g ∗
      ownDurGhost γ.raft.raftNames (AntSim.nodeId j) D ∗ rnTermLB γ.raft rs.tc ∗ rnBudget γ.raft ∗
      nodeMemB2 γ j n v x g rs.phs rs.dur D true none ∗ hsRO hsl hn ⊢
    nodeOwnB2HD (GF := GF) c γ j n v .drained none true := by
  iintro ⟨#Hd, Hrn, Hms, Hrole, Hhs, Hcause, Happ, Hconf, Hkill, Hv, Hdisk, Hstor, Hraw, Hgv, Hdur,
    Htlb, Hbud, Hmem, Hhsro⟩
  unfold nodeOwnB2HD
  iexists d, rn, ms, hsl, cl, csl, role, applied, fuse, dk
  iframe Hd Hrn Hms Hrole Hhs Hcause Happ Hconf Hkill Hv Hdisk
  isplitr
  · ipureintro
    exact ⟨hvn, hdr, fun h => absurd (hre.symm.trans h) (by decide)⟩
  iexists si, rs, qs, ip, r, x, g, D, hn
  iframe Hstor Hraw Hgv Hdur Htlb Hbud Hmem Hhsro
  isplitr
  · ipureintro; exact hsto
  isplitr
  · ipureintro; exact hD
  simp only [ite_true]
  ipureintro; trivial

end laws

end AntHarness
end EtcdGrove
end Perennial
