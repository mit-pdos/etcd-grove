/-
Lean-first (no Rocq counterpart).

# Raising the program's view of a WAL to named (W4c U5, the tester's `Boot`, B2)

The program's view of a WAL (`walDirIsI dir i (some d)`) is a lower bound of the real state
(`walOptLe`): its `named` may be `false` while the real WAL's is `true` (`Create` returns the fresh,
unnamed state, and `walNamed` separately; a crash keeps the view's `named`). `walNamed dir i` says some
past state of the generation had the WAL of incarnation `i` named, so the real state now has it named too (`absLe`), and
the view may be raised to it: `walDirIs_named`, at the WAL invariant (`walInv_open`, with the step's
`notCrashed`), over the ghost lemma `walGhost_raiseNamed`.

The tester's `Boot` raises its view before `Exist` (when its oracle says `Create` returned), so that
`Exist`'s `false` arm (`ExistFalseOk` of the view: none, or empty and unnamed) contradicts it: the
`panic` is unreachable.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- The map with `dir`'s WAL marked named stays below a real state whose WAL there is named. -/
theorem walMapLe_named {M : GMap GoString WalDur} {s : AbsDiskState} {dir : GoString} {dm ds : WalDur}
    (hM : walMapLe M s.wal) (hdm : M !! dir = some dm) (hds : s.wal !! dir = some ds)
    (hn : ds.named = true) : walMapLe (<[dir := { dm with named := true }]> M) s.wal := by
  intro k
  by_cases e : dir = k
  · subst e
    rw [GMap.lookup_insert, hds]
    have h := hM dir
    rw [hdm, hds] at h
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, -⟩ := h
    exact ⟨a1, a2, a3, a4, a5, a6, a7, fun _ => hn⟩
  · rw [GMap.lookup_insert_ne _ _ e]; exact hM k

end pure

section ghostInv
variable {GF : BundledGFunctors} [W : WalGS GF] {hlc : HasLC} [GooseExts] [GooseInterp]
  [G : GooseGlobalGS hlc GF]

/-- **The view raised to named, at the ghost state**: `walNamed dir i` of the view's (current)
incarnation and the ghost state `s` give the real WAL in `dir` named, so the program's map may mark it
named. -/
theorem walGhost_raiseNamed (s : AbsDiskState) (dir : GoString) (i : Nat) (d : WalDur) :
    ⊢@{IProp GF} walGhost (W := W) s -∗ walDirIsI (W := W) dir i (some d) -∗ walNamed (W := W) dir i ==∗
      walGhost (W := W) s ∗ walDirIsI (W := W) dir i (some { d with named := true }) := by
  iintro Hc Hd #Hn
  unfold walDirIsI
  icases Hd with ⟨%M, %I, HM, HI, %hM, %hi⟩
  subst hi
  icases walGhost_inc s I $$ Hc HI with ⟨Hc, HI⟩
  ihave %hn := walNamed_ghost (W := W) s I dir $$ Hc Hn
  ihave %hMs := walGhostI_own_agree (W := W) s I M $$ Hc HM
  obtain ⟨ds, hds, hnamed⟩ := hn
  obtain ⟨dm, hdm, hddm⟩ := (walOptLe_some_iff d _).1 hM
  have hM' := walMapLe_named hMs hdm hds hnamed
  unfold walGhostI walOwn walOwnAt
  letI := walAllG (W := W)
  icases Hc with ⟨⟨%G, Hs, -⟩, HP, Hh, Hk, Hst⟩
  icases HM with ⟨HM, Ht⟩
  imod ghostVar_update_halves (<[dir := { dm with named := true }]> M) _ _ _ $$ Hs HM with ⟨Hs, HM⟩
  imodintro
  isplitl [Hs HP Hh Hk Hst]
  · unfold walGhost walGhostI
    iexists I
    iframe HP Hh Hk Hst
    iexists _
    iframe Hs
    ipureintro; exact hM'
  · iexists _, I
    iframe HM Ht HI
    ipureintro
    refine ⟨?_, rfl⟩
    rw [GMap.lookup_insert]
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, -⟩ := hddm
    exact ⟨a1, a2, a3, a4, a5, a6, a7, fun _ => rfl⟩

end ghostInv

section inv
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable [W : WalGS GF]

/-- **The program's view of a named WAL raised to named** (see the file header), at a step of the
generation (`notCrashed`, which `wp_notCrashed_acc` gives before a step). -/
theorem walDirIs_named (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (E : CoPset) (hE : ↑walN ⊆ E) (dir : GoString) (i : Nat) (d : WalDur) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walDirIsI (W := W) dir i (some d) -∗ walNamed (W := W) dir i ={E}=∗
      notCrashed (hC := L.goose_crashGS) ∗ walDirIsI (W := W) dir i (some { d with named := true }) := by
  iintro #Hinv Hnc Hd #Hn
  imod walInv_open C Mr R jr r E hE $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hclose⟩
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, Hrest⟩
  imod walGhost_raiseNamed s dir i d $$ Hg Hd Hn with ⟨Hg, Hd⟩
  imod Hclose $$ [Hg Hrest] with -
  · iexists s, Ls, cl, n, F; iframe Hg; iexact Hrest
  imodintro
  iframe
