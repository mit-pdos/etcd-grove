/- Lean-first (no Rocq counterpart).

# `Create`'s parent fsync as an update of the WAL invariant (W4, eleventh session)

`walInv_stepS`: `walInv_step` (`CreateSteps.lean`) for a step that changes the invariant's state.
`walInv_named`: `walInvBody_named` at a program step: after the parent's fsync (`osCommitLb n`, past
the rename's entry `x`, the last writer of `nm` in the program's claim), `walNamed dir`; the WAL in
`dir` known from a past state (`walPastI`, `walPastI_ghost_le`), the fact at its incarnation (P6b).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSteps
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateNamed

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **A step of the invariant's contents that changes its state**, as an update of the invariant. -/
theorem walInv_stepS (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (P Q : IProp GF) (E : CoPset) (hE : ↑walN ⊆ E)
    (hstep : ∀ s, ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ P ={E \ ↑walN}=∗
      (∃ s', walInvBody (L := L) (W := W) C Mr R jr r s') ∗ Q) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗ P ={E}=∗
      notCrashed (hC := L.goose_crashGS) ∗ Q := by
  iintro #Hinv Hnc HP
  imod walInv_open C Mr R jr r E hE $$ Hinv Hnc with ⟨Hb, Hnc, Hcl⟩
  icases Hb with ⟨%s, Hb⟩
  ihave Hs := hstep s $$ Hb HP
  imod Hs with ⟨Hb, HQ⟩
  imod Hcl $$ [Hb] with -
  · iexact Hb
  imodintro
  iframe

/-- See the file header. -/
theorem walInv_named {Lo : List (GoString × Qp)} (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir nm : GoString) (s0 : AbsDiskState) (I0 : GMap GoString Nat) (d0 : WalDur) (N : NameSet)
    (dq : DFrac) (h : NamesH)
    (x : Nat) (e : LogEntry) (Es : Ents) (J : Ino) (n : Nat)
    (hd0 : s0.wal !! dir = some d0) (hin : InArea r dir nm) (hN : N.Mem nm)
    (hl : LastWrite h jr nm x e Es) (hx : x < n) (hJ : Es !! nm = some (.dir J)) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ osSharedInv (L := L) R -∗
      notCrashed (hC := L.goose_crashGS) -∗ walPastI (W := W) (s0, I0) -∗
      osNames (L := L) jr N dq h -∗ osCommitLb (L := L) n -∗ walNamesFragS (W := W) ⟨none, none, Lo⟩ ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ osNames (L := L) jr N dq h ∗
        walNamed (W := W) dir (incOf I0 dir) ∗ walNamesFragS (W := W) ⟨none, none, Lo⟩ := by
  iintro #Hinv #Hsi Hnc #Hp H #Hc Hnf
  iapply walInv_stepS C Mr R jr r
    iprop(osSharedInv (L := L) R ∗ walPastI (W := W) (s0, I0) ∗ osNames (L := L) jr N dq h ∗
      osCommitLb (L := L) n ∗ walNamesFragS (W := W) ⟨none, none, Lo⟩)
    iprop(osNames (L := L) jr N dq h ∗ walNamed (W := W) dir (incOf I0 dir) ∗
      walNamesFragS (W := W) ⟨none, none, Lo⟩)
    ⊤ CoPset.subseteq_top (fun s => by
      iintro Hb ⟨#Hsi, #Hp, H, #Hc, Hnf⟩
      iunfold walInvBody at Hb
      icases Hb with ⟨%Ls, %cl, %n0, %F, Hg, Hrest⟩
      iunfold walGhost at Hg
      icases Hg with ⟨%I, Hg⟩
      icases walPastI_ghost_le s I (s0, I0) $$ Hg Hp with %Hle
      rcases Nat.lt_or_eq_of_le (Hle.2.2.1 dir) with hlt | heq
      · -- the incarnation of `s0` is retired: nothing to name
        imod walGhostI_past s I $$ Hg with ⟨Hg, #HpI⟩
        ihave #Hnm := walNamed_retired s I dir (incOf I0 dir) hlt $$ HpI
        ihave Hg := walGhostI_ghost s I $$ Hg
        imodintro
        isplitl [Hg Hrest]
        · iexists s; unfold walInvBody; iexists Ls, cl, n0, F; iframe Hrest Hg
        iframe H Hnm Hnf
      obtain ⟨d, hd, -⟩ := Hle.2.2.2 dir d0 hd0 heq.symm
      ihave Hg := walGhostI_ghost s I $$ Hg
      ihave Hb : walInvBody (L := L) (W := W) C Mr R jr r s $$ [Hg Hrest]
      · unfold walInvBody; iexists Ls, cl, n0, F; iframe Hrest Hg
      imod walInvBody_named C Mr R jr r s dir nm d N dq h x e Es J n s0 I0 hd hin hN hl hx hJ
        walN_osShN_top $$ Hb Hsi H Hc Hnf Hp with ⟨Hb, H, #Hnm, Hnf⟩
      imodintro
      isplitl [Hb]
      · iexists _; iexact Hb
      iframe H Hnm Hnf)
    $$ Hinv Hnc [H Hnf]
  iframe H Hnf; iframe #

end iris

end WalFs
end EtcdGrove
end Perennial

end
