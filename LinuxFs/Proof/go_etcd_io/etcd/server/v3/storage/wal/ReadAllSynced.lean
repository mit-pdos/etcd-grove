/- Lean-first (no Rocq counterpart).

# `ReadAll`'s synced mark (W3/W5 of `notes/wal-fsext-plan.md`, twenty-fourth session)

`ReadAll` commits its update at the look before the loop (`walInv_readCommit`), at the WAL's state
`d` read there; its tail is registered next, with its own reading of the state (the tail record's
history `H`), and the fdatasync after `ZeroToEnd` gives `walSyncedLb dir |H|`. The post needs
`walSyncedLb dir |d.H|`: `walInv_tailH` compares the two through the invariant, the tail record
agreeing with the WAL's present state (`walInvBody_tailW`) and the past state holding `d` below it.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TruncSup

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics] [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- A past state is below the invariant's. -/
theorem walInvBody_pastLe (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s p : AbsDiskState) :
    ⊢ walInvBody (L := hG.goose_localGS) (W := W) C Mr R jr r s -∗ walPast (W := W) p -∗
      walInvBody (L := hG.goose_localGS) (W := W) C Mr R jr r s ∗ ⌜absLe p s⌝ := by
  iintro Hb #Hp
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, Hrest⟩
  icases walPast_ghost_le s p $$ Hg Hp with %Hle
  isplitl
  · iexists Ls, cl, n, F; iframe
  · ipureintro; exact Hle

/-- The synced mark is monotone in its bound. -/
theorem walSyncedLb_le (dir : GoString) {n n' : Nat} (h : n' ≤ n) :
    walSyncedLb (W := W) dir n ⊢ walSyncedLb (W := W) dir n' := by
  unfold walSyncedLb
  iintro ⟨%s, %d, #Hp, %hd⟩
  iexists s, d
  iframe Hp
  ipureintro; exact ⟨hd.1, Nat.le_trans h hd.2⟩

/-- **The tail record's history is the WAL's** (see the file header): every past state's history of
the WAL is at most as long. -/
theorem walInv_tailH (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (f : Loc) (fd : w64) (name dir : GoString) (γ : GName) (i : Ino) (H : List (WalOpG WalEnt))
    (md : List w8) (cuts : List Nat) (o0 sz : Nat) (out : List w8)
    (tm : Fs.OsMeta → List Fs.ByteG → Prop) (s1 : AbsDiskState) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) C Mr R jr r -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗ walPast (W := W) s1 -∗
      walTailW (W := W) f fd name dir γ i H md cuts o0 sz out tm ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗
      walTailW (W := W) f fd name dir γ i H md cuts o0 sz out tm ∗
      ⌜∀ d1, s1.wal !! dir = some d1 → d1.H.length ≤ H.length⌝ := by
  iintro #Hinv Hnc #Hp Htw
  imod walInv_open (L := hG.goose_localGS) C Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc
    with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  icases walInvBody_pastLe C Mr R jr r s s1 $$ Hb Hp with ⟨Hb, %Hle⟩
  unfold walTailW
  icases Htw with ⟨Hf, Hfd, Hoff, Hk, %m, %bs, Hm, Hby, %hp, Hv⟩
  ihave Hk : walTailKeyL (W := W) dir γ none $$ [Hk]
  · rw [walTailKeyL_none]; iexact Hk
  ihave Hv : tailVar (W := W) γ ((H, md, cuts, o0 + out.length, i, none) : TailG) $$ [Hv]
  · unfold tailVar; iexact Hv
  ihave Hm : tailHeld (L := hG.goose_localGS) ((H, md, cuts, o0 + out.length, i, none) : TailG) m $$ [Hm]
  · unfold tailHeld; iexact Hm
  icases walInvBody_tailW (L := hG.goose_localGS) C Mr R jr r s dir γ none
      ((H, md, cuts, o0 + out.length, i, none) : TailG) m $$ Hb Hk Hv Hm
    with ⟨%Ls, %cl, %n, %F, %d, %lay, %pre, %g0, %hf, Hseg, Hk, Hv, Hv2, Hm, Hclose⟩
  obtain ⟨hd, hl, hs, htg, hW, -⟩ := hf
  ihave Hb := walInvBody_tailW_same (hG := hG) C Mr R jr r s dir γ Ls cl n F d lay pre g0 hW hl hs
    $$ Hclose Hseg [Hv2]
  · rw [← htg]; iexact Hv2
  imod Hcl $$ [Hb] with -
  · iexists s; iexact Hb
  imodintro
  iframe Hnc
  ihave Hk : walTailKey (W := W) dir γ $$ [Hk]
  · rw [← walTailKeyL_none]; iexact Hk
  isplitl
  · iframe Hf Hfd Hoff Hk
    iexists m, bs
    iframe Hby
    isplitl [Hm]
    · unfold tailHeld; iexact Hm
    isplitr [Hv]
    · ipureintro; exact hp
    unfold tailVar; iexact Hv
  · ipureintro
    intro d1 hd1
    obtain ⟨d', hd', -, hlen, -⟩ := Hle.2.2 dir d1 hd1
    rw [hd] at hd'
    cases hd'
    have hH : d.H = H := by
      have := congrArg (fun t : TailG => t.1) htg
      simpa [tailG] using this.symm
    rw [← hH]; exact hlen

end iris

end WalFs
end EtcdGrove
end Perennial

end
