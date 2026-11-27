/- Lean-first (no Rocq counterpart).

# `ReadAll`'s synced mark (W3/W5 of `notes/wal-fsext-plan.md`, twenty-fourth session)

`ReadAll` commits its update at the look before the loop (`walInv_readCommit`), at the WAL's state
`d` read there; its tail is registered next, with its own reading of the state (the tail record's
history `H`), and the fdatasync after `ZeroToEnd` gives `walSyncedLb dir |H|`. The post needs
`walSyncedLb dir |d.H|`: `walInv_tailH` compares the two through the invariant, the tail record
agreeing with the WAL's present state (`walInvBody_tailW`) and the past state holding `d` below it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TruncSup

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

/-- A past state at the opening handle's incarnation is below the invariant's at `dir`
(`walOpening_pastCur`). -/
theorem walInvBody_pastCur (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s p : AbsDiskState) (I0 : GMap GoString Nat) (w : Loc) (dir : GoString) (sn : w64 × w64) (ic : Nat)
    (hI0 : incOf I0 dir = ic) :
    ⊢ walInvBody (L := hG.goose_localGS) (W := W) C Mr R jr r s -∗ walOpening (W := W) w dir sn ic -∗
      walPastI (W := W) (p, I0) -∗
      walInvBody (L := hG.goose_localGS) (W := W) C Mr R jr r s ∗ walOpening (W := W) w dir sn ic ∗
      ⌜∀ d, p.wal !! dir = some d → ∃ d', s.wal !! dir = some d' ∧ d.m ≤ d'.m ∧
        d.H.length ≤ d'.H.length ∧ (d.named = true → d'.named = true)⌝ := by
  iintro Hb Ho #Hp
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, Hrest⟩
  iunfold walGhost at Hg
  icases Hg with ⟨%Ig, Hg⟩
  icases walOpening_pastCur s Ig w dir sn ic p I0 hI0 $$ Hg Ho Hp with ⟨Hg, Ho, %hc⟩
  ihave Hg := walGhostI_ghost s Ig $$ Hg
  iframe Ho
  isplitl
  · iexists Ls, cl, n, F; iframe
  · ipureintro; exact hc

/-- The synced mark is monotone in its bound. -/
theorem walSyncedLb_le (dir : GoString) {i n n' : Nat} (h : n' ≤ n) :
    walSyncedLb (W := W) dir i n ⊢ walSyncedLb (W := W) dir i n' := by
  unfold walSyncedLb
  iintro ⟨%s, %I, #Hp, %hd⟩
  iexists s, I
  iframe Hp
  ipureintro
  rcases hd with ⟨hi, d, hd1, hd2⟩ | hlt
  · exact Or.inl ⟨hi, d, hd1, Nat.le_trans h hd2⟩
  · exact Or.inr hlt

/-- **The tail record's history is the WAL's** (see the file header): every past state's history of
the WAL is at most as long. -/
theorem walInv_tailH (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (f : Loc) (fd : w64) (name dir : GoString) (γ : GName) (i : Ino) (H : List (WalOpG WalEnt))
    (md : List w8) (cuts : List Nat) (o0 sz : Nat) (out : List w8)
    (tm : Fs.OsMeta → List Fs.ByteG → Prop) (s1 : AbsDiskState) (w : Loc) (sn : w64 × w64) (ic : Nat)
    (I1 : GMap GoString Nat) (hI1 : incOf I1 dir = ic) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) C Mr R jr r -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗ walPastI (W := W) (s1, I1) -∗
      walOpening (W := W) w dir sn ic -∗
      walTailW (W := W) f fd name dir γ i H md cuts o0 sz out tm ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ walOpening (W := W) w dir sn ic ∗
      walTailW (W := W) f fd name dir γ i H md cuts o0 sz out tm ∗
      ⌜∀ d1, s1.wal !! dir = some d1 → d1.H.length ≤ H.length⌝ := by
  iintro #Hinv Hnc #Hp Ho Htw
  imod walInv_open (L := hG.goose_localGS) C Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc
    with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  icases walInvBody_pastCur C Mr R jr r s s1 I1 w dir sn ic hI1 $$ Hb Ho Hp with ⟨Hb, Ho, %Hle⟩
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
    none trivial
    $$ Hclose Hseg [Hv2]
  · rw [← htg]; iexact Hv2
  imod Hcl $$ [Hb] with -
  · iexists s; iexact Hb
  imodintro
  iframe Hnc Ho
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
    obtain ⟨d', hd', -, hlen, -⟩ := Hle d1 hd1
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
