-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/LemmasXt.lean` (etc/copy-part.py; rerun it, do not edit).
/-
(antithesis parity B1, 2026-11-26, option (b)) The ghost facts `raft.Step` records a timeout request
(`NGhost.xt`) with: a leader's last index is past `0` (`campOwn`: its campaign log is a strict prefix
of its full log), and a leader's `Match` of another node is that node's acknowledgement at the
leader's term (`matchedOk`).
-/
module

public import KvRaft.Proof.go_etcd_io.raft.v3.Protocol.Refinement

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

/-- A map's entry, from its value defaulted at `0` when that value is not `0`. -/
theorem xt_lookup_of_getD {M : GMap w64 w64} {k v : w64} (h : (M !! k).getD (W64 0) = v)
    (hv : v ≠ W64 0) : M !! k = some v := by
  cases hk : M !! k with
  | none => rw [hk] at h; exact absurd h.symm hv
  | some x => rw [hk] at h; simp only [Option.getD_some] at h; rw [h]

section xt
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]
variable {md : Bool}
variable [CrashGS GF]

/-- A leader's last index is past `0`: its campaign log is a strict prefix of its full log
(`campOwn`). -/
theorem ownLogGhost_leader_last1 (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64)
    (W : DurMaps) :
    ⊢ ownLogGhost (GF := GF) γ id s kl W -∗
      ⌜s.role = .leader → 1 ≤ plogLastIndexZ s.base s.log⌝ ∗ ownLogGhost γ id s kl W := by
  iintro Hlg
  unfold ownLogGhost
  icases Hlg with ⟨%γm, %terms, %fp, %γw, %wins, H⟩
  iNamed H
  ihave %Hl : ⌜s.role = .leader → 1 ≤ plogLastIndexZ s.base s.log⌝ $$ []
  · cases Hr : s.role with
    | leader =>
      iunfold campOwn at Hcown
      rw [Hr]
      icases Hcown with ⟨%F0, -, %HF⟩
      ipureintro
      intro _
      have HF2 := HF.2.1
      rw [full_last_index _ _ _ Hfull.1] at HF2
      unfold plogLastIndexZ at HF2 ⊢
      rw [base0_index] at HF2
      have : uint.Z (W64 0) = 0 := rfl
      omega
    | _ => ipureintro; intro h; cases h
  isplitr
  · ipureintro; exact Hl
  iexists γm, terms, fp, γw, wins
  iframe % # ∗

/-- A leader's last index is past `0` (`ownLogGhost_leader_last1`). -/
theorem ownRaftGhost_leader_last1 (γ : RaftNames) (id : w64) (s : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id s md -∗
      ⌜s.role = .leader → 1 ≤ plogLastIndexZ s.base s.log⌝ ∗ ownRaftGhost γ id s md := by
  iintro Hown
  iunfold ownRaftGhost at Hown
  icases Hown with ⟨%γs, %V, %πc, %kl, H⟩
  iNamed H
  icases ownLogGhost_leader_last1 γ id s kl _ $$ Hlg with ⟨%Ht1, Hlg⟩
  isplitr
  · ipureintro; exact Ht1
  iapply ownRaftGhost_intro γ id s γs V πc kl Hsname Hidnz Hmode Hfresh $$ Hslot Hvirt Hpend [] Hout Htally Hlead Hlg [] [] [] Hlcm Hrd
  · ipureintro; exact Hhist
  · ipureintro; exact Hlead_ok
  · ipureintro; exact Hfollower_votes
  · ipureintro; exact Hrole_ok

/-- An accepting `MsgAppResp`'s acknowledgement (`isMessage`). -/
theorem isMessage_appResp_acked (γ : RaftNames) (m : Msg) :
    m.ty = .appResp → m.reject = false →
    ⊢ isMessage (GF := GF) γ m -∗ isAcked γ m.src m.term m.index := by
  intro Hty Hrej
  unfold isMessage; rw [Hty]; simp only [Hrej, Bool.false_eq_true, ↓reduceIte]
  iintro ⟨H, -⟩; iexact H

/-- A leader's `Match` of another node: that node's acknowledgement at the leader's term
(`matchedOk`; the exempt entry is the leader's own). -/
theorem ownLogGhost_matched_ack (γ : RaftNames) (id : w64) (s : PState) (kl : Option w64)
    (W : DurMaps) (v i : w64) (Hr : s.role = .leader) (Hv : v ≠ id) (Hm : s.matched !! v = some i) :
    ⊢ ownLogGhost (GF := GF) γ id s kl W -∗ isAcked γ v s.term i ∗ ownLogGhost γ id s kl W := by
  iintro Hlg
  unfold ownLogGhost
  icases Hlg with ⟨%γm, %terms, %fp, %γw, %wins, H⟩
  iNamed H
  have hmo : matchedOk (GF := GF) γ id s fp = iprop([∗map] v ↦ i ∈ s.matched,
      isAcked (GF := GF) γ v s.term i ∨
        ⌜v = id ∧ uint.Z i ≤ plogLastIndexZ base0 (fp ++ s.log) ∧
          ∀ j x, uint.Z j ≤ uint.Z i → plogTermAt base0 (fp ++ s.log) j = some x →
            uint.Z x < uint.Z s.term⌝) := by
    unfold matchedOk; rw [Hr]
  rw [hmo]
  ihave #Ha : isAcked (GF := GF) γ v s.term i $$ []
  · ihave #Hx := (BigSepM.bigSepM_lookup (Φ := fun (v : w64) (i : w64) =>
        iprop(isAcked (GF := GF) γ v s.term i ∨
          ⌜v = id ∧ uint.Z i ≤ plogLastIndexZ base0 (fp ++ s.log) ∧
            ∀ j x, uint.Z j ≤ uint.Z i → plogTermAt base0 (fp ++ s.log) j = some x →
              uint.Z x < uint.Z s.term⌝)) (i := v) (x := i) Hm) $$ Hmatched
    icases Hx with (#Hx | %Hx)
    · iexact Hx
    · exact absurd Hx.1 Hv
  isplitr
  · iexact Ha
  iexists γm, terms, fp, γw, wins
  rw [hmo]
  iframe % # ∗

/-- A leader's `Match` of another node is its acknowledgement (`ownLogGhost_matched_ack`). -/
theorem ownRaftGhost_matched_ack (γ : RaftNames) (id : w64) (s : PState) (v i : w64)
    (Hr : s.role = .leader) (Hv : v ≠ id) (Hm : s.matched !! v = some i) :
    ⊢ ownRaftGhost (GF := GF) γ id s md -∗ isAcked γ v s.term i ∗ ownRaftGhost γ id s md := by
  iintro Hown
  iunfold ownRaftGhost at Hown
  icases Hown with ⟨%γs, %V, %πc, %kl, H⟩
  iNamed H
  icases ownLogGhost_matched_ack γ id s kl _ v i Hr Hv Hm $$ Hlg with ⟨#Ha, Hlg⟩
  isplitr
  · iexact Ha
  iapply ownRaftGhost_intro γ id s γs V πc kl Hsname Hidnz Hmode Hfresh $$ Hslot Hvirt Hpend [] Hout Htally Hlead Hlg [] [] [] Hlcm Hrd
  · ipureintro; exact Hhist
  · ipureintro; exact Hlead_ok
  · ipureintro; exact Hfollower_votes
  · ipureintro; exact Hrole_ok

end xt

end EtcdGrove
end Perennial
