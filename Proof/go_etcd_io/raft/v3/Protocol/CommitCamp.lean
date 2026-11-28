/-
Leader completeness for a client (#33 S3c, `notes/antithesis-rawnode-design.md` §2.1,
`commitIn_camp`): what a node knows committed at a term `tm` is in the campaign log of every
leader of a later term.
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.LeaderCompleteness

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section ghost
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- **Leader completeness for a client** (#33 S3c, design §2.1, `commitIn_camp`): a log `F`
committed to `c` as known in a term `tm` is, up to `c`, a prefix of the campaign log `F0` of
the leader `j` of any later term `T`. The leader's full log `G` with records, extending `F0`,
gives `F0` its records (`isCamp` carries none). For a cluster without a bootstrap log, where
`commitJ`'s boot arm is `c = 0`.

Proof (design §2.1, revision 2, T1): `commitJ`'s quorum arm gives a commit fact `cq γ t n Gq`
with `c ≤ n`, `t ≤ tm < T` and `Gq`, `F` of one term at `c`; `lc_core` at the campaign log
puts `Gq`'s term `t` at `n` in `F0`, so `Gq` and `F0` agree up to `n` (`full_match`), and `F`
and `F0` agree at `c`, hence below (`full_take_eq`). The vote table `lc_core` needs is the
commit invariant's (`raftCommitInv`), opened inside `↑raftN γ`. -/
theorem commitIn_camp (γ : RaftNames) (F : List EntryM) (c tm : w64) (j T : w64)
    (F0 G : List EntryM) :
    γ.reBoot = [] →
    uint.Z tm < uint.Z T → PlogWf base0 F → F0 <+: G →
    ⊢ raftCommitInv (GF := GF) γ -∗
      commitIn γ F c tm -∗ logRecs γ base0 F -∗ isLeader γ j T -∗ isCamp γ j T F0 -∗
      logRecs γ base0 G ={↑(raftN γ)}=∗ ⌜F.take (uint.nat c) <+: F0⌝ := by
  intro Hboot HT HwF Hpre
  iintro #Hinv #Hcm #HrF #Hl #Hc #HrG
  ihave #Hcj := commitIn_j γ F c tm $$ Hcm
  unfold commitJ
  icases Hcj with (%H0 | ⟨%t, %n, %Gq, #Hq, %Hcn⟩)
  · -- the boot arm: without a bootstrap log, `c = 0`
    rw [Hboot] at H0
    have Hc0 : uint.nat c = 0 := by have := H0.1; simp at this; word
    imodintro; ipureintro
    rw [Hc0]; exact List.nil_prefix
  obtain ⟨Hcn, Htm, HcF⟩ := Hcn
  -- the vote table, from the commit invariant
  have HE : (↑(raftLogN γ) : CoPset) ⊆ ↑(raftN γ) := raftLogN_of (fun _ h => h)
  ihave #Hli := raftCommitInv_log γ $$ Hinv
  unfold raftLogInv raftLogInvBody
  iinv Hli with ⟨%P, HP, Hjust, >Htbl, Hwt, Hpo⟩ Hclose
  -- the campaign log, with records
  icases isCamp_ok γ j T F0 $$ Hc with %Hcok
  have HwF0 : PlogWf base0 F0 := Hcok.1
  have HF0 : G.take F0.length = F0 := by
    rw [take_of_prefix Hpre (Nat.le_refl _)]; exact List.take_length
  ihave #HrF0 := logRecs_take γ G F0.length $$ HrG
  rw [HF0]
  -- `lc_core` at the campaign log: `Gq`'s term at `n` is in `F0`
  icases lc_core γ ((uint.Z T).toNat + 1) T t n Gq j F0 F0
      (by have := uint_Z_nonneg T; omega) (by omega) HwF0 (camp_last T F0 Hcok)
      $$ Htbl Hq Hl Hc HrF0 with %HF0n
  icases cq_full γ t n Gq $$ Hq with ⟨%HwGq, #HrGq⟩
  icases cq_base γ t n Gq $$ Hq with ⟨%HGqn, -⟩
  icases full_match γ Gq F0 n HwGq HwF0 (by rw [HGqn]; rfl) (by rw [HGqn, HF0n]) $$ HrGq HrF0
    with %Hm
  have HsGq := full_term_at_some Gq c n (by rw [HGqn]; rfl) Hcn
  icases full_take_eq γ F F0 c HwF HwF0 (by rw [← HcF]; exact HsGq) (by rw [← HcF]; exact Hm c Hcn)
    $$ HrF HrF0 with %Htk
  imod Hclose $$ [HP Hjust Htbl Hwt Hpo] with -
  · inext
    iexists P
    iframe
  imodintro; ipureintro
  show F.take (uint.Z c).toNat <+: F0
  rw [Htk]; exact List.take_prefix _ _

end ghost

end EtcdGrove
end Perennial
