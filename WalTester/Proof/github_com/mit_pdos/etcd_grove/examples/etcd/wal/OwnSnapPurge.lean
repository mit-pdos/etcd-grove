/- Lean-first (no Rocq counterpart).

**`opOwnSnap`'s purge round on the tester's oracle** (unit `locks`, session 10; `notes/wal-units/locks.md`).
Before the round, every candidate's purge bound is raised to its unlock bound (`tPurNames`, the loop of
`opOwnSnap`), and the raised oracle stored. The round's removals each move the WAL's purge and read
positions to some `k ≤ p ≤ d.unl` (`walPurgeAcc`); the oracle covers them (session 5's check): the running
member's relation `tMemOk o c d` has no pending open and `d.unl ≤ c.unl ≤ c.pur`, and the invariant's
candidate likewise (`tCandOk`, with no pending open its unlock bound is `c.unl`).

* `tPurCand`, `tPurNames`, the loop's prefix `tPurPre`, and what the raise keeps (`tMemOk_pur`, ...).
* `tCandOk_purge`, `tMemOk_purge`: a removal's state is still accounted for.
* `tPurgeTok`, `tInv_purgeAcc`: the caller's repeatable commit (`walPurgeAcc`) from the tester's invariant,
  its token the member's halves of the WAL state and oracle.
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.OwnSnapAu
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PurgeDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalFs

section pure
variable [GooseExts]

/-- A candidate's purge bound raised to its unlock bound (`if c.unl > c.pur { c.pur = c.unl }`). -/
def tPurCand (cd : TCand) : TCand :=
  { cd with pur := if uint.nat cd.pur < uint.nat cd.unl then cd.unl else cd.pur }

/-- **The oracle with every candidate's purge bound raised** (`opOwnSnap`'s loop before the round). -/
def tPurNames (o : TOracle) : TOracle := { o with cands := o.cands.map tPurCand }

theorem tPurCand_h (cd : TCand) : (tPurCand cd).h = cd.h := rfl
theorem tPurCand_unl (cd : TCand) : (tPurCand cd).unl = cd.unl := rfl

theorem tPurCand_pur_le (cd : TCand) : uint.nat cd.pur ≤ uint.nat (tPurCand cd).pur := by
  unfold tPurCand; split <;> simp only [] <;> omega

theorem tPurCand_unl_le (cd : TCand) : uint.nat (tPurCand cd).unl ≤ uint.nat (tPurCand cd).pur := by
  unfold tPurCand; split <;> simp only [] <;> omega

theorem tPurNames_hist (o : TOracle) (cd : TCand) : tCandHist (tPurNames o) (tPurCand cd) = tCandHist o cd :=
  rfl

theorem tPurNames_mark (o : TOracle) (cd : TCand) : tCandMark (tPurNames o) (tPurCand cd) = tCandMark o cd :=
  rfl

theorem tPurNames_mem {o : TOracle} {cd : TCand} (h : cd ∈ o.cands) : tPurCand cd ∈ (tPurNames o).cands :=
  List.mem_map_of_mem h

theorem tPurNames_all (o : TOracle) : ∀ cd ∈ (tPurNames o).cands, uint.nat cd.unl ≤ uint.nat cd.pur := by
  intro cd hcd
  obtain ⟨cd0, -, rfl⟩ := List.mem_map.1 hcd
  exact tPurCand_unl_le cd0

theorem tPurNames_length (o : TOracle) :
    (tEncodeOracle (tPurNames o)).length = (tEncodeOracle o).length := by
  rw [tEncodeOracle_length, tEncodeOracle_length]
  simp [tOrRest, tPurNames, List.length_flatMap, tPurCand, tU64_length, Function.comp_def]

theorem tMemOk_pur {o : TOracle} {c : TCand} {d : WalDur} (h : tMemOk o c d) :
    tMemOk (tPurNames o) (tPurCand c) d := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, tPurNames_mem h2, h3, h4, Nat.le_trans h5 (tPurCand_pur_le c),
    Nat.le_trans h6 (tPurCand_pur_le c), h7, h8, h9, h10, h11⟩

theorem tMemHs_pur {o : TOracle} {d : WalDur} (h : tMemHs o d) : tMemHs (tPurNames o) d := h

theorem tCheckWf_pur {o : TOracle} (h : tCheckWf o) : tCheckWf (tPurNames o) := by
  refine ⟨h.1, ?_⟩
  intro cd hcd
  obtain ⟨cd0, hcd0, rfl⟩ := List.mem_map.1 hcd
  exact h.2 cd0 hcd0

theorem tMemSim_pur {o : TOracle} {c : TCand} {bs l cm : w64} (h : tMemSim o c bs l cm) :
    tMemSim (tPurNames o) (tPurCand c) bs l cm := h

/-- The state after a purge's removal (`walPurgeAcc`'s commit). -/
def tPurgeD (d : WalDur) (p k : Nat) : WalDur := { d with pur := max d.pur p, cut := k }

/-- **A removal's state is still accounted for by the invariant's candidate** (no pending open, the
candidate's purge bound at least its unlock bound). -/
theorem tCandOk_purge {o : TOracle} {c : TCand} {d : WalDur} (h : tCandOk o c d) (hop : o.opens = [])
    (hc : uint.nat c.unl ≤ uint.nat c.pur) {p k : Nat} (hk : k ≤ p) (hp : p ≤ d.unl) :
    tCandOk o c (tPurgeD d p k) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hb : tOpensBound o c = 0 := by simp [tOpensBound, hop]
  rw [hb] at h4
  have h4' : d.unl ≤ uint.nat c.unl := by simpa using h4
  refine ⟨h1, ?_, ?_, ?_, h5, h6, h7⟩
  · show max d.pur p ≤ _; omega
  · show k ≤ _; omega
  · show d.unl ≤ _; rw [hb]; simpa using h4'

/-- **A removal's state is still the running member's.** -/
theorem tMemOk_purge {o : TOracle} {c : TCand} {d : WalDur} (h : tMemOk o c d)
    (hc : uint.nat c.unl ≤ uint.nat c.pur) {p k : Nat} (hk : k ≤ p) (hp : p ≤ d.unl) :
    tMemOk o c (tPurgeD d p k) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, by show max d.pur p ≤ _; omega, by show k ≤ _; omega, h7, h8, h9, h10, h11⟩

theorem tMemHs_purge {o : TOracle} {d : WalDur} (h : tMemHs o d) (p k : Nat) : tMemHs o (tPurgeD d p k) := h

/-- The candidates after `k` turns of the purge-raise loop. -/
def tPurPre (o : TOracle) (k : Nat) : List TCand :=
  (o.cands.take k).map tPurCand ++ o.cands.drop k

theorem tPurPre_zero (o : TOracle) : tPurPre o 0 = o.cands := by simp [tPurPre]

theorem tPurPre_all (o : TOracle) {k : Nat} (hk : o.cands.length ≤ k) :
    tPurPre o k = (tPurNames o).cands := by
  simp [tPurPre, tPurNames, List.take_of_length_le hk, List.drop_of_length_le hk]

theorem tPurPre_get (o : TOracle) {k : Nat} {cd : TCand} (hk : o.cands[k]? = some cd) :
    (tPurPre o k)[k]? = some cd := by
  have hl : k < o.cands.length := (List.getElem?_eq_some_iff.1 hk).1
  unfold tPurPre
  rw [List.getElem?_append_right (by simp; omega)]
  simp [hk, show k - min k o.cands.length = 0 by omega]

theorem tPurPre_set (o : TOracle) {k : Nat} {cd : TCand} (hk : o.cands[k]? = some cd) :
    (tPurPre o k).set k (tPurCand cd) = tPurPre o (k + 1) := by
  have hl : k < o.cands.length := (List.getElem?_eq_some_iff.1 hk).1
  unfold tPurPre
  apply List.ext_getElem?
  intro n
  rw [List.getElem?_set]
  by_cases hn : n = k
  · subst hn
    rw [if_pos rfl]
    have : n < ((o.cands.take n).map tPurCand ++ o.cands.drop n).length := by simp; omega
    rw [if_pos this, List.getElem?_append_left (by simp; omega)]
    simp [List.getElem?_take, hk]
  · rw [if_neg (Ne.symm hn)]
    by_cases hlt : n < k
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
      simp [List.getElem?_take, hlt, show n < k + 1 by omega]
    · rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
      simp only [List.length_map, List.length_take, List.getElem?_drop]
      congr 1; omega

theorem tPurPre_length (o : TOracle) (k : Nat) : (tPurPre o k).length = o.cands.length := by
  simp [tPurPre]; omega

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- **The token of a purge round's commit**: the member's halves of the WAL state and the oracle `o`,
the state accounted for by the member's candidate `c`, its history `H`. -/
def tPurgeTok (W : WalGS GF) (γ : TGS) (o : TOracle) (c : TCand) (H : List (WalOpG WalEnt)) : IProp GF :=
  iprop(∃ d : WalDur, tWalOwn γ (some d) ∗ tOrOwn γ o none ∗ ⌜tMemOk o c d ∧ tMemHs o d ∧ d.H = H⌝)

/-- **The purge round's repeatable commit, from the tester's invariant**: with every candidate's purge
bound at least its unlock bound (`tPurNames`) and the member's candidate `c` raised so. -/
theorem tInv_purgeAcc (W : WalGS GF) (e : TEnv) (γ : TGS) (o : TOracle) (c : TCand) (H : List (WalOpG WalEnt))
    (hall : ∀ cd ∈ o.cands, uint.nat cd.unl ≤ uint.nat cd.pur) :
    TInv (W := W) e γ ⊢ walPurgeAcc (W := W) (tWalDir e.area) 0 (tPurgeTok W γ o c H) := by
  iintro #Hinv
  unfold walPurgeAcc
  iintro !> Htok
  unfold tPurgeTok
  icases Htok with ⟨%d, Hwo, Hoo, %hd⟩
  obtain ⟨hok, hhs, hH⟩ := hd
  have hcr : o.created = true := hok.1
  have hop : o.opens = [] := hok.2.2.1
  unfold atomic_acc
  iunfold TInv at Hinv
  imod inv_acc (E := WalFs.walAuMask) tN_sub_walAu $$ Hinv with ⟨Hi, Hclose⟩
  imod Hi
  iunfold TInvBody at Hi
  icases Hi with ⟨%s, %o2, %oa, %od1, Hs, %hfile, Ho1, Hwd, Hw1, #Hr1, #Ha1⟩
  ihave %hag := tWalOwn_agree γ (some d) od1 $$ Hwo Hw1
  subst hag
  ihave %hao := tOrOwn_agree (W := W) γ o o2 none oa $$ Hoo Ho1
  obtain ⟨h1, h2⟩ := hao
  subst h2; subst o2
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ WalFs.walAuMask \ ↑tN from LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  unfold WalFs.walDiskAtI
  iexists d
  iframe Hwd
  isplit
  · iintro Hwd
    imod Hclose2 with -
    imod Hclose $$ [Hs Ho1 Hwd Hw1] with -
    · inext; iunfold TInvBody; iexists s, o, none, some d; iframe; iframe #
      ipureintro; exact hfile
    imodintro
    iexists d
    iframe
    ipureintro; exact ⟨hok, hhs, hH⟩
  · iintro %p %kk ⟨%hpk, Hwd⟩
    obtain ⟨hk1, hk2, hk3⟩ := hpk
    iunfold tWalOwn at Hwo
    imod ghostVar_update_halves (some (tPurgeD d p kk)) γ.γw _ _ $$ Hwo Hw1 with ⟨Hwo, Hw1⟩
    iunfold tRelI at Hr1
    simp only [hcr, ↓reduceIte]
    icases Hr1 with ⟨%d0, %c0, %hr0, #Hsl, #Hnm⟩
    obtain ⟨hd0, hc0, hok0, hwf0⟩ := hr0
    cases hd0
    imod Hclose2 with -
    imod Hclose $$ [Hs Ho1 Hwd Hw1] with -
    · inext; iunfold TInvBody; iexists s, o, none, some (tPurgeD d p kk)
      iframe
      isplitr
      · ipureintro; exact hfile
      isplitl
      · iunfold tRelI
        simp only [hcr, ↓reduceIte]
        iexists tPurgeD d p kk, c0
        iframe #
        ipureintro
        exact ⟨rfl, hc0, tCandOk_purge hok0 hop (hall c0 hc0) hk2 hk3, hwf0⟩
      · simp only [tRelA]; iempintro
    imodintro
    iexists tPurgeD d p kk
    unfold tWalOwn
    iframe
    ipureintro
    exact ⟨tMemOk_purge hok (hall c hok.2.1) hk2 hk3, tMemHs_purge hhs p kk, hH⟩

end proof

end etcd_wal
end EtcdGrove
end Perennial
