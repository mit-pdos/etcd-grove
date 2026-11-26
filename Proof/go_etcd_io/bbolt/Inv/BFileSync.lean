/-
bbolt's `fdatasync` of its file over its shares (`bMeta`, `bBytes`), in either mode (W1 stage B of
`plans/bbolt-crash-plan.md` §7, step 3; Lean-first, no Rocq counterpart).

* `bRanges p R`: bbolt's whole share of the ranges `R` (offset, bytes) of the file.
* `wp_bFdatasync`: `syscall.Fdatasync` of the file. Outside a crash invariant, the byte-less
  `specB`; inside one, the local crash spec (`syscall.Fdatasync.specCrashIL`), its mask made of the
  ranges `R` the caller holds, which cover the ranges `L` written since the last sync (`RCov`: every
  other byte is durable, `bMeta`'s `DurOut`); the obligation from `bDur_sync_idle`. On success the
  ranges written are synced (`L = []`) and the bytes keep their values.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.BFileOps
public import Spec.syscall.Fdatasync

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
open Iris Iris.BI Iris.ProofMode

/-! ## Ranges of the file -/

/-- A range's bytes as `(offset, bytes)`; `R` covers the bytes `[r.1, r.1 + r.2.length)` of each. -/
abbrev rIn (r : Nat × List ByteG) (k : Nat) : Prop := r.1 ≤ k ∧ k < r.1 + r.2.length

/-- The mask of the ranges `R`. -/
def rMask (R : List (Nat × List ByteG)) (k : Nat) : Bool := R.any (fun r => decide (rIn r k))

/-- The ranges `R` are pairwise disjoint. -/
def RDisj (R : List (Nat × List ByteG)) : Prop :=
  R.Pairwise (fun r r' => ∀ k, rIn r k → ¬ rIn r' k)

/-- **The ranges `R` cover the bytes of the ranges `L` (offset, length) below `sz`.** -/
def RCov (R : List (Nat × List ByteG)) (L : List (Nat × Nat)) (sz : Nat) : Prop :=
  ∀ k, (∃ r ∈ L, r.1 ≤ k ∧ k < r.1 + r.2) → k < sz → ∃ r ∈ R, rIn r k

/-- Two lists of ranges with the same offsets and values. -/
def RSame (R R' : List (Nat × List ByteG)) : Prop :=
  List.Forall₂ (fun r r' => r'.1 = r.1 ∧ r'.2.map Prod.fst = r.2.map Prod.fst) R R'

theorem RSame.refl (R : List (Nat × List ByteG)) : RSame R R := by
  unfold RSame
  induction R with
  | nil => exact .nil
  | cons r R ih => exact .cons ⟨rfl, rfl⟩ ih

/-- The ranges synced: their bytes durable, as their values. -/
def rDur (R : List (Nat × List ByteG)) : List (Nat × List ByteG) :=
  R.map (fun r => (r.1, r.2.map (fun x => durB x.1)))

theorem RSame_rDur (R : List (Nat × List ByteG)) : RSame R (rDur R) := by
  unfold RSame rDur
  induction R with
  | nil => exact .nil
  | cons r R ih =>
    refine .cons ⟨rfl, ?_⟩ ih
    simp only [List.map_map]
    rfl

theorem rMask_cons (r : Nat × List ByteG) (R : List (Nat × List ByteG)) (k : Nat) :
    rMask (r :: R) k = (decide (rIn r k) || rMask R k) := by
  simp only [rMask, List.any_cons]

theorem rMask_true {R : List (Nat × List ByteG)} {k : Nat} : rMask R k = true ↔ ∃ r ∈ R, rIn r k := by
  simp only [rMask, List.any_eq_true, decide_eq_true_eq]

theorem rDur_length (R : List (Nat × List ByteG)) (r : Nat × List ByteG) (hr : r ∈ rDur R) :
    ∃ r0 ∈ R, r = (r0.1, r0.2.map (fun x => durB x.1)) := by
  unfold rDur at hr
  obtain ⟨r0, h0, he⟩ := List.mem_map.1 hr
  exact ⟨r0, h0, he.symm⟩

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **bbolt's whole share of the ranges `R` of the file `p`.** -/
def bRanges (p : BFile) (R : List (Nat × List ByteG)) : IProp GF :=
  iprop([∗list] r ∈ R, bBytes p r.1 (DFrac.own 1) r.2)

omit go_gctx sem in
/-- The ranges' bytes as the extension's and their exclusivity tokens. -/
theorem bRanges_os (p : BFile) (R : List (Nat × List ByteG)) :
    bRanges (GF := GF) p R ⊣⊢ ([∗list] r ∈ R, osBytes p.ino r.1 (p.dq (DFrac.own 1)) r.2) ∗
      ([∗list] r ∈ R, bGhost p r.1 (DFrac.own 1) r.2.length) := by
  unfold bRanges
  refine BIBase.BiEntails.trans ?_ BigSepL.bigSepL_sep_eqv
  exact ⟨BigSepL.bigSepL_mono_of_forall (fun {_ _} => (bBytes_os _ _ _ _).1),
    BigSepL.bigSepL_mono_of_forall (fun {_ _} => (bBytes_os _ _ _ _).2)⟩

/-- **The ranges as a mask** over the file's bytes `bs`, of which they are runs. -/
theorem ranges_mask (i : Ino) (dq : DFrac) (bs : List ByteG) :
    ∀ R : List (Nat × List ByteG),
    (∀ r ∈ R, r.1 + r.2.length ≤ bs.length ∧ r.2 = (bs.drop r.1).take r.2.length) → RDisj R →
    ([∗list] r ∈ R, osBytes (GF := GF) i r.1 dq r.2) ⊣⊢ cBytes i (fun _ => dq) (rMask R) 0 bs
  | [], _, _ => by
    refine BIBase.BiEntails.trans BigSepL.bigSepL_nil ?_
    exact (cBytes_none i _ _ 0 bs fun k _ => by simp [rMask]).symm
  | r :: R, h, hd => by
    have hd' := List.pairwise_cons.1 hd
    have e : rMask (r :: R) = fun k => decide (rIn r k) || rMask R k :=
      funext fun k => rMask_cons r R k
    rw [e]
    refine BIBase.BiEntails.trans BigSepL.bigSepL_cons ?_
    refine BIBase.BiEntails.trans ?_ (cBytes_or i _ _ _ 0 bs fun k hk => ?_).symm
    · refine sep_congr ?_ (ranges_mask i dq bs R (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
        hd'.2)
      obtain ⟨hl, he⟩ := h r List.mem_cons_self
      have hr := cBytes_range (GF := GF) i dq bs r.1 r.2.length hl
      have e2 : (fun k => decide (rIn r k)) = (fun k => decide (r.1 ≤ k ∧ k < r.1 + r.2.length)) := rfl
      rw [e2]
      refine BIBase.BiEntails.trans ?_ hr.symm
      rw [← he]
      exact .rfl
    · apply Classical.byContradiction
      intro hc
      rw [Bool.not_eq_false, rMask_true] at hc
      obtain ⟨r', hr', hk'⟩ := hc
      exact hd'.1 r' hr' k (by simpa using hk) hk'

/-- **The caller's ranges are the state's bytes** (`csOwnIL_agree`, range by range). -/
theorem ranges_agree {A : Type} [Pos.Countable A] (N : Namespace) (i : Ino) (γ γa γc : GName)
    (Ok : A → CSt → Prop) (s : CSt) (a : A) (E : CoPset) (hE : ↑N ⊆ E) (dq : DFrac) :
    ∀ R : List (Nat × List ByteG), (∀ r ∈ R, r.1 + r.2.length ≤ s.bs.length) →
    ⊢ csInvI (GF := GF) N i γ γa γc Ok -∗ csOwnIL (GF := GF) i γ γa s a -∗
      ([∗list] r ∈ R, osBytes (GF := GF) i r.1 dq r.2) ={E}=∗
      csOwnIL (GF := GF) i γ γa s a ∗ ([∗list] r ∈ R, osBytes (GF := GF) i r.1 dq r.2) ∗
        ⌜∀ r ∈ R, r.2 = (s.bs.drop r.1).take r.2.length⌝
  | [], _ => by
    iintro #Hinv Hown Hb
    imodintro; iframe
    ipureintro; intro r hr; cases hr
  | r :: R, h => by
    iintro #Hinv Hown Hb
    icases BigSepL.bigSepL_cons.1 $$ Hb with ⟨Hr, HR⟩
    imod csOwnIL_agree N i γ γa γc Ok s a E hE r.1 dq r.2 (h r List.mem_cons_self) $$ Hinv Hown Hr
      with ⟨Hown, Hr, %he⟩
    imod ranges_agree N i γ γa γc Ok s a E hE dq R (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
      $$ Hinv Hown HR with ⟨Hown, HR, %hR⟩
    imodintro
    iframe Hown
    isplitl [Hr HR]
    · iapply BigSepL.bigSepL_cons.2; iframe
    ipureintro
    intro r' hr'
    rcases List.mem_cons.1 hr' with rfl | hr'
    · exact he
    · exact hR r' hr'

/-- The synced ranges are runs of the synced bytes. -/
theorem rDur_runs (bs : List ByteG) (R : List (Nat × List ByteG))
    (h : ∀ r ∈ R, r.1 + r.2.length ≤ bs.length ∧ r.2 = (bs.drop r.1).take r.2.length) :
    ∀ r ∈ rDur R, r.1 + r.2.length ≤ (bs.map (fun x => durB x.1)).length ∧
      r.2 = ((bs.map (fun x => durB x.1)).drop r.1).take r.2.length := by
  intro r hr
  obtain ⟨r0, h0, rfl⟩ := rDur_length R r hr
  obtain ⟨hl, he⟩ := h r0 h0
  simp only [List.length_map]
  refine ⟨hl, ?_⟩
  rw [← List.map_drop, ← List.map_take]
  congr 1

theorem RDisj_rDur (R : List (Nat × List ByteG)) (h : RDisj R) : RDisj (rDur R) := by
  unfold RDisj rDur at *
  rw [List.pairwise_map]
  refine List.Pairwise.imp (fun {r r'} hrr k hk hk' => hrr k ?_ ?_) h
  · simpa [rIn] using hk
  · simpa [rIn] using hk'

variable [syscall.Assumptions] in
/-- **`syscall.Fdatasync` of bbolt's file**, in either mode (see the file header). -/
theorem wp_bFdatasync (hS : syscall.Fdatasync.specB (GF := GF) (hG := hG))
    (hSC : syscall.Fdatasync.specCrashIL (GF := GF) (hG := hG))
    (fd : w64) (dq : DFrac) (d : OsFd) (p : BFile) (C : CommitSt) (L : List (Nat × Nat))
    (m : OsMeta) (R : List (Nat × List ByteG)) (hd : d.ino = p.ino) (hns : bNsOk p)
    (hcov : RCov R L m.size) (hdisj : RDisj R) (hin : ∀ r ∈ R, r.1 + r.2.length ≤ m.size) :
    {{ osInv (GF := GF) ∗ bCsInv p ∗ osFd fd dq d ∗ bMeta p C L m ∗ bRanges p R }}
      (App (Val (@! syscall.Fdatasync)) (Val #fd))
    {{ (e : w64), RET #(errnoErr e); osFd fd dq d ∗
        ((⌜e = 0⌝ ∗ ∃ (m' : OsMeta) (R' : List (Nat × List ByteG)), bMeta p C [] m' ∗ bRanges p R' ∗
            ⌜m'.size = m.size ∧ m'.maps = m.maps ∧ RSame R R'⌝) ∨
         (⌜e ≠ 0 ∧ ¬ FsNoErr⌝ ∗ bMeta p C L m ∗ bRanges p R)) }} := by
  iintro %Φ ⟨#Hos, #Hinv, Hfd, Hm, HR⟩ HΦ
  cases hc : p.cs with
  | none =>
    simp only [bMeta_none hc]
    rw [← hd]
    iapply (hS fd dq d m) $$ [Hfd Hm]
    · iframe; iframe #
    inext
    iintro %e ⟨Hfd, Hr⟩
    iapply HΦ $$ %e
    iframe Hfd
    icases Hr with (⟨%he, %c, Hm⟩ | ⟨%he, Hm⟩)
    · ileft
      isplitr
      · ipureintro; exact he
      iexists m.bsynced c, R
      rw [hd]
      iframe
      ipureintro; exact ⟨rfl, rfl, RSame.refl R⟩
    · iright
      isplitr
      · ipureintro; exact ⟨he.1, he.2.2⟩
      rw [hd]
      iframe
  | some c =>
    ihave #Hci := bCsInv_some p c hc $$ Hinv
    icases bMeta_own p c hc C L m $$ Hm with ⟨%bs, %a, Hown, Ha, %Hf⟩
    obtain ⟨hph, hcur, hdur, hfs, hlh⟩ := Hf
    imod csOwnIL_ok c.N p.ino c.g c.ga c.gc bCsOk ⟨m, bs, 0, 0, .idle⟩ a ⊤ CoPset.subseteq_top
      $$ Hci Hown with ⟨Hown, %Hok⟩
    ihave %hlo := csOwnL_locOk (csTokI c.g c.ga a) p.ino ⟨m, bs, 0, 0, .idle⟩ $$ Hown
    have hbl : bs.length = m.size := hlo.1.1
    have hdq : p.dq (DFrac.own 1) = DFrac.own (1 : Qp).half := by unfold BFile.dq; rw [hc]; rfl
    icases (bRanges_os p R).1 $$ HR with ⟨HR, HG⟩
    rw [hdq]
    imod ranges_agree c.N p.ino c.g c.ga c.gc bCsOk ⟨m, bs, 0, 0, .idle⟩ a ⊤ CoPset.subseteq_top
      (DFrac.own (1 : Qp).half) R (fun r hr => by show _ ≤ bs.length; rw [hbl]; exact hin r hr)
      $$ Hci Hown HR with ⟨Hown, HR, %hag⟩
    have hruns : ∀ r ∈ R, r.1 + r.2.length ≤ bs.length ∧ r.2 = (bs.drop r.1).take r.2.length :=
      fun r hr => ⟨by rw [hbl]; exact hin r hr, hag r hr⟩
    ihave HR := (ranges_mask p.ino (DFrac.own (1 : Qp).half) bs R hruns hdisj).1 $$ HR
    have hok : bCsOk a (csSynced m [] [] bs 0 0) := fun hf =>
      bDur_sync_idle a hph m [] [] bs 0 0 (fun y hy => by cases hy) (by simpa using Hok.1 hf)
    have hcov' : ∀ b, b < m.size → m.dlo ≤ b → b < m.dhi →
        rMask R b = true ∨ ∃ x, bs[b]? = some x ∧ x = durB x.1 := by
      intro b hb _ _
      by_cases hL : ∃ r ∈ L, r.1 ≤ b ∧ b < r.1 + r.2
      · left; exact rMask_true.2 (hcov b hL hb)
      · right
        have hb' : b < bs.length := by omega
        refine ⟨bs[b], List.getElem?_eq_getElem hb', ?_⟩
        refine hdur b bs[b] (List.getElem?_eq_getElem hb') fun r hr => ?_
        apply Classical.byContradiction; intro hn
        exact hL ⟨r, hr, by omega, by omega⟩
    iapply (hSC fd dq d c.N p.ino c.g c.ga c.gc bCsOk a m bs (rMask R) hd (hns c hc) hcov' hok)
      $$ [Hfd Hown HR]
    · iframe; iframe #
    inext
    iintro %e ⟨Hfd, Hr⟩
    iapply HΦ $$ %e
    iframe Hfd
    icases Hr with (⟨%he, Hown, HR⟩ | ⟨%he, Hown, HR⟩)
    · ileft
      isplitr
      · ipureintro; exact he
      iexists m.synced, rDur R
      ihave HR := (ranges_mask p.ino (DFrac.own (1 : Qp).half) (bs.map (fun x => durB x.1)) (rDur R)
        (rDur_runs bs R hruns) (RDisj_rDur R hdisj)).2 $$ [HR]
      · have e : rMask (rDur R) = rMask R := by
          funext k
          simp [rMask, rDur, List.any_map, rIn, Function.comp_def]
        rw [e]; iexact HR
      have hGl : ([∗list] r ∈ R, bGhost (GF := GF) p r.1 (DFrac.own 1) r.2.length) ⊢
          [∗list] r ∈ rDur R, bGhost (GF := GF) p r.1 (DFrac.own 1) r.2.length := by
        unfold rDur
        rw [BigSepL.bigSepL_map]
        simp only [List.length_map]
        exact .rfl
      ihave HG := hGl $$ HG
      isplitl [Hown Ha]
      · iapply bMeta_of_own p c hc C [] m.synced (bs.map (fun x => durB x.1)) a
          ⟨hph, hcur, fun k x hk _ => by
            obtain ⟨y, -, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? hk); rfl, hfs, rfl⟩
          $$ [Hown Ha]
        iframe
      isplitl [HR HG]
      · iapply (bRanges_os p (rDur R)).2; rw [hdq]; iframe
      ipureintro; exact ⟨rfl, rfl, RSame_rDur R⟩
    · iright
      isplitr
      · ipureintro; exact he
      ihave HR := (ranges_mask p.ino (DFrac.own (1 : Qp).half) bs R hruns hdisj).2 $$ HR
      isplitl [Hown Ha]
      · iapply bMeta_of_own p c hc C L m bs a ⟨hph, hcur, hdur, hfs, hlh⟩ $$ [Hown Ha]
        iframe
      iapply (bRanges_os p R).2; rw [hdq]; iframe

end res

end bbolt
end EtcdGrove
end Perennial
