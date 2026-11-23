/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RepsOkInv.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Discharging `swift.RepsOk` (recoveredSync's premises on its reports) from the protocol
invariant: the new leader holds `reported` facts of a majority for its ballot `b'`; the
invariant's model (`PInv`: `rep_ok`, `entryOk`, `loc_ok`, `pre_ok`) gives the phases' bound, the
`cballot`s below `b'`, the pre-accepted dependencies without duplicates (they are `depsIn` of a
sequence without duplicates, or a permutation of such), and the registrations (`cmds` with the
invariant's "put or get", D10) give the commands' kinds.

The reports' total size `< 2^31` (GAP M-c, closed by D13): each report's entries are distinct
registered commands (`sp.rep_ids_nodup`), so at most `6 · 2^25` (`sp.cmds_len`, the clients'
bounds), and a majority of `N ≤ 7` replicas reports.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RepsOk
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecSyncPure
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncFacts
import all Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace sp

/-! ## Dependencies without duplicates -/

theorem lkDeps_nodup (t : Seq) (c : Cmd) (h : (t.map Prod.fst).Nodup) : (lkDeps t c).Nodup := by
  unfold lkDeps
  simp only []
  have hks : (((t.filter (fun p => p.2.key == c.key)).reverse).map Prod.fst).Nodup := by
    rw [List.map_reverse, (List.reverse_perm _).nodup_iff]
    exact (List.filter_sublist.map Prod.fst).nodup h
  have hsince : ((((t.filter (fun p => p.2.key == c.key)).reverse.takeWhile
      (fun p => !p.2.isPut)).map Prod.fst).reverse).Nodup := by
    rw [(List.reverse_perm _).nodup_iff]
    exact ((List.takeWhile_sublist _).map Prod.fst).nodup hks
  have hlast : ((((t.filter (fun p => p.2.key == c.key)).reverse.find?
      (fun p => p.2.isPut)).toList).map Prod.fst).Nodup := by
    cases (((t.filter (fun p => p.2.key == c.key)).reverse.find? (fun p => p.2.isPut))) <;> simp
  split
  · rw [List.nodup_append]
    refine ⟨hlast, hsince, ?_⟩
    intro a ha b hb hab
    subst hab
    cases hf : (((t.filter (fun p => p.2.key == c.key)).reverse.find? (fun p => p.2.isPut))) with
    | none => rw [hf] at ha; simp at ha
    | some p =>
      rw [hf] at ha
      simp only [Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton] at ha
      subst ha
      rw [List.mem_reverse] at hb
      obtain ⟨q, hq, hqp⟩ := List.mem_map.mp hb
      have hpk := List.mem_of_find?_eq_some hf
      have hpput := List.find?_some hf
      have hqk := List.takeWhile_subset _ hq
      have hqnp := List.all_eq_true.mp List.all_takeWhile q hq
      have := swift.rec.inj_of_nodup_map Prod.fst hks hqk hpk hqp
      subst this
      simp_all
  · exact hlast

theorem depsIn_nodup (s : Seq) (x : CmdId) (h : (s.map Prod.fst).Nodup) : (depsIn s x).Nodup := by
  unfold depsIn
  split
  · apply lkDeps_nodup
    unfold before
    exact ((List.takeWhile_sublist _).map Prod.fst).nodup h
  · exact List.nodup_nil

theorem seqOf_fst_sub (S : PState) (l : List CmdId) : ((S.seqOf l).map Prod.fst).Sublist l := by
  induction l with
  | nil => exact List.Sublist.slnil
  | cons y l ih =>
    unfold PState.seqOf at ih ⊢
    rw [List.filterMap_cons]
    cases hc : S.cmds y with
    | none => exact ih.cons y
    | some c => simp only [Option.map_some, List.map_cons]; exact ih.cons_cons y

/-- A report entry pre-accepted (phase 1) has dependencies without duplicates. -/
theorem entry_dep_nodup {S : PState} {N : Nat} {fr : Bool} (HI : S.PInv N fr) {r c : Nat}
    {e : RepEntry} (he : S.entryOk N r c e) (h1 : e.phase.toNat = 1) : e.dep.Nodup := by
  obtain ⟨-, -, -, -, h1', -⟩ := he
  have hnd : ∀ r' b, ((S.seqOf (S.loc r' b)).map Prod.fst).Nodup := fun r' b =>
    (seqOf_fst_sub S _).nodup (HI.loc_ok r' b).1
  rcases h1' h1 with ⟨-, -, hp⟩ | hpre
  · exact hp.nodup_iff.mpr (depsIn_nodup _ _ (hnd _ _))
  · obtain ⟨-, -, -, hD, -⟩ := HI.pre_ok r c e.id e.dep hpre
    rw [hD]; exact depsIn_nodup _ _ (hnd _ _)

theorem cmds_len {S : PState} {mC : GMap CmdId Cmd} {mQ : GMap w32 Nat}
    (hrepr : ∀ x, mC.lookup x = S.cmds x)
    (hcl : ∀ x c, mC.lookup x = some c → (∃ n, mQ.lookup x.cl = some n ∧ x.seq.toNat < n) ∧
      (c.isPut ∨ c.isGet) ∧ x.cl.toInt ≥ 1 ∧ c.val.length < 2 ^ 16 ∧ 0 ≤ x.seq.toInt ∧
      x.seq.toNat < 2 ^ 25)
    (hdom : ∀ cl n, mQ.lookup cl = some n → 1 ≤ cl.toInt ∧ cl.toInt ≤ 6)
    (l : List CmdId) (hnd : l.Nodup) (hreg : ∀ x ∈ l, S.cmds x ≠ none) : l.length ≤ 6 * 2 ^ 25 := by
  have hb : ∀ x ∈ l, 1 ≤ x.cl.toInt ∧ x.cl.toInt ≤ 6 ∧ x.seq.toNat < 2 ^ 25 := by
    intro x hx
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (hreg x hx)
    rw [← hrepr] at hc
    obtain ⟨⟨n, hn, -⟩, -, -, -, -, hs⟩ := hcl x c hc
    exact ⟨(hdom _ _ hn).1, (hdom _ _ hn).2, hs⟩
  let f : CmdId → Nat := fun x => (x.cl.toInt.toNat - 1) * 2 ^ 25 + x.seq.toNat
  have hf : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y := by
    intro x hx y hy he
    obtain ⟨hx1, hx2, hx3⟩ := hb x hx
    obtain ⟨hy1, hy2, hy3⟩ := hb y hy
    simp only [f] at he
    have h1 : x.cl.toInt.toNat = y.cl.toInt.toNat := by
      have := Nat.div_add_mod' ((x.cl.toInt.toNat - 1) * 2 ^ 25 + x.seq.toNat) (2 ^ 25)
      omega
    have h2 : x.seq.toNat = y.seq.toNat := by omega
    have hcl : x.cl = y.cl := BitVec.toInt_inj.mp (by omega)
    have hseq : x.seq = y.seq := BitVec.eq_of_toNat_eq h2
    cases x; cases y; simp_all
  have key : ∀ l' : List CmdId, l' ⊆ l → l'.Nodup → (l'.map f).Nodup := by
    intro l' hsub hn
    induction l' with
    | nil => simp
    | cons a t ih =>
      rw [List.map_cons, List.nodup_cons]
      have hn' := List.nodup_cons.mp hn
      refine ⟨fun hm => ?_, ih (fun z hz => hsub (List.mem_cons_of_mem _ hz)) hn'.2⟩
      obtain ⟨y, hy, he⟩ := List.mem_map.mp hm
      have := hf y (hsub (List.mem_cons_of_mem _ hy)) a (hsub (List.mem_cons_self ..)) he
      subst this; exact hn'.1 hy
  have hnd' : (l.map f).Nodup := key l (fun _ h => h) hnd
  have hsub : l.map f ⊆ List.range (6 * 2 ^ 25) := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hn
    obtain ⟨hx1, hx2, hx3⟩ := hb x hx
    rw [List.mem_range]
    simp only [f]
    have : x.cl.toInt.toNat - 1 ≤ 5 := by omega
    have := Nat.mul_le_mul_right (2 ^ 25) this
    omega
  have := (List.subperm_of_subset hnd' hsub).length_le
  simpa using this

/-- A report's entries are distinct (its ids: the base's order, then the replica's own
commands after it). -/
theorem rep_ids_nodup {S : PState} {N : Nat} {fr : Bool} (HI : S.PInv N fr) {r b' : Nat}
    {R : Report} (h : S.repOk N r b' R) : (R.entries.map (·.id)).Nodup := by
  obtain ⟨-, -, -, -, -, -, -, ⟨B, hB, he⟩, -⟩ := PState.repOk_parts h
  rw [he]
  have hbase : (S.base R.cbal).Nodup := by
    unfold PState.base
    cases hs : S.sync R.cbal with
    | none => simp
    | some M => simp only [Option.map_some, Option.getD_some]; unfold syncOrder; exact PState.recOrder_nodup _ _
  have hloc := (HI.loc_ok r R.cbal).1
  rw [List.nodup_append]
  refine ⟨hB.nodup_iff.mpr hbase, (List.drop_sublist _ _).nodup hloc, ?_⟩
  intro x hx y hy hxy
  subst hxy
  have hxb := hB.mem_iff.mp hx
  by_cases hl : S.loc r R.cbal = []
  · rw [hl] at hy; simp at hy
  · have hc0 : R.cbal > 0 := by
      rcases Nat.eq_zero_or_pos R.cbal with h0 | h0
      · exfalso
        unfold PState.base at hxb
        have : S.sync 0 = none := by
          cases hs : S.sync 0 with
          | none => rfl
          | some M => exact absurd (HI.sync_ok 0 M hs).1 (by omega)
        rw [h0, this] at hxb; simp at hxb
      · exact h0
    obtain ⟨t, ht⟩ := ((HI.loc_ok r R.cbal).2.2 hl).2.2 hc0 |>.2
    have hnd := hloc
    rw [← ht] at hnd hy
    rw [List.drop_left] at hy
    exact (List.nodup_append.mp hnd).2.2 x hxb x hy rfl

theorem flatMap_len_le {α β : Type} (l : List α) (f : α → List β) (K : Nat)
    (h : ∀ a ∈ l, (f a).length ≤ K) : (l.flatMap f).length ≤ l.length * K := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have := h a List.mem_cons_self
    have := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    omega

end sp

namespace swift

open sp

section ghost
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS]
variable {γ : sp.Names} {γc γm γl : GName}

/-- The reports' commands are registered (round 18, sv-swc; for `swift.syncFits`): any list of
distinct reported ids has at most `6 · 2^25` entries (D13, `sp.cmds_len`), and every reported
command's value is shorter than `2^16` (`Cmd.wf`, the registrations' fact behind `sp.cmdIs_wf`,
C20). -/
def RepsReg (reps : List (Nat × Report)) : Prop :=
  (∀ l : List CmdId, l.Nodup → (∀ x ∈ l, ∃ a ∈ reps, ∃ e ∈ a.2.entries, e.id = x) →
    l.length ≤ 6 * 2 ^ 25) ∧
  (∀ a ∈ reps, ∀ e ∈ a.2.entries, e.cmd.val.length < 2 ^ 16)

/-- **`RepsOk` from the reports' facts**: a majority's `reported` facts for ballot `b'`
(an `int32`), the configuration (`N ≤ 7`), and the reports' total size (GAP (M-c)); and
(round 18) `RepsReg`. -/
theorem repsOk_inv2 (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (b' : Nat) (reps : List (Nat × Report)) (hmaj : isMajority N (reps.map Prod.fst))
    (hN : 1 ≤ N ∧ N ≤ 7) (hb : b' < 2 ^ 31) :
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗ ([∗list] p ∈ reps, sp.reported γ p.1 b' p.2) ⊢
      |={E}=> ⌜swift.RepsOk N reps ∧ RepsReg reps⌝ := by
  unfold sp.inv
  iintro ⟨#Hinv, #Hcfg, #Hreps⟩
  iinv Hinv with Hi Hclose
  unfold sp.invBody
  icases Hi with ⟨%S, %mC, %mL, %mS, %mA, %mP, %mCo, %mR, %mN, %sh, %mD, %mQ, %mK, %mPa, HC, HL, HS, HA, HP, HCo, >HRp, HN, HH, HD, Hown, HQ, HK, HPa, >%Hrepr, Hnodes, Hproto, HQs, >%Hcl, >%Hdom, Hslots, Hconns⟩
  ihave %Hlk := sp.reported_lookups (γ := γ) b' reps mR $$ [HRp Hreps]
  · iframe HRp Hreps
  have hrep : ∀ p ∈ reps, S.rep p.1 b' = some p.2 := fun p hp => by
    rw [← Hrepr.rep]; exact Hlk p hp
  icases Hproto with (>%Hemp | ⟨%N', %fr', %l', >#Hcfg', >%HP⟩)
  · -- nothing happened yet: no report
    have hne := (swift.majority_facts hmaj hN.1).1
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil reps hne
    exact absurd ((Hemp.1.2.2.2.2.2.2.1 p.1 b').symm.trans (hrep p hp)) (by simp)
  · ihave %HNN := sp.cfg_agree (γc := γc) (γm := γm) N N' fr fr' l l' $$ [Hcfg Hcfg']
    · isplitl []
      · iexact Hcfg
      · iexact Hcfg'
    obtain ⟨rfl, rfl, rfl⟩ := HNN
    have HI := HP.1
    have hok : ∀ a ∈ reps, a.2.cbal < 2 ^ 31 ∧ ∀ e ∈ a.2.entries,
        e.phase.toNat ≤ 3 ∧ (e.cmd.isPut ∨ e.cmd.isGet) ∧ (e.phase.toNat = 1 → e.dep.Nodup) := by
      intro a ha
      have hro := sp.PState.repOk_parts (HI.rep_ok a.1 b' a.2 (hrep a ha))
      refine ⟨by have := hro.2.1; omega, fun e he => ?_⟩
      have hent := hro.2.2.2.2.2.2.2.2 e he
      refine ⟨hent.2.2.1, ?_, sp.entry_dep_nodup HI hent⟩
      have hc : mC.lookup e.id = some e.cmd := by rw [Hrepr.cmds]; exact hent.1
      exact (Hcl e.id e.cmd hc).2.1
    have hsize : (reps.flatMap (·.2.entries)).length < 2 ^ 31 := by
      have hlen := (swift.majority_facts hmaj hN.1).2.2.1
      have h1 := sp.flatMap_len_le reps (·.2.entries) (6 * 2 ^ 25) (fun a ha => by
        have hro := HI.rep_ok a.1 b' a.2 (hrep a ha)
        have := sp.cmds_len Hrepr.cmds Hcl Hdom.2 _ (sp.rep_ids_nodup HI hro) (fun x hx => by
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
          rw [((sp.PState.repOk_parts hro).2.2.2.2.2.2.2.2 e he).1]; simp)
        simpa using this)
      have : reps.length * (6 * 2 ^ 25) ≤ 7 * (6 * 2 ^ 25) := Nat.mul_le_mul_right _ (by omega)
      omega
    have hreg : RepsReg reps := by
      refine ⟨fun l' hnd hl => sp.cmds_len Hrepr.cmds Hcl Hdom.2 l' hnd (fun x hx => ?_),
        fun a ha e he => ?_⟩
      · obtain ⟨a, ha, e, he, rfl⟩ := hl x hx
        have hro := sp.PState.repOk_parts (HI.rep_ok a.1 b' a.2 (hrep a ha))
        rw [(hro.2.2.2.2.2.2.2.2 e he).1]; simp
      · have hro := sp.PState.repOk_parts (HI.rep_ok a.1 b' a.2 (hrep a ha))
        have hent := hro.2.2.2.2.2.2.2.2 e he
        have hc : mC.lookup e.id = some e.cmd := by rw [Hrepr.cmds]; exact hent.1
        exact (Hcl e.id e.cmd hc).2.2.2.1
    imod Hclose $$ [HC HL HS HA HP HCo HRp HN HH HD Hown HQ HK HPa Hnodes HQs Hslots Hconns] with -
    · inext
      iexists S, mC, mL, mS, mA, mP, mCo, mR, mN, sh, mD, mQ, mK, mPa
      iframe
      isplitr
      · ipureintro; exact Hrepr
      isplitr
      · iright
        iexists N, fr, l
        isplitr
        · iexact Hcfg
        ipureintro; exact HP
      ipureintro; exact ⟨Hcl, Hdom⟩
    imodintro
    ipureintro
    have hop : ∀ c : sp.Cmd, (c.isPut ∨ c.isGet) → c.op ≠ swift.opSCAN := by
      intro c h
      rcases h with h | h
      · unfold sp.Cmd.isPut sp.opPUT at h; simp at h; rw [h]; decide
      · unfold sp.Cmd.isGet sp.opGET at h; simp at h; rw [h]; decide
    exact ⟨swift.repsOk_of hmaj hN (fun a ha => (hok a ha).1)
      (fun a ha e he => ⟨((hok a ha).2 e he).1, hop _ ((hok a ha).2 e he).2.1,
        ((hok a ha).2 e he).2.2⟩) hsize (fun a ha e he => ((hok a ha).2 e he).2.1), hreg⟩

/-- **`RepsOk` from the reports' facts** (`repsOk_inv2`'s first part). -/
theorem repsOk_inv (E : CoPset) (hE : ↑spN ⊆ E) (N : Nat) (fr : Bool) (l : List GoString)
    (b' : Nat) (reps : List (Nat × Report)) (hmaj : isMajority N (reps.map Prod.fst))
    (hN : 1 ≤ N ∧ N ≤ 7) (hb : b' < 2 ^ 31) :
    sp.inv γ γc γm γl ∗ sp.cfg γc γm N fr l ∗ ([∗list] p ∈ reps, sp.reported γ p.1 b' p.2) ⊢
      |={E}=> ⌜swift.RepsOk N reps⌝ :=
  (repsOk_inv2 E hE N fr l b' reps hmaj hN hb).trans
    (fupd_mono (BI.pure_mono fun h => h.1))

end ghost

end swift

end Perennial.github_com.imdea_software.swiftpaxos
