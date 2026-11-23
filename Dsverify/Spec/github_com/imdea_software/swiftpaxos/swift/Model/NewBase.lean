/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swift/Model/NewBase.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
L1's protocol fact (notes/prophecy-client.md §6a): a command `z` of a possibly chosen get `x`'s
key that was not before `x` in `x`'s leader order is not before `x`'s last put `w` in any later
`MSync` (`PState.new_base_gen`; LinWitness.lean's `new_base` applies it to a command registered
after `x`'s acceptance).

Proof, by strong induction on the later ballot `b'`; `c` the highest `cballot` of its recovery
(`c ≥ bx`, a reporter of `x`'s quorum acted in `bx`). In the kept graph `z` and `w` (conflicting)
are comparable: a class-0 `z` reaches `w` by the leader's dependency chain (`w` before `z` in
`ord c`: for `c = bx` since `x` is before `z`, for `c > bx` since `w` is in `base c` and, if `z`
is too, by induction); a class-≠0 `z` against a class-0 `w`: rule 4 (`D4`; `w` reaching `z`
would make `z` class 0); both class ≠ 0: rule 3b (`D3b`, both `R[0]`'s entries). `w` is `Ac` (D33: a base
command of `c`, or reached from the safe `x`), and the recovery's order puts an `Ac` command
before what reaches it (`order_root`), so `z` before `w` in the `MSync` means `w` reaches
`z`: for a class-0 `w` then `z` is before `w` in `ord c` (`reach_gd`), against the above; for a
class-≠0 `w` (only when `c = bx`: base commands are class 0) `x`, safe in this recovery
(`safe_cur`, the case `c = b` of `ballot_safety_proof`), reaches its last put `w` (S4), so `z`,
so `z` is before `x` in `ord bx` (S3): excluded.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model

@[expose] public section

noncomputable section

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

/-- A command of a fast or slow quorum of the recovery's ballot `c` that reported: `x` is safe in
the recovery (the case `c = b` of `ballot_safety_proof`, extracted). -/
theorem safe_cur {S : PState} {N : Nat} {fr : Bool} (hI : S.PInv N fr) {b' : Nat}
    {reps : List (Nat × Report)} (hrep : ∀ p ∈ reps, S.rep p.1 b' = some p.2) {x : CmdId}
    {p : Nat × Report} (hpU : p ∈ recU (recAcks reps))
    (hxord : x ∈ S.ord N (recMaxC (recAcks reps)))
    (hpq : (p.1 = leaderOf N (recMaxC (recAcks reps)) ∨ S.acc p.1 (recMaxC (recAcks reps)) x) ∨
      (p.1 ∈ AQ N (recMaxC (recAcks reps)) ∧ S.fastChosen N (recMaxC (recAcks reps)) x))
    (hlx : S.lexec N (recMaxC (recAcks reps)) x) :
    (mkCtx hI hrep).Safe x := by
  let C := mkCtx hI hrep
  show C.Safe x
  by_cases hK : K0ok (leaderOf N (recMaxC (recAcks reps))) (recU (recAcks reps)) x
  · exact C.safe_gd ⟨hK, Or.inr hlx⟩
  · rcases hpq with (h | h) | ⟨hpAQ, hf⟩
    · exact absurd (K0_of_lexec hI hrep hpU h hlx) hK
    · exact absurd (K0_of_acc hI hrep hpU (Or.inl h)) hK
    · -- the fast path: the old leader did not report, R[0] pre-accepted x as every
      -- reporter of the fast quorum did
      have hLU : (recU (recAcks reps)).any (·.1 == leaderOf N (recMaxC (recAcks reps))) = false := by
        cases hany : (recU (recAcks reps)).any (·.1 == leaderOf N (recMaxC (recAcks reps)))
        · rfl
        · exfalso
          obtain ⟨a', ha', hal⟩ := List.any_eq_true.mp hany
          simp at hal
          exact hK (K0_of_lexec hI hrep ha' hal hlx)
      have hpL : p.1 ≠ leaderOf N (recMaxC (recAcks reps)) := by
        intro h
        have : (recU (recAcks reps)).any (·.1 == leaderOf N (recMaxC (recAcks reps))) = true :=
          List.any_eq_true.mpr ⟨p, hpU, by simpa using h⟩
        rw [hLU] at this; simp at this
      have hpR : p ∈ (recU (recAcks reps)).filter (fun a => a.1 ∈ AQ N (recMaxC (recAcks reps))) :=
        List.mem_filter.mpr ⟨hpU, by simp [hpAQ]⟩
      obtain ⟨r0, rs, hR0⟩ : ∃ r0 rs, (recU (recAcks reps)).filter
          (fun a => a.1 ∈ AQ N (recMaxC (recAcks reps))) = r0 :: rs := by
        cases hR : (recU (recAcks reps)).filter (fun a => a.1 ∈ AQ N (recMaxC (recAcks reps))) with
        | nil => rw [hR] at hpR; simp at hpR
        | cons r0 rs => exact ⟨r0, rs, rfl⟩
      obtain ⟨hr0U, hr0AQ, hrsU⟩ := R_sub hI hrep hR0
      have notL : ∀ a ∈ recU (recAcks reps), a.1 ≠ leaderOf N (recMaxC (recAcks reps)) := by
        intro a' ha' h
        have : (recU (recAcks reps)).any (·.1 == leaderOf N (recMaxC (recAcks reps))) = true :=
          List.any_eq_true.mpr ⟨a', ha', by simpa using h⟩
        rw [hLU] at this
        simp at this
      have hf' := hf
      unfold PState.fastChosen at hf'
      obtain ⟨PL, hPL, hall⟩ := hf'
      -- a reporter of R: its entry of x is a pre-acceptance with the leader's dependencies
      have entry_of : ∀ a ∈ recU (recAcks reps), a.1 ∈ AQ N (recMaxC (recAcks reps)) →
          ∃ D, S.pre a.1 (recMaxC (recAcks reps)) x = some D ∧
            D.Perm (depsIn (S.ordSeq N (recMaxC (recAcks reps))) x) ∧
            S.path a.1 (recMaxC (recAcks reps)) x = some PL ∧
            ∃ e ∈ a.2.entries, e.id = x ∧ e.phase.toNat = 1 ∧ e.dep = D := by
        intro a' ha' haq
        obtain ⟨D, hD, hDp, hpth⟩ := hall a'.1 haq (notL a' ha')
        obtain ⟨hc', hrok'⟩ := U_rep hI hrep ha'
        obtain ⟨-, -, -, -, -, hpre', -, -, hent'⟩ := PState.repOk_parts hrok'
        rw [hc'] at hpre'
        obtain ⟨e, he, hid, hph⟩ := hpre' x D hD
        refine ⟨D, hD, hDp, hpth, e, he, hid, ?_⟩
        rcases hph with hph | hph
        · exfalso; apply hK
          have := (hent' e he).2.2.1
          exact ⟨a', ha', e, he, hid, by unfold okPhase; simp; omega⟩
        · exact hph
      obtain ⟨D0, hD0, hD0p, hpth0, e0, he0, he0id, he0ph, he0dep⟩ := entry_of r0 hr0U hr0AQ
      obtain ⟨hnd0, -⟩ := R0_facts hI hrep hr0U
      -- rule 2 keeps x
      have hk1 : (C.k1.get x) = none := by
        have := ((rule1_spec C.oldL C.U).2.2 x)
        cases h' : C.k1.get x with
        | none => rfl
        | some _ =>
          exfalso; apply hK
          have h'' : (C.k1.get x).isSome := by rw [h']; rfl
          rw [show C.k1 = rule1 C.oldL C.U from C.h1] at h''
          exact this.mp h''
      have hall2 : rs.all (fun a => a.2.entries.any (fun e' =>
          e'.id == e0.id && e'.phase.toNat == 1 && depEq e0.dep e'.dep)) = true := by
        rw [List.all_eq_true]; intro a' ha'
        obtain ⟨ha'U, ha'AQ⟩ := hrsU a' ha'
        obtain ⟨D, -, hDp, -, e', he', he'id, he'ph, he'dep⟩ := entry_of a' ha'U ha'AQ
        rw [List.any_eq_true]
        refine ⟨e', he', ?_⟩
        simp only [Bool.and_eq_true, beq_iff_eq]
        refine ⟨⟨he'id.trans he0id.symm, he'ph⟩, ?_⟩
        unfold depEq; rw [List.isPerm_iff, he0dep, he'dep]
        exact hD0p.trans hDp.symm
      have hS1 : Struct C.oldL C.U C.leaderInU C.R C.acks C.k1 := by
        have := Struct_rule1 C.oldL C.U C.leaderInU C.R C.acks; rw [← C.h1] at this; exact this
      obtain ⟨-, -, hkeep⟩ := rule2_spec C.oldL C.U C.leaderInU C.R C.acks C.k1 hS1
      have hk2 : (C.k2.get x).isSome := by
        rw [C.h2]
        have := hkeep hLU r0 rs hR0 e0 he0 he0ph (by rw [he0id]; exact hk1) hall2
        rw [he0id] at this; exact this
      have hkept : (C.k4.get x).isSome :=
        (C.graph.1.keys x).mpr (C.graph.2.2.2 x hk2)
      have hpx : ∃ px, recPos r0 x = some px := by
        obtain ⟨px, h'⟩ := Ctx.recPos_of_mem he0; rw [he0id] at h'; exact ⟨px, h'⟩
      obtain ⟨px, hpx⟩ := hpx
      refine C.safe_fast hLU hR0 hK hkept hxord ?_ ?_ ?_
      · intro e he hid
        have : e = e0 := nodup_map_eq (·.id) _ hnd0 e e0 he he0 (hid.trans he0id.symm)
        subst this; rw [he0dep]; exact hD0p
      · intro z pz px' hz hx' hlt hkey
        have hpLx := hPL
        exact F2_fast hI hrep hr0U hK (hI.pre_ok _ _ _ _ hD0).2.2.1 hpth0 hpLx hz hx' hlt hkey
      · intro cx p' hcx hg hp' z pz px' hzK hz hx' hlt hput hne
        exact F3_fast hI hrep hr0U hK hxord hD0 hD0p hcx hg hp' hzK hz hx' hlt hput hne

namespace Ctx
variable {S : PState} {N : Nat} {reps : List (Nat × Report)} (C : Ctx S N reps)

/-- A command of the `MSync` is kept. -/
theorem sync_kept {y : CmdId} (h : y ∈ syncOrder (recoverSync N reps)) : (C.k4.get y).isSome := by
  obtain ⟨hmemO, hndO⟩ := C.order_mem
  let order := recOrder C.k4 C.ids
  have hreg : ∀ y ∈ order, S.cmds y ≠ none := by
    intro y hy; obtain ⟨re, hre⟩ := Option.isSome_iff_exists.mp ((hmemO y).mp hy)
    rw [C.cmd_k4 hre]; simp
  have hcsfst : (S.seqOf order).map Prod.fst = order := seqOf_fst order hreg
  have hcsnd : ((S.seqOf order).map Prod.fst).Nodup := by rw [hcsfst]; exact hndO
  obtain ⟨hmS, -, -⟩ := syncOrder_lkAlong (S.seqOf order) hcsnd
  rw [C.sync_eq, C.cs_eq] at h
  rw [hcsfst] at hmS
  exact (hmemO y).mp ((hmS y).mp h)

/-- A conflicting command reaching an `Ac` command `y` is not before `y` in the `MSync`. -/
theorem sync_reach {y z : CmdId} {cy cz : Cmd} (hcy : S.cmds y = some cy) (hcz : S.cmds z = some cz)
    (hconf : Cmd.conflict cy cz = true) (hr : Reach C.k4 z y) (hyAc : C.Ac y) :
    ¬ precedes (syncOrder (recoverSync N reps)) z y := by
  intro hzy
  obtain ⟨hmemO, hndO⟩ := C.order_mem
  let order := recOrder C.k4 C.ids
  have hreg : ∀ y ∈ order, S.cmds y ≠ none := by
    intro y hy; obtain ⟨re, hre⟩ := Option.isSome_iff_exists.mp ((hmemO y).mp hy)
    rw [C.cmd_k4 hre]; simp
  have hcsfst : (S.seqOf order).map Prod.fst = order := seqOf_fst order hreg
  have hcsnd : ((S.seqOf order).map Prod.fst).Nodup := by rw [hcsfst]; exact hndO
  have hzk := C.sync_kept (precedes_mem _ _ _ hzy)
  have hyk := C.reach_kept hr
  obtain ⟨hmS, -, hpairs⟩ := syncOrder_lkAlong (S.seqOf order) hcsnd
  rw [C.sync_eq, C.cs_eq] at hzy
  rw [hcsfst] at hmS hpairs
  have hne : z ≠ y := fun h => precedes_irrefl _ _ (h ▸ hzy)
  obtain ⟨hk, hput⟩ := (conflict_iff cz cy).mp (by rw [conflict_symm]; exact hconf)
  have hzo := (hpairs z y cz cy (List.mem_filterMap.mpr ⟨z, (hmemO z).mpr hzk, by simp [hcz]⟩)
    (List.mem_filterMap.mpr ⟨y, (hmemO y).mpr hyk, by simp [hcy]⟩) hne hk hput).mp hzy
  exact precedes_antisymm _ _ _ hzo ((C.order_root hyAc hyk).2 z hr hzk)

end Ctx

namespace PState
variable {S : PState} {N : Nat} {fr : Bool}

/-- **L1's protocol fact**: a command `z` of a possibly chosen get `x`'s key, not before `x` in
`x`'s leader order, is not before `x`'s last put `w` in a later `MSync`. -/
theorem new_base_gen (hI : S.PInv N fr) : ∀ (b' : Nat) {bx : Nat} {x w z : CmdId} {cx cz : Cmd},
    bx < b' → S.sync b' ≠ none → S.possiblyChosen N bx x → S.cmds x = some cx →
    cx.isGet = true → S.LastPut (S.ord N bx) x cx.key (some w) → S.cmds z = some cz →
    cz.key = cx.key → z ≠ x → ¬ precedes (S.ord N bx) z x → ¬ precedes (S.base b') z w := by
  intro b'
  induction b' using Nat.strongRecOn with
  | ind b' IH =>
  intro bx x w z cx cz hb hs hx hcx hg hw hcz hk hzx0 hzx hzw
  have hwb' := (ballot_safety_lastPut hI hb hs hx hcx hg hw).1
  obtain ⟨M, hM⟩ := Option.ne_none_iff_exists'.mp hs
  obtain ⟨hb'0, -, hbord, reps, hmaj, hrep, hMeq⟩ := hI.sync_ok b' M hM
  have hbase : S.base b' = syncOrder (recoverSync N reps) := by
    unfold PState.base; rw [hM, hMeq]; rfl
  rw [hbase] at hzw hwb'
  let C := mkCtx hI hrep
  have hxord := hx.1
  have hchosen := hx.2.1
  have hN : 0 < N := by
    obtain ⟨-, hlt, hlen⟩ := hmaj
    cases hr : reps.map Prod.fst with
    | nil => rw [hr] at hlen; simp at hlen
    | cons r _ => have := hlt r (by rw [hr]; simp); omega
  -- a reporter in x's quorum, which acted in bx
  obtain ⟨p, hp, hpq⟩ : ∃ p ∈ reps, (p.1 = leaderOf N bx ∨ S.acc p.1 bx x) ∨
      (p.1 ∈ AQ N bx ∧ S.fastChosen N bx x) := by
    rcases hchosen with ⟨Q, hQ, hQall⟩ | hfast
    · obtain ⟨r, hr1, hr2⟩ := majority_meet N _ Q hmaj hQ
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr1
      exact ⟨p, hp, Or.inl (hQall _ hr2)⟩
    · obtain ⟨r, hr1, hr2⟩ := majority_meet N _ _ hmaj (AQ_majority N bx hN).1
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr1
      exact ⟨p, hp, Or.inr ⟨hr2, hfast⟩⟩
  have hacted : x ∈ S.loc p.1 bx := by
    rcases hpq with (h | h) | ⟨h, hf⟩
    · rw [h]; exact hxord
    · exact (hI.acc_ok _ _ _ h).2.1
    · unfold PState.fastChosen at hf
      obtain ⟨PL, -, hall⟩ := hf
      by_cases hL : p.1 = leaderOf N bx
      · rw [hL]; exact hxord
      · obtain ⟨D, hD, -⟩ := hall p.1 h hL
        exact (hI.pre_ok _ _ _ _ hD).2.2.1
  have hprok := hI.rep_ok p.1 b' p.2 (hrep p hp)
  obtain ⟨-, hplt, -, hnone, -⟩ := PState.repOk_parts hprok
  have hpc : bx ≤ p.2.cbal := by
    apply Classical.byContradiction; intro h
    have := (hnone bx x (by omega) hb).2.2.2
    rw [this] at hacted; simp at hacted
  have hcmax := cbal_le_max _ p (acks_mem hp)
  obtain ⟨a, ha, hac⟩ := max_attained (recAcks reps) (by
    intro h; have := acks_mem hp; rw [h] at this; simp at this)
  have haU : a ∈ recU (recAcks reps) := U_of_max ha hac
  obtain ⟨-, harok⟩ := U_rep hI hrep haU
  obtain ⟨-, halt, habase, -⟩ := PState.repOk_parts harok
  rw [hac] at halt habase
  -- w, z: conflicting, kept; z does not reach w
  obtain ⟨cw, hcw, hkw, hpw⟩ := hw.2.1
  have hzw_ne : z ≠ w := fun h => precedes_irrefl _ _ (h ▸ hzw)
  have hconf : Cmd.conflict cw cz = true := by
    rw [Ctx.conflict_iff]; exact ⟨hkw.trans hk.symm, Or.inl hpw⟩
  -- w's kept closure is acyclic (D33): a base command of `c`, or reached from the safe `x`
  have hwAc : C.Ac w := by
    by_cases hbc : bx < recMaxC (recAcks reps)
    · obtain ⟨Mc, hMc, -⟩ := habase (by omega)
      have hwB := precedes_mem _ _ _
        (ballot_safety_lastPut hI hbc (by rw [hMc]; simp) hx hcx hg hw).1
      exact Or.inl ⟨K0_of_base hI hrep haU hwB, Or.inr (PState.lexec_of_base hwB)⟩
    · have hbc' : recMaxC (recAcks reps) = bx := by omega
      have hpU : p ∈ recU (recAcks reps) := U_of_max (acks_mem hp) (by omega)
      have hsafe : C.Safe x := safe_cur hI hrep hpU (by rw [hbc']; exact hxord)
        (by rw [hbc']; exact hpq) (by rw [hbc']; exact hx.2.2)
      have hw' : S.LastPut C.ord x cx.key (some w) := by
        change S.LastPut (S.ord N (recMaxC (recAcks reps))) x cx.key (some w); rw [hbc']; exact hw
      exact (C.reach_phi (hsafe.s4 cx w hcx hg hw').1 hsafe.ac).2
  have hnot : ¬ Reach C.k4 z w := fun hr => C.sync_reach hcw hcz hconf hr hwAc hzw
  have hzk := C.sync_kept (precedes_mem _ _ _ hzw)
  have hwk := C.sync_kept (precedes_mem _ _ _ hwb')
  -- in the recovery's leader order, w is before z
  have hwz : z ∈ C.ord → precedes C.ord w z := by
    intro hzo
    change z ∈ S.ord N (recMaxC (recAcks reps)) at hzo
    change precedes (S.ord N (recMaxC (recAcks reps))) w z
    by_cases hbc : bx < recMaxC (recAcks reps)
    · obtain ⟨Mc, hMc, -⟩ := habase (by omega)
      have hsc : S.sync (recMaxC (recAcks reps)) ≠ none := by rw [hMc]; simp
      have hwB : w ∈ S.base (recMaxC (recAcks reps)) :=
        precedes_mem _ _ _ (ballot_safety_lastPut hI hbc hsc hx hcx hg hw).1
      obtain ⟨T, hT⟩ := base_prefix_ord hI (recMaxC (recAcks reps))
      rw [← hT] at hzo ⊢
      by_cases hzB : z ∈ S.base (recMaxC (recAcks reps))
      · have h1 := IH _ halt hbc hsc hx hcx hg hw hcz hk hzx0 hzx
        rcases precedes_total _ w z hwB hzB hzw_ne.symm with h | h
        · exact (Ctx.precedes_append_of_mem _ T w z hzB).mpr h
        · exact absurd h h1
      · exact (precedes_append_not _ T w z hzB).mpr (Or.inl hwB)
    · have hcb : recMaxC (recAcks reps) = bx := by omega
      rw [hcb] at hzo ⊢
      rcases precedes_total _ x z hxord hzo hzx0.symm with h | h
      · exact precedes_trans _ _ _ _ hw.1 h
      · exact absurd h hzx
  have G := C.graph.1
  by_cases hzK : K0ok C.oldL C.U z
  · rcases hwAc with hwG | hl
    · apply hnot
      have hzo := C.K0ok_ord hzK
      obtain ⟨s1, s2, s3, hs'⟩ := seqOf_split S C.ord C.ordNd w z cw cz hcw hcz hzo (hwz hzo)
      obtain ⟨hk', hput'⟩ := (Ctx.conflict_iff cw cz).mp hconf
      exact C.chain_in hwG s2.length s1 s2 s3 (w, cw) (z, cz) rfl hs' rfl hk' hput' hzk
    · exact hnot (C.chain_gd (C.gall hl z hzK) hcw hcz hconf (hwz (C.K0ok_ord hzK)))
  obtain ⟨rez, hrez⟩ := Option.isSome_iff_exists.mp hzk
  obtain ⟨rew, hrew⟩ := Option.isSome_iff_exists.mp hwk
  have hzc := C.cmd_k4 hrez
  have hwc := C.cmd_k4 hrew
  rw [hcz] at hzc; cases hzc
  rw [hcw] at hwc; cases hwc
  obtain ⟨rez3b, rez3, hz3b, hz3, hz3bc, hz3c, hz3bm, hz3m⟩ := C.entries3 hrez
  obtain ⟨rew3b, rew3, hw3b, hw3, hw3bc, hw3c, hw3bm, hw3m⟩ := C.entries3 hrew
  by_cases hwK : K0ok C.oldL C.U w
  · have h4 := G.d4 z w (by rw [hz3b]; rfl) (by rw [hw3b]; rfl) rew3b rez3b hw3b hz3b
      (fun h => hzK ((C.cls_k3b hz3b).mp h)) ((C.cls_k3b hw3b).mpr hwK)
      (by rw [hw3bm, hz3bm]; exact hconf)
    rcases h4 with h | h
    · exact hnot h
    · exact hzK (C.gK0 _ (C.reach_gd h (C.gd_of_ac hwAc hwK)).1)
  -- both of class ≠ 0: R[0]'s entries (the old leader did not report), rule 3b
  have hl : C.leaderInU = false := by
    rcases hwAc with h | h
    · exact absurd (C.gK0 w h) hwK
    · exact h
  obtain ⟨hzc0, hnz⟩ := G.nk0 z rez hrez hzK
  obtain ⟨r0, rs, hR0, ez, hez, hezid, -, -⟩ := hnz hl
  obtain ⟨hwc0, hnw⟩ := G.nk0 w rew hrew hwK
  obtain ⟨r0', rs', hR0', ew, hew, hewid, -, -⟩ := hnw hl
  rw [hR0] at hR0'; simp at hR0'; obtain ⟨rfl, rfl⟩ := hR0'
  obtain ⟨pz, hpz⟩ := Ctx.recPos_of_mem hez; rw [hezid] at hpz
  obtain ⟨pw, hpw'⟩ := Ctx.recPos_of_mem hew; rw [hewid] at hpw'
  have hcmp : Reach C.k4 z w ∨ Reach C.k4 w z := by
    rcases Nat.lt_or_ge pz pw with hlt | hge
    · rcases G.d3b hl r0 rs hR0 w z (by rw [hw3]; rfl) rez3 rew3 pw pz hz3 hw3
        (by rw [hw3c]; exact hwc0) hpw' hpz (by omega) hzw_ne
        (by rw [hz3m, hw3m, Ctx.conflict_symm]; exact hconf) with h | h
      · exact Or.inr h
      · exact Or.inl h
    · exact G.d3b hl r0 rs hR0 z w (by rw [hz3]; rfl) rew3 rez3 pz pw hw3 hz3
        (by rw [hz3c]; exact hzc0) hpz hpw' hge hzw_ne.symm
        (by rw [hz3m, hw3m]; exact hconf)
  rcases hcmp with h | h
  · exact hnot h
  -- `w` reaches `z`: only when c = bx (base commands are class 0); then x is safe
  have hbc : recMaxC (recAcks reps) = bx := by
    apply Classical.byContradiction; intro hne
    have hbc : bx < recMaxC (recAcks reps) := by omega
    obtain ⟨Mc, hMc, -⟩ := habase (by omega)
    have hwB := precedes_mem _ _ _
      (ballot_safety_lastPut hI hbc (by rw [hMc]; simp) hx hcx hg hw).1
    exact hwK (K0_of_base hI hrep haU hwB)
  have hpU : p ∈ recU (recAcks reps) := U_of_max (acks_mem hp) (by omega)
  have hsafe : C.Safe x := safe_cur hI hrep hpU (by rw [hbc]; exact hxord) (by rw [hbc]; exact hpq)
    (by rw [hbc]; exact hx.2.2)
  have hw' : S.LastPut C.ord x cx.key (some w) := by
    change S.LastPut (S.ord N (recMaxC (recAcks reps))) x cx.key (some w); rw [hbc]; exact hw
  obtain ⟨hxw, -⟩ := hsafe.s4 cx w hcx hg hw'
  have hzx' := hsafe.s3 z (Relation.TransGen.trans hxw h)
  change precedes (S.ord N (recMaxC (recAcks reps))) z x at hzx'
  rw [hbc] at hzx'
  exact hzx hzx'

end PState

end sp

end Perennial.github_com.imdea_software.swiftpaxos

end
