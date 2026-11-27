/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: the initial state (#33 S4, the invariant phase)

`antSim_init` (`Stmts.lean`): `Init0` (B 755-764) is the model's `Init` (R 181-201) or, bootstrapped,
`BootInit` (B 733-753): every node at term 0 (or 1), no vote, an empty log (or the boot entry),
follower, nothing recorded (or `raft1` the leader of term 1 with the boot log); the run's fresh nodes
(`FreshView`) are related to it, and its facts are certified by any `G` with the run's boot facts.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.GC

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck

open GMap

section init
variable [GooseExts]

/-- The boot term (`BootTerm`, B 96). -/
def bootT (R : RunCfg) : Int := if R.boot then 1 else 0

/-- `Init0 R.cfg`'s state. -/
def initS (R : RunCfg) : State :=
  let n := R.cfg.server.length
  { cfg := R.cfg, currentTerm := List.replicate n (bootT R), voteTerm := List.replicate n (bootT R),
    voteFor := List.replicate n (if R.boot then nameOf (W64 1) else []),
    log := List.replicate n (logOf (bootLog R)),
    commitIndex := List.replicate n 0, role := List.replicate n follower,
    lastApplied := List.replicate n 0, config := List.replicate n R.cfg.initConf,
    confAt := List.replicate n 0,
    confirmed := List.replicate n (if R.boot then { term := 1, index := 1 } else {}),
    msgs := [], votes := [],
    leaders := if R.boot then [{ server := nameOf (W64 1), term := 1 }] else [],
    ledLog := if R.boot then [(1, logOf (bootLog R))] else [],
    ledConf := if R.boot then [(1, R.cfg.initConf)] else [],
    ledAt := if R.boot then [(1, 0)] else [], elAt := if R.boot then [(1, 0)] else [],
    i := 1, undo := List.replicate n none, pending := List.replicate n [],
    queue := List.replicate n [], reads := List.replicate n [], chain := [], termLen := [],
    viol := [] }

theorem initS_ledLog (R : RunCfg) :
    (initS R).ledLog = if R.boot then [((1 : Int), logOf (bootLog R))] else [] := rfl
theorem initS_ledAt (R : RunCfg) : (initS R).ledAt = if R.boot then [((1 : Int), (0 : Int))] else [] := rfl
theorem initS_ledConf (R : RunCfg) :
    (initS R).ledConf = if R.boot then [((1 : Int), R.cfg.initConf)] else [] := rfl
theorem initS_leaders (R : RunCfg) :
    (initS R).leaders = if R.boot then [({ server := nameOf (W64 1), term := 1 } : LeaderRec)] else [] := rfl

theorem RunCfg.initVoters_eq (R : RunCfg) : R.cfg.initVoters = namesL R.K :=
  setOf_namesL (by have := R.hK; omega)

theorem namesL_succ (k : Nat) : namesL (k + 1) = nameOf (W64 1) :: (List.range k).map
    (fun (i : Nat) => nameOf (W64 (((i + 1 : Nat) : Int) + 1))) := by
  simp [namesL, List.range_succ_eq_map, List.map_map, Function.comp_def]

theorem logOf_bootLog (R : RunCfg) :
    logOf (bootLog R) = if R.boot then [{ term := 1, type := go!"config", value := { str := [] } }] else [] := by
  unfold bootLog; cases R.boot <;> simp [logOf, entOf, bootEnt]; rfl

theorem init0_R (R : RunCfg) : init0 R.cfg = .ok (initS R) := by
  unfold init0
  cases hb : R.boot
  · simp only [RunCfg.cfg, hb, Bool.not_false, ite_true]
    simp [initS, bootT, logOf_bootLog, hb, RunCfg.cfg]; rfl
  · have hK := R.hK.1
    obtain ⟨k, hk⟩ : ∃ k, R.K = k + 1 := ⟨R.K - 1, by omega⟩
    have hv := R.initVoters_eq; rw [hk, namesL_succ] at hv
    simp only [show R.cfg.bootstrapped = true from hb, Bool.not_true]
    rw [hv]
    simp [initS, bootT, logOf_bootLog, hb]; rfl

theorem rep_length {R : RunCfg} {α : Type} (x : α) : (List.replicate R.cfg.server.length x).length = R.N := by
  rw [List.length_replicate, R.server_eq, namesL_length]

theorem rep_get {R : RunCfg} {α : Type} [Inhabited α] (x : α) (n : Fin R.N) :
    (List.replicate R.cfg.server.length x)[n.val]! = x := by
  rw [R.server_eq, namesL_length]
  simp [List.getElem!_eq_getElem?_getD, n.isLt]

theorem nameOf_zero : nameOf (W64 0) = [] := by unfold nameOf; simp

theorem nodeId_ne_zero {R : RunCfg} (n : Fin R.N) : nodeId n ≠ W64 0 := by
  have := R.hK.2.2; have := n.isLt
  intro h; unfold nodeId at h
  have h2 := congrArg (fun w : w64 => w.toNat) h
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt] at h2
  omega

theorem prefix_init (R : RunCfg) : Prefix R.cfg [] (initS R) :=
  ⟨{ state := initS R }, by rw [init0_R]; rfl, rfl, rfl⟩

theorem small_inj {i j : Nat} (hi : i < 9) (hj : j < 9) (h : W64 ((i : Int) + 1) = W64 ((j : Int) + 1)) :
    i = j := by
  have h2 := congrArg (fun w : w64 => w.toNat) h
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt] at h2
  omega

theorem mem_voters0 (R : RunCfg) {i : Nat} (hi : i < R.N) :
    W64 ((i : Int) + 1) ∈ R.voters0 ↔ i < R.K := by
  have := R.hK
  unfold RunCfg.voters0
  rw [elem_of_list_to_set, List.mem_map]
  constructor
  · rintro ⟨a, ha, he⟩
    rw [List.mem_range] at ha
    have := small_inj (by omega) (by omega) he; omega
  · intro h; exact ⟨i, List.mem_range.mpr h, rfl⟩

theorem idsView_voters0 (R : RunCfg) : idsView R.N R.voters0 = R.cfg.initVoters := by
  rw [R.initVoters_eq, ← setOf_namesL (N := R.K) (by have := R.hK; omega)]
  unfold idsView; congr 1
  have key : ∀ m, m ≤ R.N → (List.range m).filterMap (fun (i : Nat) =>
      if W64 ((i : Int) + 1) ∈ R.voters0 then some (nameOf (W64 ((i : Int) + 1))) else none) =
      namesL (min m R.K) := by
    intro m; induction m with
    | zero => intro _; simp [namesL]
    | succ m ih =>
      intro hm
      rw [List.range_succ, List.filterMap_append, ih (by omega)]
      simp only [List.filterMap_cons, List.filterMap_nil]
      by_cases hk : m < R.K
      · rw [if_pos ((mem_voters0 R (by omega)).mpr hk), show min (m + 1) R.K = min m R.K + 1 by omega,
          show min m R.K = m by omega]
        simp [namesL, List.range_succ]
      · rw [if_neg (fun h => hk ((mem_voters0 R (by omega)).mp h)), show min (m + 1) R.K = min m R.K by omega]
        simp
  rw [key R.N (Nat.le_refl _), show min R.N R.K = R.K by have := R.hK; omega]

theorem idsView_empty (N : Nat) : idsView N ∅ = [] := by
  unfold idsView
  have : (List.range N).filterMap (fun (i : Nat) =>
      if W64 ((i : Int) + 1) ∈ (∅ : GSet w64) then some (nameOf (W64 ((i : Int) + 1))) else none) = [] := by
    rw [List.filterMap_eq_nil_iff]; intro a _; simp [not_elem_of_empty]
  rw [this]; rfl

/-- The initial configuration as the binding has it (`Config.initConf`). -/
theorem confView_c0 (R : RunCfg) : confView R.N R.c0 = R.cfg.initConf := by
  unfold confView RunCfg.c0 Config.initConf
  simp only [CfgM.simple]
  rw [idsView_voters0, idsView_empty]

/-- **The initial state** (B 755-764). -/
theorem antSim_init : antSim_init.stmt := by
  intro R dec V hV
  have hbt : (initS R).bootTerm = bootT R := rfl
  have hct : ∀ n : Fin R.N, (initS R).currentTerm[n.val]! = bootT R := fun n => rep_get _ n
  have hvt : ∀ n : Fin R.N, (initS R).voteTerm[n.val]! = bootT R := fun n => rep_get _ n
  have hvote : ∀ n : Fin R.N, (initS R).vote n.val = [] := by
    intro n; unfold State.vote State.voteOf; rw [hct, hvt, hbt]; simp
  have hlog : ∀ n : Fin R.N, (initS R).log[n.val]! = logOf (bootLog R) := fun n => rep_get (R := R) _ n
  have hconf : ∀ n : Fin R.N, (initS R).confirmed[n.val]! =
      (if R.boot then { term := 1, index := 1 } else {}) := fun n => rep_get _ n
  refine ⟨initS R, prefix_init R, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact ⟨rfl, rep_length _, rep_length _, rep_length _, rep_length _, rep_length _,
      rep_length _, rep_length _, rep_length _, rep_length _, rep_length _, rep_length _,
      rep_length _, rep_length _, rep_length _⟩
  · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, List.Pairwise.nil,
      ⟨fun n => Int.le_of_eq (by rw [hct, hbt]), fun f hf => by cases hf⟩⟩
    · intro p hp; cases hp
    · intro n
      have h0 : (initS R).commitIndex[n.val]! = 0 := rep_get _ n
      rw [h0]; exact ⟨Int.le_refl _, rfl⟩
    · intro n
      left; exact rep_get _ n
    · intro n l hl
      rw [hconf] at hl ⊢; rw [hlog]
      rw [initS_ledLog] at hl
      cases hb : R.boot
      · simp only [hb, Bool.false_eq_true, ite_false] at hl; cases hl
      · simp [hb, TermFn.get] at hl
        cases hl; simp [logOf_bootLog, hb]
    · intro n a ha; cases ha
    · intro p hp
      rw [initS_ledLog] at hp
      cases hb : R.boot <;> simp [hb] at hp
      exact ⟨{ server := nameOf (W64 1), term := 1 }, by rw [initS_leaders, hb]; simp, by rw [hp]⟩
    · intro n l hl
      rw [initS_leaders] at hl
      cases hb : R.boot <;> simp [hb] at hl
      intro _; right; refine ⟨by rw [hct, hl]; simp [bootT, hb], ?_⟩
      rw [show (initS R).role[n.val]! = follower from rep_get _ n]; decide
    · intro f hf; cases hf
    · intro v hv; cases hv
    · intro n hv; exact absurd (hvote n) hv
    · intro n a ha; cases ha
    · intro n; rw [hct, hvt]; exact Int.le_refl _
    · intro j
      rw [hct, hconf]
      cases hb : R.boot
      · simp [bootT, hb]
      · refine ⟨.inr (.inl ?_), by simp [bootT, hb]⟩
        rw [initS_ledLog, hb]; simp [TermFn.has]
    · refine ⟨fun T hT => by change 0 < tlOld [] T at hT; simp [tlOld] at hT, fun n hn => ?_⟩
      have hr : (initS R).role[n.val]! = follower := rep_get _ n
      rw [hr] at hn; exact absurd hn (by decide)
    · intro T hT
      rw [initS_ledLog] at hT
      cases hb : R.boot
      · simp [hb, TermFn.has] at hT
      · simp [hb, TermFn.has] at hT; subst hT
        refine ⟨bootLog R, 0, R.c0, ?_, ?_, rfl, ?_,
          fun _ => by unfold bootLog; cases R.boot <;> simp [EntsNormal, bootEnt]⟩
        · rw [initS_ledLog, hb]; simp [TermFn.get]; rfl
        · rw [initS_ledAt, hb]; simp [TermFn.get]; rfl
        · rw [initS_ledConf, hb]; simp [TermFn.get, confView_c0]; rfl
  · unfold NetOk HbCommitOk NetShape LeadCommitMsgOk
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro m hm <;> cases hm
  · intro x hx; cases hx
  · intro n
    obtain ⟨⟨hterm, hvote0, hlead, hrole, _, hout, hbase, hlog0, hcommit, _, _, _, hsnap, hcidx, hcfg, hfp, hrd⟩,
      hdel, hdur, hundo, hmems, hcv, hca, hpre, hreads, _, ⟨hqs, hpend, hxpend, hce, hrp⟩, htold, hcause,
      hxcause⟩ := hV n
    have hpd : (V n).r.p.rd.pend = [] := by rw [hrd]
    have hfull : (V n).r.full = bootLog R := by rw [RState.full, hfp, hlog0]; rfl
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hct, hdur]; simp only [durOf]; rw [hterm]; unfold bootT; cases R.boot <;> rfl
    · rw [hvote n, hdur]; simp only [durOf]; rw [hvote0, nameOf_zero]
    · rw [hlog, hdur]; simp only [durOf]; rw [hfull]
    · rw [hdur]; simp only [durOf]; rw [hcommit]; exact rep_get _ n
    · rw [show (initS R).role[n.val]! = follower from rep_get _ n]
      rw [hrole]; rfl
    · rw [hdel]; exact rep_get (R := R) (0 : Int) n
    · rw [hcv, confView_c0]; exact rep_get _ n
    · rw [hca]; exact rep_get _ n
    · intro _ _ _ _; exact ⟨hmems, hdur, fun h => absurd hundo h⟩
    · refine ⟨?_, ?_⟩
      · rw [hundo]; simp only [Option.isNone_none, iff_true]; rw [show (initS R).undo[n.val]! = none from rep_get (R := R) (none : Option Pre) n]; rfl
      · intro p hp; rw [show (initS R).undo[n.val]! = none from rep_get _ n] at hp; cases hp
    · unfold QueueIs; rw [hmems]; exact rep_get (R := R) _ n
    · refine ⟨?_, ?_⟩
      · rw [hreads, show (initS R).reads[n.val]! = [] from rep_get _ n]; rfl
      · intro k a b ha; rw [show (initS R).reads[n.val]! = [] from rep_get _ n] at ha; cases ha
    · left; refine ⟨by rw [hcv, hcfg], ?_⟩
      rw [hca, hcidx]; rfl
    · refine ⟨hout, fun _ => ⟨hbase, hfp, hsnap⟩, fun _ => ⟨by rw [hcfg]; rfl, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hfull]; unfold bootLog; cases R.boot <;> simp [EntsNormal, bootEnt]
      · rw [hdur]; simp only [durOf]; rw [hfull]; unfold bootLog; cases R.boot <;> simp [EntsNormal, bootEnt]
      · rw [hdur]; simp only [durOf]; rw [hfull]; unfold bootLog
        cases R.boot
        · intro k e he; cases he
        · intro k e he
          match k, he with
          | 0, he => simp at he; subst he; rfl
      · rw [hdel, hce]; exact List.nil_prefix
      · rw [hdel, hce]; exact Nat.zero_le _
      · rw [hpend]; intro q hq; cases hq
      · exact ⟨by rw [hdur]; exact Int.le_refl _, fun _ => hrole, fun _ => ⟨hpd, fun h => (by rw [hrole] at h; cases h)⟩,
          fun h => (by rw [hpre] at h; cases h), fun p hp => (by rw [hpd] at hp; cases hp),
          fun h => (by rw [hrole] at h; cases h),
          fun p hp => (by rw [hpd] at hp; cases hp), fun h => (by rw [hrole] at h; cases h)⟩
    · intro h; rw [hrole] at h; cases h
    · intro h; rw [hrole] at h; cases h
    · rw [hpend]; intro q hq; cases hq
    · rw [hxpend]; intro q hq; cases hq
    · rw [hqs]; intro q hq; cases hq
    · rw [htold]; intro h; cases h
    · rw [hcause]; intro m h; cases h
    · rw [hxcause]; intro m h; cases h
    · exact ⟨fun _ => by rw [hlead]; exact (nodeId_ne_zero n).symm, .inl hlead⟩
    · intro h; rw [hrole] at h; exact absurd rfl h
  · intro G hG
    have hG1 := hG.1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hG⟩
    · intro l hl
      rw [initS_leaders] at hl
      cases hb : R.boot <;> simp [hb] at hl
      subst hl; exact .inl ⟨rfl, rfl, rfl⟩
    · intro v hv; cases hv
    · intro n; exact ⟨bootLog R, hG1, hlog n⟩
    · intro p hp
      rw [initS_ledLog] at hp
      cases hb : R.boot <;> simp [hb] at hp
      exact .inl ⟨rfl, hp⟩
    · exact ⟨0, Nat.zero_le _, rfl⟩
    · intro p hp; cases hp
    · intro m hm; cases hm

end init

end AntSim
end EtcdGrove
end Perennial
