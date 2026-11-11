/-
Lean-first (no Rocq counterpart). **A traced node's bootstrap** (2026-11-10, trace-check Q8 stage 1 slice
21, `notes/decisions.md`, "Q8 stage 1 (slice 21)"). Raft-internal (not on `etc/api/raft.txt`).

1. **The facts at the bootstrap state** (`simFx_simInit`): the simulation's invariant starts at
   `simInit C` (`TraceSimGhost.lean`: every voter a follower of term `1` with the bootstrap log, all
   of it committed, no message), and its facts (`simFx`, `TracedCap.lean`) hold there from raft's
   commit invariant: every voter's `srvFacts` with raft's bootstrap log `γ.reBoot` (its records and
   its committed prefix, `boot_facts` of `Protocol/Enter.lean`; its commit certificate the
   bootstrap arm of `commitJ`, the configuration witnesses vacuous below the bootstrap log), the
   specification invariant `SpecInv` (no leader, no candidate, no message; the entries of term `1`),
   `QuorumLogF` (every server's log is the whole committed log, kept from term `0`, its certificate
   `commitJ`'s bootstrap arm: amendment A5), and the bags' clauses (both empty:
   amendment A2's `MsgsShape` and `AppSlices` included).
2. **The bootstrap lines' gates**: an `InitState` event (`newRaft`'s `traceInitState`) and an
   `ApplyConfChange` event (`switchToConfig`'s `traceConfChangeEvent`) parse to bootstrap-named lines
   of their node (`nodeEvOf_init_boot`, `ccEvOf_boot`), the premise of the bootstrap law
   `trCap_fire_boot`; with it the gates of both hooks in either mode before the node's segment is
   over (`trCapB_hookGate_init`, `trCapB_hookGate_ccBoot`), as `trCapB_hookGate_bf` is
   `BecomeFollower`'s.
3. **The capability's introduction** (`trCapB_intro`): what `newRaft` holds once its struct exists
   (the logger field, the trace directory, the simulation's invariant, the node's share and its
   `booted` flag) is the capability, unbooted (`b = false`).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedHooksGlobal
public import Proof.go_etcd_io.raft.v3.TraceSimSpecInv
import all Proof.go_etcd_io.raft.v3.Protocol.Enter

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

/-! ## The bootstrap state's pure facts -/

section pure
variable [GooseExts]

/-- No message in flight at the bootstrap state. -/
theorem msgs_simInit (C : List w64) :
    (simInit C).messages.domain ++ (simInit C).pendingMessages.domain = [] := rfl

/-- Every server of the bootstrap state is a follower. -/
theorem simInit_state (C : List w64) (i : Etcdraft.ID) : ((simInit C).s i).state = Etcdraft.follower := by
  simp only [simInit]; split <;> rfl

/-- **`SpecInv` at the bootstrap state**: no leader, no candidate, no message; every bootstrap entry
of term `1`, each server's term. -/
theorem specInv_simInit (C : List w64) : TraceSpecInv.SpecInv (simInit C) := by
  have hl : ∀ i, ((simInit C).s i).state ≠ Etcdraft.leader :=
    fun i => by rw [simInit_state]; decide
  have hc : ∀ i, ((simInit C).s i).state ≠ Etcdraft.candidate :=
    fun i => by rw [simInit_state]; decide
  have hm : ∀ m, m ∉ TraceSpecInv.msgs (simInit C) := fun m hm => by
    simp [TraceSpecInv.msgs, msgs_simInit] at hm
  refine ⟨fun i _ h => absurd h (hl i), fun i _ h => absurd h (hl i), fun m h => absurd h (hm m),
    fun i _ h => absurd h (hc i), fun m h => absurd h (hm m), fun _ _ l _ h => absurd h (hl l),
    fun l _ h => absurd h (hl l), fun m h => absurd h (hm m), fun l _ h => absurd h (hl l),
    ⟨fun k _ e he => ?_, fun m h => absurd h (hm m)⟩, fun i hi => by rw [simInit_s_voter C i hi]; rfl⟩
  by_cases hk : k ∈ confAbs C
  · rw [simInit_s_voter C k hk] at he ⊢
    simp only [List.mem_map, List.mem_range] at he
    obtain ⟨_, _, rfl⟩ := he
    exact Int.le_refl _
  · rw [simInit_s_nonvoter C k hk] at he
    cases he

/-- Every server's committed prefix at the bootstrap state is its whole log. -/
theorem committedL_simInit (C : List w64) (i : Etcdraft.ID) :
    committedL (simInit C) i = ((simInit C).s i).log := by
  unfold committedL
  by_cases hi : i ∈ confAbs C
  · rw [simInit_s_voter C i hi]
    simp only
    rw [Int.toNat_natCast]
    exact List.take_of_length_le (by simp)
  · rw [simInit_s_nonvoter C i hi]
    rfl

/-- **`QuorumLogF`'s `KeptFrom` at the bootstrap state** (amendment A5), from term `0`: every server
holds every server's committed prefix (its whole log, the same for all), at a term at least `0`. -/
theorem keptFrom_simInit (C : List w64) (i : Etcdraft.ID) : KeptFrom (simInit C) (committedL (simInit C) i) 0 := by
  have hf : lackingAt (simInit C) (committedL (simInit C) i) 0 = [] := by
    apply List.filter_eq_nil_iff.2
    intro j hj
    rw [committedL_simInit]
    have hj' : j ∈ confAbs C := hj
    rw [simInit_s_voter C j hj']
    by_cases hi : i ∈ confAbs C
    · rw [simInit_s_voter C i hi]
      simp only [Etcdraft.isPrefix]
      simp [List.take_of_length_le]
    · rw [simInit_s_nonvoter C i hi]
      simp [bootJunk, Etcdraft.isPrefix]
  unfold KeptFrom
  rw [hf]
  simp [Etcdraft.isQuorum]

/-- The bags' clauses at the bootstrap state, both bags empty. -/
theorem msgsUniq_simInit (C : List w64) : MsgsUniq (simInit C) := by
  intro _ m1 _ h1; simp [msgs_simInit] at h1

theorem msgsShape_simInit (C : List w64) : MsgsShape (simInit C) := by
  refine ⟨fun x hx => ?_, fun i hi k hk => ?_⟩
  · simp [msgs_simInit] at hx
  · rw [simInit_s_voter C i hi] at hk
    simp at hk

theorem appSlices_simInit (C : List w64) : AppSlices (simInit C) := by
  intro m hm; simp [msgs_simInit] at hm

/-- The bootstrap state's log is raft's bootstrap log read by `logAbs` (any log of the voters' length:
`entAbs` reads a bootstrap position by its index only). -/
theorem simInit_log (C : List w64) (es : List EntryM) (hlen : es.length = C.length) (i : Etcdraft.ID)
    (hi : i ∈ confAbs C) :
    ((simInit C).s i).log = logAbs C C.length 1 es := by
  rw [simInit_s_voter C i hi]
  simp only [logAbs]
  apply List.ext_getElem
  · simp [hlen]
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_mapIdx, entAbs]
    have hk : 1 + k ≤ C.length := by simp at h1; omega
    rw [if_pos hk, Nat.add_comm 1 k]

/-- **The idle relation at the end of a fresh node's bootstrap** (`StartNode`: `newRaft` on an empty
storage, then `Bootstrap`'s configuration entries, committed, at term `1`): raft's state, a follower of
term `1` with no vote and no leader whose log is a bootstrap log of the voters' length (`es`, of term
`1`, from index `1`), all of it committed, and nothing queued, is idle-related to the bootstrap state's
server with nothing pending (`SimIdle`, the bundle's and the ticks' phase). -/
theorem simIdle_boot (C : List w64) (id : w64) (hid : id ∈ C) (s : NState) (es : List EntryM)
    (hterm : s.term = W64 1) (hrole : s.role = .follower) (hvote : s.vote = W64 0)
    (hlead : s.lead = W64 0) (hprev : s.logst.prev = entryID.mk (W64 0) (W64 0))
    (hlog : s.logst.sents ++ s.logst.uents = es) (hlen : es.length = C.length)
    (hlt : (C.length : Int) < 2 ^ 61) (hcom : s.logst.committed = W64 (C.length : Int))
    (hout : s.outbox = []) (hwf : PlogWf (entryID.mk (W64 0) (W64 0)) es)
    (hones : ∀ e ∈ es, e.Term' = W64 1) :
    SimIdle C s (toC (confAbs C) ((simInit C).s (idAbs id))) [] := by
  have hW : uint.Z (W64 (C.length : Int)) = (C.length : Int) := uint_Z_W64 _ (by omega) (by omega)
  have hlog' : (toPState s).log = es := hlog
  have hmem : idAbs id ∈ confAbs C := (mem_confAbs C id).2 hid
  rw [simInit_s_voter C _ hmem]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
    · show (1 : Int) = uint.Z (toPState s).term
      simp only [toPState, hterm]; rfl
    · simp only [toPState, hrole, proleRole, roleAbs]
    · simp only [toPState, hvote]; rfl
    · simp only [toPState, hrole, hlead]; rfl
    · simp only [toPState, hprev]; rfl
    · rw [hlog', ← simInit_s_voter C _ hmem]; exact simInit_log C es hlen _ hmem
    · show (C.length : Int) = uint.Z (toPState s).commit
      simp only [toPState, hcom, hW]
    · intro h; simp [toPState, hrole, proleRole] at h
    · intro h; simp [toPState, hrole, proleRole] at h
  · refine ⟨by simp only [toPState, hprev], by simp only [toPState, hprev]; rw [hlog]; exact hwf,
      fun k e _ he => hones e (List.mem_of_getElem? (by rw [← hlog']; exact he))⟩
  · simp only [toPState, hout, pendAbs, List.filterMap_nil]
  · rw [hterm]; decide
  · rw [hcom, hW]; omega
  · simp only [plastIndex, plogLastIndexZ, toPState, hprev]
    rw [hlog, hlen]
    have : uint.Z (W64 (uint.Z (W64 0) + (C.length : Int))) = (C.length : Int) := by
      rw [show uint.Z (W64 0) = 0 from rfl, Int.zero_add]; exact hW
    rw [this]; omega

end pure

/-! ## The bootstrap state's facts from raft's commit invariant -/

section facts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A voter's facts at the bootstrap state** (`srvFacts`): raft's bootstrap log `γ.reBoot`, of the
voters' length, with its records and committed (`boot_facts`), all of it committed at term `1`: its
commit certificate is `commitJ`'s bootstrap arm, and the configuration witnesses (`witsB`) are
vacuous below the bootstrap log's length. -/
theorem srvFacts_simInit (γ : RaftNames) (C : List w64) (j : w64) (hj : j ∈ C)
    (hlen : γ.reBoot.length = C.length) (hlt : (C.length : Int) < 2 ^ 61)
    (hwf : PlogWf base0 γ.reBoot) (hones : ∀ e ∈ γ.reBoot, e.Term' = W64 1) :
    (isCommitted (GF := GF) γ γ.reBoot ∗ logRecs γ base0 γ.reBoot) ⊢
      srvFacts γ C j ((simInit C).s (idAbs j)) := by
  iintro ⟨#Hc, #Hr⟩
  have hW : uint.Z (W64 (C.length : Int)) = (C.length : Int) := uint_Z_W64 _ (by omega) (by omega)
  have hmem : idAbs j ∈ confAbs C := (mem_confAbs C j).2 hj
  have hcom : ((simInit C).s (idAbs j)).commitIndex = (C.length : Int) := by
    rw [simInit_s_voter C _ hmem]
  have hterm : ((simInit C).s (idAbs j)).currentTerm = 1 := by rw [simInit_s_voter C _ hmem]
  iunfold srvFacts
  iexists γ.reBoot, []
  rw [List.append_nil]
  isplitr
  · ipureintro
    refine ⟨simInit_log C γ.reBoot hlen _ hmem, fun k e _ he => hones e (List.mem_of_getElem? he),
      PlogWf_wfR _ _ hwf, by omega, by rw [hcom]; omega, by rw [hcom, hlen]; exact Int.le_refl _, by rw [hterm]; decide,
      by rw [hterm]; decide, fun _ => rfl, fun e he => by cases he⟩
  isplitr
  · iexact Hr
  isplitr
  · rw [hcom, Int.toNat_natCast, ← hlen, List.take_length]; iexact Hc
  isplitr
  · rw [simInit_state]; simp only [show Etcdraft.follower ≠ Etcdraft.leader by decide, ↓reduceIte]
    iempintro
  rw [hcom]
  iunfold commitIn
  isplitr
  · iunfold commitJ
    ileft
    ipureintro
    exact ⟨by rw [hW]; omega, rfl⟩
  iunfold dynOn
  iright
  iunfold witsB
  iintro %k %hk %hb
  exfalso
  have := hk.2
  rw [hW, Int.toNat_natCast] at this
  omega

/-- **The simulation's facts at the bootstrap state** (`simFx γ C (simInit C)`), from raft's commit
invariant, for the voters `C` of the cluster's bootstrap log (`BootLogOk`, `nodeBootU`'s). -/
theorem simFx_simInit (E : CoPset) (γ : RaftNames) (C : List w64) (hE : ↑(raftN γ) ⊆ E)
    (hboot : BootLogOk C γ.reBoot) :
    raftCommitInv (GF := GF) γ ={E}=∗ simFx γ C (simInit C) := by
  iintro #Hci
  imod boot_facts E γ hE $$ Hci with ⟨#Hc, #Hr, %Hp⟩
  obtain ⟨hwf, hones⟩ := Hp
  have hlen : γ.reBoot.length = C.length := hboot.1
  have hlt : (C.length : Int) < 2 ^ 61 := by have := hboot.2.1; rw [hlen] at this; exact this
  imodintro
  iunfold simFx
  isplitr
  · iunfold allFacts
    imodintro
    iintro %j %hj
    iapply srvFacts_simInit γ C j hj hlen hlt hwf hones
    iframe Hc Hr
  isplitr
  · imodintro
    iintro %m %hm
    exfalso
    rw [msgs_simInit] at hm
    cases hm
  isplitr
  · -- (amendment A5) every committed prefix kept from term `0`, its certificate the bootstrap log's;
    -- (amendment A6) no acknowledgement in flight, every match index `0`
    iunfold QuorumLogF
    isplitr
    rotate_left
    · iunfold AckHists
      isplitr
      · imodintro
        iintro %x %hx
        exfalso
        have := hx.1
        rw [msgs_simInit] at this
        cases this
      · imodintro
        iintro %i %k %h
        exfalso
        have := h.2.2.2.2
        rw [simInit_s_voter C i h.1] at this
        simp at this
    iunfold QuorumKept
    imodintro
    iintro %i %hi
    iexists 0
    isplitr
    · ipureintro; exact keptFrom_simInit C i
    iunfold CommitCert
    iexists γ.reBoot, W64 (C.length : Int)
    have hW : uint.Z (W64 (C.length : Int)) = (C.length : Int) := uint_Z_W64 _ (by omega) (by omega)
    have hWn : uint.nat (W64 (C.length : Int)) = C.length := by
      have : uint.nat (W64 (C.length : Int)) = (uint.Z (W64 (C.length : Int))).toNat := rfl
      rw [this, hW, Int.toNat_natCast]
    isplitr
    · ipureintro
      refine ⟨?_, hwf, by rw [hW, hlen]; exact Int.le_refl _, by rw [hlen]; omega, Int.le_refl _, by decide⟩
      rw [hWn, List.take_of_length_le (Nat.le_of_eq hlen), committedL_simInit, simInit_log C γ.reBoot hlen i hi]
      exact List.prefix_refl _
    isplitr
    · iexact Hr
    iunfold commitJ
    ileft
    ipureintro
    exact ⟨by rw [hW, hlen]; exact Int.le_refl _, rfl⟩
  ipureintro
  exact ⟨specInv_simInit C, msgsUniq_simInit C, msgsShape_simInit C, appSlices_simInit C⟩

end facts

/-! ## The bootstrap lines' gates -/

section gates
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **An `InitState` node event names a bootstrap line of its node** (`newRaft`'s `traceInitState`;
the premise of `trCap_fire_boot`, as `nodeEvOf_bf_boot` is `BecomeFollower`'s). -/
theorem nodeEvOf_init_boot (id : w64) (s : NState) (c : CfgM) (e : TraceEv)
    (h : NodeEvOf (W64 0) id s c e) :
    e.nid = decStr id ∧ ∃ ln, Etcdraft.parseLine 0 (evConv e) = .ok ln ∧ ln.nid = idAbs id ∧
      Etcdraft.isBootstrapName ln.ev.name = true := by
  obtain ⟨hname, hnid, -, hvote, -, -, -, ⟨xs, ys, -, -, hconf⟩, hmsg, -, -, -, -⟩ := h
  have hname' : gsStr e.name = "InitState" := by
    simp only [evtNames] at hname
    have : e.name = go!"InitState" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  refine ⟨hnid, _, parseLine_node 0 e id s.vote xs ys hnid hvote hconf hmsg (by rw [hname']; rfl)
    (by rw [hname']; decide), rfl, ?_⟩
  simp [evConv, hname']; rfl

/-- **An `ApplyConfChange` event names a bootstrap line of its node** (`switchToConfig`'s
`traceConfChangeEvent`, during `newRaft` and `Bootstrap`, before the node's first `Ready`). -/
theorem ccEvOf_boot (id : w64) (s : NState) (c cn : CfgM) (e : TraceEv) (h : CCEvOf id s c cn e) :
    e.nid = decStr id ∧ ∃ ln, Etcdraft.parseLine 0 (evConv e) = .ok ln ∧ ln.nid = idAbs id ∧
      Etcdraft.isBootstrapName ln.ev.name = true := by
  obtain ⟨hname, hnid, -, hvote, -, -, -, ⟨xs, ys, -, -, hconf⟩, hmsg, -⟩ := h
  have hname' : gsStr e.name = "ApplyConfChange" := by
    simp only [evtNames] at hname
    have : e.name = go!"ApplyConfChange" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  refine ⟨hnid, _, parseLine_node 0 e id s.vote xs ys hnid hvote hconf hmsg (by rw [hname']; rfl)
    (by rw [hname']; decide), rfl, ?_⟩
  simp [evConv, hname']; rfl

/-- **The gate of a bootstrap line, either mode** (the node's segment not over, `b = false`): traced,
the bootstrap law `trCap_fire_boot` (the share unchanged, the last event recorded by `Λ'`); untraced,
the struct's nil logger. `E` is the hook's events, each a bootstrap-named line of the node (`hboot`),
bounded at the capability's configuration `cC` (`hOk`, `TraceEv.OkBoot`: raft's configuration grows
to the voters' meanwhile, amendment A1), each raft's next bootstrap event after the node's last
(`hBN`, `BootNext`: amendment A7). -/
theorem trCapB_hookGate_boot (tr : Option GName) (γ : RaftNames) (r : Loc) (id : w64) (cC : CfgM)
    (tl0 : GoInterface) (E : TraceEv → Prop) (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop)
    (Λ Λ' : Option TraceEv → Prop)
    (hboot : ∀ e, E e → e.nid = decStr id ∧ ∃ ln, Etcdraft.parseLine 0 (evConv e) = .ok ln ∧
      ln.nid = idAbs id ∧ Etcdraft.isBootstrapName ln.ev.name = true)
    (hBN : tr.isSome → ∀ C cs P, Φ C cs P → ∀ e, E e → ∀ o, Λ o → BootNext C id o e)
    (hΛ : ∀ e, E e → Λ' (some e))
    (hOk : tr.isSome → ∀ e, E e → TraceEv.OkBoot (elements cC.incoming).length e)
    (hok : tr = none → TraceLoggerOk tl0) :
    (r.[raft, go!"traceLogger"] ↦□ tl0 ∗ trCapB tr γ r id cC false Φ Λ : IProp GF) ⊢
      HookGate tr r E (trCapB tr γ r id cC false Φ Λ') := by
  cases tr with
  | none =>
    simp only [trCapB]
    iintro ⟨#Hl, -⟩
    iunfold HookGate
    imodintro
    iexists tl0
    isplitr
    · iexact Hl
    simp only [TraceFire]
    isplitr
    · ipureintro; exact hok rfl
    iempintro
  | some γd =>
    iintro ⟨-, Hcap⟩
    icases trCapB_logger γd γ r id cC false Φ Λ $$ Hcap with ⟨%tl, #Htl, Hcap⟩
    iunfold HookGate
    imodintro
    iexists tl
    isplitr
    · iexact Htl
    iapply trCap_fire_boot γd γ r id cC tl E Φ Λ Λ' hboot (hBN rfl) hΛ (hOk rfl)
    iframe Hcap Htl

/-- **`InitState`'s gate** (`newRaft`'s `traceInitState`, at raft's state `s` and configuration `c`,
empty at that point; the capability's `cC` the voters'), either mode. -/
theorem trCapB_hookGate_init (tr : Option GName) (γ : RaftNames) (r : Loc) (id : w64) (c cC : CfgM)
    (s : NState) (tl0 : GoInterface) (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop)
    (Λ Λ' : Option TraceEv → Prop)
    (hBN : tr.isSome → ∀ C cs P, Φ C cs P → ∀ e, NodeEvOf (W64 0) id s c e → ∀ o, Λ o → BootNext C id o e)
    (hΛ : ∀ e, NodeEvOf (W64 0) id s c e → Λ' (some e))
    (hOk : tr.isSome → ∀ e, NodeEvOf (W64 0) id s c e → TraceEv.OkBoot (elements cC.incoming).length e)
    (hok : tr = none → TraceLoggerOk tl0) :
    (r.[raft, go!"traceLogger"] ↦□ tl0 ∗ trCapB tr γ r id cC false Φ Λ : IProp GF) ⊢
      HookGate tr r (NodeEvOf (W64 0) id s c) (trCapB tr γ r id cC false Φ Λ') :=
  trCapB_hookGate_boot tr γ r id cC tl0 _ Φ Λ Λ' (nodeEvOf_init_boot id s c) hBN hΛ hOk hok

/-- **A bootstrap `ApplyConfChange`'s gate** (`switchToConfig`'s `traceConfChangeEvent` during
`newRaft` and `Bootstrap`: raft's configuration `c` before, `cn` after), either mode. -/
theorem trCapB_hookGate_ccBoot (tr : Option GName) (γ : RaftNames) (r : Loc) (id : w64) (c cn cC : CfgM)
    (s : NState) (tl0 : GoInterface) (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop)
    (Λ Λ' : Option TraceEv → Prop)
    (hBN : tr.isSome → ∀ C cs P, Φ C cs P → ∀ e, CCEvOf id s c cn e → ∀ o, Λ o → BootNext C id o e)
    (hΛ : ∀ e, CCEvOf id s c cn e → Λ' (some e))
    (hOk : tr.isSome → ∀ e, CCEvOf id s c cn e → TraceEv.OkBoot (elements cC.incoming).length e)
    (hok : tr = none → TraceLoggerOk tl0) :
    (r.[raft, go!"traceLogger"] ↦□ tl0 ∗ trCapB tr γ r id cC false Φ Λ : IProp GF) ⊢
      HookGate tr r (CCEvOf id s c cn) (trCapB tr γ r id cC false Φ Λ') :=
  trCapB_hookGate_boot tr γ r id cC tl0 _ Φ Λ Λ' (ccEvOf_boot id s c cn) hBN hΛ hOk hok

/-- **The capability's introduction** (`newRaft`'s, once its struct and its logger field exist): the
trace directory, the logger field and its contract, the simulation's invariant with raft's commit log
invariant, the node's share in phase `Φ` and its `booted` flag unset make the capability, unbooted. -/
theorem trCapB_intro (γd : GName) (tn : TraceNames) (C : List w64) (tl : GoInterface) (cs : ServerC)
    (P : List Etcdraft.Msg) (o : Option TraceEv) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop)
    (hC : tn.voters = C ∧ (elements c.incoming).Perm C ∧ c.outgoing = ∅ ∧ id ∈ C ∧
      C.length ≤ γ.reBoot.length)
    (htl : tl ≠ interface.nil) (hΦ : Φ C cs P) (hΛ : Λ o) :
    (traceDir γd tn ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗ isTraceLogger tn.tr tl ∗
        inv (simNS γ) (simInv C tn (simFx γ C)) ∗ raftLogInv γ ∗ simNode tn id cs P ∗
        simBoot tn id false o : IProp GF) ⊢
      trCapB (some γd) γ r id c false Φ Λ := by
  iintro ⟨#Hdir, #Htl, Hlog, #Hinv, #Hli, Hnode, Hboot⟩
  iunfold trCapB
  iexists tn, C, tl, cs, P
  iframe Hdir Htl Hlog Hinv Hli Hnode
  isplitr
  · ipureintro; exact hC
  isplitr
  · ipureintro; exact htl
  isplitl [Hboot]
  · iexists o
    iframe Hboot
    ipureintro; exact hΛ
  ipureintro; exact hΦ

end gates

end EtcdGrove
end Perennial
