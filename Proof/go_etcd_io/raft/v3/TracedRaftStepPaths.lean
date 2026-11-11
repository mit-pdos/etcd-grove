/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle, path by path** (2026-11-10, trace-check
Q8 stage 1 slice 15, `notes/decisions.md`, "Q8 stage 1 (slice 15)"): proofs of
`stepBundle_traced.on Path` (`TracedRaftStep.lean`) for sets of paths `Path`.

**The local messages that log no line** (`LocalNoLine`): a `MsgBeat` or a `MsgProp` at a node that is
not leading (term zero, so no preamble). Raft ignores the beat, drops the proposal (a candidate, or a
follower with no leader) or forwards it to the leader (`propForward`, an untraced `MsgProp`): no hook
fires but the receive hook, which logs nothing for a local type. The caller's resources are one traced
family (`localF`: raft's ghost state, which the receive gate is handed and the closing wand gives back,
and the capability at the idle server of `s` with the share the outbox's traced messages up to order,
`trFam`); the intermediate resources a step function may name between hooks that queue nothing
(`Gf`, `Gb1`, `Gb2`, `Gp1`) are `False`, since no path here reaches them; every other gate is guarded by
a message type or a role that is not this path's. The closing wand reads the end state from `StepEnd`
(`localNoLine_end`: unchanged, or the forward queued) and re-orders the share (`trFam_idle`).

**Not yet here**: every path of a traced type starts with a receive line, whose gate needs the line's
`FxPresR` (since amendment A2 at the phantoms `ph a` of the receiving server, `recvPhantoms`; proved for a
lower-term request, `fxPresR_staleReq`, `TracedRecvPhantom.lean`); the local paths with lines (`MsgHup`
at a non-leader, `MsgBeat`/`MsgProp` at a leader) need each line's `FxPres`.

(2026-11-10, slice 16, `notes/decisions.md`, "Q8 stage 1 (slice 16)") **A send line's phase step** at
the idle server (`phaseStepB_send`, the heartbeat's `phaseStepB_heartbeat`). Slice 16 found every send
line's `FxPres` blocked on the frozen `simFx`'s `MsgsUniq` (plan, Q15); amendment A2 adds the shape
clause `MsgsShape` to `simFx`, and the heartbeat's `FxPres` is proved (`fxPres_heartbeat`,
`TracedRecvPhantom.lean`, at phases keeping the share's server and adding the heartbeat). Amendment A2 (Q16) adds
`AppSlices`, and an `"app"` request's facts are `fxPres_app`. **Pinned phase steps** (`PinAt`,
`trCapB_pin`'s form): `phaseStepB_send_pin`, `phaseStepB_heartbeat_pin`, with `pinAt_step` and
`heartbeat_lead` giving `fxPres_heartbeat_pin`, the heartbeat line's facts at those phases.

(2026-11-10, slice 17, `notes/decisions.md`, "Q8 stage 1 (slice 17)") The heartbeat gates give the
commit exactly and the append gates the peer's `Match` at most the request's index; the append
request's phase step (`phaseStepB_msgApp`, with `appOk_slice`), from the gate's facts, a voter
destination and the log term's bound (`blt`, raft's ghost `TermsLe`, the caller's).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedFamilies
public import Proof.go_etcd_io.raft.v3.TracedHooks
public import Proof.go_etcd_io.raft.v3.TracedRecvPhantom

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- **The local messages that log no line**: a `MsgBeat` or a `MsgProp` at a node that is not leading. -/
def LocalNoLine (s : NState) (m : MessageM) : Prop :=
  (m.Type' = MsgBeat ∨ m.Type' = MsgProp) ∧ s.role ≠ .leader

/-- A type of `LocalNoLine` is not any of the types `x` names (`hx`, decided on the constants). -/
theorem localTy_ne {t : w32} (h : t = MsgBeat ∨ t = MsgProp) {x : w32} (hx : x ≠ MsgBeat ∧ x ≠ MsgProp) :
    t ≠ x := by
  rintro rfl; rcases h with h | h
  · exact hx.1 h
  · exact hx.2 h

/-- The end state of a `LocalNoLine` path (`StepEnd`, traced): unchanged, or one message of an
untraced type queued (a follower's forward to its leader). -/
theorem localNoLine_end {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} (hp : LocalNoLine s m) (hns : ¬ StaleMsg s m) (hpre : ∀ pvs, preState s m pvs = s)
    (h : StepEnd c id m ents ctx s s') :
    s' = s ∨ ∃ fwd : Msg, fwd.ty.traced = false ∧ s' = sendMsgs s [fwd] := by
  have hty : StepEndTy m.Type' := by
    unfold StepEndTy; rcases hp.1 with h | h <;> simp [h]
  have hnh : m.Type' ≠ MsgHup := localTy_ne hp.1 (by decide)
  have hnv : m.Type' ≠ MsgVote := localTy_ne hp.1 (by decide)
  obtain ⟨pvs, hfn⟩ := (h hty).2.2.2 hns hnh hnv
  rw [hpre pvs] at hfn
  obtain ⟨hf, hc, -⟩ := hfn
  have nVR : m.Type' ≠ MsgVoteResp := localTy_ne hp.1 (by decide)
  have nA : m.Type' ≠ MsgApp := localTy_ne hp.1 (by decide)
  have nH : m.Type' ≠ MsgHeartbeat := localTy_ne hp.1 (by decide)
  -- the candidate's (and pre-candidate's) result: unchanged
  have hcand : ∀ (scfg : CSLists) (sv : SnapshotM) (d : Bool) (c' : CfgM),
      CandidateStepResultC c scfg id s m ents sv d s' c' ctx → s' = s := by
    intro scfg sv d c' hres
    obtain ⟨-, hres⟩ := hres
    rw [if_neg nVR] at hres
    rcases hp.1 with ht | ht
    · have nP : m.Type' ≠ MsgProp := by
        rw [ht]; simp only [MsgBeat, MsgProp, ne_eq]; exact of_decide_eq_true rfl
      rw [if_neg nP, if_neg nA, if_neg nH, if_pos (.inl ht)] at hres
      exact hres.2
    · rw [if_pos ht] at hres
      exact hres.2
  cases hr : s.role with
  | leader => exact absurd hr hp.2
  | follower =>
    obtain ⟨scfg, sv, d, c', -, hres⟩ := hf hr
    rw [if_neg nVR] at hres
    rcases hp.1 with ht | ht
    · have nP : m.Type' ≠ MsgProp := by
        rw [ht]; simp only [MsgBeat, MsgProp, ne_eq]; exact of_decide_eq_true rfl
      rw [if_neg nP, if_neg nA, if_neg nH, if_pos (.inl ht)] at hres
      exact .inl hres.2
    · rw [if_pos ht] at hres
      by_cases hl : s.lead = W64 0
      · rw [if_pos hl] at hres; exact .inl hres.2
      · rw [if_neg hl] at hres; exact .inr ⟨_, rfl, hres.2⟩
  | candidate =>
    obtain ⟨scfg, sv, d, c', h⟩ := hc (.inl hr)
    exact .inl (hcand scfg sv d c' h)
  | preCandidate =>
    obtain ⟨scfg, sv, d, c', h⟩ := hc (.inr hr)
    exact .inl (hcand scfg sv d c' h)

/-! ### (2026-11-10, slice 16) A send line's phase step at the idle server

A send line that leaves the sender's server unchanged (a heartbeat, an append request, a vote
request, the self-acknowledgement, a vote response) moves the traced family at the idle server of
`s` from outbox `o` to `o ++ [m]`: its effect (`lineEffect_heartbeat`, `lineEffect_msgApp`, ...) adds
`m`'s specification message to the pending bag and the share. Its facts (`FxPres`) are another
matter: see `notes/decisions.md`, "Q8 stage 1 (slice 16)". -/

end pure

section sendStep
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A message's specification counterpart is from its source. -/
theorem msgAbs_source {C : List w64} {bl : Nat} {m : Msg} {ma : Etcdraft.Msg}
    (h : TraceSim.msgAbs C bl m = some ma) : ma.source = idAbs m.src := by
  unfold TraceSim.msgAbs at h
  cases hty : m.ty <;> simp only [hty] at h <;> cases h <;> rfl

/-- **A send line's phase step at the idle server** (`PhaseAt (SimIdleS · s)` from `o` to
`o ++ [m]`): the line's events are the node's and not bootstrap-named (`hE`), and at every server
the idle relation admits, the line's effect leaves the server unchanged and adds `m`'s specification
message (`heff`, from the line's `lineEffect_*`). -/
theorem phaseStepB_send (id : w64) (c : CfgM) (s : NState) (E : TraceEv → Prop) (o : List Msg) (m : Msg)
    (hsrc : m.src = id)
    (hE : ∀ e, E e → e.nid = decStr id ∧ Etcdraft.isBootstrapName (TraceSim.gsStr e.name) = false)
    (heff : ∀ (C : List w64) (e : TraceEv) (a : Etcdraft.Server), E e → (elements c.incoming).Perm C →
      c.outgoing = ∅ → id ∈ C → SimServerR C C.length (toPState s) a → LogShapeOk C.length (toPState s) →
      uint.Z s.term < 2 ^ 63 → uint.Z s.logst.committed < 2 ^ 63 →
      uint.Z (plastIndex (toPState s)) < 2 ^ 63 →
      ∃ ma, TraceSim.msgAbs C C.length m = some ma ∧
        LineEffect C false e (idAbs id) a a none _root_.id (fun b => b.with ma) (fun _ => False)) :
    PhaseStepB id c E (PhaseAt (fun C => SimIdleS C s) o) (PhaseAt (fun C => SimIdleS C s) (o ++ [m])) := by
  rintro C cs P ⟨⟨a0, ha0, hR0, hs, bt, bc, bl⟩, hP⟩ ⟨hin, hout, hC⟩ e he
  obtain ⟨hnid, hnb⟩ := hE e he
  refine ⟨hnid, isBootstrapName_bf _ hnb, ?_⟩
  intro a ha
  have hR : SimServerR C C.length (toPState s) a := simServerR_toC (ha0.trans ha.symm) hR0
  obtain ⟨ma, hma, hle⟩ := heff C e a he hin hout hC hR hs bt bc bl
  refine ⟨a, [ma], ⟨⟨a0, ha0.trans ha.symm, hR0, hs, bt, bc, bl⟩, ?_⟩, ?_, hle⟩
  · rw [pendAbs_append]
    have h1 : pendAbs C [m] = [ma] := by simp [pendAbs, hma]
    rw [h1]
    exact hP.append_right _
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    rw [msgAbs_source hma, hsrc]

/-- **A leader's heartbeat line's phase step** (`MsgBeat`'s `"#Hgbeat"` gate, the `SendAppendEntriesRequest`
line of a `MsgHeartbeat`), by `lineEffect_heartbeat`, for the commit raft computes, **exactly**
`min(committed, Match)` (`hcm`): the specification's `Heartbeat` sends exactly the minimum. Since
slice 17 the gate gives `hcm` as is (`leaderGates`' `"#Hgbeat"`, from `sendHeartbeat`'s spec; until then
only the two bounds: `notes/decisions.md`, "Q8 stage 1 (slice 16)", "(slice 17)"). -/
theorem phaseStepB_heartbeat (id : w64) (c : CfgM) (s : NState) (o : List Msg) (to cm : w64) (cl : List w8)
    (hlead : s.role = .leader) (hne : to ≠ id) (hto : to ∈ elements c.incoming)
    (hcm : uint.Z cm = min (uint.Z s.logst.committed) (uint.Z ((prvalsMatch s.prvals !! to).getD (W64 0)))) :
    PhaseStepB id c
      (SendEvOf (W64 9) id s c (Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] [] cl))
      (PhaseAt (fun C => SimIdleS C s) o)
      (PhaseAt (fun C => SimIdleS C s) (o ++ [Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] [] cl])) := by
  apply phaseStepB_send id c s _ o _ rfl
    (fun e he => ⟨he.2.1, sendEvOf_notBoot he (by decide) (by decide) (by decide)⟩)
  intro C e a he hin hout hC hR hs bt bc bl
  refine ⟨_, rfl, ?_⟩
  have hmo : matchOf (toPState s) to = (prvalsMatch s.prvals !! to).getD (W64 0) := by
    simp [matchOf, toPState, hlead]
  exact lineEffect_heartbeat C e id s c _ a he hin hout hC (hin.mem_iff.1 hto) hR hs hlead rfl rfl hne rfl rfl
    (by rw [hcm, hmo]; simp only [toPState])
    bt bc bl (by show uint.Z cm < 2 ^ 63; omega)

/-- (slice 17) An append request's entries and their bounds, from what its gate gives (`AppOk`) and the
log's shape at the idle server (base `0`, `PlogWf`): the request's range is a slice of the log from its
index, within it. -/
theorem appOk_slice (id : w64) (s : PState) (mm : Msg) (happ : AppOk id s mm)
    (hb : uint.Z s.base.index' = 0) (hl : (s.log.length : Int) < 2 ^ 63) :
    uint.nat mm.index + mm.entries.length ≤ s.log.length ∧
    mm.entries = (s.log.drop (uint.nat mm.index)).take mm.entries.length := by
  obtain ⟨-, -, -, -, hlt, -, -, hpre, -⟩ := happ
  have hi : uint.Z mm.index ≤ (s.log.length : Int) := by
    unfold plogTermAt at hlt
    split at hlt
    · cases hlt
    split at hlt
    · omega
    rename_i h1 h2
    cases hk : s.log[(uint.Z mm.index - uint.Z s.base.index' - 1).toNat]? with
    | none => rw [hk] at hlt; cases hlt
    | some e =>
      have := (List.getElem?_eq_some_iff.1 hk).1
      omega
  have hn : (uint.nat mm.index : Int) = uint.Z mm.index := by word
  have hdrop : plogFrom s.base s.log (mm.index + W64 1) = s.log.drop (uint.nat mm.index) := by
    unfold plogFrom
    congr 1
    have : uint.Z (mm.index + W64 1) = uint.Z mm.index + 1 := by word
    rw [this, hb]; omega
  rw [hdrop] at hpre
  have hlen := hpre.length_le
  rw [List.length_drop] at hlen
  refine ⟨by omega, ?_⟩
  exact (List.prefix_iff_eq_take.1 hpre)

/-- **A leader's append request's phase step** (the `SendAppendEntriesRequest` line of a `MsgApp`), by
`lineEffect_msgApp`, from what the append gates give since slice 17 (`AppOk`, the commit, the peer's
`Match` at most the index: `hmatch`), the destination a voter (`hto`), and the request's log term below
`2^63` (`blt`: a term of the leader's log, at most its term by raft's ghost `TermsLe`, which neither
the gate nor the idle relation states; the caller's family holds the ghost state). -/
theorem phaseStepB_msgApp (id : w64) (c : CfgM) (s : NState) (o : List Msg) (mm : Msg)
    (hlead : s.role = .leader) (hto : mm.dst ∈ elements c.incoming)
    (happ : AppOk id (toPState s) mm) (hcommit : mm.commit = (toPState s).commit)
    (hmatch : uint.Z ((prvalsMatch s.prvals !! mm.dst).getD (W64 0)) ≤ uint.Z mm.index)
    (blt : uint.Z mm.logterm < 2 ^ 63) :
    PhaseStepB id c (SendEvOf (W64 9) id s c mm)
      (PhaseAt (fun C => SimIdleS C s) o) (PhaseAt (fun C => SimIdleS C s) (o ++ [mm])) := by
  have hsrc : mm.src = id := happ.2.1
  apply phaseStepB_send id c s _ o _ hsrc
    (fun e he => ⟨he.2.1, sendEvOf_notBoot he (by decide) (by decide) (by decide)⟩)
  intro C e a he hin hout hC hR hs bt bc bl
  have hty : mm.ty = .app := happ.1
  refine ⟨(TraceSim.msgAbs C C.length mm).get (by simp [TraceSim.msgAbs, hty]), (Option.some_get _).symm, ?_⟩
  have hmo : matchOf (toPState s) mm.dst = (prvalsMatch s.prvals !! mm.dst).getD (W64 0) := by
    simp [matchOf, toPState, hlead]
  have hlen : ((toPState s).log.length : Int) < 2 ^ 63 := by
    have := plastIndex_length _ _ hs; omega
  obtain ⟨hpk, hents⟩ := appOk_slice id (toPState s) mm happ (by rw [hs.1]; rfl) hlen
  exact lineEffect_msgApp C e id s c mm a _ he hin hout hC (hin.mem_iff.1 hto) hR hs hlead hty hsrc
    happ.2.2.2.1 happ.2.2.1 hpk happ.2.2.2.2.1 hents hcommit (by rw [hmo]; exact hmatch)
    bt bc bl (by have := hpk; have : (uint.nat mm.index : Int) = uint.Z mm.index := by word
                 omega) blt

/-- The pinned phase at the idle server (`trCapB_pin`'s form): the voters, the share's server and
list named, the list a permutation of the outbox's traced messages. -/
abbrev PinAt (s : NState) (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (o : List Msg) :
    List w64 → ServerC → List Etcdraft.Msg → Prop :=
  fun C cs P => C = C0 ∧ cs = cs0 ∧ P = P0 ∧ PhaseAt (fun C => SimIdleS C s) o C cs P

/-- **A send line's phase step, pinned** (amendment A2, review a2-r4's open item): as
`phaseStepB_send`, from the pinned phase to the pinned phase with the server unchanged and the
message `ma0` (`m`'s specification message at the voters `C0`) added, so that the line's facts
(`fxPres_heartbeat`, `fxPres_app`, whose `hΦ'` asks exactly this: `pinAt_step`) can be given. -/
theorem phaseStepB_send_pin (id : w64) (c : CfgM) (s : NState) (E : TraceEv → Prop) (o : List Msg) (m : Msg)
    (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (ma0 : Etcdraft.Msg)
    (hma : TraceSim.msgAbs C0 C0.length m = some ma0)
    (hsrc : m.src = id)
    (hE : ∀ e, E e → e.nid = decStr id ∧ Etcdraft.isBootstrapName (TraceSim.gsStr e.name) = false)
    (heff : ∀ (C : List w64) (e : TraceEv) (a : Etcdraft.Server), E e → (elements c.incoming).Perm C →
      c.outgoing = ∅ → id ∈ C → SimServerR C C.length (toPState s) a → LogShapeOk C.length (toPState s) →
      uint.Z s.term < 2 ^ 63 → uint.Z s.logst.committed < 2 ^ 63 →
      uint.Z (plastIndex (toPState s)) < 2 ^ 63 →
      ∃ ma, TraceSim.msgAbs C C.length m = some ma ∧
        LineEffect C false e (idAbs id) a a none _root_.id (fun b => b.with ma) (fun _ => False)) :
    PhaseStepB id c E (PinAt s C0 cs0 P0 o) (PinAt s C0 cs0 (P0 ++ [ma0]) (o ++ [m])) := by
  rintro C cs P ⟨rfl, rfl, rfl, ⟨a0, ha0, hR0, hs, bt, bc, bl⟩, hP⟩ ⟨hin, hout, hC⟩ e he
  obtain ⟨hnid, hnb⟩ := hE e he
  refine ⟨hnid, isBootstrapName_bf _ hnb, ?_⟩
  intro a ha
  have hR : SimServerR C C.length (toPState s) a := simServerR_toC (ha0.trans ha.symm) hR0
  obtain ⟨ma, hma', hle⟩ := heff C e a he hin hout hC hR hs bt bc bl
  rw [hma] at hma'
  cases hma'
  refine ⟨a, [ma0], ⟨rfl, ha, rfl, ⟨a0, ha0.trans ha.symm, hR0, hs, bt, bc, bl⟩, ?_⟩, ?_, hle⟩
  · rw [pendAbs_append]
    have h1 : pendAbs C [m] = [ma0] := by simp [pendAbs, hma]
    rw [h1]
    exact hP.append_right _
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    rw [msgAbs_source hma, hsrc]

/-- **The pinned phases meet the send lines' facts' `hΦ'`**: the server kept, the message added. -/
theorem pinAt_step (s : NState) (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (o : List Msg)
    (m : Msg) (ma0 : Etcdraft.Msg) :
    ∀ C cs P cs' P', PinAt s C0 cs0 P0 o C cs P → PinAt s C0 cs0 (P0 ++ [ma0]) (o ++ [m]) C cs' (P ++ P') →
      cs' = cs ∧ P' = [ma0] := by
  rintro C cs P cs' P' ⟨-, rfl, rfl, -⟩ ⟨-, rfl, h, -⟩
  exact ⟨rfl, List.append_cancel_left h⟩

/-- **A leader's heartbeat line's phase step, pinned** (`phaseStepB_heartbeat` at `PinAt`). -/
theorem phaseStepB_heartbeat_pin (id : w64) (c : CfgM) (s : NState) (o : List Msg) (to cm : w64) (cl : List w8)
    (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (ma0 : Etcdraft.Msg)
    (hma : TraceSim.msgAbs C0 C0.length (Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] [] cl) = some ma0)
    (hlead : s.role = .leader) (hne : to ≠ id) (hto : to ∈ elements c.incoming)
    (hcm : uint.Z cm = min (uint.Z s.logst.committed) (uint.Z ((prvalsMatch s.prvals !! to).getD (W64 0)))) :
    PhaseStepB id c
      (SendEvOf (W64 9) id s c (Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] [] cl))
      (PinAt s C0 cs0 P0 o)
      (PinAt s C0 cs0 (P0 ++ [ma0]) (o ++ [Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] [] cl])) := by
  apply phaseStepB_send_pin id c s _ o _ C0 cs0 P0 ma0 hma rfl
    (fun e he => ⟨he.2.1, sendEvOf_notBoot he (by decide) (by decide) (by decide)⟩)
  intro C e a he hin hout hC hR hs bt bc bl
  refine ⟨_, rfl, ?_⟩
  have hmo : matchOf (toPState s) to = (prvalsMatch s.prvals !! to).getD (W64 0) := by
    simp [matchOf, toPState, hlead]
  exact lineEffect_heartbeat C e id s c _ a he hin hout hC (hin.mem_iff.1 hto) hR hs hlead rfl rfl hne rfl rfl
    (by rw [hcm, hmo]; simp only [toPState])
    bt bc bl (by show uint.Z cm < 2 ^ 63; omega)

/-- **The heartbeat's facts' premises at the pinned idle phase** (`fxPres_heartbeat`'s `hlead`): the
idle server is a leader of the node's term, its commit index the node's, at least the heartbeat's (the
bound only: the gate gives it, review a2-r5's 2). -/
theorem heartbeat_lead (s : NState) (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (o : List Msg)
    (id to cm : w64) (cl : List w8) (ma0 : Etcdraft.Msg)
    (hma : TraceSim.msgAbs C0 C0.length (Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] [] cl) = some ma0)
    (hlead : s.role = .leader) (hcm : uint.Z cm ≤ uint.Z s.logst.committed) :
    ∀ C cs P, PinAt s C0 cs0 P0 o C cs P →
      cs.state = Etcdraft.leader ∧ ma0.term = cs.currentTerm ∧ ma0.commitIndex ≤ cs.commitIndex := by
  rintro C cs P ⟨rfl, rfl, -, ⟨a, rfl, hR, -⟩, -⟩
  obtain ⟨hT, hS, -, -, -, -, hCm, -⟩ := hR
  simp only [TraceSim.msgAbs] at hma
  cases hma
  refine ⟨?_, ?_, ?_⟩
  · show a.state = _; rw [hS]; simp [toPState, hlead, proleRole, roleAbs]
  · show _ = a.currentTerm; rw [hT]; simp [toPState]
  · show _ ≤ a.commitIndex; rw [hCm]; simp only [toPState]; omega

end sendStep

section paths
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A traced capability's gate at a hook that logs nothing (`HookGateOpt … none`), its phase weakened. -/
theorem trCapB_gateNone (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (b : Bool)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop) (X : IProp GF)
    (h : ∀ C cs P, Φ C cs P → Φ' C cs P) :
    (X ∗ trCapB (some γd) γ r id c b Φ Λ : IProp GF) ⊢
      HookGateOpt (some γd) r none iprop(X ∗ trCapB (some γd) γ r id c b Φ' Λ) := by
  iintro ⟨HX, Hcap⟩
  icases trCapB_logger γd γ r id c b Φ Λ $$ Hcap with ⟨%tl, #Htl, Hcap⟩
  iunfold HookGateOpt
  imodintro
  iexists tl
  iframe Htl
  isplitr
  · ipureintro; intro h; cases h
  simp only [TraceFireOpt]
  iframe HX
  iapply trCapB_mono (some γd) γ r id c b Φ Φ' Λ h $$ Hcap

/-- `LocalNoLine`'s family: raft's ghost state at `s` and the capability at the idle server of `s`,
the share the outbox's traced messages up to order; the `booted` flag `b` the step's (no line). -/
def localF (b : Bool) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (Λ : Option TraceEv → Prop) (o : List Msg) : IProp GF :=
  iprop(ownStepGhost γ md c id s ∗ trFam s.gh.tr γ r id c b (fun C => SimIdleS C s) Λ o)

theorem localF_permInv (b : Bool) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (Λ : Option TraceEv → Prop) : PermInv (localF (GF := GF) b γ md c r id s Λ) := by
  intro o o' h
  unfold localF
  rw [trFam_permInv s.gh.tr γ r id c b (fun C => SimIdleS C s) Λ o o' h]

/-- `LocalNoLine`'s resources: `localF` wherever `Step` may end, `False` between hooks no path here
reaches. -/
def localR (b : Bool) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (Λ : Option TraceEv → Prop) : StepG GF where
  G := trCapB s.gh.tr γ r id c b (fun C => SimIdle C s) Λ
  G0 := localF b γ md c r id s Λ
  G1 := localF b γ md c r id s Λ
  GE := localF b γ md c r id s Λ
  Gf := iprop(⌜False⌝)
  Gb1 := iprop(⌜False⌝)
  Gb2 := iprop(⌜False⌝)
  Gp1 := iprop(⌜False⌝)
  Gp2 := localF b γ md c r id s Λ
  Gc := fun _ _ => localF b γ md c r id s Λ

/-- **`raft.Step`'s traced bundle on the local messages that log no line.** -/
theorem stepBundle_traced_localNoLine : stepBundle_traced.on (GF := GF) (hG := hG) LocalNoLine := by
  intro γ md c r id s m ents sn ctx rs γd Λ bt hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit _ _ _ _ _
  have hT0 : m.Term' = W64 0 := hloc (by rcases hp.1 with h | h <;> simp [h])
  have hnbf : ¬ PreBF m s := by
    unfold PreBF; rw [hT0]; intro h; have := h.1; simp at this
  have hpre : ∀ pvs, preState s m pvs = s := fun pvs => by simp [preState, hnbf]
  have hns : ¬ StaleMsg s m := fun h => h.1 hT0
  have hsome : s.gh.tr ≠ none := by rw [htr]; simp
  iintro ⟨Hcap, -, #Hnosnap⟩
  imodintro
  iexists localR bt γ md c r id s Λ
  isplitl [Hcap]
  · dsimp only [localR]; iexact Hcap
  isplitr
  · iunfold stepGates
    dsimp only [ghostIn, localR]
    isplitr
    · -- the receive hook: no line for a local type
      iintro ⟨Hgh, Hc⟩
      have hrg : recvGate id s c ⟨m, ents, sn, ctx, rs⟩ = none := by
        apply recvGate_none_of
        intro ty hty'
        have hm1 : mtypeOf MsgBeat = none := rfl
        have hm2 : mtypeOf MsgProp = some .propose := rfl
        rcases hp.1 with h | h <;> simp only [h] at hty'
        · rw [hm1] at hty'; cases hty'
        · rw [hm2] at hty'; cases hty'; rfl
      rw [hrg]
      unfold localF trFam
      rw [htr]
      iapply trCapB_gateNone γd γ r id c bt _ _ Λ _ (fun C cs P h => simIdle_phaseAt C s cs P h)
      iframe Hgh Hc
    isplitr
    · -- the preamble: no step-down at term zero
      unfold preGate
      iintro %_ HG0
      rw [if_neg hnbf]
      imodintro
      iexact HG0
    isplitr
    · iintro %h; exact (h.1 hT0).elim
    isplitr
    · iintro %h
      exact (h.elim (localTy_ne hp.1 (by decide)) (localTy_ne hp.1 (by decide))).elim
    isplitr
    · iintro %h; exact (localTy_ne hp.1 (by decide) h).elim
    isplitr
    · -- the step functions' gates, at `s` (no preamble)
      unfold stepFnGates
      iintro %pvs
      rw [hpre pvs]
      dsimp only
      isplit
      · iintro %hr
        unfold followerGates
        isplitr
        · iintro %h; exact (localTy_ne hp.1 (by decide) h).elim
        isplitr
        · iintro %h; exact (localTy_ne hp.1 (by decide) h).elim
        isplitr
        · -- a proposal forwarded to the leader: untraced, the family unchanged
          iintro %_ %out %hout HG
          unfold localF
          rw [trFam_untraced s.gh.tr γ r id c bt _ Λ s.outbox out hout]
          unfold trFam
          rw [htr]
          iapply trCapB_gateNone γd γ r id c bt _ _ Λ _ (fun _ _ _ h => h)
          iexact HG
        isplitr
        · iintro %h; exact (localTy_ne hp.1 (by decide) h).elim
        · imodintro; iintro %h; exact (localTy_ne hp.1 (by decide) h).elim
      isplit
      · iintro %hr
        unfold candidateGates
        isplitr
        · iintro %h; exact (h.elim (localTy_ne hp.1 (by decide)) (localTy_ne hp.1 (by decide))).elim
        isplitr
        · iintro %h; exact (localTy_ne hp.1 (by decide) h).elim
        isplitr
        · iintro %h; exact (localTy_ne hp.1 (by decide) h).elim
        isplitr
        · iintro %h; exact (localTy_ne hp.1 (by decide) h.1).elim
        isplitr
        · iintro %h; exact h.elim
        isplitr
        · iintro %h; exact h.elim
        isplitr
        · imodintro; iintro %h; exact (localTy_ne hp.1 (by decide) h.1).elim
        isplitr
        · iexact Hnosnap
        isplitr
        · iintro %h; exact (localTy_ne hp.1 (by decide) h.1).elim
        isplitr
        · imodintro; iintro %h; exact (localTy_ne hp.1 (by decide) h.1).elim
        · iintro %h
          exact (h.1.elim (fun h => localTy_ne hp.1 (by decide) h.1)
            (fun h => localTy_ne hp.1 (by decide) h.1)).elim
      · iintro %hr; exact (hp.2 hr).elim
    · ipureintro
      exact ⟨localF_permInv bt γ md c r id s Λ, IdxFree.of_some _ hsome, IdxFree.of_some _ hsome,
        IdxFree.of_some _ hsome, fun _ _ => IdxFree.of_some _ hsome⟩
  · -- the closing wand: the end state unchanged or the forward queued; the share re-ordered
    -- (slice 23a) a close at `s`
    iapply stepClose_of_at _ _ _ _ _ _ _ _ _ _ (fun _ => CloseAt.of_notLeader hp.2)
    iunfold stepCloseAt
    iintro %s' %B %recv %_ %hend Hout
    have hend' := localNoLine_end hp hns hpre (hend (by rw [htr]; rfl))
    have hS : ∀ C, SimIdleS C s = SimIdleS C s' := by
      intro C; rcases hend' with rfl | ⟨fwd, -, rfl⟩
      · rfl
      · exact (simIdleS_sendMsgs C s [fwd]).symm
    have hout : OutTrStep s s' := by
      rcases hend' with rfl | ⟨fwd, hf, rfl⟩
      · exact OutTrStep.of_sub (fun _ h => h)
      · intro _ x hx
        simp only [sendMsgs, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact .inl hx
        · exact .inr (Msg.trOk_of_untraced hf)
    ihave H : localF (GF := GF) bt γ md c r id s Λ s'.outbox $$ [Hout]
    · unfold stepOut
      dsimp only [localR]
      icases Hout with (H | H | H | H | ⟨%b, %N, H⟩) <;> iexact H
    unfold localF
    icases H with ⟨Hgh, H⟩
    imod trFam_idle s.gh.tr γ r id c bt s s' Λ hS $$ H with H
    imodintro
    iframe Hgh
    isplitl [H]
    · iexists bt
      iapply trCapB_monoΛ s.gh.tr γ r id c bt _ Λ _ (fun o h => .inl h) $$ H
    ipureintro; exact hout

/-- **A leader's heartbeat line's facts at the pinned idle phases** (`fxPres_heartbeat` with
`pinAt_step`, `heartbeat_lead`): what the `MsgBeat` path's heartbeat gate needs besides its phase step
`phaseStepB_heartbeat_pin`; `id ∈ C0` from `trCapB_pinMem`. -/
theorem fxPres_heartbeat_pin (γ : RaftNames) (id : w64) (E : TraceEv → Prop) (s : NState) (o : List Msg)
    (to cm : w64) (cl : List w8) (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (ma0 : Etcdraft.Msg)
    (hma : TraceSim.msgAbs C0 C0.length (Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] [] cl) = some ma0)
    (hC0 : id ∈ C0) (hlead : s.role = .leader) (hcm : uint.Z cm ≤ uint.Z s.logst.committed) :
    ⊢ FxPres (GF := GF) γ id E (PinAt s C0 cs0 P0 o)
      (PinAt s C0 cs0 (P0 ++ [ma0]) (o ++ [Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] [] cl])) := by
  have hma' := hma
  simp only [TraceSim.msgAbs] at hma'
  cases hma'
  exact fxPres_heartbeat γ id E _ _ _ (msgAbs_canon _ _ _ _ hma) rfl rfl (msgAbs_source hma)
    (fun C _ _ h => h.1 ▸ hC0) (heartbeat_lead s C0 cs0 P0 o id to cm cl _ hma hlead hcm)
    (pinAt_step s C0 cs0 P0 o _ _)

end paths

end EtcdGrove
end Perennial
