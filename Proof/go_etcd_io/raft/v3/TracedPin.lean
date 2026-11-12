/-
Lean-first (no Rocq counterpart). **The local paths' infrastructure** (2026-11-10, trace-check Q8 stage 1
slice 18a, `notes/decisions.md`, "Q8 stage 1 (slice 18a)").

- **A path's family** (`lineF`): raft's ghost state at the step's first state (`Step` hands it to the
  receive gate and takes it back at the close), the traced family (`trFam`) in a phase `Φs` of the
  server, and the new messages' numbers (`OutOk`: every message of the outbox the step's first state's
  or `Msg.TrOk`, what the closing wand's `OutTrStep` asks). `PermInv` (`lineF_permInv`).
- **Pin and unpin** (`trFam_pin`, `trFam_unpin`): a line's facts (`FxPres`) are asked of every result
  its phases admit, so a gate pins the share's voters, server and list (`PinAtG`, of which
  `PinAt s` is the idle server's) before the line and forgets them after.
- `hookGateOpt_mono`, `sendOutGate_one` (a gate of one traced message is its `SendEvOf`).
- `app_lead`: the `"app"` counterpart of `heartbeat_lead` (`fxPres_app`'s `hlead`) at the pinned idle
  phases, from what the append gates give (`AppOk`, the commit).
- **`AppSlices`' preservation** (amendment A2's open item): `appSlices_mono` (the bags shrink, and
  every leader of the result led the same term before with a prefix of its log, or has no append request
  of its term in flight: `Replicate`, `Commit`, a step-down, `BecomeLeader`), `appSlices_becomeLeader`
  (by `CandS`), `appSlices_extend` (one leader's log extended).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepPaths

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts]

/-! ## The new messages' numbers -/

/-- **Every message of the outbox `o` is `s`'s or carries its numbers** (`Msg.TrOk`): what the closing
wand's `OutTrStep s s'` reads at `o = s'.outbox`. (2026-11-12, implementation step 2, design revision 3's
S2) And, if `s` is in the traced scope (`TrScope`), is a `TrOutMsg`: what `OutTyStep` reads. -/
def OutOk (s : NState) (o : List Msg) : Prop :=
  ∀ x ∈ o, x ∈ s.outbox ∨ (x.TrOk ∧ (TrScope s → TrOutMsg x))

theorem outOk_self (s : NState) : OutOk s s.outbox := fun _ h => .inl h

theorem outOk_snoc {s : NState} {o : List Msg} {x : Msg} (h : OutOk s o) (hx : x.TrOk)
    (hty : TrScope s → TrOutMsg x) : OutOk s (o ++ [x]) := by
  intro y hy
  rcases List.mem_append.1 hy with hy | hy
  · exact h y hy
  · rw [List.mem_singleton.1 hy]; exact .inr ⟨hx, hty⟩

/-- `outOk_snoc` for a message of a traced type. -/
theorem outOk_snocT {s : NState} {o : List Msg} {x : Msg} (h : OutOk s o) (hx : x.TrOk)
    (hty : x.ty.traced = true) : OutOk s (o ++ [x]) :=
  outOk_snoc h hx (fun _ => .inl hty)

theorem outOk_perm (s : NState) {o o' : List Msg} (hp : o.Perm o') : OutOk s o = OutOk s o' := by
  apply propext
  constructor
  · intro h x hx; exact h x (hp.mem_iff.2 hx)
  · intro h x hx; exact h x (hp.mem_iff.1 hx)

theorem outTrStep_of_outOk {s s' : NState} (h : OutOk s s'.outbox) : OutTrStep s s' :=
  fun _ x hx => (h x hx).imp_right And.left

/-- (Implementation step 2) **`OutTyStep` from the family's `OutOk`**, the scope kept by the step. -/
theorem outTyStep_of_outOk {s s' : NState} (h : OutOk s s'.outbox) (hs : TrScope s → TrScope s') :
    OutTyStep s s' :=
  fun _ ht => ⟨hs ht, fun x hx => (h x hx).imp_right (fun h' => h'.2 ht)⟩

/-! ## A gate of one traced message -/

/-- A send gate of one message whose type `traceSendMessage` logs as `evt`: its `SendEvOf`. -/
theorem sendOutGate_one (id : w64) (s : NState) (c : CfgM) (ty : w32) (m : Msg) (evt : w64)
    (h : (mtypeOf ty).bind sendEvt = some evt) :
    sendOutGate id s c ty [m] = some (SendEvOf evt id s c m) := by
  unfold sendOutGate
  rw [h]
  simp only [Option.map_some, List.mem_singleton, exists_eq_left]

/-! ## The pinned phase -/

/-- **A phase pinned**: the share's voters, server and list named, the phase `PhaseAt Φs o`
(`PinAt s` is this at the idle server of `s`). -/
abbrev PinAtG (Φs : List w64 → ServerC → Prop) (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg)
    (o : List Msg) : List w64 → ServerC → List Etcdraft.Msg → Prop :=
  fun C cs P => C = C0 ∧ cs = cs0 ∧ P = P0 ∧ PhaseAt Φs o C cs P

/-! ## `AppSlices` preserved (amendment A2's open item) -/

/-- **`AppSlices` after a step that only removes messages and keeps every leader's term log**: for
each server leading in the result, either it led the same term before with a prefix of its log (a
`Replicate` line, a commit, a send), or no append request of its new term from it is in flight (a new
leader: `appSlices_becomeLeader`, `CandS`). Step-downs make the clause vacuous. -/
theorem appSlices_mono (σ σ' : Etcdraft.State) (h : AppSlices σ) (hsrv : σ'.server = σ.server)
    (hmsgs : ∀ m ∈ σ'.messages.domain ++ σ'.pendingMessages.domain, m ∈ σ.messages.domain ++ σ.pendingMessages.domain)
    (hlead : ∀ j ∈ σ.server, (σ'.s j).state = Etcdraft.leader →
      ((σ.s j).state = Etcdraft.leader ∧ (σ.s j).currentTerm = (σ'.s j).currentTerm ∧ (σ.s j).log <+: (σ'.s j).log) ∨
      (∀ m ∈ σ.messages.domain ++ σ.pendingMessages.domain, m.source = j → m.type = .appendEntriesRequest →
        m.term ≠ (σ'.s j).currentTerm)) :
    AppSlices σ' := by
  intro m hm hty i hi hl ht hsrc k e he
  rw [hsrv] at hi
  have hm0 := hmsgs m hm
  rcases hlead i hi hl with ⟨hl0, ht0, hpre⟩ | hno
  · have h0 := h m hm0 hty i hi hl0 (by rw [ht0, ht]) hsrc k e he
    obtain ⟨t, ht'⟩ := hpre
    rw [← ht', List.getElem?_append_left (List.getElem?_eq_some_iff.1 h0).1]
    exact h0
  · exact absurd ht.symm (hno m hm0 hsrc hty)

/-- **A new leader's clause holds vacuously** (`CandS`): a candidate has no append request of its term
in flight. -/
theorem appSlices_becomeLeader (σ : Etcdraft.State) (hc : TraceSpecInv.CandS σ) (j : Etcdraft.ID)
    (hj : j ∈ σ.server) (hcand : (σ.s j).state = Etcdraft.candidate) :
    ∀ m ∈ σ.messages.domain ++ σ.pendingMessages.domain, m.source = j → m.type = .appendEntriesRequest →
      m.term ≠ (σ.s j).currentTerm := by
  intro m hm hs ht he
  have := (hc j hj hcand).1 m hm hs ht
  rw [he] at this
  exact Int.lt_irrefl _ this

/-- **One server's log extended at the same role and term** (a `Replicate` line, a commit's or a send's
server change) keeps `AppSlices`, the bags unchanged. -/
theorem appSlices_extend (σ : Etcdraft.State) (h : AppSlices σ) (i : Etcdraft.ID) (a' : Etcdraft.Server)
    (hst : a'.state = (σ.s i).state) (ht : a'.currentTerm = (σ.s i).currentTerm) (hpre : (σ.s i).log <+: a'.log) :
    AppSlices (withNode σ i a' _root_.id _root_.id) := by
  apply appSlices_mono σ (withNode σ i a' _root_.id _root_.id) h rfl (fun m hm => hm)
  intro j _ hl
  have hsj : (withNode σ i a' _root_.id _root_.id).s j = if j = i then a' else σ.s j := rfl
  rw [hsj] at hl ⊢
  by_cases hj : j = i
  · subst hj
    rw [if_pos rfl] at hl ⊢
    exact .inl ⟨hst ▸ hl, ht.symm, hpre⟩
  · rw [if_neg hj] at hl ⊢
    exact .inl ⟨hl, rfl, List.prefix_refl _⟩

end pure

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem pinAt_eq (s : NState) (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (o : List Msg) :
    PinAt s C0 cs0 P0 o = PinAtG (fun C => SimIdleS C s) C0 cs0 P0 o := rfl

/-- **The idle server's `"app"` request's facts' premises at the pinned idle phase** (`fxPres_app`'s
`hlead`; the counterpart of `heartbeat_lead`): the idle server leads the node's term, its commit is
the request's, and the request's entries are the slice of its log after the previous index, within it
(`appOk_slice`, `SimServerR`'s log). -/
theorem app_lead (s : NState) (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (o : List Msg)
    (id : w64) (mm : Msg) (ma0 : Etcdraft.Msg)
    (hma : TraceSim.msgAbs C0 C0.length mm = some ma0)
    (hlead : s.role = .leader) (happ : AppOk id (toPState s) mm) (hcommit : mm.commit = (toPState s).commit) :
    ∀ C cs P, PinAt s C0 cs0 P0 o C cs P →
      cs.state = Etcdraft.leader ∧ ma0.term = cs.currentTerm ∧ ma0.commitIndex ≤ cs.commitIndex ∧
      0 ≤ ma0.prevLogIndex ∧ ma0.prevLogIndex + ma0.entries.length ≤ cs.log.length ∧
      ∀ (k : Nat) (e : Etcdraft.Entry), ma0.entries[k]? = some e → cs.log[ma0.prevLogIndex.toNat + k]? = some e := by
  rintro C cs P ⟨rfl, rfl, -, ⟨a, rfl, hR, hs, -, -, bl⟩, -⟩
  obtain ⟨hT, hS, -, -, hb, hlog, hCm, -⟩ := hR
  have hty : mm.ty = .app := happ.1
  have hlen : ((toPState s).log.length : Int) < 2 ^ 63 := by
    have := plastIndex_length _ _ hs; omega
  obtain ⟨hpk, hents⟩ := appOk_slice id (toPState s) mm happ hb hlen
  simp only [TraceSim.msgAbs, hty] at hma
  cases hma
  have hn : (uint.nat mm.index : Int) = uint.Z mm.index := by word
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show a.state = _; rw [hS]; simp [toPState, hlead, proleRole, roleAbs]
  · show uint.Z mm.term = a.currentTerm; rw [hT, happ.2.2.1]
  · show _ ≤ a.commitIndex; rw [hCm, hcommit]; exact Int.le_refl _
  · show (0 : Int) ≤ uint.Z mm.index; exact uint_Z_nonneg _
  · show uint.Z mm.index + ((logAbs C C.length (uint.nat mm.index + 1) mm.entries).length : Int) ≤
      ((toC (confAbs C) a).log.length : Int)
    show _ ≤ (a.log.length : Int)
    rw [hlog]; simp only [logAbs, List.length_mapIdx]; omega
  · intro k e he
    show a.log[(uint.Z mm.index).toNat + k]? = some e
    have hk : (uint.Z mm.index).toNat = uint.nat mm.index := by omega
    rw [hk, hlog]
    simp only [logAbs, List.getElem?_mapIdx] at he ⊢
    rw [hents] at he
    rw [List.getElem?_take, List.getElem?_drop] at he
    split at he
    · rw [Option.map_eq_some_iff] at he ⊢
      obtain ⟨x, hx, rfl⟩ := he
      refine ⟨x, hx, ?_⟩
      congr 1; omega
    · simp at he

/-- **The traced family, pinned**: its voters, server and list named (`trCapB_pinMem`), the node one of
the voters. -/
theorem trFam_pin (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (b : Bool)
    (Φs : List w64 → ServerC → Prop) (Λ : Option TraceEv → Prop) (o : List Msg) :
    trFam (GF := GF) (some γd) γ r id c b Φs Λ o ⊢
      ∃ (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg), ⌜PhaseAt Φs o C0 cs0 P0 ∧ id ∈ C0⌝ ∗
        trCapB (some γd) γ r id c b (PinAtG Φs C0 cs0 P0 o) Λ := by
  unfold trFam
  exact trCapB_pinMem γd γ r id c b (PhaseAt Φs o) Λ

/-- **The pinned family, unpinned.** -/
theorem trFam_unpin (tr : Option GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (b : Bool)
    (Φs : List w64 → ServerC → Prop) (Λ : Option TraceEv → Prop) (C0 : List w64) (cs0 : ServerC)
    (P0 : List Etcdraft.Msg) (o : List Msg) :
    trCapB (GF := GF) tr γ r id c b (PinAtG Φs C0 cs0 P0 o) Λ ⊢ trFam tr γ r id c b Φs Λ o := by
  unfold trFam
  exact trCapB_mono tr γ r id c b _ _ Λ (fun _ _ _ h => h.2.2.2)

/-- `HookGateOpt`'s monotonicity. -/
theorem hookGateOpt_mono (tr : Option GName) (r : Loc) (oE : Option (TraceEv → Prop)) (Q Q' : IProp GF) :
    iprop((Q -∗ Q') ∗ HookGateOpt tr r oE Q) ⊢ HookGateOpt tr r oE Q' := by
  iintro ⟨HW, H⟩
  iunfold HookGateOpt at H
  iunfold HookGateOpt
  imod H with ⟨%tl, #Htl, %Hok, H⟩
  imodintro
  iexists tl
  iframe Htl
  isplitr
  · ipureintro; exact Hok
  iapply traceFireOpt_mono tr tl oE Q Q'
  iframe HW H

/-- **A local path's family** (see the header): raft's ghost state at `s`, the traced family at the
server's phase `Φs` (with any `booted` flag: slice 22a, Q19; set once a line is logged), the outbox's
new messages' numbers. (2026-11-12, implementation step 2, design N1 and Probe B's P6) The flag at
least the step's first one, `bt`: a path's lines only set it. -/
def lineF (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (Φs : List w64 → ServerC → Prop) (Λ : Option TraceEv → Prop) (bt : Bool) (o : List Msg) : IProp GF :=
  iprop(ownStepGhost γ md c id s ∗ (∃ b : Bool, ⌜bt = true → b = true⌝ ∗ trFam s.gh.tr γ r id c b Φs Λ o) ∗
    ⌜OutOk s o⌝)

theorem lineF_permInv (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (Φs : List w64 → ServerC → Prop) (Λ : Option TraceEv → Prop) (bt : Bool) :
    PermInv (lineF (GF := GF) γ md c r id s Φs Λ bt) := by
  intro o o' h
  unfold lineF trFam
  rw [phaseAt_permInv Φs o o' h, outOk_perm s h]

/-- **A local path's family, from the idle capability** at the receive gate (a local type logs no
receive line): the phase the idle server's, the last-event predicate weakened to `stepLastEv Λ`. -/
theorem lineF_recv (γd : GName) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (Λ : Option TraceEv → Prop) (b : Bool) (htr : s.gh.tr = some γd) :
    (ownStepGhost γ md c id s ∗ trCapB s.gh.tr γ r id c b (fun C => SimIdle C s) Λ : IProp GF) ⊢
      HookGateOpt s.gh.tr r none (lineF γ md c r id s (fun C => SimIdleS C s) (stepLastEv Λ) b s.outbox) := by
  unfold lineF trFam
  rw [htr]
  iintro ⟨Hgh, Hc⟩
  ihave Hc := trCapB_monoΛ (some γd) γ r id c b _ Λ (stepLastEv Λ) (fun o h => .inl h) $$ Hc
  iapply hookGateOpt_mono (some γd) r none
    iprop(⌜OutOk s s.outbox⌝ ∗ trCapB (some γd) γ r id c b (PhaseAt (fun C => SimIdleS C s) s.outbox) (stepLastEv Λ))
  isplitl [Hgh]
  · iintro ⟨%Hok, Hc⟩; iframe Hgh; isplitl [Hc]
    · iexists b; isplitr; · ipureintro; exact fun h => h
      iexact Hc
    ipureintro; exact Hok
  iapply trCapB_gateNone γd γ r id c b _ _ _ _ (fun C cs P h => simIdle_phaseAt C s cs P h)
  iframe Hc
  ipureintro; exact outOk_self s

/-- **The closing wand's capability from a local path's family**, at an end state `s'` whose server
part is `s`'s, the share re-ordered: raft's ghost state, the idle capability and `OutTrStep`.
(Implementation step 2) With the step's `OutTyStep` (the end state in scope if `s` is, `hs`) and the
flag at least the step's first one. -/
theorem lineF_close (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s s' : NState)
    (Λ : Option TraceEv → Prop) (bt : Bool) (hS : ∀ C, SimIdleS C s = SimIdleS C s')
    (hs : TrScope s → TrScope s') :
    lineF (GF := GF) γ md c r id s (fun C => SimIdleS C s) Λ bt s'.outbox ⊢
      |={⊤}=> ownStepGhost γ md c id s ∗
        (⌜OutTyStep s s'⌝ ∗ ∃ b : Bool, ⌜bt = true → b = true⌝ ∗
          trCapB s.gh.tr γ r id c b (fun C => SimIdle C s') Λ) ∗
        ⌜OutTrStep s s'⌝ := by
  unfold lineF
  iintro ⟨Hgh, ⟨%b, %hb, H⟩, %Hok⟩
  imod trFam_idle s.gh.tr γ r id c b s s' Λ hS $$ H with H
  imodintro
  iframe Hgh
  isplitl [H]
  · isplitr; · ipureintro; exact outTyStep_of_outOk Hok hs
    iexists b; isplitr; · ipureintro; exact hb
    iexact H
  ipureintro; exact outTrStep_of_outOk Hok

/-! ## (Implementation step 2) The families that answer reads

A leader's response paths queue read-index responses (`"#Hghresp"`, `"#Hgrlresp"`), untraced, at gates
that say nothing of the read they answer, so `OutOk`'s `TrScope s → TrOutMsg x` cannot be proved at the
gate. Their families are indexed by the outbox without its responses (`rirFilter`, which the traced
family does not see: `pendAbs_rirFilter`), and the close puts them back (`lineF_unfilter`) from the end
state, which queues none in scope (`ReadIdle`). -/

/-- An outbox without its read-index responses. -/
def rirFilter (o : List Msg) : List Msg := o.filter (fun x => !decide (x.ty = .readIndexResp))

theorem rirFilter_snoc_rir {o : List Msg} {x : Msg} (h : x.ty = .readIndexResp) :
    rirFilter (o ++ [x]) = rirFilter o := by
  simp [rirFilter, List.filter_append, h]

theorem rirFilter_snoc {o : List Msg} {x : Msg} (h : x.ty ≠ .readIndexResp) :
    rirFilter (o ++ [x]) = rirFilter o ++ [x] := by
  simp [rirFilter, List.filter_append, h]

theorem pendAbs_rirFilter (C : List w64) (o : List Msg) : pendAbs C (rirFilter o) = pendAbs C o := by
  induction o with
  | nil => rfl
  | cons x o ih =>
    unfold rirFilter at ih ⊢
    rw [List.filter_cons]
    by_cases h : x.ty = .readIndexResp
    · have hn := msgAbs_untraced C C.length x (by rw [h]; rfl)
      simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [ih]; unfold pendAbs; rw [List.filterMap_cons, hn]
    · simp only [h, decide_false, Bool.not_false, ↓reduceIte]
      unfold pendAbs at ih ⊢; rw [List.filterMap_cons, List.filterMap_cons, ih]

theorem trFam_rirFilter (tr : Option GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (b : Bool)
    (Φs : List w64 → ServerC → Prop) (Λ : Option TraceEv → Prop) (o : List Msg) :
    trFam (GF := GF) tr γ r id c b Φs Λ (rirFilter o) = trFam tr γ r id c b Φs Λ o := by
  unfold trFam PhaseAt
  simp only [pendAbs_rirFilter]

/-- The family at the outbox without its read-index responses. -/
theorem lineF_filter (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (Φs : List w64 → ServerC → Prop) (Λ : Option TraceEv → Prop) (bt : Bool) (o : List Msg) :
    lineF (GF := GF) γ md c r id s Φs Λ bt o ⊢ lineF γ md c r id s Φs Λ bt (rirFilter o) := by
  unfold lineF
  simp only [trFam_rirFilter]
  iintro ⟨Hgh, Hf, %Hok⟩
  iframe Hgh Hf
  ipureintro
  intro x hx
  exact Hok x (List.mem_filter.1 hx).1

/-- The family back at the whole outbox, its read-index responses `s`'s when `s` is in scope. -/
theorem lineF_unfilter (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (Φs : List w64 → ServerC → Prop) (Λ : Option TraceEv → Prop) (bt : Bool) (o : List Msg)
    (hri : TrScope s → ∀ x ∈ o, x.ty = .readIndexResp → x ∈ s.outbox) :
    lineF (GF := GF) γ md c r id s Φs Λ bt (rirFilter o) ⊢ lineF γ md c r id s Φs Λ bt o := by
  unfold lineF
  simp only [trFam_rirFilter]
  iintro ⟨Hgh, Hf, %Hok⟩
  iframe Hgh Hf
  ipureintro
  intro x hx
  by_cases h : x.ty = .readIndexResp
  · by_cases hs : TrScope s
    · exact .inl (hri hs x hx h)
    · exact .inr ⟨Msg.trOk_of_untraced (by rw [h]; rfl), fun h' => absurd h' hs⟩
  · exact Hok x (List.mem_filter.2 ⟨hx, by simp [h]⟩)

/-- A read-index response's gate on a filtered family: no line, the family unchanged. -/
theorem lineF_rir (γd : GName) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (X : NState)
    (Φs : List w64 → ServerC → Prop) (Λ : Option TraceEv → Prop) (bt : Bool) (mm : Msg) (o : List Msg)
    (htr : X.gh.tr = some γd) (hmm : mm.ty = .readIndexResp) :
    lineF (GF := GF) γ md c r id X Φs Λ bt (rirFilter o) ⊢
      HookGateOpt X.gh.tr r none (lineF γ md c r id X Φs Λ bt (rirFilter (o ++ [mm]))) := by
  rw [rirFilter_snoc_rir hmm]
  unfold lineF
  rw [htr]
  iintro ⟨Hgh, ⟨%b, %hb, Hf⟩, %Hok⟩
  unfold trFam
  iapply hookGateOpt_mono (some γd) r none
    iprop((ownStepGhost γ md c id X ∗ ⌜OutOk X (rirFilter o)⌝) ∗
      trCapB (some γd) γ r id c b (PhaseAt Φs (rirFilter o)) Λ)
  isplitr
  · iintro ⟨⟨Hgh, %Hok'⟩, Hc⟩
    iframe Hgh
    isplitl [Hc]
    · iexists b; isplitr; · ipureintro; exact hb
      iexact Hc
    ipureintro; exact Hok'
  iapply trCapB_gateNone γd γ r id c b _ _ Λ _ (fun _ _ _ h => h)
  iframe Hgh Hf
  ipureintro; exact Hok

end ghost

end EtcdGrove
end Perennial
