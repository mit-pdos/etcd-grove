/-
Lean-first (no Rocq counterpart).

# The reached states are bounded (layer C, 2026-11-09)

Part 2 of what `CheckTrace`'s search needs (`notes/trace-validation-plan.md`, Q10): every state of the
trace specification reachable from `TraceInit` (`Trace.Reach`) meets the actions' bounds
(`State.SearchOk`), proved here (`Trace.Valid.reach_searchOk`) by induction on `Trace.Reach` over every
action `Trace.next` takes, from what `NewTrace` establishes (`Trace.Valid`), the lines in scope
(`Trace.LinesInScope`) and one bound the trace's events do not give, the lengths of their configuration
lists (`Trace.ConfsBounded`: raft's have three ids).

The invariant (`State.Inv K`): every number of the state below `K` (terms, logs, commit indices,
progress, the configurations' sizes, the bags' total count, the reconfiguration count; the messages'
fields the receivers copy), the bags without duplicates and with positive counts, no pre-vote message
or snapshot, every message's source a server (so a server's granted votes, a sorted list of servers,
are no more than the servers). A step at a line keeps it at `K`, one to the next line at `K + 1`
(a send, a client request, a timeout, a configuration applied: each adds at most one), so a state at
line `l` has it at `numBound + l`, far below the actions' bounds (`l ≤ len + 1 < numBound + 1`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Frame
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.TraceBuild

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

/-! ## What the actions need of a reached state -/

/-- Every line outside the bootstrap of a kind the workload logs (`Line.InScope`: no `ChangeConf`, no
`InitState`, no `MsgSnap` sent). -/
def Trace.LinesInScope (tr : Trace) : Prop :=
  ∀ l, 1 ≤ l → l ≤ tr.len → tr.bootstrap.getD (l - 1) false = false → (tr.line l).InScope

/-- The bounds the actions need of a state (`State.ActOk` but its flags, which every reached state has
off: `Trace.Valid.reach_frame`): the pending bag `Bag.Ok`, the two bags' total counts below `2^63`, the
reconfiguration count below `2^63 - 1`, and of every server: its log below `2^62 - 1`, its granted
votes and configuration below `2^62`, its term below `2^63 - 1`, its progress in `[0, 2^62 - 1)`. -/
def State.Bounds (st : State) : Prop :=
  st.pendingMessages.Ok ∧
  (((st.pendingMessages.map Prod.snd).sum + (st.messages.map Prod.snd).sum : Nat) : Int) < 2 ^ 63 ∧
  st.reconfigCount + 1 < 2 ^ 63 ∧
  ∀ i ∈ st.server, (st.s i).log.length + 1 < 2 ^ 62 ∧ (st.s i).votesGranted.length < 2 ^ 62 ∧
    (st.s i).currentTerm < 2 ^ 63 - 1 ∧ (st.getConfig i).length < 2 ^ 62 ∧
    ∀ j, 0 ≤ (st.s i).matchIndex j ∧ (st.s i).matchIndex j + 1 < 2 ^ 62

theorem State.Bounds.actOk {st : State} (h1 : st.preVote = false) (h2 : st.checkQuorum = false)
    (h : st.Bounds) : st.ActOk := ⟨h1, h2, h⟩

/-- What the actions need of a reached state beyond what every reached state has
(`Trace.Valid.reach_frame`): the bounds (`State.Bounds`) and the messages' (`State.MsgsOk`: the bag
`Bag.Ok`, no pre-vote message or snapshot, `prevLogIndex` in `[0, 2^62 - 1)`, entries and the
destination's log below `2^62`). -/
def State.SearchOk (st : State) : Prop := st.Bounds ∧ st.MsgsOk

/-! ## The premise on the events' configuration lists -/

/-- An event's configuration lists shorter than `numBound` (raft's: three ids): its `conf`'s incoming
list (`conf.1`; the outgoing list, `conf.2`, is not bounded: no configuration the specification applies
comes from it) and a configuration change's `newconf`. -/
def Event.ConfsBounded (e : Event) : Prop :=
  (e.conf.1.length : Int) < numBound ∧
  ∀ nc, (e.prop.bind EventProps.cc).bind EventConfChange.newconf = some nc → (nc.length : Int) < numBound

/-- Every line's event has `Event.ConfsBounded`: the configurations' sizes, which `Event.Bounded` does
not bound, come from these lists. Only the bootstrap lines' lists reach a configuration (`newTraceWith`'s
initial configurations and bootstrap log); every line is bounded, which is simpler to state and costs
`Main` nothing. -/
def Trace.ConfsBounded (tr : Trace) : Prop := ∀ ln ∈ tr.lines, ln.ev.ConfsBounded

/-- How a client gets `Trace.ConfsBounded` of the trace `NewTrace` built: from its events. -/
theorem Trace.confsBounded_of_newTrace {evs : List Event} {tr : Trace} (h : newTrace evs = .ok tr)
    (hc : ∀ e ∈ evs, e.ConfsBounded) : tr.ConfsBounded :=
  fun ln hln => hc _ (lines_ev_mem (newTraceWith_ok evs false false tr h).1 hln)

/-! ## The invariant -/

/-- A configuration entry's incoming list within `K`. -/
def Entry.ConfOk (K : Int) (e : Entry) : Prop := ∀ nc ln, e.value = .conf nc ln → (nc.length : Int) ≤ K

/-- A server's numbers within `K`, its granted votes a sorted list of servers `S`. -/
structure Server.Inv (K : Int) (S : SetIds) (v : Server) : Prop where
  log_len : (v.log.length : Int) ≤ K
  log_conf : ∀ e ∈ v.log, e.ConfOk K
  vg_sub : ∀ x ∈ v.votesGranted, x ∈ S
  vg_sorted : v.votesGranted.Pairwise (· < ·)
  term : v.currentTerm ≤ K
  cfg : (v.config.incoming.length : Int) ≤ K
  commit0 : 0 ≤ v.commitIndex
  commit : v.commitIndex ≤ K
  match0 : ∀ j, 0 ≤ v.matchIndex j
  matchK : ∀ j, v.matchIndex j ≤ K

/-- A message of the workload's kinds (no pre-vote message, no snapshot) from a server of `S`, the
fields a receiver copies within `K`. -/
structure Msg.Inv (K : Int) (S : SetIds) (m : Msg) : Prop where
  not_pvq : m.type ≠ .preVoteRequest
  not_pvr : m.type ≠ .preVoteResponse
  not_snap : m.subtype ≠ "snapshot"
  prev0 : 0 ≤ m.prevLogIndex
  prev : m.prevLogIndex + m.entries.length ≤ K
  term : m.term ≤ K
  commit0 : 0 ≤ m.commitIndex
  commit : m.commitIndex ≤ K
  match0 : 0 ≤ m.matchIndex
  matchK : m.matchIndex ≤ K
  ents : ∀ e ∈ m.entries, e.ConfOk K
  src : m.source ∈ S

/-- A bag's total count. -/
def Bag.total (b : Bag) : Nat := (b.map Prod.snd).sum

/-- A bag without duplicates, its counts positive, its messages `Msg.Inv`. -/
structure Bag.Inv (K : Int) (S : SetIds) (b : Bag) : Prop where
  nodup : (b.map Prod.fst).Nodup
  pos : ∀ it ∈ b, 0 < it.2
  msg : ∀ it ∈ b, it.1.Inv K S

/-- The invariant of a reached state, `K` its bound. -/
structure State.Inv (K : Int) (st : State) : Prop where
  srv : ∀ i, (st.s i).Inv K st.server
  pend : Bag.Inv K st.server st.pendingMessages
  msgs : Bag.Inv K st.server st.messages
  total : ((Bag.total st.pendingMessages + Bag.total st.messages : Nat) : Int) ≤ K
  rc : st.reconfigCount ≤ K

theorem Entry.ConfOk.mono {K K' : Int} {e : Entry} (h : e.ConfOk K) (hK : K ≤ K') : e.ConfOk K' :=
  fun nc ln hv => Int.le_trans (h nc ln hv) hK

theorem Server.Inv.mono {K K' : Int} {S : SetIds} {v : Server} (h : v.Inv K S) (hK : K ≤ K') : v.Inv K' S where
  log_len := Int.le_trans h.log_len hK
  log_conf := fun e he => (h.log_conf e he).mono hK
  vg_sub := h.vg_sub
  vg_sorted := h.vg_sorted
  term := Int.le_trans h.term hK
  cfg := Int.le_trans h.cfg hK
  commit0 := h.commit0
  commit := Int.le_trans h.commit hK
  match0 := h.match0
  matchK := fun j => Int.le_trans (h.matchK j) hK

theorem Msg.Inv.mono {K K' : Int} {S : SetIds} {m : Msg} (h : m.Inv K S) (hK : K ≤ K') : m.Inv K' S :=
  { h with
    prev := Int.le_trans h.prev hK
    term := Int.le_trans h.term hK
    commit := Int.le_trans h.commit hK
    matchK := Int.le_trans h.matchK hK
    ents := fun e he => (h.ents e he).mono hK }

theorem Bag.Inv.mono {K K' : Int} {S : SetIds} {b : Bag} (h : Bag.Inv K S b) (hK : K ≤ K') : Bag.Inv K' S b :=
  { h with msg := fun it hit => (h.msg it hit).mono hK }

theorem State.Inv.mono {K K' : Int} {st : State} (h : st.Inv K) (hK : K ≤ K') : st.Inv K' where
  srv := fun i => (h.srv i).mono hK
  pend := h.pend.mono hK
  msgs := h.msgs.mono hK
  total := Int.le_trans h.total hK
  rc := Int.le_trans h.rc hK

/-! ## Bags -/

theorem Bag.total_nil : Bag.total [] = 0 := rfl

theorem Bag.total_cons (x : Msg × Nat) (b : Bag) : Bag.total (x :: b) = x.2 + Bag.total b := by
  simp [Bag.total]

theorem Bag.total_append (b c : Bag) : Bag.total (b ++ c) = Bag.total b + Bag.total c := by
  simp [Bag.total]

theorem Bag.le_total {b : Bag} {it : Msg × Nat} (h : it ∈ b) : it.2 ≤ Bag.total b := by
  induction b with
  | nil => simp at h
  | cons x b ih =>
    rw [Bag.total_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

theorem Bag.map_id_of_not_mem (m : Msg) (n : Nat) :
    ∀ b : Bag, (∀ it ∈ b, it.1 ≠ m) →
      b.map (fun it => if it.1 == m then (it.1, it.2 + n) else it) = b
  | [], _ => rfl
  | x :: b, h => by
    rw [List.map_cons, Bag.map_id_of_not_mem m n b (fun it hit => h it (List.mem_cons_of_mem _ hit))]
    have : (x.1 == m) = false := by simpa using h x List.mem_cons_self
    simp [this]

theorem Bag.total_map_add_le (m : Msg) (n : Nat) :
    ∀ b : Bag, (b.map Prod.fst).Nodup →
      Bag.total (b.map (fun it => if it.1 == m then (it.1, it.2 + n) else it)) ≤ Bag.total b + n
  | [], _ => by simp [Bag.total]
  | x :: b, h => by
    rw [List.map_cons, List.nodup_cons] at h
    rw [List.map_cons, Bag.total_cons, Bag.total_cons]
    by_cases hx : x.1 = m
    · have hnm : ∀ it ∈ b, it.1 ≠ m := by
        intro it hit heq; exact h.1 (List.mem_map.2 ⟨it, hit, by rw [heq, hx]⟩)
      rw [Bag.map_id_of_not_mem m n b hnm]
      simp [hx]; omega
    · have := Bag.total_map_add_le m n b h.2
      have hx' : (x.1 == m) = false := by simpa using hx
      simp only [hx', Bool.false_eq_true, ite_false]; omega

theorem Bag.Inv.add {K : Int} {S : SetIds} {b : Bag} {m : Msg} {n : Nat} (h : Bag.Inv K S b) (hm : m.Inv K S)
    (hn : 0 < n) : Bag.Inv K S (b.add m n) ∧ Bag.total (b.add m n) ≤ Bag.total b + n := by
  unfold Bag.add
  split
  · refine ⟨⟨?_, ?_, ?_⟩, Bag.total_map_add_le m n b h.nodup⟩
    · rw [List.map_map]
      have : (Prod.fst ∘ fun it : Msg × Nat => if it.1 == m then (it.1, it.2 + n) else it) = Prod.fst := by
        funext it; simp only [Function.comp]; split <;> rfl
      rw [this]; exact h.nodup
    · intro it hit
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hit
      split
      · omega
      · exact h.pos x hx
    · intro it hit
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hit
      split
      · exact h.msg x hx
      · exact h.msg x hx
  · rename_i hany
    refine ⟨⟨?_, ?_, ?_⟩, by rw [Bag.total_append]; simp [Bag.total]⟩
    · rw [List.map_append, List.nodup_append]
      refine ⟨h.nodup, by simp, ?_⟩
      intro a ha b' hb'
      simp at hb'; subst hb'
      intro heq; subst heq
      obtain ⟨it, hit, rfl⟩ := List.mem_map.1 ha
      exact hany (List.any_eq_true.2 ⟨it, hit, by simp⟩)
    · intro it hit
      rcases List.mem_append.1 hit with hit | hit
      · exact h.pos it hit
      · simp at hit; subst hit; exact hn
    · intro it hit
      rcases List.mem_append.1 hit with hit | hit
      · exact h.msg it hit
      · simp at hit; subst hit; exact hm

theorem Bag.sub_cons (x : Msg × Nat) (b : Bag) (m : Msg) (n : Nat) :
    Bag.sub (x :: b) m n =
      if x.1 == m then (if x.2 > n then (x.1, x.2 - n) :: b.sub m n else b.sub m n) else x :: b.sub m n := by
  unfold Bag.sub
  rw [List.filterMap_cons]
  by_cases h1 : (x.1 == m) = true
  · by_cases h2 : x.2 > n
    · simp [h1, h2]
    · simp [h1, h2]
  · simp [h1]

theorem Bag.sub_keys_sublist (m : Msg) (n : Nat) :
    ∀ b : Bag, ((b.sub m n).map Prod.fst).Sublist (b.map Prod.fst)
  | [] => by simp [Bag.sub]
  | x :: b => by
    rw [Bag.sub_cons]
    have ih := Bag.sub_keys_sublist m n b
    split
    · split
      · simp only [List.map_cons]; exact ih.cons_cons _
      · simp only [List.map_cons]; exact ih.cons _
    · simp only [List.map_cons]; exact ih.cons_cons _

theorem Bag.mem_sub (m : Msg) (n : Nat) :
    ∀ (b : Bag) (it : Msg × Nat), it ∈ b.sub m n → ∃ it0 ∈ b, it.1 = it0.1 ∧ (it = it0 ∨ (n < it0.2 ∧ it.2 = it0.2 - n))
  | [], it, h => by simp [Bag.sub] at h
  | x :: b, it, h => by
    rw [Bag.sub_cons] at h
    split at h
    · split at h
      · rename_i hgt
        rcases List.mem_cons.1 h with rfl | h
        · exact ⟨x, List.mem_cons_self, rfl, .inr ⟨hgt, rfl⟩⟩
        · obtain ⟨it0, h0, h1, h2⟩ := Bag.mem_sub m n b it h
          exact ⟨it0, List.mem_cons_of_mem _ h0, h1, h2⟩
      · obtain ⟨it0, h0, h1, h2⟩ := Bag.mem_sub m n b it h
        exact ⟨it0, List.mem_cons_of_mem _ h0, h1, h2⟩
    · rcases List.mem_cons.1 h with rfl | h
      · exact ⟨it, List.mem_cons_self, rfl, .inl rfl⟩
      · obtain ⟨it0, h0, h1, h2⟩ := Bag.mem_sub m n b it h
        exact ⟨it0, List.mem_cons_of_mem _ h0, h1, h2⟩

theorem Bag.Inv.sub {K : Int} {S : SetIds} {b : Bag} (h : Bag.Inv K S b) (m : Msg) (n : Nat) :
    Bag.Inv K S (b.sub m n) where
  nodup := (Bag.sub_keys_sublist m n b).nodup h.nodup
  pos := by
    intro it hit
    obtain ⟨it0, h0, -, h2⟩ := Bag.mem_sub m n b it hit
    rcases h2 with rfl | ⟨hlt, heq⟩
    · exact h.pos _ h0
    · omega
  msg := by
    intro it hit
    obtain ⟨it0, h0, h1, -⟩ := Bag.mem_sub m n b it hit
    rw [h1]; exact h.msg _ h0

theorem Bag.total_sub_le (m : Msg) (n : Nat) : ∀ b : Bag, Bag.total (b.sub m n) ≤ Bag.total b
  | [] => by simp [Bag.sub, Bag.total]
  | x :: b => by
    rw [Bag.sub_cons]
    have := Bag.total_sub_le m n b
    split
    · split
      · rw [Bag.total_cons, Bag.total_cons]; simp only; omega
      · rw [Bag.total_cons]; omega
    · rw [Bag.total_cons, Bag.total_cons]; omega

theorem Bag.sub_of_not_mem (m : Msg) (n : Nat) : ∀ b : Bag, (∀ it ∈ b, it.1 ≠ m) → b.sub m n = b
  | [], _ => rfl
  | x :: b, h => by
    rw [Bag.sub_cons, Bag.sub_of_not_mem m n b (fun it hit => h it (List.mem_cons_of_mem _ hit))]
    have : (x.1 == m) = false := by simpa using h x List.mem_cons_self
    simp [this]

theorem Bag.total_sub_eq (m : Msg) (n c : Nat) (hn : n ≤ c) :
    ∀ b : Bag, (b.map Prod.fst).Nodup → (m, c) ∈ b → Bag.total (b.sub m n) + n = Bag.total b
  | [], _, h => by simp at h
  | x :: b, hnd, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [Bag.sub_cons, Bag.total_cons]
    by_cases hx : x.1 = m
    · have hnm : ∀ it ∈ b, it.1 ≠ m := by
        intro it hit heq; exact hnd.1 (List.mem_map.2 ⟨it, hit, by rw [heq, hx]⟩)
      have hxc : x = (m, c) := by
        rcases List.mem_cons.1 h with h | h
        · exact h.symm
        · exact absurd rfl (hnm _ h)
      subst hxc
      rw [Bag.sub_of_not_mem m n b hnm]
      simp only [beq_self_eq_true, ite_true]
      split
      · rw [Bag.total_cons]; simp only; omega
      · rename_i hle; omega
    · have hmem : (m, c) ∈ b := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd (by rw [← h]) hx
        · exact h
      have := Bag.total_sub_eq m n c hn b hnd.2 hmem
      have hx' : (x.1 == m) = false := by simpa using hx
      simp only [hx', Bool.false_eq_true, ite_false, Bag.total_cons]
      omega

theorem Bag.mem_sub_of_ne (m : Msg) (n : Nat) :
    ∀ (b : Bag) (it : Msg × Nat), it ∈ b → it.1 ≠ m → it ∈ b.sub m n
  | [], it, h, _ => by simp at h
  | x :: b, it, h, hne => by
    rw [Bag.sub_cons]
    have ih := fun h' => Bag.mem_sub_of_ne m n b it h' hne
    rcases List.mem_cons.1 h with rfl | h
    · have : (it.1 == m) = false := by simpa using hne
      simp [this]
    · split
      · split
        · exact List.mem_cons_of_mem _ (ih h)
        · exact ih h
      · exact List.mem_cons_of_mem _ (ih h)

/-- A message of the bag counted at least once. -/
theorem Bag.Inv.mem_domain {K : Int} {S : SetIds} {b : Bag} {m : Msg} (h : Bag.Inv K S b) (hm : m ∈ b.domain) :
    ∃ c, (m, c) ∈ b ∧ 1 ≤ c := by
  obtain ⟨it, hit, rfl⟩ := List.mem_map.1 hm
  exact ⟨it.2, hit, h.pos it hit⟩

theorem Bag.Inv.msg_of_domain {K : Int} {S : SetIds} {b : Bag} {m : Msg} (h : Bag.Inv K S b)
    (hm : m ∈ b.domain) : m.Inv K S := by
  obtain ⟨it, hit, rfl⟩ := List.mem_map.1 hm
  exact h.msg it hit

theorem Bag.Inv.without {K : Int} {S : SetIds} {b : Bag} {m : Msg} (h : Bag.Inv K S b) (hm : m ∈ b.domain) :
    Bag.Inv K S (b.without m) ∧ Bag.total (b.without m) + 1 = Bag.total b := by
  obtain ⟨c, hc, h1⟩ := h.mem_domain hm
  exact ⟨h.sub m 1, Bag.total_sub_eq m 1 c h1 b h.nodup hc⟩

/-- `b (-) c` of a sub-bag `c` of `b`. -/
theorem Bag.Inv.minus {K : Int} {S : SetIds} :
    ∀ (c b : Bag), Bag.Inv K S b → (c.map Prod.fst).Nodup → (∀ it ∈ c, it ∈ b) →
      Bag.Inv K S (b.minus c) ∧ Bag.total (b.minus c) + Bag.total c = Bag.total b
  | [], b, h, _, _ => ⟨h, by simp [Bag.minus, Bag.total]⟩
  | x :: c, b, h, hnd, hsub => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hb' := h.sub x.1 x.2
    have hsub' : ∀ it ∈ c, it ∈ b.sub x.1 x.2 := by
      intro it hit
      refine Bag.mem_sub_of_ne _ _ _ _ (hsub it (List.mem_cons_of_mem _ hit)) ?_
      intro heq; exact hnd.1 (List.mem_map.2 ⟨it, hit, heq⟩)
    have ih := Bag.Inv.minus c _ hb' hnd.2 hsub'
    have htot := Bag.total_sub_eq x.1 x.2 x.2 (Nat.le_refl _) b h.nodup (hsub x List.mem_cons_self)
    have : b.minus (x :: c) = (b.sub x.1 x.2).minus c := by simp [Bag.minus, List.foldl_cons]
    rw [this, Bag.total_cons]
    exact ⟨ih.1, by omega⟩

/-- `b (+) c`. -/
theorem Bag.Inv.plus {K : Int} {S : SetIds} :
    ∀ (c b : Bag), Bag.Inv K S b → Bag.Inv K S c →
      Bag.Inv K S (b.plus c) ∧ Bag.total (b.plus c) ≤ Bag.total b + Bag.total c
  | [], b, h, _ => ⟨h, by simp [Bag.plus, Bag.total]⟩
  | x :: c, b, h, hc => by
    have ha := h.add (hc.msg x List.mem_cons_self) (hc.pos x List.mem_cons_self)
    have hc' : Bag.Inv K S c :=
      ⟨(List.nodup_cons.1 (by simpa using hc.nodup)).2, fun it hit => hc.pos it (List.mem_cons_of_mem _ hit),
        fun it hit => hc.msg it (List.mem_cons_of_mem _ hit)⟩
    have ih := Bag.Inv.plus c _ ha.1 hc'
    have : b.plus (x :: c) = (b.add x.1 x.2).plus c := by simp [Bag.plus, List.foldl_cons]
    rw [this, Bag.total_cons]
    exact ⟨ih.1, by omega⟩

theorem Bag.Inv.filterMsgs {K : Int} {S : SetIds} {b : Bag} (h : Bag.Inv K S b) (p : Msg → Bool) :
    Bag.Inv K S (b.filterMsgs p) where
  nodup := (List.Sublist.map Prod.fst (List.filter_sublist)).nodup h.nodup
  pos := fun it hit => h.pos it (List.mem_filter.1 hit).1
  msg := fun it hit => h.msg it (List.mem_filter.1 hit).1

/-! ## A state's updates -/

theorem State.Inv.upd {K : Int} {st : State} {i : ID} {f : Server → Server} (h : st.Inv K)
    (hv : (f (st.s i)).Inv K st.server) : (st.upd i f).Inv K where
  srv := by
    intro j
    simp only [State.upd]
    split
    · exact hv
    · exact h.srv j
  pend := h.pend
  msgs := h.msgs
  total := h.total
  rc := h.rc

theorem State.Inv.send {K : Int} {st : State} {m : Msg} (h : st.Inv K) (hm : m.Inv (K + 1) st.server) :
    (st.send m).Inv (K + 1) := by
  have hp := (h.pend.mono (Int.le_add_of_nonneg_right (by decide))).add hm Nat.one_pos
  have ht := h.total
  refine ⟨fun i => (h.srv i).mono (by omega), hp.1, h.msgs.mono (by omega), ?_,
    Int.le_trans h.rc (Int.le_add_of_nonneg_right (by decide))⟩
  simp only [State.send, Bag.with]
  have := hp.2
  omega

theorem State.Inv.discard {K : Int} {st : State} (m : Msg) (h : st.Inv K) : (st.discard m).Inv K := by
  refine ⟨h.srv, h.pend, h.msgs.sub m 1, ?_, h.rc⟩
  simp only [State.discard, Bag.without]
  have := Bag.total_sub_le m 1 st.messages
  have := h.total
  omega

theorem State.Inv.reply {K : Int} {st : State} {resp m : Msg} (h : st.Inv K) (hm : m ∈ st.messages.domain)
    (hr : resp.Inv K st.server) : (st.reply resp m).Inv K := by
  have hp := h.pend.add hr Nat.one_pos
  have hw := h.msgs.without hm
  refine ⟨h.srv, hp.1, hw.1, ?_, h.rc⟩
  simp only [State.reply, Bag.with]
  have := hp.2
  have := hw.2
  have := h.total
  omega

theorem State.Inv.ready {K : Int} {st : State} (i : ID) (h : st.Inv K) : (st.ready i).Inv K := by
  have hF := h.pend.filterMsgs (fun m => m.source == i)
  have hpl := Bag.Inv.plus st.messages _ hF h.msgs
  have hmi := Bag.Inv.minus _ st.pendingMessages h.pend hF.nodup
    (fun it hit => (List.mem_filter.1 hit).1)
  refine ⟨?_, hmi.1, hpl.1, ?_, h.rc⟩
  · intro j
    simp only [State.ready, State.persistState, State.upd]
    split
    · exact { h.srv i with }
    · exact h.srv j
  · simp only [State.ready, State.persistState, State.upd, State.pendingFrom]
    have := hpl.2
    have := hmi.2
    have := h.total
    omega

/-! ## Pure facts the actions use -/

theorem subSeq_some {s l : List Entry} {a c : Int} (h : subSeq s a c = some l) :
    (∀ x ∈ l, x ∈ s) ∧ (l = [] ∨ (1 ≤ a ∧ a - 1 + l.length = c ∧ c ≤ s.length)) := by
  unfold subSeq at h
  split at h
  · cases h; simp
  · split at h
    · cases h
    · cases h
      rename_i h1 h2
      refine ⟨fun x hx => List.mem_of_mem_drop (List.mem_of_mem_take hx), .inr ⟨by omega, ?_, by omega⟩⟩
      simp only [List.length_take, List.length_drop]
      omega

theorem subSeqM_ok {s l : List Entry} {a c : Int} (h : subSeqM s a c = .ok l) : subSeq s a c = some l := by
  unfold subSeqM at h
  split at h
  · cases h; assumption
  · cases h

theorem foldl_range_le (n : Nat) (p : Nat → Bool) :
    ∀ (l : List Nat) (acc : Nat), (∀ x ∈ l, x + 1 ≤ n) → acc ≤ n →
      l.foldl (fun acc k => if p k then k + 1 else acc) acc ≤ n
  | [], acc, _, h => h
  | x :: l, acc, hl, h => by
    rw [List.foldl_cons]
    refine foldl_range_le n p l _ (fun y hy => hl y (List.mem_cons_of_mem _ hy)) ?_
    split
    · exact hl x List.mem_cons_self
    · exact h

theorem SetIds.add_sorted (s : SetIds) (j : ID) : (s.add j).Pairwise (· < ·) := SetIds.mk_sorted _

theorem SetIds.mem_add {s : SetIds} {j x : ID} (h : x ∈ s.add j) : x ∈ s ∨ x = j := by
  unfold SetIds.add SetIds.union at h
  rw [SetIds.mem_mk] at h
  simpa using h

theorem Entry.confOk_of_value {K : Int} {e : Entry} (h : ∀ nc ln, e.value ≠ .conf nc ln) : e.ConfOk K :=
  fun nc ln hv => absurd hv (h nc ln)

/-! ## Server updates -/

theorem State.Inv.becomeFollowerOfTerm {K : Int} {st : State} (h : st.Inv K) (i : ID) {t : Int} (ht : t ≤ K) :
    (st.becomeFollowerOfTerm i t).Inv K :=
  h.upd { h.srv i with term := ht }

theorem State.Inv.commitTo {K : Int} {st : State} (h : st.Inv K) (i : ID) {c : Int} (hc : c ≤ K) :
    (st.commitTo i c).Inv K := by
  have hv := h.srv i
  exact h.upd { hv with
    commit0 := Int.le_trans hv.commit0 (Int.le_max_left _ _)
    commit := Int.max_le.2 ⟨hv.commit, hc⟩ }

theorem State.Inv.replicate {K : Int} {st : State} (h : st.Inv K) (i : ID) (val : Value) (typ : EntryType)
    (hval : ∀ nc ln, val = .conf nc ln → (nc.length : Int) ≤ K + 1) :
    (st.replicate i val typ).Inv (K + 1) := by
  have h1 := h.mono (K' := K + 1) (by omega)
  have hv := h1.srv i
  unfold State.replicate
  refine h1.upd { hv with log_len := ?_, log_conf := ?_ }
  · simp only [List.length_append, List.length_singleton]; have := (h.srv i).log_len; omega
  · intro e he
    rcases List.mem_append.1 he with he | he
    · exact hv.log_conf e he
    · simp at he; subst he; exact hval

/-- `ApplyConfigUpdate`'s configuration comes from the log. -/
theorem State.Inv.applyConfigUpdate {K : Int} {st : State} (h : st.Inv K) (i : ID) (k : Nat) :
    (st.applyConfigUpdate i k).Inv K := by
  unfold State.applyConfigUpdate
  have hv := h.srv i
  have hcf : ∀ nc ln, ((st.s i).log[k - 1]?).map Entry.value = some (.conf nc ln) → (nc.length : Int) ≤ K := by
    intro nc ln heq
    rw [Option.map_eq_some_iff] at heq
    obtain ⟨e, he, hev⟩ := heq
    exact hv.log_conf e (List.mem_of_getElem? he) nc ln hev
  have hK : 0 ≤ K := Int.le_trans hv.commit0 hv.commit
  generalize ((st.s i).log[k - 1]?).map Entry.value = o at hcf
  rcases o with _ | ⟨_ | _ | ⟨nc, ln⟩⟩
  all_goals try simp only
  all_goals first
    | exact h.upd { hv with cfg := hcf _ _ rfl }
    | exact h.upd { hv with cfg := by simp; omega }

/-! ## The actions a line's event takes (one more line: `K + 1`) -/

section actions
variable {K : Int} {st s : State}

theorem State.timeout_inv {i : ID} (h : st.Inv K) (ht : st.timeout i = some s) : s.Inv (K + 1) := by
  unfold State.timeout at ht
  try dsimp only at ht
  split at ht
  · injection ht with ht; subst ht
    have h1 := h.mono (K' := K + 1) (by omega)
    have hv := h1.srv i
    refine h1.upd { hv with vg_sub := by simp, vg_sorted := by simp, term := ?_ }
    have := (h.srv i).term; simp only; omega
  · cases ht

theorem State.preTimeout_inv {i : ID} (h : st.Inv K) (ht : st.preTimeout i = some s) : s.Inv K := by
  unfold State.preTimeout at ht
  try dsimp only at ht
  split at ht
  · injection ht with ht; subst ht
    exact h.upd { h.srv i with vg_sub := by simp, vg_sorted := by simp }
  · cases ht

theorem State.requestVote_inv {i j : ID} (h : st.Inv K) (hi : i ∈ st.server) (ht : st.requestVote i j = some s) :
    s.Inv (K + 1) := by
  have hT := (h.srv i).term
  have hK0 : 0 ≤ K := Int.le_trans (h.srv i).commit0 (h.srv i).commit
  unfold State.requestVote at ht
  try dsimp only at ht
  split at ht
  · split at ht
    · injection ht with ht; subst ht
      exact h.send ⟨by simp, by simp, by simp, by simp, by simp; omega, by simp; omega, by simp, by simp; omega,
        by simp, by simp; omega, by simp, hi⟩
    · injection ht with ht; subst ht
      exact h.send ⟨by simp, by simp, by simp, by simp, by simp; omega, by simp; omega, by simp, by simp; omega,
        by simp, by simp; omega, by simp, hi⟩
  · cases ht

theorem State.requestPreVote_none {i j : ID} (hpv : st.preVote = false) : st.requestPreVote i j = none := by
  unfold State.requestPreVote; simp [hpv]

theorem State.becomeLeader_inv {i : ID} (h : st.Inv K) (ht : st.becomeLeader i = some s) : s.Inv K := by
  unfold State.becomeLeader at ht
  try dsimp only at ht
  split at ht
  · injection ht with ht; subst ht
    have hv := h.srv i
    have hK0 : 0 ≤ K := Int.le_trans hv.commit0 hv.commit
    refine h.upd { hv with match0 := ?_, matchK := ?_ }
    · intro j; simp only; split <;> omega
    · intro j; simp only; split
      · exact hv.log_len
      · omega
  · cases ht

theorem State.clientRequest_inv {i : ID} {v : Int} (h : st.Inv K) (ht : st.clientRequest i v = some s) :
    s.Inv (K + 1) := by
  unfold State.clientRequest at ht
  try dsimp only at ht
  split at ht
  · cases ht
  · injection ht with ht; subst ht
    exact h.replicate i _ _ (fun nc ln hv => by cases hv)

theorem State.advanceCommitIndex_inv {i : ID} (h : st.Inv K) (ht : st.advanceCommitIndex i = some s) :
    s.Inv K := by
  unfold State.advanceCommitIndex at ht
  try dsimp only at ht
  split at ht
  · cases ht
  · injection ht with ht; subst ht
    have hv := h.srv i
    refine h.commitTo i ?_
    split
    · exact Int.le_trans (Int.ofNat_le.2 (foldl_range_le (st.s i).log.length _ (List.range (st.s i).log.length) 0
        (fun x hx => by rw [List.mem_range] at hx; omega) (Nat.zero_le _))) hv.log_len
    · exact hv.commit

theorem State.appendEntriesToSelf_inv {i : ID} (h : st.Inv K) (hi : i ∈ st.server)
    (ht : st.appendEntriesToSelf i = some s) : s.Inv (K + 1) := by
  have hT := (h.srv i).term
  have hK0 : 0 ≤ K := Int.le_trans (h.srv i).commit0 (h.srv i).commit
  have hL := (h.srv i).log_len
  unfold State.appendEntriesToSelf at ht
  try dsimp only at ht
  split at ht
  · cases ht
  · injection ht with ht; subst ht
    exact h.send ⟨by simp, by simp, by simp, by simp, by simp; omega, by simp; omega, by simp, by simp; omega,
      by simp, by simp; omega, by simp, hi⟩

theorem State.appendEntriesInRangeToPeer_inv {sub : String} {i j : ID} {b e : Int} (h : st.Inv K)
    (hi : i ∈ st.server) (hsub : sub ≠ "snapshot") (hb1 : 1 ≤ b) (hbK : b - 1 ≤ K)
    (ht : st.appendEntriesInRangeToPeer sub i j b e = .ok (some s)) : s.Inv (K + 1) := by
  have hv := h.srv i
  have hK0 : 0 ≤ K := Int.le_trans hv.commit0 hv.commit
  unfold State.appendEntriesInRangeToPeer at ht
  simp only [bind, Except.bind, pure, Except.pure] at ht
  split at ht
  · cases ht
  · split at ht
    · cases ht
    · rename_i ents hents
      injection ht with ht; injection ht with ht; subst ht
      obtain ⟨hsub', hlen⟩ := subSeq_some (subSeqM_ok hents)
      refine h.send ⟨by simp, by simp, by simpa using hsub, by simp; omega, ?_, by simp; have := hv.term; omega,
        ?_, ?_, by simp, by simp; omega, ?_, hi⟩
      · simp only
        rcases hlen with hl | hl
        · subst hl; simp; omega
        · have := hv.log_len; omega
      · simp only
        have := hv.commit0; have := hv.match0 j
        split
        · omega
        · split
          · rename_i hs; exact absurd (by simpa using hs) hsub
          · omega
      · simp only
        have := hv.commit; have := hv.matchK j
        split
        · omega
        · split <;> omega
      · intro x hx; exact (hv.log_conf x (hsub' x hx)).mono (by omega)

theorem State.ignoreInLease_inv {m : Msg} (h : st.Inv K) (ht : st.ignoreInLease m = some s) : s.Inv K := by
  unfold State.ignoreInLease at ht
  try dsimp only at ht
  split at ht
  · injection ht with ht; subst ht; exact h.discard m
  · cases ht

theorem State.stepDownToFollower_inv {i : ID} (h : st.Inv K) (ht : st.stepDownToFollower i = some s) :
    s.Inv K := by
  unfold State.stepDownToFollower at ht
  try dsimp only at ht
  split at ht
  · injection ht with ht; subst ht; exact h.becomeFollowerOfTerm i (h.srv i).term
  · cases ht

theorem State.applySimpleConfChange_inv {i : ID} (h : st.Inv K) (ht : st.applySimpleConfChange i = .ok (some s)) :
    s.Inv (K + 1) := by
  have h1 := h.mono (K' := K + 1) (by omega)
  have ha := h1.applyConfigUpdate i
  have hrc : ∀ k, (({ st.applyConfigUpdate i k with reconfigCount := st.reconfigCount + 1 } : State).upd i
      (fun v => { v with pendingConfChangeIndex := 0 })).Inv (K + 1) := by
    intro k
    have hk := ha k
    have hX : ({ st.applyConfigUpdate i k with reconfigCount := st.reconfigCount + 1 } : State).Inv (K + 1) :=
      ⟨hk.srv, hk.pend, hk.msgs, hk.total, by have := h.rc; simp only; omega⟩
    exact hX.upd { hX.srv i with }
  have hfin : ∀ st' : State, st'.Inv (K + 1) → ∀ c : ID → Bool,
      (st'.upd i (fun w => { w with matchIndex := fun j => if c j then w.matchIndex j else 0 })).Inv (K + 1) := by
    intro st' h' c
    have hv := h'.srv i
    refine h'.upd { hv with match0 := ?_, matchK := ?_ }
    · intro j; simp only; split
      · exact hv.match0 j
      · exact Int.le_refl 0
    · intro j; simp only; split
      · exact hv.matchK j
      · have := hv.match0 j; have := hv.matchK j; omega
  unfold State.applySimpleConfChange at ht
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at ht
  repeat' split at ht
  all_goals first
    | (cases ht; done)
    | (injection ht with ht; injection ht with ht; subst ht
       refine hfin _ ?_ _
       first
         | exact ha _
         | exact hrc _)

end actions

/-! ## The handlers of a received message (the same `K`) -/

section handlers
variable {K : Int} {st s : State} {i j : ID} {m : Msg}

theorem State.updateTerm_inv (h : st.Inv K) (hm : m.Inv K st.server) (ht : st.updateTerm i j m = some s) :
    s.Inv K := by
  unfold State.updateTerm at ht
  try dsimp only at ht
  split at ht
  · cases ht
  · injection ht with ht; subst ht; exact h.becomeFollowerOfTerm i hm.term

theorem State.dropStaleResponse_inv (h : st.Inv K) (ht : st.dropStaleResponse i j m = some s) : s.Inv K := by
  unfold State.dropStaleResponse at ht
  try dsimp only at ht
  split at ht
  · cases ht
  · injection ht with ht; subst ht; exact h.discard m

theorem State.handleRequestVoteRequest_inv (h : st.Inv K) (hm : m ∈ st.messages.domain) (hi : i ∈ st.server)
    (ht : st.handleRequestVoteRequest i j m = some s) : s.Inv K := by
  have hT := (h.srv i).term
  have hK0 : 0 ≤ K := Int.le_trans (h.srv i).commit0 (h.srv i).commit
  unfold State.handleRequestVoteRequest at ht
  try dsimp only at ht
  split at ht
  · cases ht
  · injection ht with ht; subst ht
    have hr : ∀ st' : State, st'.Inv K → st'.messages = st.messages → st'.server = st.server →
        ∀ g : Bool, (st'.reply
          { type := .requestVoteResponse, term := (st.s i).currentTerm, voteGranted := g, source := i, dest := j }
          m).Inv K := by
      intro st' h' hms hsv g
      refine h'.reply (by rw [hms]; exact hm) ⟨by simp, by simp, by simp, by simp, by simp; omega, by simp; omega,
        by simp, by simp; omega, by simp, by simp; omega, by simp, by rw [hsv]; exact hi⟩
    split
    · exact hr _ (h.upd { h.srv i with }) rfl rfl _
    · exact hr _ h rfl rfl _

theorem State.handleRequestVoteResponse_inv (h : st.Inv K) (hj : j ∈ st.server)
    (ht : st.handleRequestVoteResponse i j m = some s) : s.Inv K := by
  unfold State.handleRequestVoteResponse at ht
  try dsimp only at ht
  split at ht
  · cases ht
  · injection ht with ht; subst ht
    refine State.Inv.discard m ?_
    split
    · exact h
    · have hv := h.srv i
      refine h.upd { hv with vg_sub := ?_, vg_sorted := ?_ }
      · simp only
        split
        · intro x hx
          rcases SetIds.mem_add hx with hx | rfl
          · exact hv.vg_sub x hx
          · exact hj
        · exact hv.vg_sub
      · simp only
        split
        · exact SetIds.add_sorted _ _
        · exact hv.vg_sorted

theorem State.handleAppendEntriesResponse_inv (h : st.Inv K) (hm : m.Inv K st.server)
    (ht : st.handleAppendEntriesResponse i j m = some s) : s.Inv K := by
  unfold State.handleAppendEntriesResponse at ht
  try dsimp only at ht
  split at ht
  · cases ht
  · injection ht with ht; subst ht
    refine State.Inv.discard m ?_
    split
    · have hv := h.srv i
      refine h.upd { hv with match0 := ?_, matchK := ?_ }
      · intro k; simp only; split
        · exact Int.le_trans (hv.match0 j) (Int.le_max_left _ _)
        · exact hv.match0 k
      · intro k; simp only; split
        · exact Int.max_le.2 ⟨hv.matchK j, hm.matchK⟩
        · exact hv.matchK k
    · exact h

theorem State.rejectAppendEntriesRequest_inv {lo : Bool} (h : st.Inv K) (hm : m ∈ st.messages.domain)
    (hi : i ∈ st.server) (ht : st.rejectAppendEntriesRequest i j m lo = some s) : s.Inv K := by
  have hT := (h.srv i).term
  have hK0 : 0 ≤ K := Int.le_trans (h.srv i).commit0 (h.srv i).commit
  unfold State.rejectAppendEntriesRequest at ht
  try dsimp only at ht
  split at ht
  · cases ht
  · injection ht with ht; subst ht
    refine h.reply hm ⟨by simp, by simp, by simp, by simp, by simp; omega, by simp; omega,
      by simp, by simp; omega, by simp, by simp; omega, by simp, hi⟩

theorem State.returnToFollowerState_inv (h : st.Inv K) (ht : st.returnToFollowerState i m = some s) :
    s.Inv K := by
  unfold State.returnToFollowerState at ht
  try dsimp only at ht
  split at ht
  · cases ht
  · injection ht with ht; subst ht; exact h.upd { h.srv i with }

theorem State.appendEntriesAlreadyDone_inv {ix : Int} (h : st.Inv K) (hm : m ∈ st.messages.domain)
    (hmi : m.Inv K st.server) (hi : i ∈ st.server) (ht : st.appendEntriesAlreadyDone i j ix m = some s) :
    s.Inv K := by
  have hv := h.srv i
  unfold State.appendEntriesAlreadyDone at ht
  try dsimp only at ht
  split at ht
  · cases ht
  · injection ht with ht; subst ht
    have hr : ∀ st' : State, st'.Inv K → st'.messages = st.messages → st'.server = st.server →
        ∀ mi : Int, 0 ≤ mi → mi ≤ K →
        (st'.reply
          { type := .appendEntriesResponse, subtype := m.subtype, term := (st.s i).currentTerm, success := true,
            matchIndex := mi, source := i, dest := j }
          m).Inv K := by
      intro st' h' hms hsv mi h0 hK
      refine h'.reply (by rw [hms]; exact hm) ⟨by simp, by simp, by simpa using hmi.not_snap, by simp,
        by simp; have := hv.term; omega, by simp; have := hv.term; omega,
        by simp, by simp; have := hv.term; omega, by simpa using h0, by simpa using hK, by simp,
        by rw [hsv]; exact hi⟩
    have hmi' : 0 ≤ m.prevLogIndex + m.entries.length := by have := hmi.prev0; omega
    have hmatch : ∀ c : Bool, 0 ≤ (if c = true then m.prevLogIndex + m.entries.length else (st.s i).commitIndex) ∧
        (if c = true then m.prevLogIndex + m.entries.length else (st.s i).commitIndex) ≤ K := by
      intro c
      split
      · exact ⟨hmi', hmi.prev⟩
      · exact ⟨hv.commit0, hv.commit⟩
    split
    · split
      · exact hr _ (h.commitTo i hmi.commit) rfl rfl _ (hmatch _).1 (hmatch _).2
      · exact hr _ h rfl rfl _ (hmatch _).1 (hmatch _).2
    · exact hr _ (h.commitTo i (Int.le_trans (Int.min_le_left _ _) hmi.commit)) rfl rfl _ (hmatch _).1 (hmatch _).2

theorem State.conflictAppendEntriesRequest_inv {ix : Int} (h : st.Inv K)
    (ht : st.conflictAppendEntriesRequest i ix m = .ok (some s)) : s.Inv K := by
  have hv := h.srv i
  unfold State.conflictAppendEntriesRequest at ht
  simp only [bind, Except.bind, pure, Except.pure] at ht
  split at ht
  · cases ht
  · split at ht
    · cases ht
    · rename_i lg hlg
      injection ht with ht; injection ht with ht; subst ht
      obtain ⟨hsub, hlen⟩ := subSeq_some (subSeqM_ok hlg)
      refine h.upd { hv with log_len := ?_, log_conf := fun e he => hv.log_conf e (hsub e he) }
      have := hv.log_len
      rcases hlen with hl | hl
      · subst hl; simp; omega
      · simp only; omega

theorem State.noConflictAppendEntriesRequest_inv {ix : Int} (h : st.Inv K) (hmi : m.Inv K st.server)
    (hix : ix = m.prevLogIndex + 1) (ht : st.noConflictAppendEntriesRequest i ix m = .ok (some s)) : s.Inv K := by
  have hv := h.srv i
  unfold State.noConflictAppendEntriesRequest at ht
  simp only [bind, Except.bind, pure, Except.pure] at ht
  split at ht
  · cases ht
  · split at ht
    · cases ht
    · rename_i sfx hsfx
      injection ht with ht; injection ht with ht; subst ht
      obtain ⟨hsub, hlen⟩ := subSeq_some (subSeqM_ok hsfx)
      refine h.upd { hv with log_len := ?_, log_conf := ?_ }
      · have := hv.log_len; have := hmi.prev
        simp only [List.length_append]
        rcases hlen with hl | hl
        · subst hl; simp; omega
        · omega
      · intro e he
        rcases List.mem_append.1 he with he | he
        · exact hv.log_conf e he
        · exact hmi.ents e (hsub e he)

end handlers

/-! ## Lists of successors -/

/-- Every successor of a list has the invariant at `K`. -/
def State.InvAll (K : Int) (l : List State) : Prop := ∀ s ∈ l, s.Inv K

theorem invAll_nil (K : Int) : State.InvAll K [] := fun _ h => by simp at h

theorem invAll_append {K : Int} {l1 l2 : List State} (h1 : State.InvAll K l1) (h2 : State.InvAll K l2) :
    State.InvAll K (l1 ++ l2) := by
  intro s hs
  rcases List.mem_append.1 hs with hs | hs
  · exact h1 s hs
  · exact h2 s hs

theorem invAll_single {K : Int} {s : State} (h : s.Inv K) : State.InvAll K [s] := by
  intro x hx; simp at hx; subst hx; exact h

theorem invAll_filter {K : Int} {l : List State} {p : State → Bool} (h : State.InvAll K l) :
    State.InvAll K (l.filter p) := fun s hs => h s (List.mem_filter.1 hs).1

theorem invAll_flatMap {α : Type} {K : Int} {l : List α} {f : α → List State}
    (h : ∀ x ∈ l, State.InvAll K (f x)) : State.InvAll K (l.flatMap f) := by
  intro s hs; obtain ⟨x, hx, hs⟩ := List.mem_flatMap.1 hs; exact h x hx s hs

theorem invAll_map {K K' : Int} {l : List State} {f : State → State} (h : State.InvAll K l)
    (hf : ∀ s, s.Inv K → (f s).Inv K') : State.InvAll K' (l.map f) := by
  intro s hs; obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs; exact hf t (h t ht)

theorem invAll_mono {K K' : Int} {l : List State} (h : State.InvAll K l) (hK : K ≤ K') : State.InvAll K' l :=
  fun s hs => (h s hs).mono hK

theorem invAll_somes {K : Int} {l : List (Option State)} (h : ∀ o ∈ l, ∀ s, o = some s → s.Inv K) :
    State.InvAll K (somes l) := by
  intro s hs
  simp only [somes, List.mem_filterMap, id] at hs
  obtain ⟨o, ho, rfl⟩ := hs
  exact h _ ho s rfl

theorem invAll_somes1 {K : Int} {o : Option State} (h : ∀ s, o = some s → s.Inv K) : State.InvAll K (somes [o]) :=
  invAll_somes (by intro o' ho s hs; simp at ho; subst ho; exact h s hs)

theorem invAll_somes2 {K : Int} {o1 o2 : Option State} (h1 : ∀ s, o1 = some s → s.Inv K)
    (h2 : ∀ s, o2 = some s → s.Inv K) : State.InvAll K (somes [o1, o2]) :=
  invAll_somes (by
    intro o ho s hs; simp at ho
    rcases ho with rfl | rfl
    · exact h1 s hs
    · exact h2 s hs)

theorem invAll_somes3 {K : Int} {o1 o2 o3 : Option State} (h1 : ∀ s, o1 = some s → s.Inv K)
    (h2 : ∀ s, o2 = some s → s.Inv K) (h3 : ∀ s, o3 = some s → s.Inv K) : State.InvAll K (somes [o1, o2, o3]) :=
  invAll_somes (by
    intro o ho s hs; simp at ho
    rcases ho with rfl | rfl | rfl
    · exact h1 s hs
    · exact h2 s hs
    · exact h3 s hs)

/-! ## `Receive` -/

section receive
variable {K : Int} {st : State} {m : Msg}

theorem State.acceptAppendEntriesRequest_inv {i j : ID} {lo : Bool} {l : List State} (h : st.Inv K)
    (hm : m ∈ st.messages.domain) (hi : i ∈ st.server) (ht : st.acceptAppendEntriesRequest i j lo m = .ok l) :
    State.InvAll K l := by
  have hmi := h.msgs.msg_of_domain hm
  unfold State.acceptAppendEntriesRequest at ht
  simp only [bind, Except.bind, pure, Except.pure] at ht
  split at ht
  · cases ht; exact invAll_nil _
  · split at ht
    · rename_i hsn; exact absurd (by simpa using hsn) hmi.not_snap
    · cases hc : st.conflictAppendEntriesRequest i (m.prevLogIndex + 1) m with
      | error e => rw [hc] at ht; cases ht
      | ok c =>
        rw [hc] at ht
        cases hn : st.noConflictAppendEntriesRequest i (m.prevLogIndex + 1) m with
        | error e => rw [hn] at ht; cases ht
        | ok n =>
          rw [hn] at ht; cases ht
          exact invAll_somes3 (fun s hs => State.appendEntriesAlreadyDone_inv h hm hmi hi hs)
            (fun s hs => State.conflictAppendEntriesRequest_inv h (by rw [hc, hs]))
            (fun s hs => State.noConflictAppendEntriesRequest_inv h hmi rfl (by rw [hn, hs]))

theorem State.handleAppendEntriesRequest_inv {i j : ID} {l : List State} (h : st.Inv K)
    (hm : m ∈ st.messages.domain) (hi : i ∈ st.server) (ht : st.handleAppendEntriesRequest i j m = .ok l) :
    State.InvAll K l := by
  unfold State.handleAppendEntriesRequest at ht
  simp only [bind, Except.bind, pure, Except.pure] at ht
  split at ht
  · cases ht; exact invAll_nil _
  · cases ha : st.acceptAppendEntriesRequest i j _ m with
    | error e => rw [ha] at ht; cases ht
    | ok acc =>
      rw [ha] at ht; cases ht
      have key : ∀ lo acc, st.acceptAppendEntriesRequest i j lo m = .ok acc →
          State.InvAll K (somes [st.rejectAppendEntriesRequest i j m lo, st.returnToFollowerState i m] ++ acc) :=
        fun lo acc ha => invAll_append (invAll_somes2 (fun s hs => State.rejectAppendEntriesRequest_inv h hm hi hs)
          (fun s hs => State.returnToFollowerState_inv h hs)) (State.acceptAppendEntriesRequest_inv h hm hi ha)
      have hout := key _ _ ha
      split
      · exact invAll_map hout (fun s hs => hs.upd { hs.srv i with })
      · exact hout

theorem State.receive_inv {l : List State} (h : st.Inv K) (hm : m ∈ st.messages.domain)
    (ht : st.receive m = .ok l) : State.InvAll K l := by
  have hmi := h.msgs.msg_of_domain hm
  unfold State.receive at ht
  simp only [bind, Except.bind, pure, Except.pure] at ht
  split at ht
  · cases ht; exact invAll_nil _
  · rename_i hc
    have hi : m.dest ∈ st.server := by simpa using hc
    have hu : State.InvAll K (somes [st.updateTerm m.dest m.source m]) :=
      invAll_somes1 (fun s hs => State.updateTerm_inv h hmi hs)
    split at ht
    · cases ht
      exact invAll_append hu (invAll_somes1 (fun s hs => State.handleRequestVoteRequest_inv h hm hi hs))
    · cases ht
      exact invAll_append hu (invAll_somes2 (fun s hs => State.dropStaleResponse_inv h hs)
        (fun s hs => State.handleRequestVoteResponse_inv h hmi.src hs))
    · cases ha : st.handleAppendEntriesRequest m.dest m.source m with
      | error e => rw [ha] at ht; cases ht
      | ok acc => rw [ha] at ht; cases ht; exact invAll_append hu (State.handleAppendEntriesRequest_inv h hm hi ha)
    · cases ht
      exact invAll_append hu (invAll_somes2 (fun s hs => State.dropStaleResponse_inv h hs)
        (fun s hs => State.handleAppendEntriesResponse_inv h hmi hs))
    · rename_i hty; exact absurd hty hmi.not_pvq
    · rename_i hty; exact absurd hty hmi.not_pvr

end receive

/-! ## The `IfLogged` actions -/

theorem Trace.isEvent_name {tr : Trace} {ts : TState} {e : String} (h : tr.isEvent ts e = true) :
    (tr.line ts.l).ev.name = e := by
  unfold Trace.isEvent at h; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.2

theorem Trace.isNodeEvent_name {tr : Trace} {ts : TState} {e : String} {i : ID}
    (h : tr.isNodeEvent ts e i = true) : (tr.line ts.l).ev.name = e := by
  unfold Trace.isNodeEvent at h; simp only [Bool.and_eq_true] at h; exact Trace.isEvent_name h.1

theorem Trace.isMessageEvent_name {tr : Trace} {ts : TState} {e : String} {i j : ID}
    (h : tr.isMessageEvent ts e i j = true) : (tr.line ts.l).ev.name = e := by
  unfold Trace.isMessageEvent at h; simp only [Bool.and_eq_true] at h; exact Trace.isEvent_name h.1.1.1

theorem Trace.mem_pairs {tr : Trace} {p : ID × ID} (h : p ∈ tr.pairs) : p.1 ∈ tr.server ∧ p.2 ∈ tr.server := by
  unfold Trace.pairs at h
  obtain ⟨i, hi, hp⟩ := List.mem_flatMap.1 h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
  exact ⟨hi, hj⟩

section iflogged
variable {tr : Trace} {ts : TState} {K : Int}

theorem Trace.requestVoteIfLogged_inv {i j : ID} (h : ts.s.Inv K) (hi : i ∈ ts.s.server)
    (hpv : ts.s.preVote = false) : State.InvAll (K + 1) (tr.requestVoteIfLogged ts i j) := by
  unfold Trace.requestVoteIfLogged
  split
  · exact invAll_nil _
  · refine invAll_filter (invAll_somes2 (fun s hs => State.requestVote_inv h hi hs) ?_)
    intro s hs; rw [State.requestPreVote_none hpv] at hs; cases hs

theorem Trace.becomeLeaderIfLogged_inv {i : ID} (h : ts.s.Inv K) :
    State.InvAll K (tr.becomeLeaderIfLogged ts i) := by
  unfold Trace.becomeLeaderIfLogged
  split
  · exact invAll_nil _
  · cases hb : ts.s.becomeLeader i with
    | none => exact invAll_nil _
    | some s2 =>
      dsimp only
      split
      · exact invAll_single (State.becomeLeader_inv h hb)
      · exact invAll_nil _

theorem Trace.clientRequestIfLogged_inv {i : ID} {v : Int} (h : ts.s.Inv K) :
    State.InvAll (K + 1) (tr.clientRequestIfLogged ts i v) := by
  unfold Trace.clientRequestIfLogged
  split
  · exact invAll_nil _
  · exact invAll_somes1 (fun s hs => State.clientRequest_inv h hs)

theorem Trace.advanceCommitIndexIfLogged_inv {i : ID} (h : ts.s.Inv K) :
    State.InvAll K (tr.advanceCommitIndexIfLogged ts i) := by
  unfold Trace.advanceCommitIndexIfLogged
  split
  · exact invAll_nil _
  · cases hb : ts.s.advanceCommitIndex i with
    | none => exact invAll_nil _
    | some s2 =>
      dsimp only
      split
      · exact invAll_single (State.advanceCommitIndex_inv h hb)
      · exact invAll_nil _

theorem Trace.appendEntriesToSelfIfLogged_inv {i : ID} (h : ts.s.Inv K) (hi : i ∈ ts.s.server) :
    State.InvAll (K + 1) (tr.appendEntriesToSelfIfLogged ts i) := by
  unfold Trace.appendEntriesToSelfIfLogged
  split
  · exact invAll_nil _
  · cases hb : ts.s.appendEntriesToSelf i with
    | none => exact invAll_nil _
    | some s2 =>
      dsimp only
      split
      · exact invAll_single (State.appendEntriesToSelf_inv h hi hb)
      · exact invAll_nil _

theorem Trace.preTimeoutIfLogged_inv {i : ID} (h : ts.s.Inv K) :
    State.InvAll K (tr.preTimeoutIfLogged ts i) := by
  unfold Trace.preTimeoutIfLogged
  split
  · exact invAll_nil _
  · cases hb : ts.s.preTimeout i with
    | none => exact invAll_nil _
    | some s2 =>
      dsimp only
      split
      · exact invAll_single (State.preTimeout_inv h hb)
      · exact invAll_nil _

theorem Trace.timeoutIfLogged_inv {i : ID} (h : ts.s.Inv K) :
    State.InvAll (K + 1) (tr.timeoutIfLogged ts i) := by
  unfold Trace.timeoutIfLogged
  split
  · exact invAll_nil _
  · cases hb : ts.s.timeout i with
    | none => exact invAll_nil _
    | some s2 =>
      dsimp only
      split
      · exact invAll_single (State.timeout_inv h hb)
      · exact invAll_nil _

theorem Trace.stepDownToFollowerIfLogged_inv {i : ID} (h : ts.s.Inv K) :
    State.InvAll K (tr.stepDownToFollowerIfLogged ts i) := by
  unfold Trace.stepDownToFollowerIfLogged
  split
  · exact invAll_nil _
  · cases hb : ts.s.stepDownToFollower i with
    | none => exact invAll_nil _
    | some s2 =>
      dsimp only
      split
      · exact invAll_single (State.stepDownToFollower_inv h hb)
      · exact invAll_nil _

theorem Trace.ignoreInLeaseIfLogged_inv (h : ts.s.Inv K) : State.InvAll K (tr.ignoreInLeaseIfLogged ts) := by
  unfold Trace.ignoreInLeaseIfLogged
  split
  · exact invAll_nil _
  · apply invAll_flatMap
    intro m _
    split
    · exact invAll_somes1 (fun s hs => State.ignoreInLease_inv h hs)
    · exact invAll_nil _

theorem Trace.changeConfIfLogged_nil {i j : ID} {a : String} (hsc : (tr.line ts.l).InScope) :
    tr.changeConfIfLogged ts i j a = [] := by
  unfold Trace.changeConfIfLogged
  split
  · rfl
  · rename_i hn
    exact absurd (Trace.isNodeEvent_name (by simpa using hn)) hsc.1

theorem Trace.readyIfLogged_inv {i : ID} (h : ts.s.Inv K) : State.InvAll K (tr.readyIfLogged ts i) := by
  unfold Trace.readyIfLogged
  split
  · exact invAll_nil _
  · exact invAll_single (h.ready i)

theorem Trace.appendEntriesIfLogged_inv {i j : ID} {b e : Int} {l : List State} (h : ts.s.Inv K)
    (hi : i ∈ ts.s.server) (hev : (tr.line ts.l).ev.Bounded) (hK : numBound ≤ K)
    (ht : tr.appendEntriesIfLogged ts i j b e = .ok l) : State.InvAll (K + 1) l := by
  unfold Trace.appendEntriesIfLogged at ht
  simp only [bind, Except.bind, pure, Except.pure] at ht
  split at ht
  · cases ht; exact invAll_nil _
  · split at ht
    · rename_i ev hev'
      split at ht
      · cases ht; exact invAll_nil _
      · rename_i hc
        simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨-, -, -, hidx, -, -⟩ := hev.2.2.2 ev hev'
        have hb1 : 1 ≤ b := by unfold numOk at hidx; omega
        have hbK : b - 1 ≤ K := by unfold numOk at hidx; omega
        split at ht
        · cases ht
        · rename_i o ho
          cases o with
          | none => cases ht; exact invAll_nil _
          | some s2 =>
            simp only at ht
            split at ht
            · cases ht
              exact invAll_single (State.appendEntriesInRangeToPeer_inv h hi (by decide) hb1 hbK ho)
            · cases ht; exact invAll_nil _
    · cases ht; exact invAll_nil _

theorem Trace.heartbeatIfLogged_inv {i j : ID} {l : List State} (h : ts.s.Inv K)
    (hi : i ∈ ts.s.server) (ht : tr.heartbeatIfLogged ts i j = .ok l) : State.InvAll (K + 1) l := by
  have hK : (0 : Int) ≤ K := Int.le_trans (h.srv i).commit0 (h.srv i).commit
  unfold Trace.heartbeatIfLogged at ht
  simp only [bind, Except.bind, pure, Except.pure] at ht
  split at ht
  · cases ht; exact invAll_nil _
  · split at ht
    · cases ht; exact invAll_nil _
    · split at ht
      · cases ht
      · rename_i o ho
        cases o with
        | none => cases ht; exact invAll_nil _
        | some s2 =>
          simp only at ht
          split at ht
          · cases ht
            exact invAll_single (State.appendEntriesInRangeToPeer_inv h hi (by decide) (by decide)
              (by omega) ho)
          · cases ht; exact invAll_nil _

theorem Trace.sendSnapshotIfLogged_nil {i j : ID} {ix : Int} {l : List State} (hsc : (tr.line ts.l).InScope)
    (ht : tr.sendSnapshotIfLogged ts i j ix = .ok l) : l = [] := by
  unfold Trace.sendSnapshotIfLogged at ht
  simp only [bind, Except.bind, pure, Except.pure] at ht
  split at ht
  · cases ht; rfl
  · rename_i hn
    have hname := Trace.isMessageEvent_name (by simpa using hn)
    split at ht
    · rename_i ev hev
      split at ht
      · cases ht; rfl
      · rename_i hc
        simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq] at hc
        exact absurd (by rw [hev]; simp [hc.1]) (hsc.2.2 hname)
    · cases ht; rfl

theorem Trace.restartIfLogged_nil {i : ID} {l : List State} (hsc : (tr.line ts.l).InScope)
    (ht : tr.restartIfLogged ts i = .ok l) : l = [] := by
  unfold Trace.restartIfLogged at ht
  simp only [pure, Except.pure] at ht
  split at ht
  · cases ht; rfl
  · rename_i hn
    exact absurd (Trace.isNodeEvent_name (by simpa using hn)) hsc.2.1

theorem Trace.applySimpleConfChangeIfLogged_inv {i : ID} {l : List State} (h : ts.s.Inv K)
    (ht : tr.applySimpleConfChangeIfLogged ts i = .ok l) : State.InvAll (K + 1) l := by
  unfold Trace.applySimpleConfChangeIfLogged at ht
  simp only [bind, Except.bind, pure, Except.pure] at ht
  split at ht
  · cases ht; exact invAll_nil _
  · split at ht
    · cases ht
    · rename_i o ho
      cases ht
      exact invAll_somes1 (fun s hs => State.applySimpleConfChange_inv h (by rw [ho, hs]))

end iflogged

/-! ## `TraceNext` -/

theorem append_step_inv {K : Int} {acc c : List State} {x : EvalM (List State)}
    (hf : ∀ r, x = .ok r → State.InvAll K r) (hacc : State.InvAll K acc)
    (h : (do return acc ++ (← x) : EvalM (List State)) = .ok c) : State.InvAll K c := by
  cases hx : x with
  | error e => rw [hx] at h; cases h
  | ok r =>
    rw [hx] at h
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact invAll_append hacc (hf r hx)

/- (its case split over the line's kinds takes more than the default heartbeats) -/
set_option maxHeartbeats 1000000 in
theorem Trace.nonReceive_inv {tr : Trace} {ts : TState} {K : Int} {out : List State} (h : ts.s.Inv K)
    (hsrv : ts.s.server = tr.server) (hpv : ts.s.preVote = false) (hsc : (tr.line ts.l).InScope)
    (hev : (tr.line ts.l).ev.Bounded) (hK : numBound ≤ K) (ht : tr.nonReceive ts = .ok out) :
    State.InvAll (K + 1) out := by
  have hK1 : K ≤ K + 1 := Int.le_add_of_nonneg_right (by decide)
  have hpair : ∀ p ∈ tr.pairs, p.1 ∈ ts.s.server := fun p hp => hsrv ▸ (Trace.mem_pairs hp).1
  have hsv : ∀ i ∈ tr.server, i ∈ ts.s.server := fun i hi => hsrv ▸ hi
  unfold Trace.nonReceive at ht
  simp only [bind, Except.bind, pure, Except.pure] at ht
  try dsimp only at ht
  repeat' split at ht
  all_goals first
    | (cases ht; done)
    | (injection ht with ht; subst ht
       try refine invAll_append ?_ (invAll_single (h.mono hK1))
       first
        | exact invAll_nil _
        | (apply invAll_flatMap; intro x hx
           first
            | exact Trace.requestVoteIfLogged_inv h (hpair x hx) hpv
            | exact invAll_mono (Trace.becomeLeaderIfLogged_inv h) hK1
            | exact Trace.clientRequestIfLogged_inv h
            | exact invAll_mono (Trace.advanceCommitIndexIfLogged_inv h) hK1
            | exact Trace.appendEntriesToSelfIfLogged_inv h (hsv x hx)
            | exact Trace.timeoutIfLogged_inv h
            | exact invAll_mono (Trace.preTimeoutIfLogged_inv h) hK1
            | exact invAll_mono (Trace.readyIfLogged_inv h) hK1
            | exact invAll_mono (Trace.stepDownToFollowerIfLogged_inv h) hK1
            | (apply invAll_flatMap; intro y _; rw [Trace.changeConfIfLogged_nil hsc]; exact invAll_nil _))
        | exact invAll_mono (Trace.ignoreInLeaseIfLogged_inv h) hK1
        | (refine foldlM_except_inv (fun acc => State.InvAll (K + 1) acc) _ _ _ _ ?_ (invAll_nil _) ‹_›
           intro acc x c hx hacc hc
           try dsimp only at hc
           first
            | exact append_step_inv (fun r hr => Trace.heartbeatIfLogged_inv h (hpair x hx) hr) hacc hc
            | exact append_step_inv (fun r hr => Trace.applySimpleConfChangeIfLogged_inv h hr) hacc hc
            | exact append_step_inv (fun r hr => by rw [Trace.restartIfLogged_nil hsc hr]; exact invAll_nil _)
                hacc hc
            | exact foldlM_except_inv (fun acc => State.InvAll (K + 1) acc) _ _ _ _ (fun acc ix c _ hacc hc =>
                append_step_inv (fun r hr => by rw [Trace.sendSnapshotIfLogged_nil hsc hr]; exact invAll_nil _)
                  hacc hc) hacc hc
            | exact foldlM_except_inv (fun acc => State.InvAll (K + 1) acc) _ _ _ _ (fun acc b c _ hacc hc =>
                foldlM_except_inv (fun acc => State.InvAll (K + 1) acc) _ _ _ _ (fun acc e c _ hacc hc =>
                  append_step_inv (fun r hr => Trace.appendEntriesIfLogged_inv h (hpair x hx) hev hK hr)
                    hacc hc) hacc hc) hacc hc))

/-- `receive`'s successors keep the invariant at the same bound. -/
theorem Trace.receive_inv {tr : Trace} {ts : TState} {K : Int} {tss : List TState} (h : ts.s.Inv K)
    (ht : tr.receive ts = .ok tss) : ∀ x ∈ tss, x.s.Inv K := by
  unfold Trace.receive at ht
  dsimp only at ht
  split at ht
  · cases ht; simp
  · refine foldlM_except_inv (fun acc : List TState => ∀ x ∈ acc, x.s.Inv K) _ _ [] tss ?_ (by simp) ht
    intro acc m c hm hacc hf
    repeat' split at hf
    all_goals first
      | (cases hf; exact hacc)
      | (revert hf
         cases hr : ts.s.receive m with
         | error e => intro hf; simp [Bind.bind, Except.bind] at hf
         | ok succ =>
           intro hf
           simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] at hf
           subst hf
           intro x hx
           rcases List.mem_append.1 hx with hx | hx
           · exact hacc x hx
           · obtain ⟨s2, hs2, rfl⟩ := List.mem_map.1 hx
             have := State.receive_inv h hm hr s2 hs2
             split <;> exact this)

/-- `receive`'s successors stay at the line or step past it. -/
theorem Trace.receive_l (tr : Trace) (ts : TState) (tss : List TState) (h : tr.receive ts = .ok tss) :
    ∀ s ∈ tss, s.l = ts.l ∨ s.l = ts.l + 1 := by
  unfold Trace.receive at h
  dsimp only at h
  split at h
  · cases h; simp
  · refine foldlM_except_inv (fun acc : List TState => ∀ s ∈ acc, s.l = ts.l ∨ s.l = ts.l + 1) _ _ [] tss
      ?_ (by simp) h
    intro acc m c _ hacc hf
    repeat' split at hf
    all_goals first
      | (cases hf; exact hacc)
      | (revert hf
         cases hr : ts.s.receive m with
         | error e => intro hf; simp [Bind.bind, Except.bind] at hf
         | ok succ =>
           intro hf
           simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] at hf
           subst hf
           intro s hs
           rcases List.mem_append.1 hs with hs | hs
           · exact hacc s hs
           · obtain ⟨s2, -, rfl⟩ := List.mem_map.1 hs
             split <;> simp)

/-- `TraceNext`'s successors stay at the line or step past it. -/
theorem Trace.next_l (tr : Trace) (f : TState) (tss : List TState) (h : tr.next f = .ok tss) :
    ∀ s ∈ tss, s.l = f.l ∨ s.l = f.l + 1 := by
  unfold Trace.next at h
  split at h
  · simp only [Pure.pure, Except.pure, Except.ok.injEq] at h; subst h; simp
  · split at h
    · simp only [Pure.pure, Except.pure, Except.ok.injEq] at h; subst h; simp
    · simp only [Bind.bind, Except.bind] at h
      cases hn : tr.nonReceive f with
      | error e => rw [hn] at h; cases h
      | ok nr =>
        rw [hn] at h
        cases hr : tr.receive f with
        | error e => rw [hr] at h; cases h
        | ok rv =>
          rw [hr] at h
          simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
          subst h
          intro s hs
          rcases List.mem_append.1 hs with hs | hs
          · obtain ⟨s2, -, rfl⟩ := List.mem_map.1 hs; simp
          · exact tr.receive_l f rv hr s hs

/-- A state with successors is at a line of the trace. -/
theorem Trace.next_l_le {tr : Trace} {f : TState} {tss : List TState} {s2 : TState} (h : tr.next f = .ok tss)
    (hs : s2 ∈ tss) : 1 ≤ f.l ∧ f.l ≤ tr.len := by
  unfold Trace.next at h
  split at h
  · cases h; simp at hs
  · rename_i hl
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, not_or] at hl
    omega

/-- `TraceNext`'s successors keep the invariant, at the bound of their line. -/
theorem Trace.next_inv {tr : Trace} {f : TState} {tss : List TState} (h : f.s.Inv (numBound + f.l))
    (hsrv : f.s.server = tr.server) (hpv : f.s.preVote = false) (hsc : tr.LinesInScope)
    (hev : ∀ l, (tr.line l).ev.Bounded) (ht : tr.next f = .ok tss) :
    ∀ x ∈ tss, x.s.Inv (numBound + x.l) := by
  intro x hx
  obtain ⟨hl1, hl2⟩ := Trace.next_l_le ht hx
  unfold Trace.next at ht
  split at ht
  · cases ht; simp at hx
  · split at ht
    · cases ht; simp at hx; subst hx; exact h.mono (by simp only; omega)
    · rename_i hb
      have hsc' : (tr.line f.l).InScope := hsc f.l hl1 hl2 (by simpa using hb)
      simp only [Bind.bind, Except.bind] at ht
      cases hn : tr.nonReceive f with
      | error e => rw [hn] at ht; cases ht
      | ok nr =>
        rw [hn] at ht
        cases hr : tr.receive f with
        | error e => rw [hr] at ht; cases ht
        | ok rv =>
          rw [hr] at ht
          simp only [Pure.pure, Except.pure, Except.ok.injEq] at ht
          subst ht
          rcases List.mem_append.1 hx with hx | hx
          · obtain ⟨s2, hs2, rfl⟩ := List.mem_map.1 hx
            have := Trace.nonReceive_inv h hsrv hpv hsc' (hev _) (by omega) hn s2 hs2
            exact this.mono (by simp only; omega)
          · have := Trace.receive_inv h hr x hx
            exact this.mono (by rcases tr.receive_l f rv hr x hx with e | e <;> rw [e] <;> omega)

/-! ## What `NewTrace` builds -/

theorem Event.bounded_default : (default : Event).Bounded := by
  have h0 : numOk 0 := by unfold numOk numBound; exact ⟨Int.le_refl 0, by decide⟩
  exact ⟨h0, h0, h0, fun m hm => by cases hm⟩

theorem Trace.Valid.line_bounded {tr : Trace} (hv : tr.Valid) (l : Nat) : (tr.line l).ev.Bounded := by
  obtain ⟨evs, hb, -, hnt⟩ := hv
  have hl := (newTraceWith_ok evs false false tr hnt).1
  unfold Trace.line
  rw [List.getD_eq_getElem?_getD]
  cases hg : tr.lines[l - 1]? with
  | none => exact Event.bounded_default
  | some x => exact hb _ (lines_ev_mem hl (List.mem_of_getElem? hg))

theorem mapM_option_length {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (r : List β), l.mapM f = some r → r.length = l.length
  | [], r, h => by simp at h; subst h; rfl
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases hf : f a with
    | none => simp [hf] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [hf, hl] at h
      | some r' =>
        simp [hf, hl] at h; subst h; simp [mapM_option_length f l r' hl]

theorem insertSorted_length_le (id : ID) : ∀ s : SetIds, (insertSorted id s).length ≤ s.length + 1
  | [] => by simp [insertSorted]
  | x :: xs => by
    unfold insertSorted
    split
    · simp
    · split
      · simp
      · simp only [List.length_cons]; have := insertSorted_length_le id xs; omega

theorem SetIds.mk_length_le (ids : List ID) : (SetIds.mk ids).length ≤ ids.length := by
  unfold SetIds.mk
  suffices H : ∀ (l : List ID) (s : SetIds), (l.foldl (fun s id => insertSorted id s) s).length ≤ s.length + l.length by
    simpa using H ids []
  intro l
  induction l with
  | nil => intro s; simp
  | cons x xs ih =>
    intro s
    simp only [List.foldl_cons, List.length_cons]
    have := ih (insertSorted x s); have := insertSorted_length_le x s; omega

theorem toSet_length {ids : List String} {c : SetIds} (h : toSet ids = some c) : c.length ≤ ids.length := by
  unfold toSet at h
  cases hm : ids.mapM parseID with
  | none => rw [hm] at h; cases h
  | some r =>
    rw [hm] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
    exact Nat.le_trans (SetIds.mk_length_le r) (Nat.le_of_eq (mapM_option_length parseID ids r hm))

theorem parseLine_conf {k : Nat} {ev : Event} {ln : Line} (h : parseLine k ev = .ok ln) :
    toSet ev.conf.1 = some ln.conf.1 := by
  unfold parseLine at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, Pure.pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (injection h with h; subst h; assumption)

theorem filterMapM_ok_mem {α β ε : Type} (f : α → Except ε (Option β)) :
    ∀ (l : List α) (r : List β), l.filterMapM f = .ok r → ∀ y ∈ r, ∃ x ∈ l, f x = .ok (some y)
  | [], r, h, y, hy => by simp [Pure.pure, Except.pure] at h; subst h; simp at hy
  | a :: l, r, h, y, hy => by
    rw [List.filterMapM_cons] at h
    simp only [bind, Except.bind] at h
    cases hfa : f a with
    | error e => rw [hfa] at h; cases h
    | ok o =>
      rw [hfa] at h
      cases o with
      | none =>
        simp only at h
        obtain ⟨x, hx, hfx⟩ := filterMapM_ok_mem f l r h y hy
        exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩
      | some b =>
        simp only at h
        cases hl : l.filterMapM f with
        | error e => rw [hl] at h; cases h
        | ok r' =>
          rw [hl] at h
          simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
          subst h
          rcases List.mem_cons.1 hy with rfl | hy
          · exact ⟨a, List.mem_cons_self, hfa⟩
          · obtain ⟨x, hx, hfx⟩ := filterMapM_ok_mem f l r' hl y hy
            exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

/-- What `NewTraceWith` builds, by the names of `newTraceTail`. -/
theorem newTraceWith_inv {evs : List Event} {pv cq : Bool} {t : Trace} (h : newTraceWith evs pv cq = .ok t) :
    ∃ (xs : List Line) (ad : List (Option ID)) (srv : SetIds) (cfgs : List (ID × SetIds))
      (bconfs : List (ID × List SetIds)),
      ((List.range evs.length).zip evs).mapM (fun p => parseLine p.1 p.2) = .ok xs ∧
      xs.mapM addedServer = .ok ad ∧ srv = SetIds.mk (xs.map Line.nid ++ ad.filterMap id) ∧
      t.lines = xs ∧ t.server = srv ∧ srv.mapM (tCfgF xs srv) = .ok cfgs ∧
      srv.mapM (tBconfF xs srv) = .ok bconfs ∧
      t.init =
        { server := srv, s := (fun i => tServerOf xs srv cfgs bconfs i), messages := [], pendingMessages := [],
          reconfigCount := 0, preVote := pv, checkQuorum := cq } := by
  have hne : evs ≠ [] := by rintro rfl; exact newTraceWith_nil pv cq t h
  have hl := (newTraceWith_ok evs pv cq t h).1
  generalize hxs : t.lines = xs at hl
  cases hadd : xs.mapM addedServer with
  | error e =>
    exfalso
    have hne' : evs.isEmpty = false := by simpa using hne
    unfold newTraceWith at h
    simp only [hne', hl, hadd, bind, Except.bind, Bool.false_eq_true, ite_false] at h
    cases h
  | ok ad =>
    rw [newTraceWith_tail pv cq hne hl hadd] at h
    generalize hS : SetIds.mk (xs.map Line.nid ++ ad.filterMap id) = srv at h
    unfold newTraceTail at h
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | contradiction
      | (injection h with h; subst h
         refine ⟨xs, ad, srv, _, _, hl, hadd, hS.symm, hxs, rfl, ?_, ?_, rfl⟩
         · unfold tCfgF; simp only [bind, Except.bind, pure, Except.pure]; assumption
         · assumption)

theorem getD_mem_or_default {α : Type} [Inhabited α] (xs : List α) (n : Nat) :
    xs.getD n default ∈ xs ∨ xs.getD n default = default := by
  rw [List.getD_eq_getElem?_getD]
  cases hg : xs[n]? with
  | none => exact .inr rfl
  | some x => exact .inl (List.mem_of_getElem? hg)

/-- What a trace's line gives the initial state: its event bounded, its configuration lists bounded,
its parsed configuration the event's. -/
def Line.InitOk (x : Line) : Prop :=
  x.ev.Bounded ∧ x.ev.ConfsBounded ∧ toSet x.ev.conf.1 = some x.conf.1

theorem Line.initOk_default : (default : Line).InitOk := by
  refine ⟨Event.bounded_default, ⟨by decide, ?_⟩, rfl⟩
  intro nc hnc; cases hnc

theorem Line.InitOk.getD {xs : List Line} (hx : ∀ x ∈ xs, x.InitOk) (n : Nat) : (xs.getD n default).InitOk := by
  rcases getD_mem_or_default xs n with h | h
  · exact hx _ h
  · rw [h]; exact Line.initOk_default

theorem tBC_bound {xs : List Line} {last : Nat} {c : SetIds} (hx : ∀ x ∈ xs, x.InitOk) (h : tBC xs last = .ok c) :
    (c.length : Int) < numBound := by
  have hln := Line.InitOk.getD hx (last - 1)
  unfold tBC at h
  generalize xs.getD (last - 1) default = y at h hln
  simp only [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · split at h
    · cases h
    · rename_i nc hnc
      split at h
      · rename_i c' hc'
        cases h
        have := hln.2.1.2 nc hnc
        have := toSet_length hc'
        omega
      · cases h
  · cases h
    have := hln.2.1.1
    have := toSet_length hln.2.2
    omega

theorem bconf_bound {xs : List Line} {srv : SetIds} {i : ID} {p : ID × List SetIds} (hx : ∀ x ∈ xs, x.InitOk)
    (h : tBconfF xs srv i = .ok p) : ∀ c ∈ p.2, (c.length : Int) < numBound := by
  unfold tBconfF at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i cs hcs
    cases h
    intro c hc
    obtain ⟨k, -, hk⟩ := filterMapM_ok_mem _ _ _ hcs c hc
    have hln := Line.InitOk.getD hx k
    generalize xs.getD k default = y at hk hln
    simp only [throw, throwThe, MonadExceptOf.throw] at hk
    split at hk
    · cases hk
    · split at hk
      · cases hk
      · rename_i nc hnc
        split at hk
        · rename_i c' hc'
          cases hk
          have := hln.2.1.2 nc hnc
          have := toSet_length hc'
          omega
        · cases hk

theorem tServerOf_inv {xs : List Line} {srv : SetIds} {cfgs : List (ID × SetIds)} {bconfs : List (ID × List SetIds)}
    (hx : ∀ x ∈ xs, x.InitOk) (hcfg : ∀ p ∈ cfgs, (p.2.length : Int) < numBound)
    (hbc : ∀ p ∈ bconfs, ∀ c ∈ p.2, (c.length : Int) < numBound) (S : SetIds) (i : ID) :
    (tServerOf xs srv cfgs bconfs i).Inv numBound S := by
  have hlb := (Line.InitOk.getD hx (tLast xs srv i - 1)).1
  have hcf : ((((cfgs.find? (fun p => p.1 == i)).map Prod.snd).getD []).length : Int) < numBound := by
    cases hf : cfgs.find? (fun p => p.1 == i) with
    | none => decide
    | some p => simpa using hcfg p (List.mem_of_find?_eq_some hf)
  have hbf : ∀ c ∈ (((bconfs.find? (fun p => p.1 == i)).map Prod.snd).getD []), (c.length : Int) < numBound := by
    cases hf : bconfs.find? (fun p => p.1 == i) with
    | none => simp
    | some p => simpa using hbc p (List.mem_of_find?_eq_some hf)
  unfold tServerOf
  generalize xs.getD (tLast xs srv i - 1) default = lb at hlb
  generalize ((cfgs.find? (fun p => p.1 == i)).map Prod.snd).getD [] = cfg at hcf
  generalize ((bconfs.find? (fun p => p.1 == i)).map Prod.snd).getD [] = bc at hbf
  obtain ⟨hterm, hcommit, hlog, -⟩ := hlb
  unfold numOk at hterm hcommit hlog
  refine ⟨?_, ?_, by simp, by simp, ?_, ?_, ?_, ?_, by simp, ?_⟩
  · simp only [List.length_map, List.length_range]; omega
  · intro e he nc ln hv
    simp only [List.mem_map, List.mem_range] at he
    obtain ⟨k, -, rfl⟩ := he
    simp only [Value.conf.injEq] at hv
    obtain ⟨rfl, -⟩ := hv
    rw [List.getD_eq_getElem?_getD]
    cases hg : bc[k]? with
    | none => simp only [Option.getD_none]; omega
    | some c => simp only [Option.getD_some]; have := hbf c (List.mem_of_getElem? hg); omega
  · simp only; omega
  · simp only; omega
  · simp only; omega
  · simp only; omega
  · intro j; simp only; unfold numBound; decide

/-- `TraceInit` has the invariant at `numBound`. -/
theorem Trace.Valid.init_inv {tr : Trace} (hv : tr.Valid) (hcb : tr.ConfsBounded) : tr.init.Inv numBound := by
  obtain ⟨evs, hb, -, hnt⟩ := hv
  obtain ⟨xs, ad, srv, cfgs, bconfs, hl, -, -, hxs, -, hcf, hbf, hinit⟩ := newTraceWith_inv hnt
  have hx : ∀ x ∈ xs, x.InitOk := by
    intro x hxm
    obtain ⟨p, -, hp⟩ := mapM_ok_mem _ _ _ hl x hxm
    exact ⟨hb _ (lines_ev_mem hl hxm), hcb x (hxs ▸ hxm), by rw [parseLine_ev hp]; exact parseLine_conf hp⟩
  have hcfg : ∀ p ∈ cfgs, (p.2.length : Int) < numBound := by
    intro p hp
    obtain ⟨i, -, hi⟩ := mapM_ok_mem _ _ _ hcf p hp
    simp only [tCfgF, bind, Except.bind, pure, Except.pure] at hi
    split at hi
    · cases hi
    · rename_i c hc; cases hi; exact tBC_bound hx hc
  have hbc : ∀ p ∈ bconfs, ∀ c ∈ p.2, (c.length : Int) < numBound := by
    intro p hp
    obtain ⟨i, -, hi⟩ := mapM_ok_mem _ _ _ hbf p hp
    exact bconf_bound hx hi
  rw [hinit]
  exact ⟨fun i => tServerOf_inv hx hcfg hbc _ i, ⟨by simp, by simp, by simp⟩, ⟨by simp, by simp, by simp⟩,
    by simp [Bag.total, numBound], by simp [numBound]⟩

/-- A trace's servers: at most one per line and one per added server. -/
theorem Trace.Valid.server_length {tr : Trace} (hv : tr.Valid) : tr.server.length ≤ 2 * tr.len := by
  obtain ⟨evs, -, -, hnt⟩ := hv
  obtain ⟨xs, ad, srv, -, -, -, hadd, hS, hxs, hsv, -⟩ := newTraceWith_inv hnt
  rw [hsv, hS]
  have h1 := SetIds.mk_length_le (xs.map Line.nid ++ ad.filterMap id)
  have h2 := List.length_filterMap_le id ad
  have h3 := mapM_ok_length _ _ _ hadd
  simp only [List.length_append, List.length_map] at h1
  unfold Trace.len; rw [hxs]
  omega

/-! ## The reachability invariant -/

/-- Every reached state has the invariant at the bound of its line, and its line is at most one past
the trace's last. -/
theorem Trace.Valid.reach_inv {tr : Trace} (hv : tr.Valid) (hsc : tr.LinesInScope) (hcb : tr.ConfsBounded)
    {ts : TState} (h : tr.Reach ts) : ts.s.Inv (numBound + ts.l) ∧ ts.l ≤ tr.len + 1 := by
  induction h with
  | init =>
    refine ⟨(hv.init_inv hcb).mono (by simp only [Trace.initState]; omega), by simp [Trace.initState]⟩
  | step f tss s2 hf hn hs ih =>
    obtain ⟨hsrv, hpv, -⟩ := hv.reach_frame hf
    refine ⟨Trace.next_inv ih.1 hsrv hpv hsc hv.line_bounded hn s2 hs, ?_⟩
    have := Trace.next_l_le hn hs
    rcases tr.next_l f tss hn s2 hs with e | e <;> omega

/-- **Part 2 of `CheckTrace`'s premise, proved**: every state of the trace specification reachable from
`TraceInit` meets the actions' bounds, for a trace `NewTrace` built (`Trace.Valid`) whose lines are in
scope and whose events' configuration lists are bounded. -/
theorem Trace.Valid.reach_searchOk {tr : Trace} (hv : tr.Valid) (hsc : tr.LinesInScope) (hcb : tr.ConfsBounded)
    {ts : TState} (h : tr.Reach ts) : ts.s.SearchOk := by
  obtain ⟨hinv, hl⟩ := hv.reach_inv hsc hcb h
  have hlen := hv.len_lt
  have hsl := hv.server_length
  obtain ⟨hsrv, -, -⟩ := hv.reach_frame h
  have hK : numBound + (ts.l : Int) < 2 ^ 42 := by unfold numBound at *; omega
  have hS : (ts.s.server.length : Int) < 2 ^ 42 := by rw [hsrv]; unfold numBound at *; omega
  have hbag : ∀ {b : Bag}, Bag.Inv (numBound + ts.l) ts.s.server b → (Bag.total b : Int) < 2 ^ 42 →
      b.Ok := fun {b} hb ht => ⟨hb.nodup, fun it hit => by have := Bag.le_total hit; omega⟩
  have htot := hinv.total
  refine ⟨⟨hbag hinv.pend (by omega), by simp only [Bag.total] at htot ⊢; omega, by have := hinv.rc; omega, ?_⟩,
    ⟨hbag hinv.msgs (by omega), ?_⟩⟩
  · intro i _
    have hv' := hinv.srv i
    have hvg : (ts.s.s i).votesGranted.length ≤ ts.s.server.length :=
      List.Nodup.length_le_of_subset (hv'.vg_sorted.imp Nat.ne_of_lt) hv'.vg_sub
    refine ⟨by have := hv'.log_len; omega, by omega, by have := hv'.term; omega, ?_, fun j => ?_⟩
    · unfold State.getConfig; have := hv'.cfg; omega
    · have := hv'.match0 j; have := hv'.matchK j; omega
  · intro m hm
    have hmi := hinv.msgs.msg_of_domain hm
    have := hmi.prev0; have := hmi.prev
    refine ⟨hmi.not_pvq, hmi.not_pvr, hmi.not_snap, hmi.prev0, by omega, by omega, fun _ => ?_⟩
    have := (hinv.srv m.dest).log_len
    omega

end Etcdraft
end EtcdGrove
end Perennial
