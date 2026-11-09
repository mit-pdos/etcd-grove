/-
Lean-first (no Rocq counterpart).

# The search's copy-on-write: owned copies (Probe, 2026-11-08)

The checker's search never writes a state it was handed: an action `clone`s the state (a new
struct and a new server map sharing the servers) and `mut`s the server it changes (a `copy`: a
new struct and a new `MatchIndex` map), writes the copies, and returns the clone, which nobody
writes again. So a state or a server is read-only (`stateRO`, `serverRO`, `Rep.lean`) except
while the action building it holds it: `serverOwn` is a server copy being written, persisted into
`serverRO` once done (`serverOwn_persist`). Layer C's Probe (`notes/trace-validation-plan.md`,
"Probe set") checks this design on `(*State).Timeout`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Rep

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

/-- An id below `2^64` read back from its word. -/
theorem uint_nat_W64_of_lt (j : Nat) (h : j < 2 ^ 64) : uint.nat (W64 (Int.ofNat j)) = j := by
  show BitVec.toNat (BitVec.ofInt 64 (Int.ofNat j)) = j
  rw [BitVec.toNat_ofInt]
  have : (j : Int) < 2 ^ 64 := by exact_mod_cast h
  simp only [Int.ofNat_eq_natCast]
  omega

/-- Go `==` on signed-read words is `=` on their values (layer C's actions, 2026-11-09). -/
theorem sint_eq_iff (a b : w64) (x y : Int) (ha : sint.Z a = x) (hb : sint.Z b = y) : a = b ↔ x = y := by
  subst ha hb
  constructor
  · rintro rfl; rfl
  · intro h; word

/-- Go `==` on unsigned-read words is `=` on their values. -/
theorem uint_eq_iff (a b : w64) (x y : Nat) (ha : uint.nat a = x) (hb : uint.nat b = y) : a = b ↔ x = y := by
  subst ha hb
  constructor
  · rintro rfl; rfl
  · intro h; exact word.unsigned_inj (by have := congrArg (fun n : Nat => (n : Int)) h; simpa using this)

/-- The Go's message types are distinct. -/
theorem msgTypeW_inj {t t' : MsgType} (h : msgTypeW t = msgTypeW t') : t = t' := by
  cases t <;> cases t' <;> first | rfl | exact absurd h (by decide)

/-- Go `==` on a message's type, as the Lean's. -/
theorem msgTypeW_decide {w : w8} {t : MsgType} (h : w = msgTypeW t) (t' : MsgType) :
    decide (w = msgTypeW t') = decide (t = t') := by
  subst h
  exact decide_eq_decide.2 ⟨msgTypeW_inj, fun e => e ▸ rfl⟩

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- `s[:len(s):len(s)]` (Go's way to force `append` to copy) holds `s`'s elements, with no spare
capacity (layer C's `replicate`, 2026-11-09; a general fact about slices, a candidate for
Perennial's `Slice.lean`). -/
theorem ownSlice_fullSlice_len {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (s : GoSlice)
    (vs : List V) (dq : DFrac) :
    ownSlice (GF := GF) s vs dq ⊢ ownSlice (slice.fullSlice s V (W64 0) s.len s.len) vs dq := by
  have hz : sint.Z (W64 0) = 0 := rfl
  have he : slice.fullSlice s V (W64 0) s.len s.len = slice.mk s.ptr s.len s.len := by
    simp only [slice.fullSlice, sliceIndexRef, hz, go.arrayIndexRef_0]
    congr 1 <;> simp
  rw [he, ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, %Hl⟩)
  · obtain ⟨rfl, rfl⟩ := H
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  · iright
    iframe H
    ipureintro; exact Int.le_refl _

/-- The empty log, nil (a new message's `Entries`). -/
theorem logRO_nil : ⊢ logRO (GF := GF) slice.nil [] := by
  iunfold logRO
  iexists []
  ihave #H := ownSlice_nil (V := G.Entry) (GF := GF) DfracDiscarded
  iframe H
  iapply BigSepL2.bigSepL2_nil.2
  ipureintro; trivial

/-- A `*Server` copy being written: `serverRO`'s, with the struct and the `MatchIndex` map owned. -/
def serverOwn (p : Loc) (v : Server) : IProp GF :=
  iprop(∃ (g : G.Server) (mm : GMap w64 w64), p ↦ g ∗
    ⌜sint.Z g.CurrentTerm' = v.currentTerm ∧ strRel g.State' v.state ∧
      uint.nat g.VotedFor' = v.votedFor ∧ uint.nat g.Lead' = v.lead ∧ sint.Z g.CommitIndex' = v.commitIndex ∧
      sint.Z g.PendingConfChangeIndex' = v.pendingConfChangeIndex⌝ ∗
    logRO g.Log' v.log ∗ setRO g.VotesResponded' v.votesResponded ∗
    setRO g.VotesGranted' v.votesGranted ∗
    g.MatchIndex' ↦$ mm ∗
    ⌜∀ j : w64, sint.Z ((mm !! j).getD (W64 0)) = v.matchIndex (uint.nat j)⌝ ∗
    configRO g.Config' v.config ∗ durableRO g.Durable' v.durable)

/-- A copy, from its struct's fields (layer C's actions, 2026-11-09: a write to the copy `mut` returned
builds the new struct, then this). -/
theorem serverOwn_intro (p : Loc) (g : G.Server) (mm : GMap w64 w64) (v : Server)
    (hf : sint.Z g.CurrentTerm' = v.currentTerm ∧ strRel g.State' v.state ∧
      uint.nat g.VotedFor' = v.votedFor ∧ uint.nat g.Lead' = v.lead ∧ sint.Z g.CommitIndex' = v.commitIndex ∧
      sint.Z g.PendingConfChangeIndex' = v.pendingConfChangeIndex)
    (hm : ∀ j : w64, sint.Z ((mm !! j).getD (W64 0)) = v.matchIndex (uint.nat j)) :
    p ↦ g ∗ g.MatchIndex' ↦$ mm ∗ logRO g.Log' v.log ∗ setRO g.VotesResponded' v.votesResponded ∗
      setRO g.VotesGranted' v.votesGranted ∗ configRO g.Config' v.config ∗ durableRO g.Durable' v.durable ⊢
      serverOwn (GF := GF) p v := by
  iintro ⟨Hp, Hm, Hl, Hr, Hg, Hc, Hd⟩
  iunfold serverOwn
  iexists g, mm
  iframe Hp Hm Hl Hr Hg Hc Hd
  ipureintro; exact ⟨hf, hm⟩

/-- A written copy, frozen. -/
theorem serverOwn_persist (p : Loc) (v : Server) :
    serverOwn (GF := GF) p v ⊢ |==> serverRO p v := by
  iintro H
  iunfold serverOwn at H
  icases H with ⟨%g, %mm, Hp, %Hf, #Hl, #Hr, #Hg, Hm, %Hmi, #Hc, #Hd⟩
  ipersist Hp
  ipersist Hm
  imodintro
  iunfold serverRO
  iexists g, mm
  iframe Hp Hl Hr Hg Hm Hc Hd
  ipureintro; exact ⟨Hf, Hmi⟩

/-- A `*State` clone being built: the struct and the server map owned; the servers in `M` are
copies being written (`serverOwn`), the others shared (`serverRO`). -/
def stateOwn (p : Loc) (st : State) (M : List ID) : IProp GF :=
  iprop(∃ (g : G.State) (sm : GMap w64 Loc), p ↦ g ∗ setRO g.Server' st.server ∗
    g.S' ↦$ sm ∗
    ⌜∀ k : w64, (sm !! k).isSome ↔ uint.nat k ∈ st.server⌝ ∗
    ⌜st.server.Nodup⌝ ∗
    ([∗list] i ∈ st.server, ∃ q : Loc, ⌜sm !! (W64 (Int.ofNat i)) = some q⌝ ∗
      (if i ∈ M then serverOwn q (st.s i) else serverRO q (st.s i))) ∗
    bagRO g.Messages' st.messages ∗ bagRO g.PendingMessages' st.pendingMessages ∗
    ⌜sint.Z g.ReconfigCount' = st.reconfigCount ∧ g.PreVote' = st.preVote ∧ g.CheckQuorum' = st.checkQuorum⌝)

/-- A built clone, frozen. -/
theorem stateOwn_persist (p : Loc) (st : State) (M : List ID) :
    stateOwn (GF := GF) p st M ⊢ |==> stateRO p st := by
  iintro H
  iunfold stateOwn at H
  icases H with ⟨%g, %sm, Hp, #Hsrv, Hm, %Hkeys, %Hnd, Hsrvs, #Hb1, #Hb2, %Hrc⟩
  ipersist Hp
  ipersist Hm
  ihave Hsrvs : iprop([∗list] i ∈ st.server, |==> ∃ q : Loc, ⌜sm !! (W64 (Int.ofNat i)) = some q⌝ ∗
      serverRO (GF := GF) q (st.s i)) $$ [Hsrvs]
  · iapply (BigSepL.bigSepL_mono (fun {_ i} _ => ?_)) $$ Hsrvs
    iintro ⟨%q, %Hq, Hs⟩
    by_cases hi : i ∈ M
    · simp only [hi, ite_true]
      imod serverOwn_persist $$ Hs with Hs
      imodintro; iexists q; iframe Hs; ipureintro; exact Hq
    · simp only [hi, ite_false]
      imodintro; iexists q; iframe Hs; ipureintro; exact Hq
  imod BigSepL.bigSepL_bupd _ _ $$ Hsrvs with Hsrvs
  imodintro
  iunfold stateRO
  iexists g, sm
  iframe Hp Hsrv Hm Hb1 Hb2 Hsrvs
  ipureintro; exact ⟨Hkeys, Hnd, Hrc⟩

/-- A clone whose server `i` is a copy at `c` held apart (`mut`'s result, being written): `stateOwn`
without server `i`'s resource. -/
def stateOwnHole (p : Loc) (st : State) (M : List ID) (i : ID) (c : Loc) : IProp GF :=
  iprop(∃ (g : G.State) (sm : GMap w64 Loc), p ↦ g ∗ setRO g.Server' st.server ∗
    g.S' ↦$ sm ∗
    ⌜∀ k : w64, (sm !! k).isSome ↔ uint.nat k ∈ st.server⌝ ∗
    ⌜st.server.Nodup⌝ ∗
    ⌜sm !! (W64 (Int.ofNat i)) = some c⌝ ∗
    ([∗list] j ∈ st.server, if j = i then emp else ∃ q : Loc, ⌜sm !! (W64 (Int.ofNat j)) = some q⌝ ∗
      (if j ∈ M then serverOwn q (st.s j) else serverRO q (st.s j))) ∗
    bagRO g.Messages' st.messages ∗ bagRO g.PendingMessages' st.pendingMessages ∗
    ⌜sint.Z g.ReconfigCount' = st.reconfigCount ∧ g.PreVote' = st.preVote ∧ g.CheckQuorum' = st.checkQuorum⌝)

/-- Server `i`, written to `v`, put back: the clone holds `st` with server `i` set to `v`. -/
theorem stateOwnHole_close (p : Loc) (st : State) (M : List ID) (i : ID) (c : Loc) (v : Server)
    (hi : i ∈ st.server) :
    stateOwnHole (GF := GF) p st M i c ∗ serverOwn c v ⊢
      stateOwn p (st.upd i (fun _ => v)) (i :: M) := by
  iintro ⟨H, Hc⟩
  iunfold stateOwnHole at H
  icases H with ⟨%g, %sm, Hp, #Hsrv, Hm, %Hkeys, %Hnd, %Hci, Hsrvs, #Hb1, #Hb2, %Hrc⟩
  obtain ⟨l1, l2, Hsplit⟩ := List.append_of_mem hi
  have hnd' := Hnd
  rw [Hsplit] at hnd'
  have hi1 : i ∉ l1 := by
    intro h
    have := (List.nodup_append.1 hnd').2.2
    exact this i h i List.mem_cons_self rfl
  have hi2 : i ∉ l2 := (List.nodup_cons.1 (List.nodup_append.1 hnd').2.1).1
  iunfold stateOwn
  iexists g, sm
  iframe Hp Hm
  simp only [State.upd]
  iframe Hsrv Hb1 Hb2
  isplitr
  · ipureintro; exact Hkeys
  isplitr
  · ipureintro; exact Hnd
  isplitl [Hsrvs Hc]
  · rw [Hsplit]
    icases BigSepL.bigSepL_append.1 $$ Hsrvs with ⟨H1, H2⟩
    icases BigSepL.bigSepL_cons.1 $$ H2 with ⟨-, H2⟩
    iapply BigSepL.bigSepL_append.2
    isplitl [H1]
    · iapply (BigSepL.bigSepL_mono (fun {_ j} hj => ?_)) $$ H1
      have hji : j ≠ i := fun h => hi1 (h ▸ List.mem_of_getElem? hj)
      simp only [hji, ite_false, List.mem_cons, false_or]
      exact .rfl
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hc]
    · simp only [ite_true, List.mem_cons, true_or]
      iexists c; iframe Hc; ipureintro; exact Hci
    iapply (BigSepL.bigSepL_mono (fun {_ j} hj => ?_)) $$ H2
    have hji : j ≠ i := fun h => hi2 (h ▸ List.mem_of_getElem? hj)
    simp only [hji, ite_false, List.mem_cons, false_or]
    exact .rfl
  ipureintro; exact Hrc

/-- `stateOwnHole_close`, with the server's update as a function (the Lean actions' `upd`). -/
theorem stateOwnHole_close_upd (p : Loc) (st : State) (M : List ID) (i : ID) (c : Loc) (f : Server → Server)
    (hi : i ∈ st.server) :
    stateOwnHole (GF := GF) p st M i c ∗ serverOwn c (f (st.s i)) ⊢ stateOwn p (st.upd i f) (i :: M) :=
  stateOwnHole_close p st M i c (f (st.s i)) hi

/-- The builtin `max` on `int` (layer C's actions, 2026-11-09). -/
theorem wp_max_int (x y : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.max [go.int, go.int])) (Val #x)) (Val #y))
    {{ RET #(if sint.Z y < sint.Z x then x else y); True }} := by
  wp_start
  by_cases h : sint.Z y < sint.Z x
  · rw [decide_eq_true h, ite_eq_left_of_eq_true _ _ (eq_true h)]; wp_auto; iapply HΦ; itrivial
  · rw [decide_eq_false h, ite_eq_right_of_eq_false _ _ (eq_false h)]; wp_auto; iapply HΦ; itrivial

/-- The builtin `min` on `int`. -/
theorem wp_min_int (x y : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.min [go.int, go.int])) (Val #x)) (Val #y))
    {{ RET #(if sint.Z x < sint.Z y then x else y); True }} := by
  wp_start
  by_cases h : sint.Z x < sint.Z y
  · rw [decide_eq_true h, ite_eq_left_of_eq_true _ _ (eq_true h)]; wp_auto; iapply HΦ; itrivial
  · rw [decide_eq_false h, ite_eq_right_of_eq_false _ _ (eq_false h)]; wp_auto; iapply HΦ; itrivial

theorem sint_max (x y : w64) : sint.Z (if sint.Z y < sint.Z x then x else y) = max (sint.Z x) (sint.Z y) := by
  split <;> omega

theorem sint_min (x y : w64) : sint.Z (if sint.Z x < sint.Z y then x else y) = min (sint.Z x) (sint.Z y) := by
  split <;> omega

end defs

/-! ## Tactics for the actions' proofs (layer C, 2026-11-09)

Hygiene off: they name the proof's hypotheses. `mut_open p, st, M, i, H` calls `p.mut(i)` (the callee's spec
`wp_mut` in scope, `stateOwn p st M` as `H`, `Hi : uint.nat i ∈ st.server`), leaving the hole `Hh` and
the copy at `cp`, its struct `gc` split into its named fields, its map `Hcm` (`mc`, `Hcmi`), its other
predicates `Hcl Hcr Hcg Hcc Hcd`, `Hcf` its pure facts. `close_copy gv, f, hv` puts the fields back as
the struct `gv`, holding `f (st.s (uint.nat i))` (`hv` its pure facts, as `serverOwn_intro`'s), and
closes the hole: `Hs : stateOwn p (st.upd (uint.nat i) f) (uint.nat i :: M)`. -/

set_option hygiene false in
macro "mut_open" p:term "," st:term "," M:term "," i:term "," H:ident : tactic => `(tactic| (
    wp_apply wp_mut $p $st $M $i $$ [$H:ident] as %cp ⟨Hh, Hc⟩
    · iframe $H:ident; ipureintro; exact Hi
    try wp_auto
    iunfold serverOwn at Hc
    icases Hc with ⟨%gc, %mc, Hcp, %Hcf, #Hcl, #Hcr, #Hcg, Hcm, %Hcmi, #Hcc, #Hcd⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hcp with ⟨Hcp, %Hcnn⟩
    icases typedPointsto_split _ _ _ $$ Hcp with Hcpf
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hcpf))

set_option hygiene false in
macro "close_copy" gv:term "," f:term "," hv:term : tactic => `(tactic| (
    ihave Hcp : cp ↦ ($gv : G.Server) $$ [CurrentTerm State VotedFor Lead Log CommitIndex VotesResponded
        VotesGranted MatchIndex PendingConfChangeIndex Config Durable]
    · iapply typedPointsto_combine _ _ _ Hcnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hc := serverOwn_intro cp ($gv : G.Server) mc (($f : Server → Server) (st.s (uint.nat i))) $hv Hcmi
        $$ [Hcp Hcm]
    · iframe Hcp Hcm Hcl Hcr Hcg Hcc Hcd
    ihave Hs := stateOwnHole_close_upd _ _ _ _ _ ($f : Server → Server) Hi $$ [Hh Hc]
    · iframe))



/-! `read_server`: from `Hst : stateRO p st` and `Hi : uint.nat i ∈ st.server`, the state's struct `g`
split (`P1`..`P7`), its map `Hm` (`sm`), server `i`'s pointer `q0` (`Hq0 : sm !! i = some q0`), its
struct `gs` split (`V1`..`V12`), `Hf` its pure facts, its predicates `Hlog Hvr Hvg Hmm Hmi Hcfg Hdur`,
its log's slice `Hes` (`es`, `Hesl`, `Hell`, `Hel`). `lookup_server` then steps over `s.S[i]`. -/
set_option hygiene false in
macro "read_server" : tactic => `(tactic| (
    ihave #Hst0 := Hst
    iunfold stateRO at Hst0
    icases Hst0 with ⟨%g, %sm, #Hp, #Hsrv, #Hm, %Hkeys, %Hnd, #Hsrvs, #Hb1, #Hb2, %Hrc⟩
    obtain ⟨k, hk, hki⟩ := List.mem_iff_getElem.1 Hi
    icases (BigSepL.bigSepL_lookup (Φ := fun _ j => iprop(∃ q : Loc, ⌜sm !! (W64 (Int.ofNat j)) = some q⌝ ∗
        serverRO (GF := GF) q (st.s j))) (List.getElem?_eq_some_iff.2 ⟨hk, hki⟩)) $$ Hsrvs with ⟨%q0, %Hq0, #Hsv⟩
    have Hii : W64 (Int.ofNat (uint.nat i)) = i := by apply BitVec.eq_of_toNat_eq; simp
    rw [Hii] at Hq0
    icases typedPointsto_split _ _ _ $$ Hp with Hpf
    simp only [TypedPointsto.typedPointstoDef]
    icases Hpf with ⟨#P1, #P2, #P3, #P4, #P5, #P6, #P7, -⟩
    iunfold serverRO at Hsv
    icases Hsv with ⟨%gs, %mm, #Hq', %Hf, #Hlog, #Hvr, #Hvg, #Hmm, %Hmi, #Hcfg, #Hdur⟩
    icases typedPointsto_split _ _ _ $$ Hq' with Hqf
    simp only [TypedPointsto.typedPointstoDef]
    icases Hqf with ⟨#V1, #V2, #V3, #V4, #V5, #V6, #V7, #V8, #V9, #V10, #V11, #V12, -⟩
    ihave #Hlog0 := Hlog
    iunfold logRO at Hlog0
    icases Hlog0 with ⟨%es, #Hes, #Hel⟩
    ihave %Hesl := ownSlice_len $$ Hes
    ihave %Hell := BigSepL2.bigSepL2_length $$ Hel))

set_option hygiene false in
macro "lookup_server" : tactic => `(tactic| (
    wp_apply wp_map_lookup1 $$ [Hm] as -
    · iexact Hm
    rw [Hq0]
    simp only [Option.getD_some]
    try wp_auto))

/-! `read_msg`: from `Hmsg : msgRO q m`, the message's struct `gm` split (`M1`..`M14`), `Hv` its pure
facts, `Hve` its entries. -/
set_option hygiene false in
macro "read_msg" : tactic => `(tactic| (
    ihave #Hm0 := Hmsg
    iunfold msgRO at Hm0
    icases Hm0 with ⟨%gm, #Hq, %Hv, #Hve⟩
    icases typedPointsto_split _ _ _ $$ Hq with Hqmf
    simp only [TypedPointsto.typedPointstoDef]
    icases Hqmf with ⟨#M1, #M2, #M3, #M4, #M5, #M6, #M7, #M8, #M9, #M10, #M11, #M12, #M13, #M14, -⟩))

/-! `close_copy' gv, f, hv with Hl Hr Hg Hc Hd`: `close_copy`, the new struct's log, votes, configuration
and durable state given by the named hypotheses (a write that replaced one of them). -/
set_option hygiene false in
macro "close_copy'" gv:term "," f:term "," hv:term "with" hl:ident hr:ident hg:ident hc:ident hd:ident :
    tactic => `(tactic| (
    ihave Hcp : cp ↦ ($gv : G.Server) $$ [CurrentTerm State VotedFor Lead Log CommitIndex VotesResponded
        VotesGranted MatchIndex PendingConfChangeIndex Config Durable]
    · iapply typedPointsto_combine _ _ _ Hcnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hc := serverOwn_intro cp ($gv : G.Server) mc (($f : Server → Server) (st.s (uint.nat i))) $hv Hcmi
        $$ [Hcp Hcm]
    · iframe Hcp Hcm $hl:ident $hr:ident $hg:ident $hc:ident $hd:ident
    ihave Hs := stateOwnHole_close_upd _ _ _ _ _ ($f : Server → Server) Hi $$ [Hh Hc]
    · iframe))

end Etcdraft
end EtcdGrove
end Perennial
