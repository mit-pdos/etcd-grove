/-
Lean-first (no Rocq counterpart). #33 S4: **the reports of `Cluster.drain`**, the pieces its proof
(`Cluster__drain.lean`) records them with, in `Cluster__reportCause.lean`'s shape:
- the run after a report (`antRun_snoc`: the checker's prefix and relation from the report's lemma,
  the stream's bounds from the report's numbers, its receipts' fit, no configuration change) and
  after a step that reports nothing (`antRun_quiet`, `antSim_quiet`); the reports' `ChgOk 0`
  (`entOf` changes no name);
- raft's facts grown (`RaftFacts.Le`: every list larger, the committed log extended) keep `GlobalOk`
  (`globalOk_mono`);
- **one atomic update for every report of a drain** (`report_au`): the run's invariant opened (open:
  the caller's `live` token), raft's facts grown by the caller's persistent extension
  (`factsExt`, at the invariant's mask: a `ready` adds the node's new log, leadership, vote and
  commit, a `send` its message's), and at the commit the report's pure step (the caller's: the
  report's `antSim_*` lemma through `antRun_snoc`), the view moved, the messages `add` sent;
- **a step that reports nothing** (`quiet_upd`, `antSim_quiet`): the view moved under the
  invariant, no report.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessInv
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessRunLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Quiet
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Mono

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The run after a report -/

section pure
variable [GooseExts]

theorem weight_sum' (evs : List AntCheck.Event) :
    (evs.map AntCheck.Event.weight).sum = (evs.map AntCheck.Event.size).sum + 2 * evs.length := by
  induction evs with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, AntCheck.Event.weight, ih]
    omega

/-- **The run after a report** `ev`: the checker took it (`hP'`, the report's lemma), the relation
holds after it (`hA'`), and the stream's bounds: the receipts' fit, the report's numbers, no
configuration change. -/
theorem antRun_snoc (GF : BundledGFunctors) [ReceiptGS GF] {evs : List AntCheck.Event}
    {S S' : AntCheck.State} {V V' : Fin 3 → AntSim.NodeView} {net net' : List Msg}
    {ev : AntCheck.Event}
    (hR : AntRun evs S V net) (hP' : AntSim.Prefix AntSim.cfg3 (evs ++ [ev]) S')
    (hA' : AntSim.AntSim S' V' net') (hnums : ev.NumsOk) (hchg : ev.ChgOk 0)
    (hfit : Stream.Fits GF (evs ++ [ev])) (hrf : antRunFits GF) :
    AntRun (evs ++ [ev]) S' V' net' := by
  obtain ⟨-, -, hB, -, hC⟩ := hR
  refine ⟨hP', hA', ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · unfold Stream.Fits at hfit
      unfold antRunFits at hrf
      rw [weight_sum'] at hfit
      simp only [List.length_append, List.length_singleton, AntCheck.numBound] at hfit ⊢
      push_cast
      omega
    · intro e he
      rcases List.mem_append.1 he with h | h
      · exact hB.2 e h
      · rw [List.mem_singleton.1 h]; exact hnums
  · refine ⟨0, ?_, ?_⟩
    · intro e he
      rcases List.mem_append.1 he with h | h
      · exact hC e h
      · rw [List.mem_singleton.1 h]; exact hchg
    · rw [AntSim.cfg3_initVoters, AntSim.namesL_three]
      simp
  · intro e he
    rcases List.mem_append.1 he with h | h
    · exact hC e h
    · rw [List.mem_singleton.1 h]; exact hchg

/-- **The run after a step that reports nothing** (`antSim_quiet`). -/
theorem antRun_quiet {evs : List AntCheck.Event} {S : AntCheck.State}
    {V : Fin 3 → AntSim.NodeView} {net : List Msg} {G : AntSim.RaftFacts} {j : Fin 3}
    {v' : AntSim.NodeView} (hR : AntRun evs S V net) (hL : AntSim.RaftLaws G)
    (hG : AntSim.GlobalOk S net G) (hq : AntSim.Quiet (AntSim.nodeId j) net (V j) v') :
    AntRun evs S (AntSim.setV V j v') net := by
  obtain ⟨hP, hA, hB, hCB, hC⟩ := hR
  exact ⟨hP, AntSim.antSim_quiet S V net G j v' hA hL hG hq, hB, hCB, hC⟩

/-- A reported entry changes no name. -/
theorem entOf_chgSize (e : EntryM) : (AntSim.entOf e).chgSize = 0 := by
  unfold AntSim.entOf
  split <;> simp [AntCheck.Entry.chgSize]

theorem logOf_chgOk {l : List EntryM} : ∀ x ∈ AntSim.logOf l, x.chgSize ≤ 0 := by
  intro x hx
  simp only [AntSim.logOf, List.mem_map] at hx
  obtain ⟨e, -, rfl⟩ := hx
  exact Nat.le_of_eq (entOf_chgSize e)

theorem chgOk_evReady (id : w64) (b : AntCheck.Str) (r : Role) (t vo c : w64) (es : List EntryM) :
    (AntSim.evReady id b r t vo c es).ChgOk 0 := by
  intro l hl e he
  simp only [AntSim.evReady, AntCheck.Event.entryLists, Option.getD_some, Option.map_none,
    Option.getD_none, List.flatMap_nil, List.append_nil, List.mem_cons, List.not_mem_nil,
    or_false, List.nil_append] at hl
  subst hl
  exact logOf_chgOk e he

theorem chgOk_evSend (id : w64) (b : AntCheck.Str) (m : Msg) : (AntSim.evSend id b m).ChgOk 0 := by
  intro l hl e he
  simp only [AntSim.evSend, AntCheck.Event.entryLists, AntSim.msgOf, AntCheck.Msg.entryLists,
    Option.getD_none, Option.map_some, Option.getD_some, List.flatMap_nil, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · simp at he
  · exact logOf_chgOk e he

theorem chgOk_evApply (id : w64) (b : AntCheck.Str) (ce : List EntryM) :
    (AntSim.evApply id b ce).ChgOk 0 := by
  intro l hl e he
  simp only [AntSim.evApply, AntCheck.Event.entryLists, Option.getD_some, Option.map_none,
    Option.getD_none, List.flatMap_nil, List.append_nil, List.mem_cons, List.not_mem_nil,
    or_false, List.nil_append] at hl
  subst hl
  exact logOf_chgOk e he

/-- `setV` keeps every view's log certified when the new view's is. -/
theorem setV_logs {V : Fin 3 → AntSim.NodeView} {j : Fin 3} {v' : AntSim.NodeView}
    {L : List (List EntryM)} (h : ∀ i : Fin 3, (V i).ps.log ∈ L) (h' : v'.ps.log ∈ L) :
    ∀ i : Fin 3, (AntSim.setV V j v' i).ps.log ∈ L := by
  intro i
  unfold AntSim.setV
  split
  · exact h'
  · exact h i

/-! ## Raft's facts grown -/

/-- **`G'` extends `G`**: every list of facts larger, the committed log extended. -/
def RaftFacts.Le (G G' : AntSim.RaftFacts) : Prop :=
  (∀ x ∈ G.leaders, x ∈ G'.leaders) ∧ (∀ x ∈ G.votes, x ∈ G'.votes) ∧
  (∀ x ∈ G.logs, x ∈ G'.logs) ∧ (∀ x ∈ G.camps, x ∈ G'.camps) ∧
  G.committed <+: G'.committed ∧ (∀ x ∈ G.commits, x ∈ G'.commits)

theorem RaftFacts.Le.refl (G : AntSim.RaftFacts) : RaftFacts.Le G G :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, List.prefix_refl _, fun _ h => h⟩

theorem RaftFacts.Le.trans {G1 G2 G3 : AntSim.RaftFacts} (h1 : RaftFacts.Le G1 G2)
    (h2 : RaftFacts.Le G2 G3) : RaftFacts.Le G1 G3 :=
  ⟨fun x h => h2.1 x (h1.1 x h), fun x h => h2.2.1 x (h1.2.1 x h),
    fun x h => h2.2.2.1 x (h1.2.2.1 x h), fun x h => h2.2.2.2.1 x (h1.2.2.2.1 x h),
    h1.2.2.2.2.1.trans h2.2.2.2.2.1, fun x h => h2.2.2.2.2.2 x (h1.2.2.2.2.2 x h)⟩

/-- **`GlobalOk` is kept by larger facts.** -/
theorem globalOk_mono {S : AntCheck.State} {net : List Msg} {G G' : AntSim.RaftFacts}
    (hG : AntSim.GlobalOk S net G) (hle : RaftFacts.Le G G') : AntSim.GlobalOk S net G' := by
  obtain ⟨hl, hv, hlog, hled, ⟨c, hc, hch⟩, htl, happ⟩ := hG
  obtain ⟨hL, hV, hLg, hC, hP, hCs⟩ := hle
  refine ⟨?_, ?_, ?_, ?_, ⟨c, ?_, ?_⟩, ?_, ?_⟩
  · intro l h
    obtain ⟨j, t, hm, h1, h2⟩ := hl l h
    exact ⟨j, t, hL _ hm, h1, h2⟩
  · intro x h
    obtain ⟨a, t, c, hm, h1, h2, h3⟩ := hv x h
    exact ⟨a, t, c, hV _ hm, h1, h2, h3⟩
  · intro n
    obtain ⟨l, hm, h1⟩ := hlog n
    exact ⟨l, hLg _ hm, h1⟩
  · intro p h
    obtain ⟨l, hm, h1, t, l0, h2, h3, h4⟩ := hled p h
    exact ⟨l, hLg _ hm, h1, t, l0, h2, hC _ h3, h4⟩
  · exact Nat.le_trans hc hP.length_le
  · rw [hch]
    obtain ⟨d, hd⟩ := hP
    rw [← hd, List.take_append_of_le_length hc]
  · intro p h
    obtain ⟨h0, x, h1, h2⟩ := htl p h
    exact ⟨h0, x, h1, hCs _ h2⟩
  · intro m hm hty
    obtain ⟨l, hl', h1⟩ := happ m hm hty
    exact ⟨l, hLg _ hl', h1⟩


/-! ## A `Ready`'s data at the protocol level -/

theorem lcpLen_take : ∀ (l1 l2 : List EntryM), l1.take (lcpLen l1 l2) = l2.take (lcpLen l1 l2)
  | [], _ => by simp [lcpLen]
  | _ :: _, [] => by simp [lcpLen]
  | a :: xs, b :: ys => by
    unfold lcpLen
    split
    · rename_i h; subst h; simp [lcpLen_take xs ys]
    · simp

theorem lcpLen_ne : ∀ (l1 l2 : List EntryM) (a b : EntryM), l1[lcpLen l1 l2]? = some a →
    l2[lcpLen l1 l2]? = some b → a ≠ b
  | [], _, _, _ => by simp [lcpLen]
  | _ :: _, [], _, _ => by simp [lcpLen]
  | x :: xs, y :: ys, a, b => by
    unfold lcpLen
    split
    · intro h1 h2; exact lcpLen_ne xs ys a b (by simpa using h1) (by simpa using h2)
    · rename_i hne
      intro h1 h2
      simp at h1 h2
      rw [← h1, ← h2]; exact hne

/-- The `Ready`'s data as the harness reads it (`AntSim.ReadyD`), at the node's state `ps` (the
role and hard state `ReadyOut` reports), its entries `es`, its messages to others `msgs` (their
protocol readings), its queue `qs` and committed entries `ce`. -/
def readyDOf (ps : PState) (es : List EntryM) (msgs qs : List Msg) (ce : List EntryM) :
    AntSim.ReadyD :=
  { role := ps.role, term := ps.term, vote := ps.vote, commit := ps.commit, ents := es,
    msgs := msgs, qs := qs, ce := ce }

/-- **`ReadyOut` at the protocol level** (`ReadyOutP`): raft's `Ready` binding, at a loop head (the
record against the view, `RsView`; no committed entries left to report; the in-progress boundary at
the common prefix of the view's log and the node's), with the boundary fact of its first entry, its
queue, the log's shape (`base0`, its indices its positions), log matching between the view's log and
the node's (`hmatch`, from raft's laws: both are certified logs) and the messages' destinations
(`hvot`, `ReadyMsgsToVoters`: `msgShape.stmt`'s). -/
theorem readyOutP_of {id : w64} {v : AntSim.NodeView} {rs : RNState} {ps : PState} {h : HardStateM}
    {es ce : List EntryM} {ms : List QMsg} {ss : Option (w64 × StateType)} {L : Option SnapLoan}
    {qs : List Msg} {ip : Nat}
    (hRs : RsView rs v) (hce : v.ce = []) (hip : ip = lcpLen v.ps.log ps.log)
    (hout : ReadyOut id rs ps h es ce ms ss L) (hfirst : ∀ e0 ∈ es.head?, uint.nat e0.Index' = ip + 1)
    (hqs : qs.Perm (ps.outbox.filter (fun m => decide (m.dst = id))))
    (hbase : ps.base = base0) (hidx : AntSim.LogIdx ps.log)
    (hmatch : ∀ (k : Nat) (e f : EntryM), v.ps.log[k]? = some e → ps.log[k]? = some f →
      e.Term' = f.Term' → e = f)
    (hvot : ∀ q ∈ ms.filterMap (fun q => absMsgOf q.st), ∃ j : Fin 3, q.dst = AntSim.nodeId j) :
    AntSim.ReadyOutP id v ps (readyDOf ps es (ms.filterMap (fun q => absMsgOf q.st)) qs ce) := by
  obtain ⟨-, -, hdur, hdrop, hmsgs, -, hdlv, hdlen, hL⟩ := hout
  obtain ⟨-, -, hents, hdel, -, -, -⟩ := hRs
  subst hL
  rw [hce, List.append_nil] at hdel
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, hqs, hmsgs, ?_, ?_, hbase, hidx, hvot⟩
  · intro hnil
    simp only [readyDOf] at hnil
    subst hnil
    rw [← hdur, ← hents]
    simp [readyDurable, RaftState.next, appendEnts]
  · intro e0 he0
    simp only [readyDOf] at he0 ⊢
    have hi := hfirst e0 he0
    have hk : uint.nat e0.Index' - 1 = lcpLen v.ps.log ps.log := by omega
    rw [hk]
    have hd := hdrop e0 he0
    rw [hk] at hd
    refine ⟨?_, ?_⟩
    · rw [lcpLen_take, ← hd, List.take_append_drop]
    · intro e he hte
      have hf : ps.log[lcpLen v.ps.log ps.log]? = some e0 := by
        have : (ps.log.drop (lcpLen v.ps.log ps.log))[0]? = some e0 := by
          rw [hd, ← List.head?_eq_getElem?]; exact he0
        simpa using this
      exact lcpLen_ne _ _ e e0 he hf (hmatch _ e e0 he hf hte)
  · rw [hdel] at hdlv; exact hdlv
  · rw [hdel] at hdlen; exact hdlen

end pure

/-! ## The reports' atomic update -/

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **Raft's facts grown to `Q`** (what a report's caller supplies, persistent): any facts `G`
satisfying raft's laws, owned, extend at the invariant's mask to `G'`, still lawful, satisfying `Q`.
(`factsExt_none`: `Q` true of every `G`, nothing added.) -/
def factsExt (γ : AntNames) (Q : AntSim.RaftFacts → Prop) : IProp GF :=
  iprop(∀ G : AntSim.RaftFacts, ⌜AntSim.RaftLaws G⌝ -∗ raftFactsOwn γ.raft.raftNames G ={⊤ \ ↑antN}=∗
    ∃ G' : AntSim.RaftFacts, raftFactsOwn γ.raft.raftNames G' ∗
      ⌜AntSim.RaftLaws G' ∧ RaftFacts.Le G G' ∧ Q G'⌝)

theorem factsExt_none (γ : AntNames) : ⊢ factsExt (GF := GF) γ (fun _ => True) := by
  unfold factsExt
  iintro %G %HL #HF
  imodintro
  iexists G
  iframe HF
  ipureintro
  exact ⟨HL, RaftFacts.Le.refl G, trivial⟩

/-- **A report's atomic update** (every report of a drain): the run's invariant opened (open: the
caller's `live` token excludes the run being over), raft's facts grown (`factsExt`), the stream's
half given to the recorder; at the commit, the report's pure step `hstep` taken from the invariant's
state (the view `v`, the messages sent since the caller's lower bound `net₀`, the grown facts
satisfying `Q`): the view moves to `v'`, the messages `add` are sent. The caller gets a new lower
bound of the sent list, which has `add`. -/
theorem report_au (γ : AntNames) (j : Fin 3) (v v' : AntSim.NodeView) (ev : AntCheck.Event)
    (net₀ add : List Msg) (Q : AntSim.RaftFacts → Prop)
    (hstep : ∀ (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin 3 → AntSim.NodeView)
      (net : List Msg) (G : AntSim.RaftFacts),
      AntRun evs S V net → AntSim.RaftLaws G → AntSim.GlobalOk S net G →
      (∀ i : Fin 3, (V i).ps.log ∈ G.logs) → V j = v → Q G → net₀ <+: net →
      Stream.Fits GF (evs ++ [ev]) →
      ∃ S', AntRun (evs ++ [ev]) S' (AntSim.setV V j v') (net ++ add) ∧
        AntSim.GlobalOk S' (net ++ add) G ∧ v'.ps.log ∈ G.logs) :
    iprop(inv antN (antInv (GF := GF) γ) ∗ sentLb γ net₀ ∗ □ factsExt γ Q) ∗
        iprop(viewFrag γ j v ∗ nodeLive γ j) ⊢
      AU <{ ∃∃ evs, recAuth (GF := GF) γ.strm evs }> @ ⊤, ∅
        <{ recAuth γ.strm (evs ++ [ev]) ∗ ⌜Stream.Fits GF (evs ++ [ev])⌝,
          COMM viewFrag γ j v' ∗ nodeLive γ j ∗
            ∃ net : List Msg, sentLb γ net ∗ ⌜net₀ <+: net ∧ ∀ m ∈ add, m ∈ net⌝ }> := by
  refine sep_and.trans (aupd_intro ?_)
  iintro ⟨⟨#Hinv, #Hlb, #Hext⟩, ⟨Hv, Hl⟩⟩
  iunfold sentLb at Hlb
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold antInv at Hi
  icases Hi with (Hi | Hover)
  · iunfold antOpen at Hi
    icases Hi with ⟨%evs, %S, %V, %net, %G0, Hstr, H0, H1, H2, Hnet, %Hpure, #HF0⟩
    iunfold factsExt at Hext
    imod Hext $$ %G0 %Hpure.2.1 HF0 with ⟨%G, #HF, %HG⟩
    obtain ⟨hL, hle, hQ⟩ := HG
    have hGo : AntSim.GlobalOk S net G := globalOk_mono Hpure.2.2.1 hle
    have hlogs : ∀ i : Fin 3, (V i).ps.log ∈ G.logs := fun i => hle.2.2.1 _ (Hpure.2.2.2 i)
    ihave %Hpre := mono_list_auth_lb_valid (GF := GF) γ.sent 1 net net₀ $$ Hnet Hlb
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists ⟨evs, ⟨⟩⟩
    simp only [Std.Tele.app]
    unfold recAuth
    iframe Hstr
    isplit
    · iintro Hstr
      imod Hmask with -
      imod Hclose $$ [Hstr H0 H1 H2 Hnet] with -
      · inext
        iunfold antInv
        ileft
        iunfold antOpen
        iexists evs, S, V, net, G
        iframe Hstr H0 H1 H2 Hnet HF
        ipureintro; exact ⟨Hpure.1, hL, hGo, hlogs⟩
      imodintro
      iframe Hv Hl
    · iintro %y ⟨Hstr, %Hfit⟩
      imod Hmask with -
      imod view_update _ γ j V v v' $$ [Hv H0 H1 H2] with ⟨%HVj, Hv, H0, H1, H2⟩
      · iframe Hv H0 H1 H2
      obtain ⟨S', hR', hG', hlog'⟩ := hstep evs S V net G Hpure.1 hL hGo hlogs HVj hQ Hpre.2 Hfit
      imod monoListAuthOwn_update_app (GF := GF) (γ := γ.sent) add $$ Hnet with ⟨Hnet, #Hlb'⟩
      imod Hclose $$ [Hstr H0 H1 H2 Hnet] with -
      · inext
        iunfold antInv
        ileft
        iunfold antOpen
        iexists evs ++ [ev], S', AntSim.setV V j v', net ++ add, G
        iframe Hstr H0 H1 H2 Hnet HF
        ipureintro; exact ⟨hR', hL, hG', setV_logs hlogs hlog'⟩
      imodintro
      iframe Hv Hl
      iexists net ++ add
      iunfold sentLb
      iframe Hlb'
      ipureintro
      exact ⟨Hpre.2.trans (List.prefix_append _ _), fun m hm => List.mem_append_right _ hm⟩
  · iexfalso
    iapply nodeLive_over γ j
    iframe Hl Hover

/-- **A step that reports nothing** (`antSim_quiet`): the view moves under the invariant (open: the
caller's `live` token), over a lower bound `net₀` of the sent list. -/
theorem quiet_upd (γ : AntNames) (j : Fin 3) (v v' : AntSim.NodeView) (net₀ : List Msg)
    (hq : AntSim.Quiet (AntSim.nodeId j) net₀ v v') (hlog : v'.ps.log = v.ps.log) :
    inv antN (antInv (GF := GF) γ) ∗ sentLb γ net₀ ∗ viewFrag γ j v ∗ nodeLive γ j ⊢
      |={⊤}=> viewFrag γ j v' ∗ nodeLive γ j := by
  iintro ⟨#Hinv, #Hlb, Hv, Hl⟩
  iunfold sentLb at Hlb
  iinv Hinv with >Hi Hclose
  iunfold antInv at Hi
  icases Hi with (Hi | Hover)
  · iunfold antOpen at Hi
    icases Hi with ⟨%evs, %S, %V, %net, %G, Hstr, H0, H1, H2, Hnet, %Hpure, #HF⟩
    ihave %Hpre := mono_list_auth_lb_valid (GF := GF) γ.sent 1 net net₀ $$ Hnet Hlb
    imod view_update _ γ j V v v' $$ [Hv H0 H1 H2] with ⟨%HVj, Hv, H0, H1, H2⟩
    · iframe Hv H0 H1 H2
    have hq' : AntSim.Quiet (AntSim.nodeId j) net (V j) v' := by
      rw [HVj]; exact hq.mono Hpre.2
    have hR' := antRun_quiet Hpure.1 Hpure.2.1 Hpure.2.2.1 hq'
    have hlogs := setV_logs (j := j) (v' := v') Hpure.2.2.2
      (by rw [hlog, ← HVj]; exact Hpure.2.2.2 j)
    imod Hclose $$ [Hstr H0 H1 H2 Hnet] with -
    · inext
      iunfold antInv
      ileft
      iunfold antOpen
      iexists evs, S, AntSim.setV V j v', net, G
      iframe Hstr H0 H1 H2 Hnet HF
      ipureintro; exact ⟨hR', Hpure.2.1, Hpure.2.2.1, hlogs⟩
    imodintro
    iframe Hv Hl
  · iexfalso
    iapply nodeLive_over γ j
    iframe Hl Hover

end proof

end AntHarness
end EtcdGrove
end Perennial
