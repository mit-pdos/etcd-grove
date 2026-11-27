/-
# Leader completeness through the node API (2026-11-24, `notes/etcd-dist-d6.md`, T4 round 4)

Two laws over the API's sealed `raftState`, for a client that needs a node's durable log to hold a log
committed earlier (the server's replay terms, `rnReplayJob_of_history`):

- **L1** (`raftState_cmtBefore`): with its durable state `S0`, a node marks a committed log `l` as
  committed before every campaign it has made so far (`cmtBefore γ id S0.term l`, persistent, sealed).
- **L2** (`raftState_cmtBefore_agree`): a node that leads its durable state's term `S.term`, a term
  above the mark's (`T0 < S.term`), has `l` in its durable log (`durLogAgrees S l`); given a cluster
  whose membership is fixed (`confFixed`).

Why `T0 < S.term` and the fixed membership: `notes/etcd-dist-d6.md`, T4 round 4. A leader commits
entries of its own term before it saves them, so a mark at the leader's own term proves nothing of
its durable log (the commit-before-save run); and the case of a commit certificate at a term above
the leader's needs a voter of both quorums, which two quorums of one configuration have (with
membership changes it needs a recursion over the certificate's witness tree, not done).
-/
module
public import Proof.go_etcd_io.raft.v3.InvNodeRule
import Proof.go_etcd_io.raft.v3.Protocol.LeaderCompleteness
import all Proof.go_etcd_io.raft.v3.InvNodeRule
import all Proof.go_etcd_io.raft.v3.InvNode
import Proof.go_etcd_io.raft.v3.InvApi
import Proof.go_etcd_io.raft.v3.InvApiDec
import Proof.go_etcd_io.raft.v3.Protocol.Enter

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics] [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ## The vocabulary -/

/-- **`S`'s durable log agrees with `l`**: at every index of `l` that `S` has not compacted, `S`'s log
has `l`'s term (the entry at position `i` of `l` is at index `i + 1`). -/
def durLogAgrees (S : RaftState) (l : List LogEntry) : Prop :=
  ∀ (i : Nat) (e : LogEntry), uint.nat S.base.index' ≤ i + 1 → l[i]? = some e →
    plogTermAt S.base S.ents (W64 ((i : Int) + 1)) = some e.term

/-- **The cluster's membership is `m0` after every committed log** (L2's premise): what a client
whose configuration never changes can show (the server: `srv_confAt_simple`). -/
def confFixed (γ : Cluster) (E : CoPset) (m0 : Membership) : IProp GF :=
  iprop(□ ∀ l : List LogEntry, isCommittedLogLb γ l ={E}=∗ confAt γ l.length m0)

instance confFixed_persistent (γ : Cluster) (E : CoPset) (m0 : Membership) :
    Persistent (confFixed (GF := GF) γ E m0) := by
  unfold confFixed; infer_instance

/-- (internal) A vote event of `v`'s history, with its candidate. -/
@[no_expose] def voteHas (γ : RaftNames) (v : w64) : Aev → IProp GF
  | .vote T _ _ => iprop(∃ c, isVote γ v T c)
  | .ack _ _ => iprop(True)

/-- (internal) A vote event of `v`'s history, for `id` only at a term `≤ T0`. -/
@[no_expose] def voteBefore (γ : RaftNames) (id T0 v : w64) : Aev → IProp GF
  | .vote T _ _ => iprop(∃ c, isVote γ v T c ∗ ⌜c = id → uint.Z T ≤ uint.Z T0⌝)
  | .ack _ _ => iprop(True)

instance voteHas_persistent (γ : RaftNames) (v : w64) (e : Aev) :
    Persistent (voteHas (GF := GF) γ v e) := by
  cases e <;> unfold voteHas <;> infer_instance

instance voteBefore_persistent (γ : RaftNames) (id T0 v : w64) (e : Aev) :
    Persistent (voteBefore (GF := GF) γ id T0 v e) := by
  cases e <;> unfold voteBefore <;> infer_instance

/-- (internal) `v` acknowledged at `t`, every vote before it for `id` only at a term `≤ T0`. -/
@[no_expose] def ackBefore (γ : RaftNames) (id T0 v t : w64) : IProp GF :=
  iprop(∃ γe La i, ⌜γ.reEvs !! v = some γe ∧ Aev.ack t i ∈ La ∧ EvSorted La⌝ ∗
    monoListLbOwn γe La ∗ [∗list] e ∈ La, voteBefore γ id T0 v e)

instance ackBefore_persistent (γ : RaftNames) (id T0 v t : w64) :
    Persistent (ackBefore (GF := GF) γ id T0 v t) := by
  unfold ackBefore; infer_instance

/-- (internal) `cmtBefore`'s body over raft's names: `l` is empty, or within the bootstrap log, or
within a commit certificate (`cqAt`) whose leader is `id` only at a term `≤ T0` and whose quorum's
acknowledgements followed votes for `id` only at terms `≤ T0`. -/
@[no_expose] def cmtBeforeR (γ : RaftNames) (id T0 : w64) (l : List LogEntry) : IProp GF :=
  iprop(⌜l = []⌝ ∨ ⌜l <+: strip γ.reBoot ∧ PlogWf base0 γ.reBoot⌝ ∨
    ∃ (t n : w64) (G : List EntryM) (a : w64) (c : CfgM) (q : GSet w64) (ldr : w64),
      ⌜l <+: strip (G.take (uint.Z n).toNat) ∧ 0 < uint.Z n⌝ ∗ cqAt γ t n G a c q ∗
      isLeader γ ldr t ∗ ⌜ldr = id → uint.Z t ≤ uint.Z T0⌝ ∗
      [∗map] v ↦ _u ∈ toMap q, ackBefore γ id T0 v t)

instance cmtBeforeR_persistent (γ : RaftNames) (id T0 : w64) (l : List LogEntry) :
    Persistent (cmtBeforeR (GF := GF) γ id T0 l) := by
  unfold cmtBeforeR; infer_instance

/-- **`l` was committed before every campaign `id` had made when its durable term was `T0`**
(persistent, sealed; L1 makes it, L2 uses it). -/
@[no_expose] def cmtBefore (γ : Cluster) (id T0 : w64) (l : List LogEntry) : IProp GF :=
  cmtBeforeR (ApiImpl.Cluster.raft γ) id T0 l

instance cmtBefore_persistent (γ : Cluster) (id T0 : w64) (l : List LogEntry) :
    Persistent (cmtBefore (GF := GF) γ id T0 l) := by
  unfold cmtBefore; infer_instance

/-! ## Pure lemmas -/

private theorem keep_pure {P : IProp GF} {φ : Prop} (h : P ⊢ ⌜φ⌝) : P ⊢ P ∗ ⌜φ⌝ :=
  (and_intro .rfl h).trans persistent_and_sep.1

private theorem wf_len_lt (F : List EntryM) (hw : PlogWf base0 F) : F.length < 2 ^ 64 := by
  rcases Nat.eq_zero_or_pos F.length with h0 | hpos
  · omega
  · obtain ⟨e, he⟩ : ∃ e, F[F.length - 1]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hi := hw _ e he
    rw [base0_index] at hi
    have := uint_Z_lt e.Index'
    omega

/-- A log agreeing with a full log `fp ++ S.ents` up to `P`'s end has `P`'s prefixes. -/
theorem durLogAgrees_of (S : RaftState) (fp P : List EntryM) (l : List LogEntry)
    (hfull : FullOk S.base fp) (hl : l <+: strip P) (hP : P.length < 2 ^ 64)
    (hag : ∀ j : w64, 0 < uint.Z j → uint.Z j ≤ P.length →
      plogTermAt base0 (fp ++ S.ents) j = plogTermAt base0 P j) :
    durLogAgrees S l := by
  intro i e hb hi
  obtain ⟨r, hr⟩ := hl
  have hil : i < l.length := (List.getElem?_eq_some_iff.mp hi).1
  have hs : (strip P)[i]? = some e := by
    rw [← hr, List.getElem?_append_left hil]; exact hi
  unfold strip at hs
  rw [List.getElem?_map] at hs
  cases hx : P[i]? with
  | none => rw [hx] at hs; cases hs
  | some x =>
    rw [hx] at hs
    simp only [Option.map_some, Option.some.injEq] at hs
    subst hs
    have hiP : i < P.length := (List.getElem?_eq_some_iff.mp hx).1
    have hj : uint.Z (W64 ((i : Int) + 1)) = (i : Int) + 1 := by
      rw [uint_Z_W64 _ (by omega) (by omega)]
    have h1 : plogTermAt base0 P (W64 ((i : Int) + 1)) = some x.Term' :=
      plogTermAt_lookup base0 P _ i x hx (by rw [hj, base0_index]; push_cast; omega)
    have h2 := hag (W64 ((i : Int) + 1)) (by rw [hj]; omega) (by rw [hj]; omega)
    rw [h1, full_term_at S.base fp S.ents _ hfull (by rw [hj]; have := uint_nat_eq S.base.index'; omega)] at h2
    exact h2

/-- A sorted history holding `v`'s vote at `T` and, in a comparable history, an acknowledgement at a
later term has the vote before the acknowledgement. -/
theorem ev_vote_mem (L0 La : List Aev) (t i T : w64) (d : Bool) (F : List EntryM) :
    uint.Z T < uint.Z t → Aev.ack t i ∈ La → EvSorted (L0 ++ [Aev.vote T d F]) →
    (La <+: L0 ++ [Aev.vote T d F] ∨ L0 ++ [Aev.vote T d F] <+: La) →
    Aev.vote T d F ∈ La := by
  intro HTt Hin Hsort Hp
  rcases Hp with Hp | Hp
  · exfalso
    have Hin' := Hp.subset Hin
    rcases List.mem_append.mp Hin' with H0 | H1
    · obtain ⟨p, Hp0⟩ := List.mem_iff_getElem?.mp H0
      have hpl : p < L0.length := (List.getElem?_eq_some_iff.mp Hp0).1
      have := Hsort p L0.length (Aev.ack t i) (Aev.vote T d F) hpl
        (by rw [List.getElem?_append_left hpl]; exact Hp0) (by simp)
      simp only [aevTerm] at this; omega
    · simp at H1
  · exact Hp.subset (by simp)

/-! ## Ghost lemmas -/

theorem durShares_campK (γ : RaftNames) (id T : w64) (q : Qp) (E : DurMaps) (F : List EntryM)
    (k : w64) : durShares (GF := GF) γ id q E ∗ isCampK γ id T F k ⊢ ⌜E.camps !! T = some (F, k)⌝ := by
  unfold durShares isCampK
  iintro ⟨⟨%γv, %γa, %γc, %γl, %γe, %Hγ, -, -, Hc, -, -⟩, ⟨%γc', %Hc', #Hf, -⟩⟩
  have h := Hc'.1
  rw [Hγ.2.2.1] at h
  cases h
  iapply ghost_map_lookup $$ Hc Hf

theorem isLeader_campK (γ : RaftNames) (id T : w64) :
    isLeader (GF := GF) γ id T ⊢ ∃ F k, isCampK γ id T F k := by
  unfold isLeader
  iintro ⟨%V, #Hw⟩
  icases isWin_core γ id T V $$ Hw with ⟨%c, #Hc⟩
  iunfold isWinCore at Hc
  icases Hc with ⟨%γw, %F0, %k, %M, -, #HcK, -⟩
  iexists F0, k
  iexact HcK

/-- A vote for `id` was cast in a campaign of `id`, which its campaign authority bounds. -/
theorem vote_id_le (γ : RaftNames) (id v T T0 : w64) (q : Qp) (E : DurMaps)
    (Hb : ∀ T, (E.camps !! T).isSome → uint.Z T ≤ uint.Z T0) :
    votesTbl (GF := GF) γ ∗ durShares γ id q E ∗ isVote γ v T id ⊢ ⌜uint.Z T ≤ uint.Z T0⌝ := by
  iintro ⟨Htbl, Hsh, #Hv⟩
  ihave #Hj := votesTbl_just γ v T id $$ Htbl Hv
  iunfold voteJust at Hj
  icases Hj with ⟨%k, %d, %Fv, %Fc, -, #Hc, -⟩
  iunfold isCamp at Hc
  icases Hc with ⟨%kc, #HcK⟩
  icases durShares_campK γ id T q E Fc kc $$ [$Hsh $HcK] with %H
  ipureintro
  exact Hb T (by rw [H]; rfl)

/-- An acknowledgement's vote events, as a list. -/
theorem ackEv_votes (γ : RaftNames) (v : w64) (La : List Aev) :
    (□ ∀ (T : w64) (d : Bool) (F : List EntryM), ∀ (_ : Aev.vote T d F ∈ La), ∃ c, isVote (GF := GF) γ v T c)
      ⊢ [∗list] e ∈ La, voteHas γ v e := by
  apply BigSepL.bigSepL_intro
  intro k e he
  cases e with
  | ack t i =>
    unfold voteHas
    iintro -
    ipureintro; trivial
  | vote T d F =>
    unfold voteHas
    iintro #H
    iapply H $$ %T %d %F %(List.mem_of_getElem? he)

/-- L1's step: an acknowledgement of the quorum, its votes timed against the campaigns. -/
theorem ackBefore_of (γ : RaftNames) (id T0 v t i : w64) (E : DurMaps) (Em : CoPset)
    (Hb : ∀ T, (E.camps !! T).isSome → uint.Z T ≤ uint.Z T0) (Hi : 0 < uint.Z i) :
    ⊢ (votesTbl (GF := GF) γ ∗ durShares γ id (1 : Qp).half E) -∗ isAcked γ v t i ={Em}=∗
      (votesTbl γ ∗ durShares γ id (1 : Qp).half E) ∗ ackBefore γ id T0 v t := by
  iintro R #Ha
  unfold isAcked
  icases Ha with (%H0 | ⟨-, #Hev⟩)
  · exfalso; omega
  unfold ackEv
  icases Hev with ⟨%γe, %La, %Hp, #Hlb, #Hall⟩
  ihave #Hl := ackEv_votes γ v La $$ Hall
  imod bigSepL_fupd_thread Em (iprop(votesTbl (GF := GF) γ ∗ durShares γ id (1 : Qp).half E))
      (voteHas γ v) (voteBefore γ id T0 v) La $$ [] R Hl with ⟨R, #Hl'⟩
  · imodintro
    iintro %x ⟨Htbl, Hsh⟩ #Hx
    cases x with
    | ack t' i' =>
      imodintro
      iframe Htbl Hsh
      unfold voteBefore
      ipureintro; trivial
    | vote T d F =>
      unfold voteHas
      icases Hx with ⟨%c, #Hv⟩
      by_cases hc : c = id
      · subst hc
        icases keep_pure (vote_id_le γ c v T T0 (1 : Qp).half E Hb) $$ [$Htbl $Hsh $Hv]
          with ⟨⟨Htbl, Hsh, -⟩, %Hle⟩
        imodintro
        iframe Htbl Hsh
        unfold voteBefore
        iexists c
        iframe Hv
        ipureintro; intro _; exact Hle
      · imodintro
        iframe Htbl Hsh
        unfold voteBefore
        iexists c
        iframe Hv
        ipureintro; intro h; exact absurd h hc
  imodintro
  iframe R
  unfold ackBefore
  iexists γe, La, i
  iframe Hlb Hl'
  ipureintro; exact Hp

/-- The voter of both quorums (L2's case `t > T`): its acknowledgement at `t` followed its vote at
`T` for `id`, which the mark puts at a term `≤ T0`. -/
theorem ackBefore_vote (γ : RaftNames) (id T0 v t T : w64) :
    uint.Z T0 < uint.Z T → uint.Z T < uint.Z t →
    votesTbl (GF := GF) γ ∗ ackBefore γ id T0 v t ∗ isVote γ v T id ⊢ ⌜False⌝ := by
  intro HT0 HTt
  iintro ⟨Htbl, #Hab, #Hv⟩
  ihave #Hj := votesTbl_just γ v T id $$ Htbl Hv
  iunfold voteJust at Hj
  icases Hj with ⟨%k, %d, %Fv, %Fc, -, -, -, -, -, #Hvev, -⟩
  iunfold voteEv at Hvev
  icases Hvev with ⟨%γe', %L0, %Hγ', #Hlb', %Hsort, -⟩
  unfold ackBefore
  icases Hab with ⟨%γe, %La, %i, %Hp, #Hlb, #Hlist⟩
  obtain ⟨Hγ, Hin, -⟩ := Hp
  rw [Hγ] at Hγ'
  cases Hγ'
  icases mono_list_lb_valid _ _ _ $$ Hlb Hlb' with %Hcmp
  have Hmem := ev_vote_mem L0 La t i T d Fv HTt Hin Hsort Hcmp
  ihave ⟨#Hx, -⟩ := BigSepL.bigSepL_mem_acc Hmem $$ Hlist
  unfold voteBefore
  icases Hx with ⟨%c, #Hvc, %Himp⟩
  icases isVote_agree γ v T c id $$ Hvc Hv with %Hc
  ipureintro
  have := Himp Hc
  omega

private theorem lb_api (γ : Cluster) (l : List LogEntry) :
    ApiImpl.isCommittedLogLb (GF := GF) γ l ⊢ isCommittedLogLb γ l := by
  unfold isCommittedLogLb; exact .rfl

/-- The certificate's leader, if `id`, led at a term of a campaign the authority has. -/
theorem ldr_le (γ : RaftNames) (id ldr t T0 : w64) (q : Qp) (E : DurMaps)
    (Hb : ∀ T, (E.camps !! T).isSome → uint.Z T ≤ uint.Z T0) :
    durShares (GF := GF) γ id q E ∗ isLeader γ ldr t ⊢ ⌜ldr = id → uint.Z t ≤ uint.Z T0⌝ := by
  iintro ⟨Hsh, #Hl⟩
  by_cases h : ldr = id
  · subst h
    icases isLeader_campK γ ldr t $$ Hl with ⟨%F, %k, #HcK⟩
    icases durShares_campK γ ldr t q E F k $$ [$Hsh $HcK] with %H
    ipureintro; intro _; exact Hb t (by rw [H]; rfl)
  · ipureintro; intro h'; exact absurd h' h

/-- A recorded configuration of a committed prefix, in a cluster of fixed membership, is the
membership's. -/
private theorem cfgAt_fixed (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E) (m0 : Membership)
    (D : DynCfg) (M : DecMap) (P : List EntryM) (c : CfgM)
    (HD : (ApiImpl.Cluster.raft γ).dyn = some D) (Hc : CfgAt (ApiImpl.Cluster.raft γ) M P c) :
    ⊢ isCluster (GF := GF) γ N -∗ confFixed γ E m0 -∗ decLb (ApiImpl.Cluster.raft γ) M -∗
      isCommitted (ApiImpl.Cluster.raft γ) P ={E}=∗ ⌜c = ApiImpl.cfgOf m0⌝ := by
  iintro #Hcl #Hfix #HM #HP
  iunfold isCluster at Hcl
  iunfold ApiImpl.isClusterU at Hcl
  icases Hcl with ⟨%Huni, #Hci, -⟩
  obtain ⟨⟨c0, g, hmd⟩, -⟩ := Huni
  have hc := CfgAt.dyn HD Hc
  rw [ApiImpl.ModeDec.fold hmd D HD M P] at hc
  obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hc
  imod ApiImpl.api_committed_lb γ N E HE P $$ Hci HP with ⟨Hlb, -⟩
  ihave #Hlb := lb_api γ (strip P) $$ Hlb
  unfold confFixed
  imod Hfix $$ %(strip P) Hlb with #Hc0
  have Hcm : (isCommittedLogLb (GF := GF) γ (strip P) ∗ decLb (ApiImpl.Cluster.raft γ) M : IProp GF) ⊢
      confAt γ (strip P).length m := by
    unfold confAt ApiImpl.confAtU isCommittedLogLb
    iintro ⟨H1, #H2⟩
    iexists (strip P), M
    iframe H1 H2
    ipureintro
    refine ⟨Nat.le_refl _, c0, g, hmd, ?_⟩
    rw [List.take_of_length_le (Nat.le_refl _)]; exact hm
  ihave #Hcm' := Hcm $$ [$Hlb $HM]
  icases confAt_agree γ _ m m0 $$ [$Hcm' $Hc0] with %Heq
  imodintro
  ipureintro; rw [Heq]

/-- The two quorums meet (L2's case `t > T`): statically, any two recorded configurations; with a
fixed membership, both are the membership's. -/
private theorem quorums_meet (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E) (m0 : Membership)
    (t n : w64) (G : List EntryM) (a : w64) (c : CfgM) (q : GSet w64) (id T : w64) (V : GSet w64) :
    ⊢ isCluster (GF := GF) γ N -∗ confFixed γ E m0 -∗ cqAt (ApiImpl.Cluster.raft γ) t n G a c q -∗
      isWin (ApiImpl.Cluster.raft γ) id T V ={E}=∗ ⌜∃ v, v ∈ q ∧ v ∈ V⌝ := by
  iintro #Hcl #Hfix #Hcq #Hw
  icases cqAt_parts (ApiImpl.Cluster.raft γ) t n G a c q $$ Hcq with ⟨%M, %Hq, #HM, -, #HcP, -⟩
  icases isWin_core (ApiImpl.Cluster.raft γ) id T V $$ Hw with ⟨%cW, #Hcore⟩
  iunfold isWinCore at Hcore
  icases Hcore with ⟨%γw, %F0, %kw, %MW, %Hwp, #HcK, -, -, #HMW⟩
  ihave #HcF0 := isCampK_committed (ApiImpl.Cluster.raft γ) id T F0 kw $$ HcK
  cases HD : (ApiImpl.Cluster.raft γ).dyn with
  | none =>
    imodintro; ipureintro
    exact CfgAt.overlap (RaftNames.dyn_eq_none.1 HD) Hq.2.2.1 Hwp.2.2 q V Hq.2.2.2 Hwp.2.1
  | some D =>
    imod cfgAt_fixed γ N E HE m0 D M _ c HD Hq.2.2.1 $$ Hcl Hfix HM HcP with %H1
    imod cfgAt_fixed γ N E HE m0 D MW _ cW HD Hwp.2.2 $$ Hcl Hfix HMW HcF0 with %H2
    imodintro; ipureintro
    have hf := CfgAt.dyn HD Hq.2.2.1
    have Hov := D.adj M _ _ c c (List.prefix_refl _) (by omega) hf hf
    have Hjw := Hwp.2.1
    rw [H2, ← H1] at Hjw
    exact Hov q V Hq.2.2.2 Hjw

/-- Opening the commit invariant for a pure fact of the vote table. -/
private theorem tbl_pure (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E) (P : IProp GF)
    [Persistent P] (φ : Prop) (H : votesTbl (ApiImpl.Cluster.raft γ) ∗ P ⊢ ⌜φ⌝) :
    ⊢ isCluster (GF := GF) γ N -∗ P ={E}=∗ ⌜φ⌝ := by
  iintro #Hcl #HP
  iunfold isCluster at Hcl
  iunfold ApiImpl.isClusterU at Hcl
  icases Hcl with ⟨-, #Hci, -⟩
  iunfold ApiImpl.clusterInv at Hci
  icases Hci with ⟨%HNs, #Hcinv, -⟩
  ihave #Hli := raftCommitInv_log (ApiImpl.Cluster.raft γ) $$ Hcinv
  have Hl : (↑(raftLogN (ApiImpl.Cluster.raft γ)) : CoPset) ⊆ E := by
    unfold raftLogN raftN; rw [HNs]
    intro p hp
    exact (Iris.Std.LawfulSet.mem_diff.mp (ApiImpl.raftN_api N HE "log" p hp)).1
  unfold raftLogInv raftLogInvBody logRest
  iinv Hli with ⟨%P', >HP', >#Hj, >Htbl, >Hwt, >#Hds, >Hq1⟩ Hclose1
  icases keep_pure H $$ [$Htbl $HP] with ⟨⟨Htbl, -⟩, %Hφ⟩
  imod Hclose1 $$ [HP' Htbl Hwt Hq1] with -
  · inext
    iexists P'
    iframe HP' Hj Htbl Hwt Hds Hq1
  imodintro
  ipureintro; exact Hφ

/-- L2's core over raft's names: a full log `X` with records extending the campaign log `F0` of
`id`'s term `T > T0` agrees, up to its end, with a log `cmtBefore` covers. -/
private theorem cmtBefore_core (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E) (m0 : Membership)
    (id T0 T : w64) (l : List LogEntry) (X F0 : List EntryM) (kw : w64) :
    uint.Z T0 < uint.Z T → PlogWf base0 X → F0 <+: X →
    ⊢ isCluster (GF := GF) γ N -∗ confFixed γ E m0 -∗ cmtBeforeR (ApiImpl.Cluster.raft γ) id T0 l -∗
      isLeader (ApiImpl.Cluster.raft γ) id T -∗ isCampK (ApiImpl.Cluster.raft γ) id T F0 kw -∗ logRecs (ApiImpl.Cluster.raft γ) base0 X ={E}=∗
      ⌜l = [] ∨ ∃ P, l <+: strip P ∧ P.length < 2 ^ 64 ∧ ∀ j : w64, 0 < uint.Z j →
        uint.Z j ≤ P.length → plogTermAt base0 X j = plogTermAt base0 P j⌝ := by
  intro HT0 hwX hF0
  iintro #Hcl #Hfix #Hcb #Hl #HcK #HrX
  icases isCampK_boot (ApiImpl.Cluster.raft γ) id T F0 kw $$ HcK with %Hboot
  ihave #Hc := isCampK_camp (ApiImpl.Cluster.raft γ) id T F0 kw $$ HcK
  icases isCamp_ok (ApiImpl.Cluster.raft γ) id T F0 $$ Hc with %Hcok
  unfold cmtBeforeR
  icases Hcb with (%Hnil | %Hb | ⟨%t, %n, %G, %a, %c, %q, %ldr, %Hp, #Hcqa, #Hldr, %Hldr', #Hab⟩)
  · imodintro; ipureintro; left; exact Hnil
  · -- the bootstrap log, which `X` starts with
    imodintro; ipureintro; right
    refine ⟨_, Hb.1, wf_len_lt _ Hb.2, fun j hj0 hj => ?_⟩
    apply plogTermAt_prefix base0 _ X j (Hboot.1.trans hF0)
    apply plogTermAt_in_range
    rw [base0_index]; unfold plogLastIndexZ; rw [base0_index]; omega
  · obtain ⟨hl, hn0⟩ := Hp
    ihave #Hcq := cqAt_cq (ApiImpl.Cluster.raft γ) t n G a c q $$ Hcqa
    icases cq_full (ApiImpl.Cluster.raft γ) t n G $$ Hcq with ⟨%hwG, #HrG⟩
    icases cq_base (ApiImpl.Cluster.raft γ) t n G $$ Hcq with ⟨%HGn, -⟩
    have hlen : (G.take (uint.Z n).toNat).length < 2 ^ 64 := by
      have := uint_Z_lt n; rw [List.length_take]; omega
    -- agreement with `G` up to `n` gives the conclusion
    have fin : (∀ j : w64, uint.Z j ≤ uint.Z n → plogTermAt base0 X j = plogTermAt base0 G j) →
        l = [] ∨ ∃ P, l <+: strip P ∧ P.length < 2 ^ 64 ∧ ∀ j : w64, 0 < uint.Z j →
          uint.Z j ≤ P.length → plogTermAt base0 X j = plogTermAt base0 P j := by
      intro Hm
      right
      refine ⟨_, hl, hlen, fun j _ hj => ?_⟩
      have hjn : uint.Z j ≤ uint.Z n := by rw [List.length_take] at hj; omega
      rw [plogTermAt_take_full G _ j (by omega)]
      exact Hm j hjn
    rcases Int.lt_trichotomy (uint.Z t) (uint.Z T) with Hlt | Heq | Hgt
    · -- an earlier term: leader completeness
      imod tbl_pure γ N E HE iprop(cq (ApiImpl.Cluster.raft γ) t n G ∗ isLeader (ApiImpl.Cluster.raft γ) id T ∗ isCamp (ApiImpl.Cluster.raft γ) id T F0 ∗
          logRecs (ApiImpl.Cluster.raft γ) base0 X) (plogTermAt base0 X n = some t)
          (by
            iintro ⟨Htbl, #Hq, #Hl, #Hc, #Hr⟩
            iapply lc_core (ApiImpl.Cluster.raft γ) ((uint.Z T).toNat + 1) T t n G id F0 X
              (by have := uint_Z_nonneg T; omega) Hlt hwX (prefix_camp_last T F0 X Hcok hF0)
              $$ Htbl Hq Hl Hc Hr) $$ Hcl [] with %HXn
      · iframe Hcq Hl Hc HrX
      icases full_match (ApiImpl.Cluster.raft γ) X G n hwX hwG (by rw [HXn]; rfl) (by rw [HXn, HGn]) $$ HrX HrG
        with %Hm
      imodintro; ipureintro; exact fin Hm
    · -- the same term: `T`'s leader is `id`, whose campaign at `T > T0` the mark excludes
      have : t = T := uint_Z_inj.mp Heq
      subst this
      icases isLeader_unique (ApiImpl.Cluster.raft γ) ldr id t $$ Hldr Hl with %Hid
      exfalso; have := Hldr' Hid; omega
    · -- a later term: a voter of both quorums
      iunfold isLeader at Hl
      icases Hl with ⟨%V, #Hw⟩
      imod quorums_meet γ N E HE m0 t n G a c q id T V $$ Hcl Hfix Hcqa Hw with %Hmeet
      obtain ⟨v, hvq, hvV⟩ := Hmeet
      ihave #Hav := BigSepM.bigSepM_lookup (Φ := fun v _ => ackBefore (GF := GF) (ApiImpl.Cluster.raft γ) id T0 v t)
        ((GMap.elem_of_gset _ _).mp hvq) $$ Hab
      ihave #Hvs := isWin_votes (ApiImpl.Cluster.raft γ) id T V $$ Hw
      ihave #Hvv := BigSepM.bigSepM_lookup (Φ := fun v _ => isVote (GF := GF) (ApiImpl.Cluster.raft γ) v T id)
        ((GMap.elem_of_gset _ _).mp hvV) $$ Hvs
      imod tbl_pure γ N E HE iprop(ackBefore (ApiImpl.Cluster.raft γ) id T0 v t ∗ isVote (ApiImpl.Cluster.raft γ) v T id) False
          (by
            iintro ⟨Htbl, #Ha, #Hv⟩
            iapply ackBefore_vote (ApiImpl.Cluster.raft γ) id T0 v t T HT0 Hgt $$ [$Htbl $Ha $Hv]) $$ Hcl [] with %Hf
      · iframe Hav Hvv
      exact Hf.elim

/-! ## The laws -/

/-- **L1: marking a committed log** with the node's durable term: `l` was committed before every
campaign of `id` so far (`cmtBefore`). -/
theorem raftState_cmtBefore (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E) (id : w64)
    (S0 : RaftState) (l : List LogEntry) :
    raftState (GF := GF) γ id S0 ∗ isCluster γ N ∗ isCommittedLogLb γ l ⊢
      |={E}=> raftState γ id S0 ∗ cmtBefore γ id S0.term l := by
  iintro ⟨Hst, #Hcl, #Hlb⟩
  iunfold isCluster at Hcl
  iunfold ApiImpl.isClusterU at Hcl
  icases Hcl with ⟨-, #Hci, -⟩
  iunfold raftState at Hst
  iunfold ApiImpl.raftStateU at Hst
  icases Hst with ⟨Hdur, #Hterm, #Hbudget⟩
  iunfold ownDurGhost at Hdur
  icases Hdur with ⟨%E', Hsh, #Hpers, Hslot, Hi1⟩
  ihave #Hfacts := Hpers
  iunfold durPers at Hfacts
  icases Hfacts with ⟨%kd, %fp, %hf, -⟩
  have Hb : ∀ T, (E'.camps !! T).isSome → uint.Z T ≤ uint.Z S0.term := hf.2.2.1
  unfold isCommittedLogLb
  imod ApiImpl.api_committed_cert γ N E HE l $$ Hci Hlb with
    (%Hnil | ⟨%P, %Hp, -, Hc⟩)
  · imodintro
    isplitl [Hsh Hslot Hi1]
    · iunfold raftState; iunfold ApiImpl.raftStateU; iframe Hterm Hbudget
      iunfold ownDurGhost; iexists E'; iframe Hsh Hpers Hslot Hi1
    unfold cmtBefore cmtBeforeR
    ileft; ipureintro; exact Hnil
  icases Hc with (%Hboot | ⟨%t, %n, %G, %ldr, #Hcq, %HPG, #Hldr⟩)
  · imodintro
    isplitl [Hsh Hslot Hi1]
    · iunfold raftState; iunfold ApiImpl.raftStateU; iframe Hterm Hbudget
      iunfold ownDurGhost; iexists E'; iframe Hsh Hpers Hslot Hi1
    unfold cmtBefore cmtBeforeR
    iright; ileft; ipureintro
    obtain ⟨hP, hw, -⟩ := Hboot
    subst hP
    exact ⟨Hp.1, hw⟩
  by_cases hn0 : uint.Z n = 0
  · imodintro
    isplitl [Hsh Hslot Hi1]
    · iunfold raftState; iunfold ApiImpl.raftStateU; iframe Hterm Hbudget
      iunfold ownDurGhost; iexists E'; iframe Hsh Hpers Hslot Hi1
    unfold cmtBefore cmtBeforeR
    ileft; ipureintro
    have h := Hp.1
    rw [HPG, hn0] at h
    simpa [strip] using h
  -- the certificate's leader
  icases keep_pure (ldr_le (ApiImpl.Cluster.raft γ) id ldr t S0.term (1 : Qp).half E' Hb) $$ [$Hsh $Hldr]
    with ⟨⟨Hsh, -⟩, %Hld⟩
  icases cq_cqAt (ApiImpl.Cluster.raft γ) t n G $$ Hcq with ⟨%a, %c, %q, #Hcqa⟩
  icases cqAt_parts (ApiImpl.Cluster.raft γ) t n G a c q $$ Hcqa with ⟨%M, -, -, -, -, #Hacks, -⟩
  -- the quorum's acknowledgements, their votes timed against the campaigns (the vote table)
  iunfold ApiImpl.clusterInv at Hci
  icases Hci with ⟨%HNs, #Hcinv, -⟩
  ihave #Hli := raftCommitInv_log (ApiImpl.Cluster.raft γ) $$ Hcinv
  have Hl : (↑(raftLogN (ApiImpl.Cluster.raft γ)) : CoPset) ⊆ E := by
    unfold raftLogN raftN; rw [HNs]
    intro p hp
    exact (Iris.Std.LawfulSet.mem_diff.mp (ApiImpl.raftN_api N HE "log" p hp)).1
  unfold raftLogInv raftLogInvBody logRest
  iinv Hli with ⟨%P', >HP', >#Hj, >Htbl, >Hwt, >#Hds, >Hq1⟩ Hclose1
  imod bigSepM_fupd_thread (E \ ↑(raftLogN (ApiImpl.Cluster.raft γ)))
      (iprop(votesTbl (GF := GF) (ApiImpl.Cluster.raft γ) ∗ durShares (ApiImpl.Cluster.raft γ) id (1 : Qp).half E'))
      (fun v _ => iprop(∃ i', ⌜uint.Z n ≤ uint.Z i'⌝ ∗ isAcked (GF := GF) (ApiImpl.Cluster.raft γ) v t i'))
      (fun v _ => ackBefore (GF := GF) (ApiImpl.Cluster.raft γ) id S0.term v t) (toMap q)
      $$ [] [$Htbl $Hsh] Hacks with ⟨⟨Htbl, Hsh⟩, #Hab⟩
  · imodintro
    iintro %v %u R ⟨%i', %Hi', #Ha⟩
    iapply ackBefore_of (ApiImpl.Cluster.raft γ) id S0.term v t i' E' _ Hb (by have := uint_Z_nonneg n; omega) $$ R Ha
  imod Hclose1 $$ [HP' Htbl Hwt Hq1] with -
  · inext
    iexists P'
    iframe HP' Hj Htbl Hwt Hds Hq1
  imodintro
  isplitl [Hsh Hslot Hi1]
  · iunfold raftState; iunfold ApiImpl.raftStateU; iframe Hterm Hbudget
    iunfold ownDurGhost; iexists E'; iframe Hsh Hpers Hslot Hi1
  unfold cmtBefore cmtBeforeR
  iright; iright
  iexists t, n, G, a, c, q, ldr
  iframe Hcqa Hldr Hab
  ipureintro
  refine ⟨⟨by rw [← HPG]; exact Hp.1, by have := uint_Z_nonneg n; omega⟩, Hld⟩

/-- **L2: a leader of a term above the mark has the marked log** in its durable state, in a cluster
whose membership is fixed. -/
theorem raftState_cmtBefore_agree (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E)
    (m0 : Membership) (id T0 : w64) (S : RaftState) (l : List LogEntry) :
    uint.Z T0 < uint.Z S.term →
    isCluster (GF := GF) γ N ∗ confFixed γ E m0 ∗ cmtBefore γ id T0 l ∗ raftState γ id S ∗
      snapshotLeader γ id S.term ⊢ |={E}=> raftState γ id S ∗ ⌜durLogAgrees S l⌝ := by
  intro HT0
  iintro ⟨#Hcl, #Hfix, #Hcb, Hst, #Hsl⟩
  iunfold snapshotLeader at Hsl
  unfold cmtBefore
  iunfold raftState at Hst
  iunfold ApiImpl.raftStateU at Hst
  icases Hst with ⟨Hdur, #Hterm, #Hbudget⟩
  iunfold ownDurGhost at Hdur
  icases Hdur with ⟨%E', Hsh, #Hpers, Hslot, Hi1⟩
  ihave #Hfacts := Hpers
  iunfold durPers at Hfacts
  icases Hfacts with ⟨%kd, %fp, %hf, #Hents, -, #Hpre, -, -, -, -, -, -, -, -, #Hlink, -⟩
  obtain ⟨-, -, -, -, hfull, hwf, -, -, -⟩ := hf
  ihave #HrX := logRecs_full (ApiImpl.Cluster.raft γ) S.base fp S.ents hfull $$ Hpre Hents
  have hwX := full_wf S.base fp S.ents hfull hwf
  icases isLeader_campK (ApiImpl.Cluster.raft γ) id S.term $$ Hsl with ⟨%F0, %kw, #HcK⟩
  icases keep_pure (durShares_campK (ApiImpl.Cluster.raft γ) id S.term (1 : Qp).half E' F0 kw) $$ [$Hsh $HcK]
    with ⟨⟨Hsh, -⟩, %HEc⟩
  iunfold campLink at Hlink
  icases Hlink with (%Hlk | ⟨%L, #HL, %HLne⟩)
  rotate_left
  · icases isLeader_unique (ApiImpl.Cluster.raft γ) L id S.term $$ HL Hsl with %h
    exact absurd h HLne
  have hF0 := Hlk F0 kw HEc
  imod cmtBefore_core γ N E HE m0 id T0 S.term l (fp ++ S.ents) F0 kw HT0 hwX hF0
    $$ Hcl Hfix Hcb Hsl HcK HrX with %Hag
  imodintro
  isplitl [Hsh Hslot Hi1]
  · iunfold raftState; iunfold ApiImpl.raftStateU; iframe Hterm Hbudget
    iunfold ownDurGhost; iexists E'; iframe Hsh Hpers Hslot Hi1
  ipureintro
  rcases Hag with Hnil | ⟨P, hl, hP, hag⟩
  · subst Hnil; intro i e _ h; simp at h
  · exact durLogAgrees_of S fp P l hfull hl hP hag

/-- (2026-11-24, the campaign map's closure: `notes/etcd-dist-d6.md`, option (a)) **L2 at the durable
state, for a leadership shown later**: with its durable state `S`, a node marks it as agreeing with a
log `l` committed before its campaigns up to `T0 < S.term` (`cmtBefore`), for when it is shown to
lead `S.term` (`snapshotLeader`), whenever that is. The campaign map's key `S.term` is set and final
at `S` (`durPers`, `campFrag`): a record, whose log `S`'s full log extends (`campLink`), or closed,
which no leader of `S.term` can be (`isCampNone_campK`). -/
theorem raftState_leadAgree (γ : Cluster) (N : Namespace) (E : CoPset) (HE : ↑N ⊆ E)
    (m0 : Membership) (id T0 : w64) (S : RaftState) (l : List LogEntry) :
    uint.Z T0 < uint.Z S.term →
    isCluster (GF := GF) γ N ∗ confFixed γ E m0 ∗ cmtBefore γ id T0 l ∗ raftState γ id S ⊢
      |={E}=> raftState γ id S ∗ □ (snapshotLeader γ id S.term ={E}=∗ ⌜durLogAgrees S l⌝) := by
  intro HT0
  iintro ⟨#Hcl, #Hfix, #Hcb, Hst⟩
  unfold cmtBefore
  ihave #Hcl' := Hcl
  iunfold isCluster at Hcl'
  iunfold ApiImpl.isClusterU at Hcl'
  icases Hcl' with ⟨-, #Hci, -⟩
  iunfold ApiImpl.clusterInv at Hci
  icases Hci with ⟨%HNs, -⟩
  have Hs : (↑(slotN (ApiImpl.Cluster.raft γ) id) : CoPset) ⊆ E := by
    unfold slotN raftN; rw [HNs]
    intro p hp
    have h1 := nclose_subseteq ((N .@ "raft") .@ "slot") id p hp
    exact (Iris.Std.LawfulSet.mem_diff.mp (ApiImpl.raftN_api N HE "slot" p h1)).1
  iunfold raftState at Hst
  iunfold ApiImpl.raftStateU at Hst
  icases Hst with ⟨Hdur, #Hterm, #Hbudget⟩
  iunfold ownDurGhost at Hdur
  icases Hdur with ⟨%E', Hsh, #Hpers, #Hslot, Hi1⟩
  ihave #Hfacts := Hpers
  iunfold durPers at Hfacts
  icases Hfacts with ⟨%kd, %fp, %hf, #Hents, -, #Hpre, -, -, -, -, -, -, -, -, #Hlink, %Hset⟩
  obtain ⟨-, -, -, -, hfull, hwf, -, -, -⟩ := hf
  ihave #HrX := logRecs_full (ApiImpl.Cluster.raft γ) S.base fp S.ents hfull $$ Hpre Hents
  have hwX := full_wf S.base fp S.ents hfull hwf
  -- the key of `S.term`: set (the term is past `T0`, so not the initial `0`)
  have Hsome : (E'.camps !! S.term).isSome := by
    rcases Hset with h | h
    · have := uint_Z_nonneg T0; omega
    · exact h
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp Hsome
  imod durShares_frags E (ApiImpl.Cluster.raft γ) id E' Hs $$ Hsh Hslot with ⟨Hsh, #Hfr⟩
  iunfold durFrags at Hfr
  icases Hfr with ⟨-, -, #Hfc, -⟩
  ihave #Hx := BigSepM.bigSepM_lookup (Φ := fun (t : w64) (x : List EntryM × w64) =>
    campFrag (GF := GF) (ApiImpl.Cluster.raft γ) id t x) hx $$ Hfc
  imodintro
  isplitl [Hsh Hi1]
  · iunfold raftState; iunfold ApiImpl.raftStateU; iframe Hterm Hbudget
    iunfold ownDurGhost; iexists E'; iframe Hsh Hpers Hslot Hi1
  iintro !> #Hsl
  iunfold snapshotLeader at Hsl
  icases isLeader_campK (ApiImpl.Cluster.raft γ) id S.term $$ Hsl with ⟨%F0, %kw, #HcK⟩
  iunfold campFrag at Hx
  icases Hx with (#HxK | ⟨%Hxn, #Hnone⟩)
  · -- a campaign record: `id`'s campaign of `S.term`, whose log `S`'s full log extends
    icases isCampK_agree (ApiImpl.Cluster.raft γ) id S.term x.1 F0 x.2 kw $$ HxK HcK with %Heq
    have HEc : E'.camps !! S.term = some (F0, kw) := by rw [hx, ← Heq.1, ← Heq.2]
    iunfold campLink at Hlink
    icases Hlink with (%Hlk | ⟨%L, #HL, %HLne⟩)
    · have hF0 := Hlk F0 kw HEc
      imod cmtBefore_core γ N E HE m0 id T0 S.term l (fp ++ S.ents) F0 kw HT0 hwX hF0
        $$ Hcl Hfix Hcb Hsl HcK HrX with %Hag
      imodintro
      ipureintro
      rcases Hag with Hnil | ⟨P, hl, hP, hag⟩
      · subst Hnil; intro i e _ h; simp at h
      · exact durLogAgrees_of S fp P l hfull hl hP hag
    · icases isLeader_unique (ApiImpl.Cluster.raft γ) L id S.term $$ HL Hsl with %h
      exact absurd h HLne
  · -- closed: no leader of `S.term` is `id`
    iexfalso
    iapply isCampNone_campK (ApiImpl.Cluster.raft γ) id S.term F0 kw $$ Hnone HcK

end EtcdGrove
end Perennial
