/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/ReplSnap.lean (241f27e).
-/
/-
Snapshots in the replication subsystem (stage 3): the leader's last snapshot as a valid install of
its term (or the term moved on), and the parts of a valid install the replication goroutine uses
(the previous entry of an AppendEntries, the commitment's `lciOk`).

* `snap_valid`: the last snapshot `(si, st)` (`getLastSnapshot`'s, or the snapshot store's latest, both
  with `durLb ∨ snapFollow`) is `aeValid γ T si st [] si` while `i` leads `T`, or `i` left `T`
  (`gprot.snapValid_or_left`, `gprot.snapValid_follow`);
* `aeValid_prevOk`, `aeValid_lciOk`: the previous entry and the commit index of a valid request.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.ReplBase

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft

open proto gprot

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

/-- (Unfolds gprot's `aeValid`.) The previous entry of a valid request. -/
theorem aeValid_prevOk (γ : GNames) (T prev pt : Nat) (ents : List Entry) (lci : Nat) :
    aeValid (GF := GF) γ T prev pt ents lci ⊢ prevOk γ T prev pt := by
  unfold aeValid prevOk
  iintro ⟨-, #Hp, -⟩
  iexact Hp

/-- (Unfolds gprot's `aeValid`.) The commit index of a valid request. -/
theorem aeValid_lciOk (γ : GNames) (T prev pt : Nat) (ents : List Entry) (lci : Nat) :
    aeValid (GF := GF) γ T prev pt ents lci ⊢ lciOk γ T lci := by
  unfold aeValid
  iintro ⟨-, -, -, #Hc⟩
  iexact Hc

/-- (Unfolds gprot's `InvBody`, a missing gprot law.) A committed index is below the bound on log
lengths (`2^62`). -/
theorem CIdx_lt (γ : GNames) (E : CoPset) (hE : ↑gprotN ⊆ E) (x : Nat) (e : Entry) :
    Inv (GF := GF) γ ∗ CIdx γ x e ⊢ |={E}=> ⌜x < 2 ^ 62⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr, Hcc⟩, #Hc⟩
  ihave ⟨Hh, %hC⟩ := H_C_lookup γ σ x e $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hc
  ihave ⟨Hr, %hb⟩ := receipt_bound _ $$ Hr
  isplitl [Hh Hs Hr Hcc]
  · iframe; ipureintro; exact hg
  ipureintro
  have hl := proto.ent_le_length (C_llog σ x e hg.1 hC)
  have hm := (PInv.bounds hg.1).2.1 e.term
  omega

/-- **The leader's snapshot is a valid install of its term** (or the term moved on): a committed
entry `(si, st)`, `si ≥ 1`, durable at `i` (`snapValid_or_left`) or installed while `i` followed
(`snapFollow`, unfolded: `snapValid_follow`). -/
theorem snap_valid (γ : GNames) (i : SID) (T si st : Nat) (e : Entry) (hsi : 1 ≤ si) :
    Inv (GF := GF) γ ∗ isSrv γ i ∗ leaderIs γ T i ∗ termLb γ i T ∗ CIdx γ si e ∗ ⌜e.term = st⌝ ∗
      (durLb γ i si ∨ snapFollow γ i si st) ⊢
    |={⊤}=> aeValid γ T si st [] si ∨ termLb γ i (T + 1) := by
  iintro ⟨#Hinv, #Hv, #Hl, #Hlb, #Hc, %He, #Hd | #Hf⟩
  · subst He
    iapply snapValid_or_left γ ⊤ (by solve_ndisj) i T si e hsi
    iframe #
  · unfold snapFollow
    icases Hf with ⟨%t, %ℓ, #Hae, #Hlt, #Hlbt, %Hℓ⟩
    iapply snapValid_follow γ ⊤ (by solve_ndisj) i ℓ t T si st Hℓ.1 hsi
    iframe #

/-- (Unfolds core's `replShared`.) The follower is not the leader. -/
theorem replShared_ne (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) (j : SID) (s : Loc) :
    replShared (GF := GF) r γ rc i T j s ⊢ ⌜j ≠ i⌝ := by
  unfold replShared
  iintro ⟨%cm, %stopCh, %trig, %notif, %sd, %tde, %γs, -, -, -, %h, -⟩
  ipureintro; exact h

/-- What the replication goroutine keeps about the snapshot store's latest snapshot `(m, b)`
(persistent; read off `snapCell` when it opens it): `latestOk`'s facts (with `snapP` boxed) and the
snapshot durable at `i` or installed while `i` followed. -/
def latestGood (γ : GNames) (rc : RCtx GF) (i : SID) (lat : SnapLatest) : IProp GF :=
  match lat with
  | none => iprop(True)
  | some (m, b) => iprop((∃ e : Entry, CIdx γ (uint.nat m.Index') e ∗
        ⌜e.term = uint.nat m.Term' ∧ 1 ≤ uint.nat m.Index'⌝) ∗
      □ rc.snapP (uint.nat m.Index') b ∗
      (∃ ss : List Server, cfgVal γ m.Configuration' ss ∗
        snapCfg γ (uint.nat m.Index') (uint.nat m.ConfigurationIndex') ss) ∗
      ⌜m.Version' = W64 1 ∧ uint.nat m.Size' = b.length ∧
        b.length < 2 ^ 63 ∧ m.Peers' = slice.nil⌝ ∗
      (durLb γ i (uint.nat m.Index') ∨ snapFollow γ i (uint.nat m.Index') (uint.nat m.Term')))

instance latestGood_persistent γ rc i lat : Persistent (latestGood (GF := GF) γ rc i lat) := by
  unfold latestGood; split <;> infer_instance

/-- (Unfolds core's `latestOk`; hraft_robust: over `durBody`'s `latestDur`.) Reading `latestGood` off
what raft keeps about its snapshot store. -/
theorem latest_good (γ : GNames) (rc : RCtx GF) (i : SID) (fsmI : GoInterfaceOk) (lat : SnapLatest)
    (pend : Option (Nat × Nat × GoString)) (dp : Option DiscPend) :
    isFSM fsmI γ i rc.fsmOwn rc.respP rc.snapP ∗ latestDur γ rc i lat pend dp ⊢
    latestDur γ rc i lat pend dp ∗ latestGood γ rc i lat := by
  iintro ⟨#Hfsm, Hd⟩
  unfold latestDur
  icases Hd with ⟨Hlat, Hm⟩
  rcases lat with _ | ⟨m, b⟩
  · iframe; unfold latestGood; itrivial
  unfold latestOk latestGood
  dsimp only
  icases Hlat with ⟨#He, Hsp, #Hcfg, %Hp⟩
  ihave #Hsp2 := isFSM_snapP_persistent fsmI γ i rc.fsmOwn rc.respP rc.snapP _ b $$ [Hsp]
  · iframe #; iexact Hsp
  rcases pend with _ | ⟨s, st, id⟩
  · dsimp only
    icases Hm with (%Hn | ⟨%m', %b', %Heq, Hdd⟩)
    · cases Hn
    cases Heq
    icases Hdd with (⟨#Hd, %Hdn⟩ | ⟨#Hf, %Hdp, Ha⟩)
    · isplitl []
      · isplitl []; · iframe #; ipureintro; exact Hp
        iright; iexists m, b; isplitr; · ipureintro; rfl
        ileft; iframe #; ipureintro; exact Hdn
      iframe #; isplitr; · ipureintro; exact Hp
      ileft; iexact Hd
    · isplitl [Ha]
      · isplitl []; · iframe #; ipureintro; exact Hp
        iright; iexists m, b; isplitr; · ipureintro; rfl
        iright; iframe #; iframe; ipureintro; exact Hdp
      iframe #; isplitr; · ipureintro; exact Hp
      iright; iexact Hf
  · dsimp only
    icases Hm with ⟨%m', %b', %a, %Hq, #Hf, Ha⟩
    obtain ⟨Heq, Hid, Hs, Hst, Ha'⟩ := Hq
    cases Heq
    subst Hs Hst
    isplitl [Ha]
    · isplitl []; · iframe #; ipureintro; exact Hp
      iexists m, b, a; iframe #; iframe; ipureintro; exact ⟨rfl, Hid, rfl, rfl, Ha'⟩
    iframe #; isplitr; · ipureintro; exact Hp
    iright; iexact Hf

/-- (Unfolds iface's `openPost`.) `Open` of the latest's id (Goose's left-nested triple
`((meta, rc), err)`; REPL3-1, applied at 972bec9). -/
theorem openPost_hit (m : SnapshotMeta) (b : List w8) (id : GoString) (eof : GoInterface) (v : val)
    (h : m.ID' = id) :
    openPost (GF := GF) (some (m, b)) id eof v ⊢
      ∃ (mp : Loc) (rd : GoInterfaceOk) (R : List w8 → IProp GF),
        ⌜v = PairV (PairV #mp #(GoInterface.ok rd)) #interface.nil⌝ ∗ mp ↦ m ∗
        readCloserOk rd R eof ∗ R b ∗ ⌜go.typeSetContains rd.ty io.WriterTo.ty = false⌝ := by
  unfold openPost
  dsimp only
  rw [if_pos h]

/-- (Unfolds iface's `openPost`.) `Open` of another id fails. -/
theorem openPost_miss (lat : SnapLatest) (id : GoString) (eof : GoInterface) (v : val)
    (h : ∀ m b, lat = some (m, b) → m.ID' ≠ id) :
    openPost (GF := GF) lat id eof v ⊢
      ∃ err : GoInterface, ⌜v = PairV (PairV #null #interface.nil) #err ∧ err ≠ interface.nil⌝ := by
  unfold openPost
  rcases lat with _ | ⟨m, b⟩
  · dsimp only; exact .rfl
  · dsimp only
    rw [if_neg (h m b rfl)]

end lemmas

end github_com.hashicorp.raft

end Perennial
