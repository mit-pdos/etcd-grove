/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/InstallBase.lean (241f27e).
-/
/-
(stage 3, snap) The ghost steps of `installSnapshot` (and of the snapshot goroutine's own snapshot):
the sink's commit (`snapCell`: the install becomes the latest and the pending record is set), the
`setLastApplied` update that ends the pending record, the log store steps (keep: `GetLog`; discard:
`DeleteRange` with `installDiscard_upd`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws
public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Install
public import Dsverify.Proof.github_com.hashicorp.raft.core.Helpers
public import Dsverify.Proof.github_com.hashicorp.raft.FsmBase
public import Spec.io.Copy
public import Dsverify.Proof.github_com.hashicorp.raft.proto.Read
public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Internal
public import Dsverify.Spec.github_com.hashicorp.raft.countingReader__Read
public import Dsverify.Proof.github_com.hashicorp.raft.core.CrashLaws
public import Dsverify.Proof.github_com.hashicorp.raft.leader.DurView

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft proto gprot

namespace github_com.hashicorp.raft.snapProof

theorem gprotN_snapN : (↑gprotN : CoPset) ⊆ ⊤ \ ↑snapN := gprotN_diff_raft "snap"

/-- The latest snapshot `(m, b)` of the store: its committed entry. -/
theorem latestOk_some (γ : GNames) (rc : RCtx GF) (m : SnapshotMeta) (b : List w8) :
    latestOk γ rc (some (m, b)) ⊢ ∃ e : Entry, CIdx γ (uint.nat m.Index') e ∗
      ⌜e.term = uint.nat m.Term' ∧ 1 ≤ uint.nat m.Index'⌝ := by
  unfold latestOk
  iintro ⟨H, -⟩
  iexact H

/-- A lower bound of `lastApplied` is below any half of its authority. -/
theorem applLb_le (rc : RCtx GF) (q : Qp) (a x : Nat) :
    ⊢ monoNatAuthOwn rc.dur.applied q a -∗ applLb rc x -∗ ⌜x ≤ a⌝ := by
  unfold applLb
  iintro H1 H2
  ihave %Hv := monoNatLbOwn_valid _ _ _ _ $$ H1 H2
  ipureintro; exact Hv.2

/-- `lastApplied`'s lower bound from a half of its authority. -/
theorem applLb_get (rc : RCtx GF) (q : Qp) (a : Nat) :
    monoNatAuthOwn rc.dur.applied q a ⊢ applLb rc a := by
  unfold applLb
  iintro H
  iapply monoNatLbOwn_get $$ H

/-- A lower bound of the compaction frontier is below its authority. -/
theorem compLb_le (rc : RCtx GF) (q : Qp) (c x : Nat) :
    ⊢ monoNatAuthOwn rc.dur.comp q c -∗ compLb rc x -∗ ⌜x ≤ c⌝ := by
  unfold compLb
  iintro H1 H2
  ihave %Hv := monoNatLbOwn_valid _ _ _ _ $$ H1 H2
  ipureintro; exact Hv.2

/-- Raising the compaction frontier (the main goroutine's authority). -/
theorem compLb_raise (rc : RCtx GF) (c c' : Nat) (h : c ≤ c') :
    monoNatAuthOwn rc.dur.comp 1 c ⊢ |==> (monoNatAuthOwn rc.dur.comp 1 c' ∗ compLb rc c') := by
  unfold compLb
  iintro H
  imod mono_nat_own_update c' h $$ H with ⟨Ha, #Hb⟩
  imodintro
  iframe Ha
  iexact Hb

/-- Closing `snapCell` after the install's commit: the install's snapshot is the latest, pending. -/
theorem install_close (γ : GNames) (rc : RCtx GF) (i : SID) (s st a : Nat) (id : GoString)
    (ver idx term cfgIdx : w64) (cfg : Configuration) (b : List w8) (e : Entry)
    (hs : uint.nat idx = s) (ht : uint.nat term = st) (hver : ver = W64 1) (ss : List Server)
    (hb : b.length < 2 ^ 63) (has : a < s) (h1 : 1 ≤ s) (he : e.term = st) :
    CIdx (GF := GF) γ s e ∗ snapFollow γ i s st ∗ rc.snapP s b ∗ cfgVal γ cfg ss ∗
      snapCfg γ s (uint.nat cfgIdx) ss ∗
      monoNatAuthOwn rc.dur.applied (1 : Qp).half a ∗
      ghostVar rc.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) ∗
      ghostVar rc.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) ∗
      rc.ownSS (some (sinkMeta ver idx term cfgIdx cfg id b, b)) ∗
      ((▷ ∃ (lat : SnapLatest) (pend : Option (Nat × Nat × GoString)),
        rc.ownSS lat ∗ latestOk γ rc lat ∗ ghostVar rc.dur.pend (1 : Qp).half pend ∗
        (match pend with
          | none => ⌜lat = none⌝ ∨ ∃ (m : SnapshotMeta) (b : List w8), ⌜lat = some (m, b)⌝ ∗
              applLb rc (uint.nat m.Index') ∗
              (durLb γ i (uint.nat m.Index') ∨ snapFollow γ i (uint.nat m.Index') (uint.nat m.Term'))
          | some (s, st, id) => ∃ (m : SnapshotMeta) (b : List w8) (a : Nat),
              ⌜lat = some (m, b) ∧ m.ID' = id ∧ uint.nat m.Index' = s ∧ uint.nat m.Term' = st ∧ a < s⌝ ∗
              snapFollow γ i s st ∗ monoNatAuthOwn rc.dur.applied (1 : Qp).half a)) ={⊤ \ ↑snapN,⊤}=∗
        emp) ⊢
    |={⊤ \ ↑snapN,⊤}=> ghostVar rc.dur.pend (1 : Qp).half (some (s, st, id)) := by
  iintro ⟨#HC, #Hfol, HsP, #Hcfg, #Hscfg, Happ, Hpend, Hpd, Hown, Hclose⟩
  imod ghostVar_update_halves (some (s, st, id)) rc.dur.pend none none $$ Hpend Hpd with ⟨Hpend, Hpd⟩
  imod Hclose $$ [Hown Hpd Happ HsP] with -
  · inext
    iexists (some (sinkMeta ver idx term cfgIdx cfg id b, b)), (some (s, st, id))
    iframe Hown Hpd
    isplitl [HsP]
    · unfold latestOk sinkMeta
      dsimp only
      rw [hs]
      iframe HsP
      isplitr
      · iexists e; iframe HC; ipureintro; exact ⟨by rw [he, ht], h1⟩
      isplitr
      · iexists ss; iframe Hcfg Hscfg
      ipureintro
      refine ⟨hver, ?_, hb, rfl⟩
      word
    · iexists (sinkMeta ver idx term cfgIdx cfg id b), b, a
      iframe Happ Hfol
      ipureintro
      exact ⟨rfl, rfl, hs, ht, has⟩
  imodintro
  iexact Hpend

/- hraft_robust L0: statement obsolete (its stage restates or deletes it)
/-- **The install's commit** (its sink's `Close`): the store's latest is none, or at most
`lastApplied = a < s` (the main goroutine's half of the authority) with a committed entry of a term
`≤ st` (`CIdx_term_mono`): the install's snapshot is newer and becomes the latest; the pending
record `(s, st, id)` is set, with the main goroutine's half of `lastApplied`'s authority moved into
`snapCell`. -/
theorem install_commit (γ : GNames) (rc : RCtx GF) (i : SID) (s st a : Nat) (id : GoString)
    (ver idx term cfgIdx : w64) (cfg : Configuration) (b : List w8) (e : Entry)
    (hs : uint.nat idx = s) (ht : uint.nat term = st) (hver : ver = W64 1) (ss : List Server)
    (hb : b.length < 2 ^ 63) (has : a < s) (h1 : 1 ≤ s) (he : e.term = st) :
    Inv (GF := GF) γ ∗ snapCell rc γ i ∗ CIdx γ s e ∗ snapFollow γ i s st ∗ rc.snapP s b ∗
      cfgVal γ cfg ss ∗ snapCfg γ s (uint.nat cfgIdx) ss ∗
      monoNatAuthOwn rc.dur.applied (1 : Qp).half a ∗
      ghostVar rc.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) ⊢
    |={⊤,∅}=> ▷ ∃ old, rc.ownSS old ∗
      (rc.ownSS (newerSnap old (sinkMeta ver idx term cfgIdx cfg id b) b) ={∅,⊤}=∗
        ghostVar rc.dur.pend (1 : Qp).half (some (s, st, id))) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

/- hraft_robust L0: statement obsolete (its stage restates or deletes it)
-/
/-- **The install's `setLastApplied(s)`** (its logically atomic update): the pending record
`(s, st, id)` (the main goroutine's half, back from the restore) finds the main goroutine's half of
`lastApplied`'s authority in `snapCell` at `a < s`; it takes it, and the authority moves to `s`; the
record ends (`none`), and the latest (the install's) is now at most `lastApplied` (`applLb s`) and
installed while following (`snapFollow`, kept from the pending case). -/
theorem install_applied_au (γ : GNames) (rc : RCtx GF) (i : SID) (s st : Nat) (id : GoString)
    (Ψ : IProp GF) :
    snapCell rc γ i ∗ ghostVar rc.dur.pend (1 : Qp).half (some (s, st, id)) ∗
      (ghostVar rc.dur.pend (1 : Qp).half (none : Option (Nat × Nat × GoString)) -∗
        monoNatAuthOwn rc.dur.applied (1 : Qp).half s -∗ Ψ) ⊢
    |={⊤ \ ↑appliedN, ∅}=> ▷ ∃ a : Nat, monoNatAuthOwn rc.dur.applied (1 : Qp).half a ∗
      ⌜a ≤ s⌝ ∗ (monoNatAuthOwn rc.dur.applied (1 : Qp).half s ={∅, ⊤ \ ↑appliedN}=∗ Ψ) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)

/- hraft_robust L0: statement obsolete (its stage restates or deletes it)
-/
/-- **A main-goroutine read of the log store** (`GetLog(k)`'s atomic update) past the compaction
frontier (`cm < k`, the main goroutine's authority): the store's entries are entries of the server's
log, and it holds the log's entry at `k` if the log reaches `k`. -/
theorem logCell_getLog (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (cm k : Nat)
    (hk : cm < k) (Ψ : LogAbs → IProp GF) :
    Inv (GF := GF) γ ∗ srvDurInv γ rc i ∗ srvOwn γ i s ∗
      ghostVar rc.names.logPend (1 : Qp).half ([] : RLog) ∗ monoNatAuthOwn rc.dur.comp 1 cm ∗
      (∀ A : LogAbs,
        ⌜(∀ k' e, A.m.lookup k' = some e → ent s.log k' = some e) ∧
          (k ≤ s.log.length → A.m.lookup k = ent s.log k)⌝ -∗
        srvOwn γ i s -∗ ghostVar rc.names.logPend (1 : Qp).half ([] : RLog) -∗
        monoNatAuthOwn rc.dur.comp 1 cm -∗ Ψ A) ⊢
    |={⊤,∅}=> ▷ ∃ A, rc.ownL A ∗ (rc.ownL A ={∅,⊤}=∗ Ψ A) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)
-/

/-- What the install's `GetLog(s)` tells (`¬ prevMatch`: the discard case). -/
theorem getLog_prevMatch (L : RLog) (m : GMap Nat Entry) (k st : Nat) (hk : 1 ≤ k)
    (hsub : ∀ k' e, m.lookup k' = some e → ent L k' = some e)
    (hwin : k ≤ L.length → m.lookup k = ent L k) :
    (∀ e, m.lookup k = some e → e.term = st → prevMatch L k st) ∧
    ((m.lookup k = none ∨ ∃ e, m.lookup k = some e ∧ e.term ≠ st) → ¬ prevMatch L k st) := by
  constructor
  · intro e he het
    have h := hsub k e he
    right
    exact ⟨(proto.ent_le_length h).2, by rw [proto.termAt_of_ent h, het]⟩
  · intro h hp
    rcases hp with h0 | ⟨hl, ht⟩
    · omega
    obtain ⟨e, he⟩ := proto.ent_isSome L k hk hl
    rcases h with hn | ⟨e', he', hne⟩
    · rw [hwin hl, he] at hn; cases hn
    · have h2 := hsub k e' he'
      rw [proto.termAt_of_ent h2] at ht
      exact hne ht

omit [GooseSemantics] [GooseInterp] go_gctx package_sem hRB in
theorem del_lookup_some (m : GMap Nat Entry) (mn mx k : Nat) (e : Entry) :
    (LogAbs.del m mn mx).lookup k = some e ↔ m.lookup k = some e ∧ ¬ (mn ≤ k ∧ k ≤ mx) := by
  unfold LogAbs.del
  have h := GMap.mapLookup_filter_Some (fun k (_ : Entry) => decide (¬ (mn ≤ k ∧ k ≤ mx))) m k e
  simp only [decide_eq_true_eq] at h
  exact h

/- hraft_robust L0: statement obsolete (its stage restates or deletes it)
/-- **The install's discard** (`DeleteRange(1, |log|)`'s atomic update, then `setLastLog(s, st)`):
the store loses every entry (they are all within `1..|log|`), the protocol log becomes the committed
prefix up to `x` (`installDiscard_upd`) and the store's window starts past it (`lo = x + 1`, the
compaction frontier raised to `x` first). -/
theorem logCell_discard (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (x st : Nat) (ℓ : SID)
    (hℓ : ℓ ≠ i) (hx : 1 ≤ x) (hn : ¬ prevMatch s.log x st) (mx : Nat) (hmx : mx = s.log.length)
    (Ψ : IProp GF) :
    Inv (GF := GF) γ ∗ srvDurInv γ rc i ∗ srvOwn γ i s ∗ durView γ i (1 : Qp).half s.dur.1 ∗
      aeValid γ s.term x st [] x ∗ leaderIs γ s.term ℓ ∗
      ghostVar rc.names.logPend (1 : Qp).half ([] : RLog) ∗ compLb rc x ∗
      (∀ (L' : RLog) (d : Nat × Nat), srvOwn γ i { s with log := L', dur := d } -∗
        durView γ i (1 : Qp).half d.1 -∗ durLb γ i x -∗
        ⌜L'.length = x ∧ lastTerm L' = st ∧ d.1 = x⌝ -∗
        ghostVar rc.names.logPend (1 : Qp).half ([] : RLog) -∗ Ψ) ⊢
    |={⊤,∅}=> ▷ ∃ A, rc.ownL A ∗
      (∀ hi' : w64, rc.ownL ⟨LogAbs.del A.m 1 mx, hi'⟩ ={∅,⊤}=∗ Ψ) := by
  sorry -- hraft_robust L0: re-proved by its stage (HANDOFF.md)
-/

instance batchStart_persistent (rc : RCtx GF) (n k : Nat) :
    Persistent (batchStart (GF := GF) rc n k) := by
  unfold batchStart; infer_instance

/-- **The install's restore item** on `fsmMutateCh` (the main goroutine, FSM producer, handed the FSM
`a < x`): the item ends at the snapshot's index `x` (its `batchEnd`), after the previous end `e ≤ a`;
afterwards the producer's state is at `x` (nothing in `(x, x]`). -/
theorem fsmProd_restore_send (γ : GNames) (rc : RCtx GF) (i : SID) (a x : Nat) (v : GoInterface)
    (hax : a < x) :
    fsmProd γ rc a ∗ (∀ k0 : Nat, ⌜k0 ≤ a⌝ -∗ fsmRestoreP γ rc k0 x v) ⊢ |==>
      ∃ sent : List GoInterface, spscProducer rc.names.fsmCh sent ∗
        fsmP γ rc i sent.length v ∗
        (spscProducer rc.names.fsmCh (sent ++ [v]) -∗ fsmProd γ rc x) := by
  unfold fsmProd
  iintro ⟨⟨%sent, %Mb, %e, Hp, Ha, %Hdom, Hend, -⟩, HR⟩
  obtain ⟨Hdom, Hea, Hle⟩ := Hdom
  have hnone : Mb.lookup sent.length = none := by
    have h := Hdom sent.length
    cases hl : Mb.lookup sent.length with
    | none => rfl
    | some _ => exfalso; rw [hl] at h; simp at h
  ihave #Hst : batchStart rc sent.length e $$ [Ha Hend]
  · unfold batchStart
    icases Hend with (%Hn | #Hend)
    · ileft; ipureintro; rw [Hn.1]; exact ⟨rfl, Hn.2⟩
    · cases hs : sent with
      | nil =>
        unfold batchEnd
        rw [hs] at Hdom
        simp only [List.length_nil, Nat.zero_sub]
        ihave %Hl := ghost_map_lookup $$ Ha Hend
        exfalso
        have h := (Hdom 0).mp (by rw [Hl]; rfl)
        simp at h
      | cons y ys =>
        iright; iexists ys.length
        isplitr
        · ipureintro; simp
        · simp only [List.length_cons, Nat.add_sub_cancel]
          iexact Hend
  imod ghost_map_insert_persist sent.length x hnone $$ Ha with ⟨Ha, #Hend1⟩
  imodintro
  iexists sent
  iframe Hp
  isplitl [HR Hst]
  · unfold fsmP
    iexists e, x
    simp only [Int.toNat_natCast]
    iframe Hst
    isplitr
    · ipureintro; omega
    isplitr
    · unfold batchEnd; iexact Hend1
    iright; iright
    iapply HR $$ %e
    ipureintro; exact Hea
  · iintro Hp
    iexists sent ++ [v], Mb.insert sent.length x, x
    iframe Hp Ha
    isplitr
    · ipureintro
      refine ⟨fun m => ?_, Nat.le_refl _, fun m k h => ?_⟩
      · by_cases hm : m = sent.length
        · subst hm; simp
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hm), Hdom m]
          simp only [List.length_append, List.length_singleton]
          omega
      · by_cases hm : m = sent.length
        · subst hm; rw [GMap.lookup_insert_eq] at h; cases h; exact Nat.le_refl _
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hm)] at h
          have := Hle m k h; omega
    isplitr
    · iright
      simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
      unfold batchEnd
      iexact Hend1
    iapply fsmProof.noCmdBetween_self

/-- `io.EOF`'s value is not nil (an `errors.New` error). -/
theorem eof_ne_nil (eof : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.io ∗ globalAddr io.EOF ↦□ eof ⊢ ⌜eof ≠ interface.nil⌝ := by
  iintro ⟨#Hinit, #Heof⟩
  ihave #Hn := io.eof_of_init $$ Hinit
  unfold errors.newVar
  icases Hn with ⟨%x, #Hx, -⟩
  icombine Heof Hx gives %h
  ipureintro; rw [h]; simp [interface.mkOk]

/-- `io.EOF`'s value is pointer-typed (an `errors.New` error, an `*errors.errorString`). -/
theorem eof_ptrTyped (eof : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.io ∗ globalAddr io.EOF ↦□ eof ⊢
      ⌜_root_.Perennial.io.ptrTyped eof⌝ := by
  iintro ⟨#Hinit, #Heof⟩
  ihave #Hn := io.eof_of_init $$ Hinit
  unfold errors.newVar
  icases Hn with ⟨%x, #Hx, -⟩
  icombine Heof Hx gives %h
  ipureintro; rw [h]
  intro ii T h' _; cases h'; exact ⟨x, rfl⟩

/-- A `streamReaderOk` error (`nil` or `io.EOF`) is pointer-typed when `io.EOF`'s value is. -/
theorem streamReaderOk_err_ptrTyped {eof err : GoInterface} {n : w64} {cs : List w8}
    (hpt : _root_.Perennial.io.ptrTyped eof)
    (h : err = interface.nil ∨ (err = eof ∧ sint.nat n = cs.length)) :
    _root_.Perennial.io.ptrTyped err := by
  rcases h with h | ⟨h, _⟩
  · subst h; exact _root_.Perennial.io.ptrTyped_nil
  · subst h; exact hpt

/-- A reader that never fails is a byte stream for `io.Copy` (`io.streamReader`). -/
theorem streamReader_of_ok (rd : GoInterfaceOk) (R : List w8 → IProp GF) (eof : GoInterface)
    (heof : eof ≠ interface.nil) (hpt : _root_.Perennial.io.ptrTyped eof) :
    streamReaderOk rd R eof ⊢ io.streamReader rd R eof := by
  unfold streamReaderOk io.streamReader
  iintro #H
  iintro !> %p %buf %cs %Φ %Hbuf HR Hp HΦ
  iapply H $$ %p %buf %cs %Φ [] HR Hp
  · ipureintro; exact Hbuf
  iintro %n %err %Hn Hp HR
  obtain ⟨h1, h2, h3, h4⟩ := Hn
  iapply HΦ $$ %n %err [] Hp HR
  ipureintro
  refine ⟨h1, h2, h3, fun he => ?_, streamReaderOk_err_ptrTyped hpt h4⟩
  rcases h4 with h | ⟨_, h⟩
  · subst h; exact absurd he.symm heof
  · exact h

/-- The install's counting reader over the RPC's stream is a byte stream for `io.Copy`. -/
theorem streamReader_counting
    (wp_cr_Read : github_com.hashicorp.raft.countingReader.Read.spec (GF := GF) (hG := hG))
    (cr : Loc) (rd : GoInterfaceOk) (R : List w8 → IProp GF) (eof : GoInterface)
    (heof : eof ≠ interface.nil) (hpt : _root_.Perennial.io.ptrTyped eof) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
      countingReaderIs cr (GoInterface.ok rd) ∗ streamReaderOk rd R eof ⊢
    io.streamReader (interface.mk (go.GoType.PointerType countingReader.ty) #cr) R eof := by
  unfold io.streamReader
  iintro ⟨#Hpkg, #Hcr, #H⟩
  iintro !> %p %buf %cs %Φ %Hbuf HR Hp HΦ
  wp_apply wp_cr_Read cr rd R eof p buf cs $$ [$Hcr $H $HR $Hp] as %n %err ⟨%Hn, Hp, HR⟩
  · ipureintro; exact Hbuf
  obtain ⟨h1, h2, h3, h4⟩ := Hn
  iapply HΦ $$ %n %err [] Hp HR
  ipureintro
  refine ⟨h1, h2, h3, fun he => ?_, streamReaderOk_err_ptrTyped hpt h4⟩
  rcases h4 with h | ⟨_, h⟩
  · subst h; exact absurd he.symm heof
  · exact h

/-- A sink is a byte stream writer for `io.Copy` (its owner's state `own (some ws)`). -/
theorem streamWriter_sink (k : GoInterfaceOk) (id : GoString) (own : Option (List w8) → IProp GF)
    (Q R : List w8 → IProp GF) :
    isSink k id own Q R ⊢ io.streamWriter k (fun ws => own (some ws)) := by
  unfold io.streamWriter isSink
  iintro ⟨-, #HW, -⟩
  iintro !> %p %c %ws %dq %Φ Hown Hp HΦ
  ihave %Hlen := ownSlice_len _ _ _ $$ Hp
  iapply HW $$ %p %dq %ws %c %Φ Hown Hp
  iintro Hown Hp
  obtain ⟨h1, h2⟩ := Hlen
  have hl : sint.nat (W64 c.length) = c.length := by rw [h1]; word
  iapply HΦ $$ [] [Hown] [Hp]
  · ipureintro
    constructor
    · rw [h1]; word
    · omega
  · rw [hl, List.take_length]
    iexact Hown
  · iexact Hp

/-- (SNAP-1) The install's response (`Term` an existing term; no header: nil `ID`/`Addr`). -/
theorem isResp_intro (γ : GNames) (rp : InstallSnapshotResponse) (h : rp.RPCHeader' = zeroValDef) :
    termOk (GF := GF) γ (uint.nat rp.Term') ⊢ isResp γ rp := by
  unfold isResp
  iintro #Ht
  iframe Ht
  rw [h]
  iexists [], []
  isplitl
  · iapply ownSlice_nil
  · iapply ownSlice_nil

/-! ### Main-goroutine helpers (as `handlers/Base`'s, which does not build at the freeze) -/

instance snap_termCouple_timeless (γ : GNames) (i : SID) (t : Nat) :
    Timeless (termCouple (GF := GF) γ i t) := by
  unfold termCouple; infer_instance

/-- The server's own term, as a persistent lower bound (hraft_robust: through the view, `srvV_termLb`). -/
theorem termLb_of_srv (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) :
    srvDurInv γ rc i ∗ srvV rc s ⊢ |NC={⊤}=> srvV rc s ∗ termLb γ i s.term :=
  srvV_termLb γ rc i (by solve_ndisj) s

/-- The ghost update at the `currentTerm` store: the protocol step `setTerm`. -/
theorem setTerm_step (γ : GNames) (i : SID) (s : SState) (t : Nat) (ht : s.term ≤ t) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ termOk γ t ⊢
      ∀ t0 : Nat, termCouple γ i t0 ={⊤ \ ↑termN}=∗ termCouple γ i t ∗
        (srvOwn γ i { s with term := t } ∗ termLb γ i t) := by
  iintro ⟨#HI, Hs, #Hok⟩ %t0 Hcp
  imod termCouple_agree γ (⊤ \ ↑termN) gprotN_diff_termN i s _ $$ [$HI $Hs $Hcp] with ⟨Hs, Hcp, %h0⟩
  subst h0
  imod setTerm_upd γ (⊤ \ ↑termN) gprotN_diff_termN i s t ht $$ [$HI $Hs $Hcp $Hok] with ⟨Hs, Hcp, #Hlb⟩
  imodintro
  iframe
  iexact Hlb

omit [GooseSemantics] [GooseInterp] go_gctx package_sem hRB in
/-- Writing the `CurrentTerm` key of the stable store keeps the last vote. -/
theorem voteMatches_term (sst : StableAbs) (s : SState) (v : w64) (t : Nat) (ht : s.term ≤ t)
    (h : voteMatches sst s) :
    voteMatches { sst with ints := sst.ints.insert (go!"CurrentTerm" : List w8) v }
      { s with term := t } := by
  unfold voteMatches at *
  obtain ⟨h1, h2⟩ := h
  have hne : (go!"CurrentTerm" : List w8) ≠ (go!"LastVoteTerm" : List w8) := by decide
  refine ⟨?_, ?_⟩
  · simp only
    rw [GMap.lookup_insert_ne _ _ hne]; exact h1
  · rcases h2 with h2 | h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl (by simp only; omega))
    · exact Or.inr (Or.inr h2)

theorem obsArg_state (γ : GNames) (i : SID) (s : SState) (st : w32) (h : st ≠ stLeader) :
    ⊢ obsArg (GF := GF) γ i s (interface.mkOk RaftState.ty #st) := by
  apply obsArg_other
  rotate_left
  · intro v hv; rw [interface_mkOk_inj] at hv; exact ⟨st, hv.2.symm⟩
  unfold leaderObs
  rw [Ne, interface_mkOk_inj]
  intro ⟨_, h2⟩
  apply h
  exact go.IntoValInj.intoVal_inj (V := w32) h2

/-- The `state` cell holds one of the three states (the main goroutine's half agrees). -/
theorem stateCell_val (r : Loc) (rc : RCtx GF) (st : w32) :
    stateCell r rc ∗ ghostVar rc.names.state (1 : Qp).half st ⊢ |={⊤}=>
      ghostVar rc.names.state (1 : Qp).half st ∗ ⌜st = stFollower ∨ st = stCandidate ∨ st = stLeader⌝ := by
  iintro ⟨#Hc, Hst⟩
  unfold stateCell
  iinv Hc with ⟨%st', Hpt, >Hg, >%Hv⟩ Hclose
  ihave %he := ghostVar_agree _ _ _ _ _ $$ Hst Hg
  subst he
  imod Hclose $$ [Hpt Hg] with -
  · inext; iexists st; iframe; ipureintro; exact Hv
  imodintro
  iframe; ipureintro; exact Hv

omit [GooseSemantics] [GooseInterp] go_gctx package_sem hRB in
/-- A compaction's deletion keeps the log store's coupling, with the window past what it deleted. -/
theorem logOk_delete (A : LogAbs) (L : RLog) (lo mn mx : Nat) (hi' : w64) (h : logOk A L lo) :
    logOk (A.delete mn mx hi') L (Max.max lo (mx + 1)) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro k e hk
    exact h1 k e ((del_lookup_some A.m mn mx k e).1 hk).1
  · intro k hlo hk
    have hk1 : lo ≤ k := by omega
    have hk2 : mx < k := by omega
    rw [← h2 k hk1 hk]
    show (LogAbs.del A.m mn mx).lookup k = A.m.lookup k
    cases hm : A.m.lookup k with
    | none =>
      cases hd : (LogAbs.del A.m mn mx).lookup k with
      | none => rfl
      | some e => rw [(del_lookup_some A.m mn mx k e).1 hd |>.1] at hm; cases hm
    | some e => exact (del_lookup_some A.m mn mx k e).2 ⟨hm, by omega⟩

/-- (hraft_robust R4b) **A compaction** (`DeleteRange(mn, mx)`'s atomic update, any goroutine) up to
`mx` with the compaction frontier and the latest snapshot's index at least `mx` (`compLb`, `latLb`, its
window): the store's window moves past `mx`. -/
theorem logCell_compact (γ : GNames) (rc : RCtx GF) (i : SID) (mn mx : Nat) (Ψ : IProp GF) :
    srvDurInv γ rc i ∗ compLb rc mx ∗ latLb rc mx ∗ Ψ ⊢
    |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ A, rc.ownL A ∗
      (∀ hi' : w64, rc.ownL (A.delete mn mx hi') ={∅, ⊤ \ ↑storeN}=∗ Ψ) := by
  iintro ⟨#Hd, #Hc, #Hl, HΨ⟩
  iapply (logDelete_au γ rc i mn mx iprop(compLb rc mx ∗ latLb rc mx ∗ Ψ) Ψ) $$ Hd [HΨ]
  · iframe; iframe #
  iintro %X %hi' HX ⟨#Hc, #Hl, HΨ⟩
  unfold durCore
  icases HX with ⟨Hs, Hdv, Hlc, Htc, Hcc, Hsv, Hst, Htv, Hcv, %Hok, Hcomp, Hpd, Htp, Hdp, Hlat, Hbp⟩
  ihave %Hmc := compLb_le rc _ X.c mx $$ Hcomp Hc
  ihave %Hml : ⌜mx ≤ latIdxD X.lat⌝ $$ [Hlat]
  · unfold latLb
    ihave %Hv := monoNatLbOwn_valid _ _ _ _ $$ Hlat Hl
    ipureintro; exact Hv.2
  obtain ⟨hlog, hlo, hv, ht, hci, ⟨hdl, hpd, hll⟩, ⟨hdc, hrest⟩⟩ := Hok
  imodintro
  iexists { X with A := X.A.delete mn mx hi', lo := Max.max X.lo (mx + 1) }
  isplitl [Hs Hdv Hlc Htc Hcc Hsv Hst Htv Hcv Hcomp Hpd Htp Hdp Hlat Hbp]
  · iframe
    ipureintro
    refine ⟨logOk_delete X.A X.s.log X.lo mn mx hi' hlog, ?_, hv, ht, hci, ⟨?_, hpd, ?_⟩, ⟨hdc, hrest⟩⟩
    · simp only [Nat.max_def]; split <;> omega
    · intro d hd; have := hdl d hd; have := hdc d hd; simp only [Nat.max_def]; split <;> omega
    · simp only [Nat.max_def]; split <;> omega
  isplitr; · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  imodintro; iexact HΨ

/-- The snapshot goroutine's snapshot `(x, tx)` as the store's latest (`latestOk`; the length bound
of its bytes from the store's commit, SNAP-2). -/
theorem own_latestOk (γ : GNames) (rc : RCtx GF) (x tx : Nat) (id : GoString) (cfg : Configuration)
    (ci : w64) (ss : List Server)
    (b : List w8) (e : Entry) (hx : 1 ≤ x) (hx62 : x < 2 ^ 62) (he : e.term = tx) (htx : tx < 2 ^ 62)
    (hb : b.length < 2 ^ 63) :
    CIdx (GF := GF) γ x e ∗ rc.snapP x b ∗ cfgVal γ cfg ss ∗ snapCfg γ x (uint.nat ci) ss ⊢
      latestOk γ rc (some (sinkMeta (W64 1) (W64 x) (W64 tx) ci cfg id b, b)) := by
  iintro ⟨#HC, HsP, #Hcfg, #Hscfg⟩
  unfold latestOk sinkMeta
  dsimp only
  have h1 : uint.nat (W64 x) = x := by word
  have h2 : uint.nat (W64 tx) = tx := by word
  rw [h1, h2]
  iframe HsP
  isplitr
  · iexists e; iframe HC; ipureintro; exact ⟨he, hx⟩
  isplitr
  · iexists ss; iframe Hcfg Hscfg
  ipureintro
  refine ⟨rfl, ?_, hb, rfl⟩
  word

/-- `CIdx_term_mono` with its order premise as an implication. -/
theorem CIdx_term_mono_imp (γ : GNames) (E : CoPset) (hE : ↑gprotN ⊆ E) (x y : Nat) (e1 e2 : Entry) :
    Inv (GF := GF) γ ∗ CIdx γ x e1 ∗ CIdx γ y e2 ⊢ |={E}=> ⌜x ≤ y → e1.term ≤ e2.term⌝ := by
  iintro ⟨#HI, #H1, #H2⟩
  by_cases h : x ≤ y
  · imod CIdx_term_mono γ E hE x y e1 e2 h $$ [$HI $H1 $H2] with %Ht
    imodintro; ipureintro; intro _; exact Ht
  · imodintro; ipureintro; intro h'; exact absurd h' h

/-- The boot pin's `lastApplied` bound for a new latest at `x` with `applLb rc x`. -/
theorem bootPinF_newLat (rc : RCtx GF) (lat lat' : SnapLatest) (pend : Option (Nat × Nat × GoString))
    (dp : Option DiscPend) (x : Nat) (h : latIdxD lat' = x) :
    bootPinF rc lat pend dp ∗ applLb rc x ⊢ bootPinF rc lat' pend dp := by
  iintro ⟨Hb, #Ha⟩
  unfold bootPinF
  icases Hb with (Hb | -)
  · ileft; iexact Hb
  iright
  unfold latApplF
  rcases lat' with _ | ⟨m, b⟩
  · itrivial
  dsimp only
  iright
  simp only [latIdxD] at h
  rw [h]; iexact Ha

instance ib_CIdx_timeless (γ : GNames) (k : Nat) (e : Entry) : Timeless (CIdx (GF := GF) γ k e) := by
  unfold CIdx; infer_instance

/-- (hraft_robust R4b) **The snapshot goroutine's commit** (its sink's `Close`, `takeSnapshot`, inside
`snapWrite_au`): its snapshot `(x, tx)` (at most `lastApplied` and durable) becomes the latest unless
the latest is newer; during a pending install it is not newer (`x ≤ a < s`, `CIdx_term_mono`). The
latest's index never decreases (committed entries' terms grow with their index), and it is at least
`x` afterwards (`latLb`, for the compaction). -/
theorem own_commit (γ : GNames) (rc : RCtx GF) (i : SID) (x tx : Nat) (id : GoString)
    (cfg : Configuration) (ci : w64) (b : List w8) (e : Entry) (hx : 1 ≤ x)
    (hx62 : x < 2 ^ 62) (he : e.term = tx) (htx : tx < 2 ^ 62) :
    Inv (GF := GF) γ ∗ srvDurInv γ rc i ∗ CIdx γ x e ∗ applLb rc x ∗ durLb γ i x ∗
      latestOk γ rc (some (sinkMeta (W64 1) (W64 x) (W64 tx) ci cfg id b, b)) ⊢
    |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ old, rc.ownSS old ∗
      (rc.ownSS (newerSnap old (sinkMeta (W64 1) (W64 x) (W64 tx) ci cfg id b) b) ={∅, ⊤ \ ↑storeN}=∗
        latLb rc x) := by
  have hE : (↑gprotN : CoPset) ⊆ (⊤ \ ↑storeN) \ ↑durN := by
    unfold storeN durN raftN gprotN; solve_ndisj
  have hix : uint.nat (W64 x) = x := by word
  have htt : uint.nat (W64 tx) = tx := by word
  iintro ⟨#HI, #Hd, #HC, #Hlb, #Hdl, Hnew⟩
  iapply (snapWrite_au γ rc i
    (fun old => newerSnap old (sinkMeta (W64 1) (W64 x) (W64 tx) ci cfg id b) b)
    iprop(latestOk γ rc (some (sinkMeta (W64 1) (W64 x) (W64 tx) ci cfg id b, b))) (latLb rc x))
    $$ Hd [Hnew]
  · iexact Hnew
  iintro %X HX Hld Hnew
  unfold durCore
  icases HX with ⟨Hs, Hdv, Hlc, Htc, Hcc, Hsv, Hst, Htv, Hcv, %Hok, Hcomp, Hpd, Htp, Hdp, Hlat, Hbp⟩
  unfold latestDur
  icases Hld with ⟨Hlok, Hcase⟩
  rcases hp : X.pend with _ | ⟨s0, st0, id0⟩
  · rcases hl : X.lat with _ | ⟨m0, b0⟩
    · -- no latest: the snapshot becomes it
      simp only [hp, hl]
      have hnew : newerSnap none (sinkMeta (W64 1) (W64 x) (W64 tx) ci cfg id b) b = some ((sinkMeta (W64 1) (W64 x) (W64 tx) ci cfg id b), b) := rfl
      have hdpn : X.dp = none := by
        cases hd : X.dp with
        | none => rfl
        | some d => obtain ⟨_, _, h, _⟩ := Hok.2.2.2.2.2.2.2.2 d hd; rw [hl] at h; cases h
      imod mono_nat_own_update (latIdxD (some ((sinkMeta (W64 1) (W64 x) (W64 tx) ci cfg id b), b))) (by simp [latIdxD]) $$ Hlat with ⟨Hlat, #Hlbn⟩
      ihave Hbp := bootPinF_newLat rc _ (some ((sinkMeta (W64 1) (W64 x) (W64 tx) ci cfg id b), b)) _ _ x (by simp only [latIdxD, sinkMeta]; omega) $$ [Hbp]
      · iframe; iframe #
      imodintro
      iexists { X with lat := some ((sinkMeta (W64 1) (W64 x) (W64 tx) ci cfg id b), b) }
      simp only
      try rw [hp]
      isplitl [Hs Hdv Hlc Htc Hcc Hsv Hst Htv Hcv Hcomp Hpd Htp Hdp Hlat Hbp]
      · iframe
        ipureintro
        obtain ⟨h1, h2, h3, h4, h5, ⟨h6, h7, h8⟩, ⟨h9, ⟨h10, h11⟩⟩⟩ := Hok
        refine ⟨h1, h2, h3, h4, h5, ⟨h6, fun _ _ _ h => by simp at h, ?_⟩,
          ⟨h9, ⟨h10, fun d hd => by rw [hdpn] at hd; cases hd⟩⟩⟩
        simp only [latIdxD, sinkMeta, hl] at h8 ⊢; omega
      isplitl [Hnew]
      · inext
        simp only [hp]
        iframe Hnew
        iright; iexists (sinkMeta (W64 1) (W64 x) (W64 tx) ci cfg id b), b
        isplitr; · ipureintro; rfl
        ileft; simp only [sinkMeta]; rw [hix]; iframe Hdl; ipureintro; exact hdpn
      isplitr
      · ipureintro; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | exact hnew.symm | (rw [hl]; exact hnew.symm)
      imodintro
      unfold latLb
      iapply monoNatLbOwn_le x (by simp only [latIdxD, sinkMeta]; omega) $$ Hlbn
    · -- a latest `(m0, b0)`, own or installed (its discard done)
      simp only [hp, hl]
      unfold latestOk
      icases Hlok with ⟨He0, HsP0, Hcf0, >%Hp0⟩
      imod later_exists_except0 $$ He0 with ⟨%e0, He0⟩
      icases He0 with ⟨>#HC0, >%He0⟩
      by_cases hc : uint.nat m0.Term' < tx ∨ (uint.nat m0.Term' = tx ∧ uint.nat m0.Index' ≤ x)
      · have hnew : newerSnap (some (m0, b0)) (sinkMeta (W64 1) (W64 x) (W64 tx) ci cfg id b) b = some ((sinkMeta (W64 1) (W64 x) (W64 tx) ci cfg id b), b) := by
          unfold newerSnap; simp only [sinkMeta, htt, hix]; rw [if_pos hc]
        imod CIdx_term_mono_imp γ _ hE x (uint.nat m0.Index') e e0 $$ [$HI $HC $HC0] with %Ht
        have hle : uint.nat m0.Index' ≤ x := by
          rcases Nat.lt_or_ge x (uint.nat m0.Index') with h | h
          · have := Ht (by omega); omega
          · exact h
        rcases hd : X.dp with _ | d
        · -- no discard pending: the own snapshot becomes the latest, durable
          imod mono_nat_own_update (latIdxD (some ((sinkMeta (W64 1) (W64 x) (W64 tx) ci cfg id b), b))) (by simp only [latIdxD, sinkMeta]; omega)
            $$ Hlat with ⟨Hlat, #Hlbn⟩
          ihave Hbp := bootPinF_newLat rc _ (some ((sinkMeta (W64 1) (W64 x) (W64 tx) ci cfg id b), b)) _ _ x (by simp only [latIdxD, sinkMeta]; omega) $$ [Hbp]
          · iframe; iframe #
          imodintro
          iexists { X with lat := some ((sinkMeta (W64 1) (W64 x) (W64 tx) ci cfg id b), b) }
          simp only
          try rw [hp]
          try rw [hd]
          isplitl [Hs Hdv Hlc Htc Hcc Hsv Hst Htv Hcv Hcomp Hpd Htp Hdp Hlat Hbp]
          · iframe
            ipureintro
            rw [hd] at Hok
            obtain ⟨h1, h2, h3, h4, h5, ⟨h6, h7, h8⟩, ⟨h9, ⟨h10, h11⟩⟩⟩ := Hok
            refine ⟨h1, h2, h3, h4, h5, ⟨h6, fun _ _ _ h => by simp at h, ?_⟩,
              ⟨h9, ⟨h10, fun d hd' => by cases hd'⟩⟩⟩
            simp only [latIdxD, sinkMeta, hl] at h8 ⊢; rw [hix]; omega
          isplitl [Hnew]
          · inext
            simp only [hp]
            iframe Hnew
            iright; iexists (sinkMeta (W64 1) (W64 x) (W64 tx) ci cfg id b), b
            isplitr; · ipureintro; rfl
            ileft; simp only [sinkMeta]; rw [hix]; iframe Hdl
          isplitr
          · ipureintro; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | exact hnew.symm | (rw [hl]; exact hnew.symm)
          imodintro
          unfold latLb
          iapply monoNatLbOwn_le x (by simp only [latIdxD, sinkMeta]; omega) $$ Hlbn
        · -- a discard pending (the install's snapshot, at `lastApplied ≥ x`): the own snapshot is the
          -- same entry, and replaces it with the same index and term
          obtain ⟨m1, b1, hl1, hi1, ht1⟩ := Hok.2.2.2.2.2.2.2.2 d hd
          rw [hl] at hl1
          cases hl1
          ihave Hcase := later_or.1 $$ Hcase
          icases Hcase with (>%Hn | Hc)
          · cases Hn
          imod later_exists_except0 $$ Hc with ⟨%m2, Hc⟩
          imod later_exists_except0 $$ Hc with ⟨%b2, Hc⟩
          icases Hc with ⟨>%Heq2, Hd2⟩
          ihave Hd2 := later_or.1 $$ Hd2
          icases Hd2 with (⟨-, >%Hdn⟩ | ⟨Hfol0, >%Hdp0, Ha⟩)
          · simp at Hdn
          imod later_exists_except0 $$ Ha with ⟨%a0, Ha⟩
          icases Ha with ⟨>Hauth, >%Hale⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at Heq2
          obtain ⟨rfl, rfl⟩ := Heq2
          ihave %Hxa := applLb_le rc _ _ _ $$ Hauth Hlb
          have hxe : x = uint.nat m0.Index' := by omega
          ihave #HC0' : CIdx γ x e0 $$ []
          · rw [hxe]; iexact HC0
          ihave %Heqe := CIdx_agree γ x e e0 $$ [$HC $HC0']
          have htx0 : tx = uint.nat m0.Term' := by rw [← he, Heqe]; exact He0.1
          imod mono_nat_own_update (latIdxD (some ((sinkMeta (W64 1) (W64 x) (W64 tx) ci cfg id b), b))) (by simp only [latIdxD, sinkMeta]; omega)
            $$ Hlat with ⟨Hlat, #Hlbn⟩
          ihave Hbp := bootPinF_newLat rc _ (some ((sinkMeta (W64 1) (W64 x) (W64 tx) ci cfg id b), b)) _ _ x (by simp only [latIdxD, sinkMeta]; omega) $$ [Hbp]
          · iframe; iframe #
          imodintro
          iexists { X with lat := some ((sinkMeta (W64 1) (W64 x) (W64 tx) ci cfg id b), b) }
          simp only
          try rw [hp]
          try rw [hd]
          isplitl [Hs Hdv Hlc Htc Hcc Hsv Hst Htv Hcv Hcomp Hpd Htp Hdp Hlat Hbp]
          · iframe
            ipureintro
            rw [hd] at Hok
            obtain ⟨h1, h2, h3, h4, h5, ⟨h6, h7, h8⟩, ⟨h9, ⟨h10, h11⟩⟩⟩ := Hok
            refine ⟨h1, h2, h3, h4, h5, ⟨h6, fun _ _ _ h => by simp at h, ?_⟩,
              ⟨h9, ⟨h10, fun d' hd' => ?_⟩⟩⟩
            · simp only [latIdxD, sinkMeta, hl] at h8 ⊢; rw [hix]; omega
            · simp only [Option.some.injEq] at hd'; subst hd'
              refine ⟨(sinkMeta (W64 1) (W64 x) (W64 tx) ci cfg id b), b, rfl, ?_, ?_⟩ <;> simp only [sinkMeta] <;> omega
          isplitl [Hnew Hauth Hfol0]
          · inext
            simp only [hp]
            iframe Hnew
            iright; iexists (sinkMeta (W64 1) (W64 x) (W64 tx) ci cfg id b), b
            isplitr; · ipureintro; rfl
            iright
            simp only [sinkMeta]
            rw [hix, htt]
            rw [hxe, htx0]
            iframe Hfol0
            isplitr; · ipureintro; first | exact Hdp0 | (rw [hd] at Hdp0; exact Hdp0) | (rw [← hd]; exact Hdp0)
            iexists a0; iframe; ipureintro; exact Hale
          isplitr
          · ipureintro; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | exact hnew.symm | (rw [hl]; exact hnew.symm)
          imodintro
          unfold latLb
          iapply monoNatLbOwn_le x (by simp only [latIdxD, sinkMeta]; omega) $$ Hlbn
      · have hnew : newerSnap (some (m0, b0)) (sinkMeta (W64 1) (W64 x) (W64 tx) ci cfg id b) b = some (m0, b0) := by
          simp only [newerSnap, sinkMeta, htt, hix]; split <;> first | rfl | (exfalso; omega) | simp_all
        imod CIdx_term_mono_imp γ _ hE (uint.nat m0.Index') x e0 e $$ [$HI $HC $HC0] with %Ht
        have hge : x ≤ uint.nat m0.Index' := by
          rcases Nat.lt_or_ge (uint.nat m0.Index') x with h | h
          · have := Ht (by omega); exfalso; apply hc; omega
          · exact h
        ihave #Hlbn := monoNatLbOwn_get _ _ _ $$ Hlat
        iclear Hnew
        imodintro
        iexists X
        try rw [hp]
        rw [hl]
        isplitl [Hs Hdv Hlc Htc Hcc Hsv Hst Htv Hcv Hcomp Hpd Htp Hdp Hlat Hbp]
        · iframe; ipureintro; simp only [hp, hl] at Hok ⊢; exact Hok
        isplitl [HsP0 Hcf0 Hcase]
        · inext
          dsimp only
          isplitr [Hcase]
          · iframe HsP0 Hcf0
            isplitr
            · iexists e0; iframe #; ipureintro; exact He0
            ipureintro; exact Hp0
          iexact Hcase
        isplitr
        · ipureintro; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | exact hnew.symm | (rw [hl]; exact hnew.symm)
        imodintro
        unfold latLb
        iapply monoNatLbOwn_le x (by (try rw [hl]); simp only [latIdxD]; exact hge) $$ Hlbn
  · -- an install pending: its snapshot (above `lastApplied ≥ x`) stays the latest
    simp only [hp]
    imod later_exists_except0 $$ Hcase with ⟨%m, Hcase⟩
    imod later_exists_except0 $$ Hcase with ⟨%b', Hcase⟩
    imod later_exists_except0 $$ Hcase with ⟨%a', Hcase⟩
    icases Hcase with ⟨>%Hm, Hfol, >Happ⟩
    obtain ⟨hl, hid, hidx, htm, ha⟩ := Hm
    ihave %Hxa := applLb_le rc _ _ _ $$ Happ Hlb
    rw [hl]
    unfold latestOk
    icases Hlok with ⟨He0, HsP0, Hcf0, >%Hp0⟩
    imod later_exists_except0 $$ He0 with ⟨%e0, He0⟩
    icases He0 with ⟨>#HC0, >%He0⟩
    imod CIdx_term_mono γ _ hE x (uint.nat m.Index') e e0 (by omega) $$ [$HI $HC $HC0] with %Ht
    have hc : ¬ (uint.nat m.Term' < tx ∨ (uint.nat m.Term' = tx ∧ uint.nat m.Index' ≤ x)) := by omega
    have hnew : newerSnap (some (m, b')) (sinkMeta (W64 1) (W64 x) (W64 tx) ci cfg id b) b = some (m, b') := by
      simp only [newerSnap, sinkMeta, htt, hix]; split <;> first | rfl | (exfalso; omega) | simp_all
    ihave #Hlbn := monoNatLbOwn_get _ _ _ $$ Hlat
    iclear Hnew
    imodintro
    iexists X
    try rw [hp]
    rw [hl]
    isplitl [Hs Hdv Hlc Htc Hcc Hsv Hst Htv Hcv Hcomp Hpd Htp Hdp Hlat Hbp]
    · iframe; ipureintro; simp only [hp, hl] at Hok ⊢; exact Hok
    isplitl [HsP0 Hcf0 Hfol Happ]
    · inext
      dsimp only
      (try rw [hl]); (try unfold latestOk)
      iframe HsP0 Hcf0
      isplitr [Hfol Happ]
      · isplitr
        · iexists e0; iframe #; ipureintro; exact He0
        ipureintro; exact Hp0
      iexists m, b', a'; iframe; ipureintro; exact ⟨rfl, hid, hidx, htm, ha⟩
    isplitr
    · ipureintro; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | exact hnew.symm | (rw [hl]; exact hnew.symm)
    imodintro
    unfold latLb
    iapply monoNatLbOwn_le x (by (try rw [hl]); simp only [latIdxD]; omega) $$ Hlbn


/-- (Unfolds gprot's `InvBody`, a missing gprot law, as `ReplSnap.CIdx_lt`.) A committed entry's term
is below the bound on terms (`2^62`). -/
theorem CIdx_term_lt (γ : GNames) (E : CoPset) (hE : ↑gprotN ⊆ E) (x : Nat) (e : Entry) :
    Inv (GF := GF) γ ∗ CIdx γ x e ⊢ |={E}=> ⌜e.term < 2 ^ 62⌝ := by
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
  have hl := C_llog σ x e hg.1 hC
  have hle : e.term ≤ σ.maxT := by
    apply Classical.byContradiction; intro hc
    rw [llog_gt_maxT hg.1 (by omega)] at hl
    simp [ent] at hl
  omega

/-- (Unfolds gprot's `InvBody`, a missing gprot law.) (Stage 4; stage 3: a committed configuration
entry is the genesis, at index 1, false now: Design question I1-7/I2) A committed configuration entry
encodes a valid configuration (`proto.ICfgOk`: its voters are valid, so its data encodes a valid
configuration over the servers, `cfgDec_valid`): what `runFSM` needs for `DecodeConfiguration` and the
FSM's `StoreConfiguration`. -/
theorem CIdx_config (γ : GNames) (E : CoPset) (hE : ↑gprotN ⊆ E) (x : Nat) (e : Entry)
    (hcv : γ.cv = cfgDec γ.srvs) :
    Inv (GF := GF) γ ∗ CIdx γ x e ⊢ |={E}=>
      ⌜e.kind = kConfig → ∃ ss : List Server, e.data = encodeServers ss ∧ srvsOk γ ss⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr, Hcc⟩, #Hc⟩
  ihave ⟨Hh, %hC⟩ := H_C_lookup γ σ x e $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hc
  isplitl [Hh Hs Hr Hcc]
  · iframe; ipureintro; exact hg
  ipureintro
  intro hk
  have hl := C_llog σ x e hg.1 hC
  have hv : cfgValid σ.srvs (σ.cv e.data) := hg.1.2.2.1.2.2.2.2 e.term x e hl hk
  rw [hg.2.1, hg.2.2.2.1, hcv] at hv
  obtain ⟨ss, hd, hss⟩ := cfgDec_valid γ.srvs e.data hv.1
  exact ⟨ss, hd, hss⟩
  /- stage-3 statement: `Inv γ ∗ CIdx γ x e ⊢ |={E}=> ⌜e.kind = kConfig → x = 1⌝`; stage-3 proof:
  := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, #Hc⟩
  ihave ⟨Hh, %hC⟩ := H_C_lookup γ σ x e $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hc
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  ipureintro
  have hl := C_llog σ x e hg.1 hC
  exact hg.1.2.2.1.2.2.2.2.2 e.term x e hl
  -/

omit [GooseSemantics] [GooseInterp] go_gctx package_sem hRB in
/-- The prefix through an index with an entry. -/
theorem take_ent (L : RLog) (k : Nat) (e : Entry) (h : ent L k = some e) :
    L.take k = L.take (k - 1) ++ [e] := by
  have hk := proto.ent_le_length h
  rw [gprot.ent_eq_getElem? L k hk.1] at h
  have h1 : k = (k - 1) + 1 := by omega
  conv => lhs; rw [h1]
  rw [List.take_succ, h]; rfl

/-- (stage 4) **The snapshot's configuration in a log whose prefix through `x` is committed**: the
configuration entry the snapshot names (`snapCfg`) is the log's latest at or below `x`. -/
theorem snapCfg_take (γ : GNames) (L : RLog) (x ci : Nat) (ss : List Server) (hx : x ≤ L.length) :
    CLb (GF := GF) γ (L.take x) ∗ snapCfg γ x ci ss ⊢
      ⌜lastCfgIdx (L.take x) = ci ∧ 1 ≤ ci ∧ ci ≤ x ∧ srvsOk γ ss ∧
        ∃ e, ent L ci = some e ∧ e.kind = kConfig ∧ e.data = encodeServers ss⌝ := by
  iintro ⟨#HL, #Hsc⟩
  unfold snapCfg
  icases Hsc with ⟨%Hc, ⟨%e, #HCe, %He⟩, #Hn⟩
  obtain ⟨h1, h2, h3⟩ := Hc
  have hlen : (L.take x).length = x := by simp; omega
  obtain ⟨e', he'⟩ := proto.ent_isSome (L.take x) ci h1 (by omega)
  ihave #HCe' := CLb_idx γ (L.take x) ci e' he' $$ HL
  ihave %Heq := CIdx_agree γ ci e' e $$ [$HCe' $HCe]
  subst Heq
  have hentL : ent L ci = some e' := by rw [← proto.ent_take L x ci h2]; exact he'
  obtain ⟨hs1, hs2, hs3⟩ := proto.lastCfgIdx_spec (L.take x)
  -- no configuration entry of `L.take x` lies after `ci`
  by_cases hlt : ci < lastCfgIdx (L.take x)
  · have hm0 : lastCfgIdx (L.take x) ≠ 0 := by omega
    obtain ⟨em, hem, hemk⟩ := hs2.resolve_left hm0
    have hmx : lastCfgIdx (L.take x) ≤ x := by omega
    have hj : (List.range' (ci + 1) (x + 1 - (ci + 1)))[lastCfgIdx (L.take x) - (ci + 1)]? =
        some (lastCfgIdx (L.take x)) := by
      rw [List.getElem?_range'] <;> simp <;> omega
    unfold noCfgBetween
    ihave ⟨%e2, #HC2, %Hk2⟩ := BigSepL.bigSepL_lookup
      (Φ := fun _ k => iprop(∃ e' : Entry, CIdx (GF := GF) γ k e' ∗ ⌜e'.kind ≠ kConfig⌝)) hj $$ Hn
    ihave #HCm := CLb_idx γ (L.take x) _ em hem $$ HL
    ihave %Heq2 := CIdx_agree γ _ em e2 $$ [$HCm $HC2]
    subst Heq2
    exact absurd hemk Hk2
  · have hge : ¬ lastCfgIdx (L.take x) < ci := by
      intro h; exact hs3 ci e' h he' He.1
    ipureintro
    exact ⟨by omega, h1, h2, h3, e', hentL, He⟩

/-- (stage 4) **The install's configurations** (`setLatestConfiguration`/`setCommittedConfiguration`
to the request's): with the snapshot's index `x` durable, its configuration entry (`snapCfg`) is the
server's log's latest at or below `x`, at `ci` (`cfgAtIs`), committed (`cmtIdx`, as `ci ≤ x ≤ dur`). -/
theorem install_cfgs (γ : GNames) (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState)
    (x ci : Nat) (ss : List Server) (c : Configuration) (hx : x ≤ s.dur.1) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ snapCfg γ x ci ss ∗ c.Servers' ↦*□ ss ⊢ |={E}=>
      srvOwn γ i s ∗ cfgAtIs γ s.log ci c ∗ cmtIdx γ s.term s.log ci ∗
      ⌜lastCfgIdx (s.log.take x) = ci ∧ 1 ≤ ci ∧ ci ≤ x ∧ x ≤ s.log.length⌝ := by
  iintro ⟨#HI, Hs, #Hsc, #Hc⟩
  imod srvOwn_facts γ E hE i s $$ [$HI $Hs] with ⟨Hs, -, %Hf⟩
  imod srvOwn_CLb γ E hE i s $$ [$HI $Hs] with ⟨Hs, #HL⟩
  have ht : (s.log.take s.dur.1).take x = s.log.take x := by
    rw [List.take_take, Nat.min_eq_left hx]
  ihave #HL' : CLb γ (s.log.take x) $$ [HL]
  · rw [← ht]; iapply CLb_take; iexact HL
  ihave %H := snapCfg_take γ s.log x ci ss (by omega) $$ [$HL' $Hsc]
  obtain ⟨hl, h1, h2, h3, e, he, hk, hd⟩ := H
  imod cmtIdx_dur γ E hE i s ci (by omega) $$ [$HI $Hs] with ⟨Hs, #Hcm⟩
  imodintro
  iframe Hs Hcm
  isplitl
  · unfold cfgAtIs; iright; iexists ss, e; unfold cfgVal; iframe Hc
    isplitr
    · ipureintro; exact h3
    ipureintro; exact ⟨h1, he, hk, hd⟩
  ipureintro; exact ⟨hl, h1, h2, by omega⟩

/-- **The restore's `Open(id)`** (the FSM goroutine, holding the pending record's main-goroutine half,
lent through the restore future; hraft_robust: over `srvDurInv`): the store's latest is the install's
snapshot `(s, st)` with id `id` (`latestDur`'s pending case): `Open` returns its metadata and a reader
over its bytes, a snapshot of `s`. -/
theorem restore_open (γ : GNames) (rc : RCtx GF) (i : SID) (fx : GoInterfaceOk) (s st : Nat)
    (id : GoString) (eof : GoInterface) (Ψ : val → IProp GF) :
    srvDurInv γ rc i ∗ isFSM fx γ i rc.fsmOwn rc.respP rc.snapP ∗
      ghostVar rc.dur.pend (1 : Qp).half (some (s, st, id)) ∗
      (∀ (m : SnapshotMeta) (b : List w8) (mp : Loc) (rd : GoInterfaceOk) (R : List w8 → IProp GF),
        ⌜uint.nat m.Index' = s ∧ uint.nat m.Term' = st ∧ 1 ≤ s⌝ -∗ mp ↦ m -∗ readCloserOk rd R eof -∗ R b -∗
        rc.snapP s b -∗ ghostVar rc.dur.pend (1 : Qp).half (some (s, st, id)) -∗
        Ψ (PairV (PairV #mp #(GoInterface.ok rd)) #interface.nil)) ⊢
    |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ old, rc.ownSS old ∗
      (rc.ownSS old ={∅, ⊤ \ ↑storeN}=∗ ∀ v, openPost old id eof v -∗ Ψ v) := by
  iintro ⟨#Hsc0, #HisFSM, Hpend, HΨ⟩ Hnc
  iunfold srvDurInv at Hsc0
  icases Hsc0 with ⟨#Hsc, -⟩
  ihave Hacc := durAcc γ rc i (E := ⊤ \ ↑storeN) (by unfold durN raftN storeN; solve_ndisj) $$ Hsc
  imod Hacc $$ Hnc with ⟨Hnc, HX, Hclose⟩
  imod later_exists_except0 $$ HX with ⟨%X, HX⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iframe Hnc
  inext
  unfold durBody
  icases HX with ⟨Hs, Hdv, Hlc, Htc, Hcc, Hsv, Hst, Htv, Hcv, HownL, HownS, Hown, HpA, HpB, Hbp,
    Hcomp, HpC, HpD, Hla, Hld, Hpd, Hrest⟩
  iexists X.lat
  iframe Hown
  iintro Hown
  imod Hmask with -
  ihave %Hpdq := ghostVar_agree _ _ _ _ _ $$ Hpend Hpd
  unfold latestDur
  icases Hld with ⟨Hlat, Hcase⟩
  rw [← Hpdq]
  icases Hcase with ⟨%m, %b, %a', %Hm, #Hfol, Happ⟩
  obtain ⟨Hl, Hid, Hi, Ht, Ha⟩ := Hm
  rw [Hl]
  unfold latestOk
  icases Hlat with ⟨#HCm, HsP, #Hcfgm, %Hmfacts⟩
  ihave ⟨%e1, -, %He1⟩ := HCm
  ihave #HsP := isFSM_snapP_persistent _ γ i _ _ _ _ b $$ [$HisFSM $HsP]
  imod Hclose $$ [Hs Hdv Hlc Htc Hcc Hsv Hst Htv Hcv HownL HownS Hown HpA HpB Hbp Hcomp HpC HpD Hla Hpd
    Hrest Happ] with -
  · inext
    iexists X
    rw [Hl, ← Hpdq]
    iframe
    try unfold latestDur
    try unfold latestOk
    dsimp only
    isplitr
    · iframe #; ipureintro; exact Hmfacts
    iexists m, b, a'
    iframe Happ Hfol
    ipureintro; exact ⟨rfl, Hid, Hi, Ht, Ha⟩
  imodintro
  iintro %v Hpost
  unfold openPost
  dsimp only
  rw [if_pos Hid]
  icases Hpost with ⟨%mp, %rd, %R, %Hv, Hmp, #Hrc, HR, %HnWT⟩
  subst Hv
  subst Hi
  iapply HΨ $$ %m %b %mp %rd %R [] Hmp Hrc HR HsP Hpend
  ipureintro; exact ⟨rfl, Ht, He1.2⟩


end github_com.hashicorp.raft.snapProof

end proof

end Perennial
