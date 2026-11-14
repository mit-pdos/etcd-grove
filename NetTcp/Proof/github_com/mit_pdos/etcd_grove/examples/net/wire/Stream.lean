/-
A per-direction stream protocol, for the proofs of `examples/net/` (proved, not trusted): what a
direction's writer has written and its reader has read, as ghost state, tied to the direction's
unread bytes (`tcpDir`, the semantics' state) by an invariant (`dirInv`).

* `sentAll γ W` (the writer's): the writer has written `W` into the direction, in all. A half of a
  monotone list; the invariant holds the other half. `sentLb γ W` (persistent): it has written at
  least `W`.
* `rcvdAll γ R` (the reader's): the reader has read `R` from it, in all. A half of a ghost
  variable; the invariant holds the other half.
* `DirOk d W R`: the read bytes followed by the unread ones are what was written, exactly while
  the connection is not broken (`d.status ≠ .cut`), a prefix of it once it is (bytes were lost).
  So the reader's bytes are always a prefix of the writer's (`read_au` gives `sentLb γ R`).

The histories `W` and `R` are the proofs' bookkeeping: the semantics and the `net` specs have only
the unread bytes (`notes/net-tcp.md`). The atomic updates of the operations, for an end its thread
owns (`tcpEnd`): `write_au`, `read_au` (and `read_acc`, the accessor `wire.ReadFull`'s spec takes),
`close_au`, `closeWrite_au`; their pure parts are `dirOk_write`, `dirOk_read`, `dirOk_shut`.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Addr
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.GhostVar

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp

namespace github_com.mit_pdos.etcd_grove.examples.net.wire

/-! ## The pure part -/

section pure

/-- A direction's unread bytes and what its writer wrote (`W`) and its reader read (`R`) agree:
exactly, unless the connection broke, and as a prefix once it did. -/
def DirOk (d : TcpDir) (W R : List w8) : Prop :=
  if d.status = .cut then R ++ d.bytes <+: W else R ++ d.bytes = W

theorem dirOk_prefix {d : TcpDir} {W R : List w8} (h : DirOk d W R) : R <+: W := by
  unfold DirOk at h
  split at h
  · exact (List.prefix_append R d.bytes).trans h
  · rw [← h]; exact List.prefix_append R d.bytes

theorem dirOk_fresh : DirOk TcpDir.fresh [] [] := by
  simp [DirOk, TcpDir.fresh]

theorem dirOk_cut {d : TcpDir} {W R : List w8} (k : Nat) (h : DirOk d W R) :
    DirOk ⟨d.bytes.take k, .cut⟩ W R := by
  simp only [DirOk, ↓reduceIte]
  have hp : R ++ d.bytes.take k <+: R ++ d.bytes :=
    (List.prefix_append_right_inj R).2 (List.take_prefix k d.bytes)
  unfold DirOk at h
  split at h
  · exact hp.trans h
  · rw [← h]; exact hp

theorem dirOk_avail {st : TcpEnd} {d d' : TcpDir} {W R : List w8} {n : Nat} {r : ReadRes}
    (h : DirOk d W R) (hr : ReadAvail st d n r d') : DirOk d' W (R ++ r.got) := by
  rcases hr with ⟨k, -, -, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ |
    ⟨-, rfl, rfl⟩
  · simp only [ReadRes.got, DirOk, List.append_assoc, List.take_append_drop] at h ⊢
    exact h
  all_goals simpa [ReadRes.got] using h

/-- A read keeps `DirOk`, the reader having read what it returned. -/
theorem dirOk_read {st : TcpEnd} {d d' : TcpDir} {W R : List w8} {n : Nat} {r : ReadRes}
    (h : DirOk d W R) (hr : ReadOutcome st d n r d') : DirOk d' W (R ++ r.got) := by
  unfold ReadOutcome at hr
  split at hr
  · obtain ⟨rfl, rfl⟩ := hr; simpa [ReadRes.got] using h
  · split at hr
    · obtain ⟨rfl, rfl⟩ := hr; simpa [ReadRes.got] using h
    · rcases hr with hr | ⟨k, -, hr⟩
      · exact dirOk_avail h hr
      · exact dirOk_avail (dirOk_cut k h) hr

/-- A write keeps `DirOk`, the writer having written what it appended. -/
theorem dirOk_write {st : TcpEnd} {d d' : TcpDir} {W R bs : List w8} {k : Nat} {ok : Bool}
    (h : DirOk d W R) (hw : WriteOutcome st d bs k ok d') : DirOk d' (W ++ bs.take k) R := by
  unfold WriteOutcome at hw
  split at hw
  · obtain ⟨rfl, -, rfl⟩ := hw; simpa using h
  · rename_i hnc
    split at hw
    · rename_i hcut
      obtain ⟨-, rfl⟩ := hw
      simp only [DirOk, hcut, ↓reduceIte] at h ⊢
      exact h.trans (List.prefix_append W _)
    · rename_i hcut
      simp only [DirOk, hcut, ↓reduceIte] at h
      rcases hw with ⟨rfl, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩
      · simp only [DirOk, hcut, ↓reduceIte, List.take_length, ← List.append_assoc, h]
      · simp only [DirOk, ↓reduceIte, ← List.append_assoc, h]
        exact List.prefix_refl _
      · simp only [DirOk, hcut, ↓reduceIte, ← List.append_assoc, h]

/-- A write that returns success wrote all of it. -/
theorem writeOutcome_ok {st : TcpEnd} {d d' : TcpDir} {bs : List w8} {k : Nat}
    (hw : WriteOutcome st d bs k true d') : k = bs.length := by
  unfold WriteOutcome at hw
  split at hw
  · cases hw.2.1
  · split at hw
    · rcases hw.1 with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · cases h
    · rcases hw with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h, -⟩
      · exact h
      · cases h
      · cases h

/-- A write returns at most what it was given. -/
theorem writeOutcome_le {st : TcpEnd} {d d' : TcpDir} {bs : List w8} {k : Nat} {ok : Bool}
    (hw : WriteOutcome st d bs k ok d') : k ≤ bs.length := by
  unfold WriteOutcome at hw
  split at hw
  · rw [hw.1]; exact Nat.zero_le _
  · split at hw
    · rcases hw.1 with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
    · rcases hw with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩ <;> omega

theorem dirOk_shut {d : TcpDir} {W R : List w8} (h : DirOk d W R) : DirOk d.shut W R := by
  unfold TcpDir.shut
  split
  · rename_i ho
    simp only [DirOk, ho, ↓reduceIte] at h ⊢
    simpa using h
  · exact h

theorem dirOk_close {st st' : TcpEnd} {d d' : TcpDir} {W R : List w8} {ok : Bool}
    (h : DirOk d W R) (hc : CloseOutcome st d ok st' d') : DirOk d' W R := by
  unfold CloseOutcome at hc
  split at hc
  · obtain ⟨-, -, rfl⟩ := hc; exact h
  · obtain ⟨-, rfl⟩ := hc; exact dirOk_shut h

theorem dirOk_closeWrite {st : TcpEnd} {d d' : TcpDir} {W R : List w8} {ok : Bool}
    (h : DirOk d W R) (hc : CloseWriteOutcome st d ok d') : DirOk d' W R := by
  unfold CloseWriteOutcome at hc
  split at hc
  · obtain ⟨-, rfl⟩ := hc; exact h
  · rcases hc with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact dirOk_shut h
    · exact h

/-- A read of `m` bytes returns at most `m`, and some unless `m = 0`. -/
theorem readOutcome_got_le {st : TcpEnd} {d : TcpDir} {m : Nat} {r : ReadRes} {d' : TcpDir}
    (h : ReadOutcome st d m r d') : r.got.length ≤ m ∧ (r = .bytes [] → m = 0) := by
  have hav : ∀ d0, ReadAvail st d0 m r d' → r.got.length ≤ m ∧ (r = .bytes [] → m = 0) := by
    intro d0 h
    rcases h with ⟨k, hk1, hk, hkd, rfl, -⟩ | ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, -⟩ | ⟨-, rfl, -⟩ |
      ⟨-, rfl, -⟩
    · refine ⟨by simp only [ReadRes.got, List.length_take]; omega, ?_⟩
      intro h
      have h' := congrArg (fun r => r.got.length) h
      simp only [ReadRes.got, List.length_take, List.length_nil] at h'
      omega
    all_goals simp [ReadRes.got]
  unfold ReadOutcome at h
  split at h
  · obtain ⟨rfl, -⟩ := h; simp [ReadRes.got]
  split at h
  · obtain ⟨rfl, -⟩ := h; simp [ReadRes.got]; assumption
  rcases h with h | ⟨k, -, h⟩
  · exact hav _ h
  · exact hav _ h

/-- A read of `n > 0` bytes that returns bytes returns at least one. -/
theorem readOutcome_bytes_pos {st : TcpEnd} {d d' : TcpDir} {n : Nat} {bs : List w8}
    (h : ReadOutcome st d n (.bytes bs) d') (hn : 0 < n) : 1 ≤ bs.length := by
  have hav : ∀ (d0 : TcpDir), ReadAvail st d0 n (.bytes bs) d' → 1 ≤ bs.length := by
    intro d0 hr
    rcases hr with ⟨k, hk1, -, hkl, hr, -⟩ | ⟨-, -, hr, -⟩ | ⟨-, -, hr, -⟩ | ⟨-, hr, -⟩ |
      ⟨-, hr, -⟩
    · cases hr; simp only [List.length_take]; omega
    all_goals cases hr
  unfold ReadOutcome at h
  split at h
  · cases h.1
  · split at h
    · omega
    · rcases h with h | ⟨k, -, h⟩
      · exact hav d h
      · exact hav _ h

/-- A close leaves the end closed. -/
theorem closeOutcome_closed {st : TcpEnd} {d : TcpDir} {ok : Bool} {st' : TcpEnd} {d' : TcpDir}
    (h : CloseOutcome st d ok st' d') : st'.closed = true := by
  unfold CloseOutcome at h
  split at h
  · rw [h.2.1]; assumption
  · rw [h.1]

/-- A close of a closed end fails and changes nothing. -/
theorem closeOutcome_of_closed {st : TcpEnd} {d : TcpDir} {ok : Bool} {st' : TcpEnd}
    {d' : TcpDir} (hc : st.closed = true) (h : CloseOutcome st d ok st' d') :
    ok = false ∧ st' = st := by
  simp only [CloseOutcome, hc, ↓reduceIte] at h
  exact ⟨h.1, h.2.1⟩

/-- A write on a closed end fails. -/
theorem writeOutcome_of_closed {st : TcpEnd} {d : TcpDir} {bs : List w8} {k : Nat} {ok : Bool}
    {d' : TcpDir} (hc : st.closed = true) (h : WriteOutcome st d bs k ok d') : ok = false := by
  simp only [WriteOutcome, hc, Bool.true_or, ↓reduceIte] at h
  exact h.2.1

/-- A read on a closed end fails. -/
theorem readOutcome_of_closed {st : TcpEnd} {d : TcpDir} {n : Nat} {r : ReadRes} {d' : TcpDir}
    (hc : st.closed = true) (h : ReadOutcome st d n r d') : r = .err := by
  simp only [ReadOutcome, hc, ↓reduceIte] at h
  exact h.1

end pure

/-! ## The ghost state and the invariant -/

/-- The ghost names of a direction's protocol: the writer's monotone list, the reader's ghost
variable. -/
structure DirNames where
  w : GName
  r : GName

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The writer has written `W`, in all. -/
def sentAll (γ : DirNames) (W : List w8) : IProp GF :=
  @monoListAuthOwn GF (G (Gg := Gg)).allG _ _ γ.w (1 : Qp).half W

/-- The writer has written at least `W` (persistent). -/
def sentLb (γ : DirNames) (W : List w8) : IProp GF :=
  @monoListLbOwn GF (G (Gg := Gg)).allG _ _ γ.w W

/-- The reader has read `R`, in all. -/
def rcvdAll (γ : DirNames) (R : List w8) : IProp GF :=
  @ghostVar GF (G (Gg := Gg)).allG _ _ γ.r (1 : Qp).half R

instance sentAll_timeless (γ : DirNames) (W : List w8) : Timeless (sentAll (Gg := Gg) γ W) := by
  unfold sentAll; letI := (G (Gg := Gg)).allG; infer_instance
instance sentLb_timeless (γ : DirNames) (W : List w8) : Timeless (sentLb (Gg := Gg) γ W) := by
  unfold sentLb; letI := (G (Gg := Gg)).allG; infer_instance
instance sentLb_persistent (γ : DirNames) (W : List w8) : Persistent (sentLb (Gg := Gg) γ W) := by
  unfold sentLb; letI := (G (Gg := Gg)).allG; infer_instance
instance rcvdAll_timeless (γ : DirNames) (R : List w8) : Timeless (rcvdAll (Gg := Gg) γ R) := by
  unfold rcvdAll; letI := (G (Gg := Gg)).allG; infer_instance

/-- The direction from the end `s` of `c`: its unread bytes, what its writer wrote and its reader
read, agreeing (`DirOk`). -/
def dirInv (c : Nat) (s : Bool) (γ : DirNames) : IProp GF :=
  iprop(∃ (d : TcpDir) (W R : List w8), tcpDir G c s d ∗
    @monoListAuthOwn GF (G (Gg := Gg)).allG _ _ γ.w (1 : Qp).half W ∗
    @ghostVar GF (G (Gg := Gg)).allG _ _ γ.r (1 : Qp).half R ∗ ⌜DirOk d W R⌝)

instance dirInv_timeless (c : Nat) (s : Bool) (γ : DirNames) :
    Timeless (dirInv (Gg := Gg) c s γ) := by
  unfold dirInv; letI := (G (Gg := Gg)).allG; infer_instance

theorem sentLb_get (γ : DirNames) (W : List w8) : sentAll (Gg := Gg) γ W ⊢ sentLb γ W := by
  unfold sentAll sentLb
  letI := (G (Gg := Gg)).allG
  exact monoListLbOwn_get γ.w _ W

theorem sentLb_le (γ : DirNames) {W : List w8} (W' : List w8) (h : W' <+: W) :
    sentLb (Gg := Gg) γ W ⊢ sentLb γ W' := by
  unfold sentLb
  letI := (G (Gg := Gg)).allG
  exact monoListLbOwn_le W' h

/-- What the writer has written includes every lower bound of it. -/
theorem sentLb_prefix (γ : DirNames) (W W0 : List w8) :
    sentAll (Gg := Gg) γ W -∗ sentLb γ W0 -∗ ⌜W0 <+: W⌝ := by
  unfold sentAll sentLb
  letI := (G (Gg := Gg)).allG
  iintro Ha Hl
  icases mono_list_auth_lb_valid γ.w _ W W0 $$ Ha Hl with %H
  ipureintro; exact H.2

theorem sentLb_valid (γ : DirNames) (W1 W2 : List w8) :
    sentLb (Gg := Gg) γ W1 -∗ sentLb γ W2 -∗ ⌜W1 <+: W2 ∨ W2 <+: W1⌝ := by
  unfold sentLb
  letI := (G (Gg := Gg)).allG
  iintro H1 H2
  iapply mono_list_lb_valid γ.w W1 W2 $$ H1 H2

/-- A new direction's protocol state, from its fresh resource: the invariant's body (to put in a
protocol's own invariant, as when a dialer's deposit must stay timeless) and the writer's and
reader's halves, nothing written or read. -/
theorem dirInv_body_alloc (c : Nat) (s : Bool) :
    tcpDir (G (Gg := Gg)) c s TcpDir.fresh ==∗ ∃ γ, dirInv c s γ ∗ sentAll γ [] ∗
      rcvdAll γ [] := by
  letI := (G (Gg := Gg)).allG
  iintro Hd
  imod mono_list_own_alloc (GF := GF) ([] : List w8) with ⟨%γw, Hw, -⟩
  icases (show monoListAuthOwn (GF := GF) γw 1 ([] : List w8) ⊣⊢
      iprop(monoListAuthOwn γw (1 : Qp).half [] ∗ monoListAuthOwn γw (1 : Qp).half []) by
    conv => lhs; rw [← Qp.half_add_half 1]
    exact (monoListAuthOwn_fractional γw []).fractional _ _).mp $$ Hw with ⟨Hw1, Hw2⟩
  imod ghostVar_alloc (GF := GF) ([] : List w8) with ⟨%γr, Hr⟩
  icases (ghostVar_split_half γr 1 ([] : List w8)).mp $$ Hr with ⟨Hr1, Hr2⟩
  imodintro
  iexists ⟨γw, γr⟩
  unfold dirInv sentAll rcvdAll
  isplitl [Hd Hw1 Hr1]
  · iexists TcpDir.fresh, [], []
    iframe Hd Hw1 Hr1
    ipureintro; exact dirOk_fresh
  iframe Hw2 Hr2

/-- A new direction's protocol, from its fresh resource: its invariant, nothing written or read. -/
theorem dirInv_alloc (N : Namespace) (E : CoPset) (c : Nat) (s : Bool) :
    tcpDir (G (Gg := Gg)) c s TcpDir.fresh ={E}=∗ ∃ γ, inv N (dirInv c s γ) ∗ sentAll γ [] ∗
      rcvdAll γ [] := by
  iintro Hd
  imod dirInv_body_alloc c s $$ Hd with ⟨%γ, Hb, Hw, Hr⟩
  imod inv_alloc N E (dirInv c s γ) $$ [Hb] with #Hinv
  · inext; iexact Hb
  imodintro
  iexists γ
  iframe Hinv Hw Hr

theorem sentAll_app (γ : DirNames) (W W' x : List w8) :
    @monoListAuthOwn GF (G (Gg := Gg)).allG _ _ γ.w (1 : Qp).half W -∗ sentAll γ W' ==∗
      ⌜W = W'⌝ ∗ @monoListAuthOwn GF (G (Gg := Gg)).allG _ _ γ.w (1 : Qp).half (W ++ x) ∗
        sentAll γ (W ++ x) := by
  unfold sentAll
  letI := (G (Gg := Gg)).allG
  iintro H1 H2
  icases monoListAuthOwn_agree γ.w _ _ W W' $$ H1 H2 with %Hag
  obtain ⟨-, rfl⟩ := Hag
  have hs : ∀ l : List w8, monoListAuthOwn (GF := GF) γ.w 1 l ⊣⊢
      iprop(monoListAuthOwn γ.w (1 : Qp).half l ∗ monoListAuthOwn γ.w (1 : Qp).half l) := by
    intro l
    conv => lhs; rw [← Qp.half_add_half 1]
    exact (monoListAuthOwn_fractional γ.w l).fractional _ _
  ihave H := (hs W).mpr $$ [H1 H2]
  · iframe H1 H2
  imod monoListAuthOwn_update_app x $$ H with ⟨H, -⟩
  icases (hs (W ++ x)).mp $$ H with ⟨H1, H2⟩
  imodintro
  iframe H1 H2
  ipureintro; rfl

/-! ## The atomic updates, for an end its thread owns -/

/-- A write at the end `s` of `c` (its state `st` the thread's) into the direction from it, whose
writer has written `W`: it has then written `W ++ bs.take k`. -/
theorem write_au (N : Namespace) (c : Nat) (s : Bool) (γ : DirNames) (st : TcpEnd) (W bs : List w8) :
    ⊢ inv N (dirInv (Gg := Gg) c s γ) -∗ tcpEnd G c s st -∗ sentAll γ W -∗
      |={⊤,∅}=> ∃ st0 d, tcpEnd G c s st0 ∗ tcpDir G c s d ∗
        ∀ k ok d', ⌜WriteOutcome st0 d bs k ok d'⌝ -∗ tcpEnd G c s st0 -∗ tcpDir G c s d'
          ={∅,⊤}=∗ tcpEnd G c s st ∗ sentAll γ (W ++ bs.take k) ∗
            ⌜∃ d d', WriteOutcome st d bs k ok d'⌝ := by
  iintro #Hinv Hend Hw
  iinv Hinv with Hi Hclose
  unfold dirInv
  icases Hi with ⟨%d, %W', %R, >Hd, >Hw', >Hr, >%Hok⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, d
  iframe Hend Hd
  iintro %k %ok %d' %Hwr Hend Hd
  imod Hmask
  imod sentAll_app γ W' W (bs.take k) $$ Hw' Hw with ⟨%Heq, Hw', Hw⟩
  subst Heq
  imod Hclose $$ [Hd Hw' Hr] with -
  · inext
    iexists d', W' ++ bs.take k, R
    iframe Hd Hw' Hr
    ipureintro; exact dirOk_write Hok Hwr
  imodintro
  iframe Hend Hw
  ipureintro; exact ⟨d, d', Hwr⟩

/-- A read at the end `s` of `c` (its state `st` the thread's) from the direction towards it,
whose reader has read `R`: it has then read `R ++ r.got`, which the writer has written. -/
theorem read_au (N : Namespace) (c : Nat) (s : Bool) (γ : DirNames) (st : TcpEnd) (R : List w8)
    (n : Nat) :
    ⊢ inv N (dirInv (Gg := Gg) c (!s) γ) -∗ tcpEnd G c s st -∗ rcvdAll γ R -∗
      |={⊤,∅}=> ∃ st0 d, tcpEnd G c s st0 ∗ tcpDir G c (!s) d ∗
        ∀ r d', ⌜ReadOutcome st0 d n r d' ∧ r ≠ .wait⌝ -∗ tcpEnd G c s st0 -∗ tcpDir G c (!s) d'
          ={∅,⊤}=∗ tcpEnd G c s st ∗ rcvdAll γ (R ++ r.got) ∗ sentLb γ (R ++ r.got) ∗
            ⌜∃ d d', ReadOutcome st d n r d' ∧ r ≠ .wait⌝ := by
  iintro #Hinv Hend Hr
  iinv Hinv with Hi Hclose
  unfold dirInv
  icases Hi with ⟨%d, %W, %R', >Hd, >Hw, >Hr', >%Hok⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, d
  iframe Hend Hd
  iintro %r %d' %Hrd Hend Hd
  imod Hmask
  unfold rcvdAll
  letI := (G (Gg := Gg)).allG
  icases ghostVar_agree $$ Hr' Hr with %Heq
  subst Heq
  imod ghostVar_update_halves (R' ++ r.got) $$ Hr' Hr with ⟨Hr', Hr⟩
  have Hok' := dirOk_read Hok Hrd.1
  ihave #Hlb : (sentLb (Gg := Gg) γ (R' ++ r.got) : IProp GF) $$ [Hw]
  · unfold sentLb
    iapply monoListLbOwn_le _ (dirOk_prefix Hok')
    iapply monoListLbOwn_get
    iexact Hw
  imod Hclose $$ [Hd Hw Hr'] with -
  · inext
    iexists d', W, R' ++ r.got
    iframe Hd Hw Hr'
    ipureintro; exact Hok'
  imodintro
  iframe Hend Hr Hlb
  ipureintro; exact ⟨d, d', Hrd⟩

/-- The reader's predicate of `wire.ReadFull` for an end its thread owns: its state, and the bytes
`got` this call has read after the `R0` read before, all of which the writer has written. -/
def readP (γ : DirNames) (c : Nat) (s : Bool) (st : TcpEnd) (R0 got : List w8) : IProp GF :=
  iprop(tcpEnd G c s st ∗ rcvdAll (Gg := Gg) γ (R0 ++ got) ∗ sentLb γ (R0 ++ got))

/-- The accessor `wire.ReadFull`'s spec takes, for `readP`. -/
theorem read_acc (N : Namespace) (c : Nat) (s : Bool) (γ : DirNames) (st : TcpEnd) (R0 : List w8) :
    inv N (dirInv (Gg := Gg) c (!s) γ) ⊢
      □ (∀ (got : List w8) (m : Nat), readP γ c s st R0 got -∗
        |={⊤,∅}=> ∃ st0 d, tcpEnd G c s st0 ∗ tcpDir G c (!s) d ∗
          ∀ r d', ⌜ReadOutcome st0 d m r d' ∧ r ≠ .wait⌝ -∗ tcpEnd G c s st0 -∗
            tcpDir G c (!s) d' ={∅,⊤}=∗ readP γ c s st R0 (got ++ r.got)) := by
  iintro #Hinv
  imodintro
  iintro %got %m HP
  unfold readP
  icases HP with ⟨Hend, Hr, -⟩
  imod read_au N c s γ st (R0 ++ got) m $$ Hinv Hend Hr with ⟨%st0, %d, Hend, Hd, Hk⟩
  imodintro
  iexists st0, d
  iframe Hend Hd
  iintro %r %d' %Hrd Hend Hd
  imod Hk $$ %r %d' %Hrd Hend Hd with ⟨Hend, Hr, #Hlb, -⟩
  imodintro
  rw [List.append_assoc]
  iframe Hend Hr Hlb

/-- A close of the end `s` of `c` (its state `st` the thread's): the direction from it is shut
(`CloseOutcome`). -/
theorem close_au (N : Namespace) (c : Nat) (s : Bool) (γ : DirNames) (st : TcpEnd) :
    ⊢ inv N (dirInv (Gg := Gg) c s γ) -∗ tcpEnd G c s st -∗
      |={⊤,∅}=> ∃ st0 d, tcpEnd G c s st0 ∗ tcpDir G c s d ∗
        ∀ ok st' d', ⌜CloseOutcome st0 d ok st' d'⌝ -∗ tcpEnd G c s st' -∗ tcpDir G c s d'
          ={∅,⊤}=∗ tcpEnd G c s st' ∗ ⌜∃ d d', CloseOutcome st d ok st' d'⌝ := by
  iintro #Hinv Hend
  iinv Hinv with Hi Hclose
  unfold dirInv
  icases Hi with ⟨%d, %W, %R, >Hd, >Hw, >Hr, >%Hok⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, d
  iframe Hend Hd
  iintro %ok %st' %d' %Hc Hend Hd
  imod Hmask
  imod Hclose $$ [Hd Hw Hr] with -
  · inext
    iexists d', W, R
    iframe Hd Hw Hr
    ipureintro; exact dirOk_close Hok Hc
  imodintro
  iframe Hend
  ipureintro; exact ⟨d, d', Hc⟩

/-- A `CloseWrite` of the end `s` of `c` (its state `st` the thread's): the direction from it is
shut (`CloseWriteOutcome`). -/
theorem closeWrite_au (N : Namespace) (c : Nat) (s : Bool) (γ : DirNames) (st : TcpEnd) :
    ⊢ inv N (dirInv (Gg := Gg) c s γ) -∗ tcpEnd G c s st -∗
      |={⊤,∅}=> ∃ st0 d, tcpEnd G c s st0 ∗ tcpDir G c s d ∗
        ∀ ok d', ⌜CloseWriteOutcome st0 d ok d'⌝ -∗ tcpEnd G c s st0 -∗ tcpDir G c s d'
          ={∅,⊤}=∗ tcpEnd G c s st ∗ ⌜∃ d d', CloseWriteOutcome st d ok d'⌝ := by
  iintro #Hinv Hend
  iinv Hinv with Hi Hclose
  unfold dirInv
  icases Hi with ⟨%d, %W, %R, >Hd, >Hw, >Hr, >%Hok⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, d
  iframe Hend Hd
  iintro %ok %d' %Hc Hend Hd
  imod Hmask
  imod Hclose $$ [Hd Hw Hr] with -
  · inext
    iexists d', W, R
    iframe Hd Hw Hr
    ipureintro; exact dirOk_closeWrite Hok Hc
  imodintro
  iframe Hend
  ipureintro; exact ⟨d, d', Hc⟩

/-- `close_au` for a caller that keeps nothing of the close (`Conn.Close.spec` with `Q := True`). -/
theorem close_drop_au (N : Namespace) (c : Nat) (s : Bool) (γ : DirNames) (st : TcpEnd) :
    ⊢ inv N (dirInv (Gg := Gg) c s γ) -∗ tcpEnd G c s st -∗
      |={⊤,∅}=> ∃ st0 d, tcpEnd G c s st0 ∗ tcpDir G c s d ∗
        ∀ ok st' d', ⌜CloseOutcome st0 d ok st' d'⌝ -∗ tcpEnd G c s st' -∗ tcpDir G c s d'
          ={∅,⊤}=∗ (True : IProp GF) := by
  iintro #Hinv Hend
  imod close_au N c s γ st $$ Hinv Hend with ⟨%st0, %d, Hend, Hdir, Hk⟩
  imodintro
  iexists st0, d
  iframe Hend Hdir
  iintro %ok %st' %d' %Hc Hend Hdir
  imod Hk $$ %ok %st' %d' %Hc Hend Hdir with -
  imodintro
  itrivial

end ghost

end github_com.mit_pdos.etcd_grove.examples.net.wire
end Perennial
