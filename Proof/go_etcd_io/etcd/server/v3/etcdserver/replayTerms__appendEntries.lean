/- Prefixes retained by appendEntries are shared with previously delivered Ready batches. -/
module
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.raft.v3.Protocol.Ghost

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The update to the output of the outer loop. An equal term extends the
last run while retaining the first index at which that term occurred. -/
def replayJoin (runs : List replayTermRun) (r : replayTermRun) : List replayTermRun :=
  match runs.getLast? with
  | some old =>
    if old.term' = r.term' then runs.dropLast ++ [{ r with first' := old.first' }]
    else runs ++ [r]
  | none => [r]

theorem replayJoin_snoc (pre : List replayTermRun) (a b : replayTermRun) :
    replayJoin (pre ++ [a]) b =
      if a.term' = b.term' then pre ++ [{ b with first' := a.first' }] else (pre ++ [a]) ++ [b] := by
  simp [replayJoin, List.getLast?_append]

theorem replayJoin_same (pre : List replayTermRun) (a b : replayTermRun) (h : a.term' = b.term') :
    replayJoin (replayJoin pre a) b = replayJoin pre { b with first' := a.first' } := by
  by_cases he : pre = []
  · subst pre
    change replayJoin ([] ++ [a]) b = _
    simp [replayJoin_snoc, replayJoin, h]
  · obtain ⟨xs, last, rfl⟩ : ∃ xs last, pre = xs ++ [last] :=
      ⟨pre.dropLast, pre.getLast he, (List.dropLast_concat_getLast he).symm⟩
    by_cases hm : last.term' = a.term'
    · simp [replayJoin_snoc, hm, h, hm.trans h]
    · have hm' : last.term' ≠ b.term' := fun e => hm (e.trans h.symm)
      simp [replayJoin_snoc, hm, hm', h]
      rw [show xs ++ [last, a] = (xs ++ [last]) ++ [a] by simp, replayJoin_snoc]
      simp [h]

def replayAddEntry (runs : List replayTermRun) (e : EntryModel) : List replayTermRun :=
  replayJoin runs ⟨e.index, e.index, e.term⟩

/-- Emitting an entire equal-term group gives the same output as feeding the
physical entries one at a time, including when the previous batch ends in that term. -/
theorem replayFold_same (es : List EntryModel) (pre : List replayTermRun) (r : replayTermRun)
    (hall : ∀ e ∈ es, e.term = r.term') :
    es.foldl replayAddEntry (replayJoin pre r) =
      replayJoin pre { r with last' := (es.getLast?.map EntryModel.index).getD r.last' } := by
  induction es generalizing r with
  | nil => simp
  | cons e xs ih =>
    have he := hall e (by simp)
    let next := replayTermRun.mk r.first' e.index r.term'
    have hmerge : replayAddEntry (replayJoin pre r) e = replayJoin pre next := by
      unfold replayAddEntry
      rw [replayJoin_same pre r _ he.symm]
      simp only [next, he]
    rw [List.foldl_cons, hmerge, ih next (fun x hx => hall x (List.mem_cons_of_mem _ hx))]
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp [next, List.getLast?_cons_cons, List.getLast?_eq_some_getLast (List.cons_ne_nil x xs)]

/-- Removing a processed prefix from the entries and adding its single run gives
the same remaining fold as the whole batch. -/
theorem replayFold_group (pre : List replayTermRun) (e : EntryModel) (es : List EntryModel)
    (c : Nat) (hc : 0 < c) (hb : c ≤ (e :: es).length)
    (ht : ∀ (i : Nat) (hi : i < (e :: es).length), i < c → (e :: es)[i].term = e.term) :
    ((e :: es).drop c).foldl replayAddEntry
        (replayJoin pre ⟨e.index, (e :: es)[c - 1].index, e.term⟩) =
      (e :: es).foldl replayAddEntry pre := by
  suffices hpre : ((e :: es).take c).foldl replayAddEntry pre =
      replayJoin pre ⟨e.index, (e :: es)[c - 1].index, e.term⟩ by
    rw [← hpre, ← List.foldl_append, List.take_append_drop]
  cases c with
  | zero => omega
  | succ k =>
    have hk : k < (e :: es).length := by omega
    have hlast : ((e :: es).take (k + 1)).getLast? = some (e :: es)[k] := by
      rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left hb]
      simp only [Nat.add_sub_cancel, List.getElem?_take, Nat.lt_succ_self, ↓reduceIte]
      exact List.getElem?_eq_getElem hk
    rw [List.take_succ_cons] at hlast ⊢
    have hall : ∀ x ∈ es.take k, x.term = e.term := by
      intro x hx
      obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hx
      have hjes : j < es.length := by simp only [List.length_take] at hj; omega
      have hjk : j < k := by simp only [List.length_take] at hj; omega
      have hterm := ht (j + 1) (by simp; omega) (by omega)
      simpa only [List.getElem_cons_succ, ← hget, List.getElem_take] using hterm
    rw [List.foldl_cons, replayAddEntry, replayFold_same _ _ _ hall]
    cases tail : es.take k with
    | nil =>
      rw [tail] at hlast
      simpa using congrArg (fun z : Option EntryModel => (z.map EntryModel.index).getD e.index) hlast
        |> fun h => congrArg (fun i => replayJoin pre ⟨e.index, i, e.term⟩) h
    | cons x xs =>
      rw [tail, List.getLast?_cons_cons] at hlast
      simp [hlast]

/-- The third index in `r[:n:n]` gives the writer a prefix with no writable slack.
The old Ready can continue reading every run, including the discarded suffix. -/
theorem replayTerms_prefix (r : GoSlice) (runs : List replayTermRun) (n : w64)
    (hn : 0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z r.len) :
    let out := slice.fullSlice r replayTermRun (W64 0) n n
    (r ↦*□ runs : IProp GF) ⊢ out ↦*□ runs.take (sint.nat n) ∗
      ownSliceCap replayTermRun out (DFrac.own 1) := by
  dsimp only
  iintro #Hr
  isplitr
  · icases (ownSlice_slice n n r DFrac.discard runs ⟨hn.1, Int.le_refl _, hn.2⟩).1 $$ Hr with ⟨Hpre, -, -⟩
    rw [ownSlice_unseal]; unfold ownSliceDef
    icases Hpre with (%Hnil | ⟨Harr, -⟩)
    · ileft; ipureintro
      obtain ⟨hp, hlen, _⟩ := (slice_mk_eq_nil ..).mp Hnil.1
      exact ⟨(slice_mk_eq_nil ..).mpr ⟨hp, hlen, hlen⟩, Hnil.2⟩
    · iright; isplitl [Harr]
      · iExactEq Harr; rfl
      · ipureintro; exact Int.le_refl _
  · iapply ownSliceCap_empty _ rfl (by dsimp [slice.fullSlice]; word)

/-- The backwards scan at the start of `appendEntries`, after its three
closures have captured the receiver, count, and incoming first index. -/
def replayTrimLoop [GooseExts] [GoGlobalContext] (rp np fp : Loc) : Expr :=
  let n := App (Val (GoInstruction (GoLoad go.int))) (Val #np)
  let prev := App (Val (GoInstruction (GoOp GoSub go.int))) (Pair n (Val #(W64 1)))
  let r := App (Val (GoInstruction (GoLoad replayTerms.ty))) (Val #rp)
  let elem := App (Val (GoInstruction (IndexRef replayTerms.ty))) (Pair r prev)
  let last := App (Val (GoInstruction (GoLoad go.uint64)))
    (App (Val (GoInstruction (StructFieldRef replayTermRun.ty go!"last"))) elem)
  let first := App (Val (GoInstruction (GoLoad go.uint64))) (Val #fp)
  let test := If (App (Val (GoInstruction (GoOp GoGt go.int))) (Pair n (Val #(W64 0))))
    (App (Val (GoInstruction (GoOp GoGe go.uint64))) (Pair last first)) (Val #false)
  let body := App (Val doExecute) (App (Val (GoInstruction (GoStore go.int))) (Pair (Val #np) prev))
  App (App (App (Val doFor) (Val (LamV BAnon test))) (Val (LamV BAnon body)))
    (Val (LamV BAnon (Val #())))

/-- Exactly the discarded suffix has been scanned. Its runs all end at or
above the replacement index, and the last kept run ends strictly before it. -/
theorem replayTrimLoop_wp (rp np fp : Loc) (r : GoSlice) (first : w64)
    (runs : List replayTermRun) (Φ : val → IProp GF) :
    rp ↦ r ∗ np ↦ r.len ∗ fp ↦ first ∗ r ↦*□ runs ∗
      (∀ n : w64, rp ↦ r -∗ np ↦ n -∗ fp ↦ first -∗
        ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ runs.length ∧
          (∀ (i : Nat) (x : replayTermRun), sint.nat n ≤ i → runs[i]? = some x →
            uint.nat first ≤ uint.nat x.last') ∧
          (sint.nat n = 0 ∨ ∃ x, runs[sint.nat n - 1]? = some x ∧ uint.nat x.last' < uint.nat first)⌝ -∗
        Φ executeVal) ⊢ WP (replayTrimLoop rp np fp) {{ Φ }} := by
  iintro ⟨Hr, Hn, Hf, #Hsl, HΦ⟩
  ihave %hlen := ownSlice_len r _ runs $$ Hsl
  unfold replayTrimLoop
  ihave HI : (∃ n : w64, "Hn" ∷ np ↦ n ∗
      "%hi" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ runs.length ∧
        ∀ (i : Nat) (x : replayTermRun), sint.nat n ≤ i → runs[i]? = some x →
          uint.nat first ≤ uint.nat x.last'⌝ : IProp GF) $$ [Hn]
  · iexists r.len; iframe Hn
    ipureintro
    refine ⟨hlen.2, by omega, ?_⟩
    intro i x hb hx
    have := (List.getElem?_eq_some_iff.mp hx).1
    omega
  wp_for HI
  obtain ⟨hn0, hn, hcut⟩ := hi
  have cz : sint.Z (W64 0) = 0 := by decide
  by_cases hnz : 0 < sint.Z n
  · have hb : 0 ≤ sint.Z (n - W64 1) ∧ sint.Z (n - W64 1) < sint.Z r.len := by
      constructor <;> word
    have hprev : sint.nat (n - W64 1) = sint.nat n - 1 := by word
    have hprevlt : sint.nat (n - W64 1) < runs.length := by word
    let x := runs[sint.nat (n - W64 1)]
    have hx : runs[sint.nat (n - W64 1)]? = some x := List.getElem?_eq_getElem hprevlt
    icases ownSlice_elem_acc (sint.Z (n - W64 1)) x r DFrac.discard runs hb.1 hx $$ Hsl with ⟨#Hx, -⟩
    iStructNamed Hx
    (try wp_auto)
    simp only [cz, hnz, _root_.decide_true, ↓reduceIte]
    (try wp_auto)
    (try simp only [hb, ↓reduceIte])
    (try wp_auto)
    by_cases h : uint.Z first ≤ uint.Z x.last'
    · simp only [h, _root_.decide_true, ↓reduceIte]
      (try wp_auto)
      wp_for_post
      iframe
      iexists n - W64 1; iframe
      ipureintro
      refine ⟨hb.1, by omega, ?_⟩
      intro i y hi hy
      by_cases he : i = sint.nat (n - W64 1)
      · rw [he, hx] at hy; cases hy; word
      · exact hcut i y (by omega) hy
    · simp only [h, decide_false, ↓reduceIte]
      (try wp_auto)
      simp only [intoVal_eq_iff, Bool.false_eq_true, decide_false, _root_.decide_true, ↓reduceIte]
      iapply HΦ $$ %n Hr Hn Hf
      ipureintro
      exact ⟨hn0, hn, hcut, Or.inr ⟨x, by simpa only [hprev] using hx, by word⟩⟩
  · (try wp_auto)
    simp only [cz, hnz, decide_false, ↓reduceIte]
    (try wp_auto)
    simp only [intoVal_eq_iff, Bool.false_eq_true, decide_false, _root_.decide_true, ↓reduceIte]
    iapply HΦ $$ %n Hr Hn Hf
    ipureintro; exact ⟨hn0, hn, hcut, Or.inl (by word)⟩

/-- A recorded Raft entry carries the bound on its predecessor term, including the first
bootstrap entry whose predecessor has term zero. -/
theorem replayRecord_prev_le (γ : RaftNames) (e : EntryM) (prev : w64) :
    isEntryR (GF := GF) γ e prev ⊢ ⌜uint.Z prev ≤ uint.Z e.Term'⌝ := by
  iunfold isEntryR
  iintro (⟨%ldr, %γt, %b, %l0, %F0, -, -, -, -, %h, -, -, -⟩ | ⟨%boot, -⟩)
  · ipureintro; exact h.2.1
  · ipureintro
    obtain ⟨_, _, ht, hp⟩ := boot
    rw [hp, ht]; split <;> decide

/-- Two indexed entries of a recorded full log have nondecreasing terms. -/
theorem replayLog_term_le (γ : RaftNames) (es : List EntryM) (i j : Nat)
    (hi : i < es.length) (hj : j < es.length) (hij : i ≤ j) (bound : es.length < 2 ^ 64) :
    logRecs (GF := GF) γ base0 es ⊢ ⌜uint.Z es[i].Term' ≤ uint.Z es[j].Term'⌝ := by
  induction j with
  | zero =>
    have h : i = 0 := by omega
    subst i; iintro _; ipureintro; exact Int.le_refl _
  | succ j ih =>
    by_cases h : i = j + 1
    · subst i; iintro _; ipureintro; exact Int.le_refl _
    have hj' : j < es.length := by omega
    iintro #Hr
    ihave %lower := ih hj' (by omega) $$ Hr
    icases logRecs_lookup γ es (j + 1) es[j + 1] (List.getElem?_eq_getElem hj) (by omega) $$ Hr
      with ⟨%prev, %hprev, #Hentry⟩
    have hread := plogTermAt_lookup base0 es (W64 ((j + 1 : Nat) : Int)) j es[j]
      (List.getElem?_eq_getElem hj') (by rw [base0_index, uint_Z_W64 _ (by omega) (by omega)]; omega)
    rw [hread] at hprev
    cases hprev
    ihave %next := replayRecord_prev_le γ _ _ $$ Hentry
    ipureintro; exact Int.le_trans lower next

/-- Ready and WAL batches that are sublists of the recorded log inherit its term ordering. -/
theorem replayBatch_ordered (γ : RaftNames) (full : List EntryM) (es : List EntryModel)
    (sub : (es.map EntryModel.toM).Sublist full) (bound : full.length < 2 ^ 64) :
    logRecs (GF := GF) γ base0 full ⊢ ⌜es.Pairwise (fun a b => uint.nat a.term ≤ uint.nat b.term)⌝ := by
  have order : logRecs (GF := GF) γ base0 full ⊢
      ⌜full.Pairwise (fun a b => uint.nat a.Term' ≤ uint.nat b.Term')⌝ := by
    rw [List.pairwise_iff_getElem]
    refine (BI.forall_intro fun i => ?_).trans BI.pure_forall.2
    refine (BI.forall_intro fun j => ?_).trans BI.pure_forall.2
    refine (BI.forall_intro fun hi => ?_).trans BI.pure_forall.2
    refine (BI.forall_intro fun hj => ?_).trans BI.pure_forall.2
    refine (BI.forall_intro fun hij => ?_).trans BI.pure_forall.2
    iintro #Hr
    ihave %hle := replayLog_term_le γ full i j hi hj (by omega) bound $$ Hr
    ipureintro; word
  iintro #Hr
  ihave %ordered := order $$ Hr
  ipureintro
  have hbatch := ordered.sublist sub
  exact (List.pairwise_map (f := EntryModel.toM) (R := fun a b => uint.nat a.Term' ≤ uint.nat b.Term')).mp hbatch

/-- The equal-endpoints shortcut in `appendEntries` represents every entry in this batch
by one run when the log terms are nondecreasing. -/
theorem replayBatch_sameTerm (es : List EntryModel) (nonempty : 0 < es.length)
    (ordered : es.Pairwise (fun a b => uint.nat a.term ≤ uint.nat b.term))
    (ends : es[es.length - 1].term = es[0].term) (i : Nat) (hi : i < es.length) :
    es[i].term = es[0].term := by
  have leAt (a b : Nat) (ha : a < es.length) (hb : b < es.length) (hle : a ≤ b) :
      uint.nat es[a].term ≤ uint.nat es[b].term := by
    by_cases h : a = b
    · subst b; exact Nat.le_refl _
    · exact ordered.rel_getElem_of_lt ha hb (by omega)
  have hlo := leAt 0 i nonempty hi (Nat.zero_le _)
  have hhi := leAt i (es.length - 1) hi (by omega) (by omega)
  rw [ends] at hhi
  exact uint_nat_inj _ _ (Nat.le_antisymm hhi hlo)

/-- In the mixed-term branch the last entry is a sentinel. As long as the entries already
examined have the first term, the next indexed read is in bounds. -/
theorem replayBatch_scan_lt (es : List EntryModel) (nonempty : 0 < es.length)
    (term : w64) (different : es[es.length - 1].term ≠ term) (count : Nat)
    (scanned : ∀ (i : Nat) (hi : i < es.length), i < count → es[i].term = term) :
    count < es.length := by
  by_cases h : count < es.length
  · exact h
  exact False.elim (different (scanned (es.length - 1) (by omega) (by omega)))

/-- The mixed-term branch advances count to the first entry of the next term. -/
def replayCountLoop [GooseExts] [GoGlobalContext] (ep cp tp : Loc) : Expr :=
  let entryPtr := go.GoType.PointerType go_etcd_io.raft.v3.raftpb.Entry.ty
  let sliceTy := go.GoType.SliceType entryPtr
  let count := App (Val (GoInstruction (GoLoad go.int))) (Val #cp)
  let ents := App (Val (GoInstruction (GoLoad sliceTy))) (Val #ep)
  let slot := App (Val (GoInstruction (IndexRef sliceTy))) (Pair ents count)
  let ent := App (Val (GoInstruction (GoLoad entryPtr))) slot
  let getTerm := App (App (Val (GoInstruction (MethodResolve entryPtr go!"GetTerm"))) ent) (Val #())
  let t := App (Val (GoInstruction (GoLoad go.uint64))) (Val #tp)
  let test := App (Val (GoInstruction (GoOp GoEquals go.uint64))) (Pair getTerm t)
  let next := App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair count (Val #(W64 1)))
  let body := App (Val doExecute) (App (Val (GoInstruction (GoStore go.int))) (Pair (Val #cp) next))
  App (App (App (Val doFor) (Val (LamV BAnon test))) (Val (LamV BAnon body)))
    (Val (LamV BAnon (Val #())))

theorem replayCountLoop_wp (ep cp tp : Loc) (ents : GoSlice) (ls : List Loc) (es : List EntryModel)
    (hne : 0 < es.length) (t : w64) (hfirst : es[0].term = t)
    (hlast : es[es.length - 1].term ≠ t) (getTerm : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG))
    (Φ : val → IProp GF) :
    ep ↦ ents ∗ cp ↦ W64 1 ∗ tp ↦ t ∗ ents ↦*□ ls ∗ entriesAt ls es ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗
      (∀ c : w64, ep ↦ ents -∗ cp ↦ c -∗ tp ↦ t -∗
        ⌜0 < sint.Z c ∧ ∃ h : sint.nat c < es.length, es[sint.nat c].term ≠ t ∧
          ∀ (i : Nat) (hi : i < es.length), i < sint.nat c → es[i].term = t⌝ -∗
        Φ executeVal) ⊢ WP (replayCountLoop ep cp tp) {{ Φ }} := by
  iintro ⟨He, Hc, Ht, #Hsl, #Hents, #Hpb, HΦ⟩
  iunfold entriesAt at Hents
  icases Hents with ⟨%hlen, #Hat⟩
  ihave %hl := ownSlice_len ents _ ls $$ Hsl
  unfold replayCountLoop
  ihave HI : (∃ c : w64, "Hc" ∷ cp ↦ c ∗ "%hc" ∷ ⌜0 < sint.Z c ∧
      ∀ (i : Nat) (hi : i < es.length), i < sint.nat c → es[i].term = t⌝ : IProp GF) $$ [Hc]
  · iexists W64 1; iframe Hc; ipureintro
    refine ⟨by decide, ?_⟩
    intro i hi h
    have hi0 : i = 0 := by word
    subst i; exact hfirst
  wp_for HI
  have hb := replayBatch_scan_lt es hne t hlast (sint.nat c) hc.2
  have hls : sint.nat c < ls.length := by omega
  let ptr := ls[sint.nat c]
  let ent := es[sint.nat c]
  have hptr : ls[sint.nat c]? = some ptr := List.getElem?_eq_getElem hls
  have hent : es[sint.nat c]? = some ent := List.getElem?_eq_getElem hb
  ihave #Hent := Hat $$ %(sint.nat c) %ptr %ent %hptr %hent
  icases ownSlice_elem_acc (sint.Z c) ptr ents DFrac.discard ls (by omega) hptr $$ Hsl with ⟨#Hp, -⟩
  have hs : sint.nat c < sint.nat ents.len := hl.1 ▸ hls
  have hbound : 0 ≤ sint.Z c ∧ sint.Z c < sint.Z ents.len := by
    change (sint.Z c).toNat < (sint.Z ents.len).toNat at hs
    omega
  (try wp_auto)
  (try simp only [hbound, ↓reduceIte])
  (try wp_auto)
  wp_apply wp_entryAt_GetTerm getTerm ptr ent $$ [$Hpb $Hent]
  (try wp_auto)
  by_cases heq : ent.term = t
  · simp only [heq, _root_.decide_true, ↓reduceIte]
    (try wp_auto)
    wp_for_post
    iframe
    iexists c + W64 1; iframe
    ipureintro; refine ⟨by word, ?_⟩
    intro i hi hi'
    by_cases h : i = sint.nat c
    · subst i; exact heq
    · exact hc.2 i hi (by word)
  · simp only [heq, decide_false, ↓reduceIte]
    (try wp_auto)
    (try simp only [intoVal_eq_iff, Bool.false_eq_true, decide_false, _root_.decide_true, ↓reduceIte])
    iapply HΦ $$ %c He Hc Ht
    ipureintro; exact ⟨hc.1, hb, heq, hc.2⟩

/-- A Ready with no new entries returns exactly the existing slice, for any receiver. -/
theorem replayTerms.appendEntries_empty (r ents : GoSlice) (hempty : ents.len = W64 0) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver }}
      (App (Val (r @!! replayTerms.ty @!! go!"appendEntries")) (Val #ents))
    {{ RET #r; True }} := by
  wp_start
  (try wp_auto)
  simp only [hempty, decide_true]
  (try wp_auto)
  iapply HΦ; itrivial

attribute [local instance] pure_test_execute

/-- Bootstrap builds from a nil receiver. When the first and last entries share a term,
the translated method emits one run with exactly those two indices. -/
theorem replayTerms.appendEntries_oneRun (ents : GoSlice) (ls : List Loc) (nonempty : 0 < ls.length)
    (first last : EntryModel) (same : last.term = first.term)
    (getIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (getTerm : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
       ents ↦*□ ls ∗ entryAt ls[0] first ∗ entryAt ls[ls.length - 1] last }}
      (App (Val (slice.nil @!! replayTerms.ty @!! go!"appendEntries")) (Val #ents))
    {{ (out : GoSlice), RET #out; out ↦*□ [replayTermRun.mk first.index last.index first.term] }} := by
  wp_start as ⟨#Hents, #Hfirst, #Hlast⟩
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave %hlen := ownSlice_len ents _ ls $$ Hents
  have hpos : 0 < sint.Z ents.len := by word
  have hne : ents.len ≠ W64 0 := by word
  have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z ents.len := ⟨by decide, hpos⟩
  have hend : 0 ≤ sint.Z (ents.len - W64 1) ∧ sint.Z (ents.len - W64 1) < sint.Z ents.len := by word
  have hlastIndex : (sint.Z (ents.len - W64 1)).toNat = ls.length - 1 := by word
  icases ownSlice_elem_acc (sint.Z (W64 0)) ls[0] ents DFrac.discard ls (by decide)
    (List.getElem?_eq_getElem nonempty) $$ Hents with ⟨#Hef, -⟩
  icases ownSlice_elem_acc (sint.Z (ents.len - W64 1)) ls[ls.length - 1] ents DFrac.discard ls hend.1
    (by rw [hlastIndex]; exact List.getElem?_eq_getElem (by omega)) $$ Hents with ⟨#Hel, -⟩
  (try wp_auto)
  simp only [hne, decide_false]
  (try wp_auto)
  simp only [hb]
  (try wp_auto)
  wp_apply wp_entryAt_GetIndex getIndex _ first $$ [$Hpb $Hfirst]
  (try wp_auto)
  wp_for
  rw [doFor_unseal]
  unfold doForDef
  (try wp_auto)
  simp only [hb.2, _root_.decide_true]
  (try wp_auto)
  simp only [hb]
  (try wp_auto)
  wp_apply wp_entryAt_GetTerm getTerm _ first $$ [$Hpb $Hfirst]
  simp only [hend]
  (try wp_auto)
  wp_apply wp_entryAt_GetTerm getTerm _ last $$ [$Hpb $Hlast]
  simp only [same]
  simp only [_root_.decide_true]
  (try wp_auto)
  (try simp only [hb])
  (try wp_auto)
  wp_apply wp_entryAt_GetIndex getIndex _ first $$ [$Hpb $Hfirst]
  (try simp only [hend])
  (try wp_auto)
  wp_apply wp_entryAt_GetIndex getIndex _ last $$ [$Hpb $Hlast]
  (try wp_auto)
  wp_apply wp_slice_literal (V := replayTermRun) [replayTermRun.mk first.index last.index first.term]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  (try wp_auto)
  have hnil : slice.fullSlice slice.nil replayTermRun (W64 0) 0 0 = slice.nil :=
    (slice_slice_trivial (V := replayTermRun) slice.nil).symm
  rw [hnil]
  ihave #Hnil := ownSlice_nil (GF := GF) (V := replayTermRun) DFrac.discard
  ihave Hcap := ownSliceCap_nil (GF := GF) (V := replayTermRun)
  wp_apply wp_slice_append_persistent (V := replayTermRun) slice.nil [] _ _ (DFrac.own 1) $$ [$Hnil $Hcap $Hsl]
    as %result ⟨#Hresult, -, -⟩
  (try wp_auto)
  ihave %hwf := ownSlice_wf ents _ ls $$ Hents
  have hb' : 0 ≤ sint.Z ents.len ∧ sint.Z ents.len ≤ sint.Z ents.len ∧ sint.Z ents.len ≤ sint.Z ents.cap :=
    ⟨hlen.2, Int.le_refl _, hwf.2⟩
  (try simp only [hb'])
  (try wp_auto)
  wp_pures
  (try wp_auto)
  (try simp only [slice.slice])
  (try wp_auto)
  simp only [show ¬sint.Z (W64 0) < sint.Z (ents.len - ents.len) by word, decide_false]
  (try wp_auto)
  iapply HΦ
  simp only [List.nil_append]
  iexact Hresult

end EtcdGrove
end Perennial
