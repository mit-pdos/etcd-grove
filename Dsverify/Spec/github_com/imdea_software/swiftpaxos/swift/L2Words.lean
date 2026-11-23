/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swift/L2Words.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
L2 (notes/l2-design.md §5, notes/prove-s2-e.md): a node's predicted events (`PEv`,
Spec/swift/Model/Trace.lean) as the words its ghost resolves (the fork's client/ghost.go:
`Invoke`, `Accept`, `Step`), and their decoding. The encoding is prefix-free for well-formed
events (`encP_inj`), so a node's future words decode to its predicted events, and resolving one
event's words leaves the decoding of the rest (`decodeP_enc`).

Words: the first is the event's kind; a client's invocation's kind is its command's op (1 put,
2 get), its acceptance's 3, a replica's events 4 .. 11. Naturals are one word (below `2 ^ 64`),
a client id or sequence number one word (`uint64(uint32(.))`), a byte one word, a list its
length then its elements.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.Trace

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

/-! ## Words -/

/-- `uint64(b)` of a byte, `uint64(uint32(n))` of an `int32`. -/
def w8w (b : w8) : w64 := W64 b.toNat
def w32w (n : w32) : w64 := W64 n.toNat

/-- `resolveBytes`: the length, then each byte. -/
def wordsOf (bs : List w8) : List w64 := W64 bs.length :: bs.map w8w

/-- A natural as a word. -/
def natW (n : Nat) : w64 := W64 n

/-- A list: its length, then each element's words. -/
def listW {α : Type} (f : α → List w64) (l : List α) : List w64 :=
  W64 l.length :: l.flatMap f

/-- A command id: its client, its sequence number. -/
def idW (x : CmdId) : List w64 := [w32w x.cl, w32w x.seq]

/-- A command: its op, its key, its value's bytes. -/
def cmdW (c : Cmd) : List w64 := w8w c.op :: c.key :: wordsOf c.val

/-- A report's entry: its id, phase, command, dependencies. -/
def repEntryW (e : RepEntry) : List w64 := idW e.id ++ e.phase :: cmdW e.cmd ++ listW idW e.dep

/-- **A predicted event's words.** -/
def encP : PEv → List w64
  | .inv x c => w8w c.op :: idW x ++ c.key :: wordsOf c.val
  | .resp x v => W64 3 :: idW x ++ wordsOf v
  | .handle b x c => W64 4 :: natW b :: idW x ++ cmdW c
  | .preaccept b y D => W64 5 :: natW b :: idW y ++ listW idW D
  | .accept b y => W64 6 :: natW b :: idW y
  | .commit b y => W64 7 :: natW b :: idW y
  | .newBallot b' => [W64 8, natW b']
  | .report b' R => W64 9 :: natW b' :: natW R.cbal :: listW repEntryW R.entries
  | .computeSync b' ids => W64 10 :: natW b' :: listW (fun r => [natW r]) ids
  | .takeSync b' => [W64 11, natW b']

/-- Bounds of a command's words. -/
def CmdWf (c : Cmd) : Prop := c.val.length < 2 ^ 64

def EntryWf (e : RepEntry) : Prop := CmdWf e.cmd ∧ e.dep.length < 2 ^ 64

/-- **A well-formed event**: its numbers below `2 ^ 64`; an invocation's command a put or a
get. -/
def PEvWf : PEv → Prop
  | .inv _ c => (c.op = opPUT ∨ c.op = opGET) ∧ CmdWf c
  | .resp _ v => v.length < 2 ^ 64
  | .handle b _ c => b < 2 ^ 64 ∧ CmdWf c
  | .preaccept b _ D => b < 2 ^ 64 ∧ D.length < 2 ^ 64
  | .accept b _ => b < 2 ^ 64
  | .commit b _ => b < 2 ^ 64
  | .newBallot b' => b' < 2 ^ 64
  | .report b' R => b' < 2 ^ 64 ∧ R.cbal < 2 ^ 64 ∧ R.entries.length < 2 ^ 64 ∧
      ∀ e ∈ R.entries, EntryWf e
  | .computeSync b' ids => b' < 2 ^ 64 ∧ ids.length < 2 ^ 64 ∧ ∀ r ∈ ids, r < 2 ^ 64
  | .takeSync b' => b' < 2 ^ 64

theorem encP_length_pos (e : PEv) : 0 < (encP e).length := by
  cases e <;> simp [encP]

/-! ## Prefix-freeness -/

/-- `f`'s words are prefix-free on the `w`-elements. -/
def PFw {α : Type} (f : α → List w64) (w : α → Prop) : Prop :=
  ∀ a b r r', w a → w b → f a ++ r = f b ++ r' → a = b ∧ r = r'

theorem w64_inj_lt {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : (W64 (a : Int)) = W64 (b : Int)) : a = b := by
  have := congrArg BitVec.toNat h
  simp only [W64, BitVec.toNat_ofInt] at this
  omega

theorem w8w_inj {a b : w8} (h : w8w a = w8w b) : a = b := by
  have := w64_inj_lt (by have := a.isLt; omega) (by have := b.isLt; omega) h
  exact BitVec.eq_of_toNat_eq this

theorem w32w_inj {a b : w32} (h : w32w a = w32w b) : a = b := by
  have := w64_inj_lt (by have := a.isLt; omega) (by have := b.isLt; omega) h
  exact BitVec.eq_of_toNat_eq this

theorem PFw_one {α : Type} (f : α → w64) (w : α → Prop) (hf : ∀ a b, w a → w b → f a = f b → a = b) :
    PFw (fun a => [f a]) w := by
  intro a b r r' ha hb h
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
  exact ⟨hf a b ha hb h.1, h.2⟩

theorem PFw_nat : PFw (fun n => [natW n]) (· < 2 ^ 64) :=
  PFw_one _ _ (fun _ _ ha hb h => w64_inj_lt ha hb h)

theorem PFw_w8 : PFw (fun b => [w8w b]) (fun _ => True) :=
  PFw_one _ _ (fun _ _ _ _ h => w8w_inj h)

theorem PFw_w64 : PFw (fun b : w64 => [b]) (fun _ => True) :=
  PFw_one _ _ (fun _ _ _ _ h => h)

theorem PFw_pair {α β : Type} {f : α → List w64} {g : β → List w64} {wa : α → Prop}
    {wb : β → Prop} (hf : PFw f wa) (hg : PFw g wb) :
    PFw (fun p : α × β => f p.1 ++ g p.2) (fun p => wa p.1 ∧ wb p.2) := by
  intro a b r r' ha hb h
  simp only [List.append_assoc] at h
  obtain ⟨e1, h⟩ := hf _ _ _ _ ha.1 hb.1 h
  obtain ⟨e2, h⟩ := hg _ _ _ _ ha.2 hb.2 h
  exact ⟨Prod.ext e1 e2, h⟩

/-- Through an injective translation. -/
theorem PFw_map {α β : Type} {f : β → List w64} {w : β → Prop} (φ : α → β)
    (hφ : ∀ a b, φ a = φ b → a = b) (hf : PFw f w) :
    PFw (fun a => f (φ a)) (fun a => w (φ a)) := by
  intro a b r r' ha hb h
  obtain ⟨e, h⟩ := hf _ _ _ _ ha hb h
  exact ⟨hφ _ _ e, h⟩

theorem PFw_mono {α : Type} {f : α → List w64} {w w' : α → Prop} (hf : PFw f w)
    (h : ∀ a, w' a → w a) : PFw f w' :=
  fun a b r r' ha hb e => hf a b r r' (h a ha) (h b hb) e

theorem PFw_elems {α : Type} {f : α → List w64} {w : α → Prop} (hf : PFw f w) :
    ∀ (l l' : List α) (r r' : List w64), l.length = l'.length → (∀ a ∈ l, w a) →
      (∀ a ∈ l', w a) → l.flatMap f ++ r = l'.flatMap f ++ r' → l = l' ∧ r = r' := by
  intro l
  induction l with
  | nil =>
    intro l' r r' hl _ _ h
    cases l' with
    | nil => simpa using h
    | cons _ _ => simp at hl
  | cons a l ih =>
    intro l' r r' hl hw hw' h
    cases l' with
    | nil => simp at hl
    | cons b l' =>
      simp only [List.flatMap_cons, List.append_assoc] at h
      obtain ⟨e1, h⟩ := hf _ _ _ _ (hw a (by simp)) (hw' b (by simp)) h
      obtain ⟨e2, h⟩ := ih l' r r' (by simpa using hl) (fun x hx => hw x (by simp [hx]))
        (fun x hx => hw' x (by simp [hx])) h
      exact ⟨by rw [e1, e2], h⟩

theorem PFw_list {α : Type} {f : α → List w64} {w : α → Prop} (hf : PFw f w) :
    PFw (listW f) (fun l => l.length < 2 ^ 64 ∧ ∀ a ∈ l, w a) := by
  intro l l' r r' hl hl' h
  simp only [listW, List.cons_append, List.cons.injEq] at h
  have hlen := w64_inj_lt hl.1 hl'.1 h.1
  exact PFw_elems hf l l' r r' hlen hl.2 hl'.2 h.2

theorem wordsOf_eq (bs : List w8) : wordsOf bs = listW (fun b => [w8w b]) bs := by
  unfold wordsOf listW
  congr 1
  induction bs with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem PFw_bytes : PFw wordsOf (fun bs => bs.length < 2 ^ 64) := by
  have := PFw_mono (PFw_list PFw_w8) (fun (bs : List w8) h => ⟨h, fun _ _ => trivial⟩)
  intro a b r r' ha hb h
  rw [wordsOf_eq, wordsOf_eq] at h
  exact this a b r r' ha hb h

theorem PFw_id : PFw idW (fun _ => True) := by
  have h := PFw_map (fun x : CmdId => (x.cl, x.seq)) (by
      rintro ⟨a, b⟩ ⟨c, d⟩ h; simp only [Prod.mk.injEq] at h; rw [h.1, h.2])
    (PFw_pair (PFw_one (fun a : w32 => w32w a) (fun _ => True) (fun _ _ _ _ e => w32w_inj e))
      (PFw_one (fun a : w32 => w32w a) (fun _ => True) (fun _ _ _ _ e => w32w_inj e)))
  intro a b r r' _ _ e
  exact h a b r r' ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ e

theorem PFw_cmd : PFw cmdW CmdWf := by
  have h := PFw_map (fun c : Cmd => (c.op, c.key, c.val)) (by
      rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h; simp only [Prod.mk.injEq] at h; rw [h.1, h.2.1, h.2.2])
    (PFw_pair PFw_w8 (PFw_pair PFw_w64 PFw_bytes))
  intro a b r r' ha hb e
  exact h a b r r' ⟨trivial, trivial, ha⟩ ⟨trivial, trivial, hb⟩ (by simpa [cmdW] using e)

theorem PFw_entry : PFw repEntryW EntryWf := by
  have h := PFw_map (fun e : RepEntry => (e.id, e.phase, e.cmd, e.dep)) (by
      rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h; simp only [Prod.mk.injEq] at h
      rw [h.1, h.2.1, h.2.2.1, h.2.2.2])
    (PFw_pair PFw_id (PFw_pair PFw_w64 (PFw_pair PFw_cmd (PFw_list PFw_id))))
  intro a b r r' ha hb e
  exact h a b r r' ⟨trivial, trivial, ha.1, ha.2, fun _ _ => trivial⟩
    ⟨trivial, trivial, hb.1, hb.2, fun _ _ => trivial⟩ (by simpa [repEntryW] using e)

/-- The tag of an event (its first word), as a natural. -/
def tagOf : PEv → Nat
  | .inv _ c => c.op.toNat
  | .resp _ _ => 3
  | .handle .. => 4
  | .preaccept .. => 5
  | .accept .. => 6
  | .commit .. => 7
  | .newBallot .. => 8
  | .report .. => 9
  | .computeSync .. => 10
  | .takeSync .. => 11

theorem encP_cons (e : PEv) : ∃ t, encP e = W64 (tagOf e) :: t := by
  cases e <;> simp [encP, tagOf, w8w]

theorem tagOf_lt (e : PEv) : tagOf e < 2 ^ 64 := by
  cases e with
  | inv x c => have := c.op.isLt; simp only [tagOf]; omega
  | _ => simp only [tagOf]; omega

/-- **Prefix-freeness**: a well-formed event's words determine it and the rest. -/
theorem encP_inj {e e' : PEv} {ws ws' : List w64} (he : PEvWf e) (he' : PEvWf e')
    (h : encP e ++ ws = encP e' ++ ws') : e = e' ∧ ws = ws' := by
  -- the tags agree
  have ht : tagOf e = tagOf e' := by
    obtain ⟨t, et⟩ := encP_cons e
    obtain ⟨t', et'⟩ := encP_cons e'
    rw [et, et'] at h
    simp only [List.cons_append, List.cons.injEq] at h
    exact w64_inj_lt (tagOf_lt e) (tagOf_lt e') h.1
  cases e <;> cases e'
  all_goals try simp only [tagOf] at ht
  all_goals try (exfalso; omega)
  all_goals try (exfalso; simp only [PEvWf] at he; rcases he with ⟨hop | hop, -⟩ <;>
    rw [hop] at ht <;> simp [opPUT, opGET] at ht <;> done)
  all_goals try (exfalso; simp only [PEvWf] at he'; rcases he' with ⟨hop | hop, -⟩ <;>
    rw [hop] at ht <;> simp [opPUT, opGET] at ht <;> done)
  all_goals simp only [encP, List.cons_append, List.append_assoc, List.cons.injEq] at h
  all_goals simp only [PEvWf] at he he'
  -- inv
  case inv.inv x c x' c' =>
    obtain ⟨h1, h⟩ := h
    obtain ⟨ex, h⟩ := PFw_id x x' _ _ trivial trivial h
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨hk, h⟩ := h
    obtain ⟨ev, h⟩ := PFw_bytes _ _ _ _ he.2 he'.2 h
    refine ⟨?_, h⟩
    have : c = c' := by
      cases c; cases c'; simp only at h1 hk ev; rw [w8w_inj h1, hk, ev]
    rw [ex, this]
  case resp.resp x v x' v' =>
    obtain ⟨ex, h⟩ := PFw_id x x' _ _ trivial trivial h.2
    obtain ⟨ev, h⟩ := PFw_bytes _ _ _ _ he he' h
    exact ⟨by rw [ex, ev], h⟩
  case handle.handle b x c b' x' c' =>
    obtain ⟨-, hb, h⟩ := h
    obtain ⟨ex, h⟩ := PFw_id x x' _ _ trivial trivial h
    obtain ⟨ec, h⟩ := PFw_cmd _ _ _ _ he.2 he'.2 h
    exact ⟨by rw [w64_inj_lt he.1 he'.1 hb, ex, ec], h⟩
  case preaccept.preaccept b y D b' y' D' =>
    obtain ⟨-, hb, h⟩ := h
    obtain ⟨ey, h⟩ := PFw_id y y' _ _ trivial trivial h
    obtain ⟨eD, h⟩ := PFw_list PFw_id D D' _ _ ⟨he.2, fun _ _ => trivial⟩
      ⟨he'.2, fun _ _ => trivial⟩ h
    exact ⟨by rw [w64_inj_lt he.1 he'.1 hb, ey, eD], h⟩
  case accept.accept b y b' y' =>
    obtain ⟨-, hb, h⟩ := h
    obtain ⟨ey, h⟩ := PFw_id y y' _ _ trivial trivial h
    exact ⟨by rw [w64_inj_lt he he' hb, ey], h⟩
  case commit.commit b y b' y' =>
    obtain ⟨-, hb, h⟩ := h
    obtain ⟨ey, h⟩ := PFw_id y y' _ _ trivial trivial h
    exact ⟨by rw [w64_inj_lt he he' hb, ey], h⟩
  case newBallot.newBallot b b' =>
    obtain ⟨-, hb, h⟩ := h
    exact ⟨by rw [w64_inj_lt he he' hb], h⟩
  case report.report b R b' R' =>
    obtain ⟨-, hb, hc, h⟩ := h
    obtain ⟨eE, h⟩ := PFw_list PFw_entry R.entries R'.entries _ _ ⟨he.2.2.1, he.2.2.2⟩
      ⟨he'.2.2.1, he'.2.2.2⟩ h
    refine ⟨?_, h⟩
    have e1 := w64_inj_lt he.2.1 he'.2.1 hc
    have : R = R' := by
      cases R; cases R'; simp only at e1 eE; subst e1; subst eE; rfl
    rw [w64_inj_lt he.1 he'.1 hb, this]
  case computeSync.computeSync b ids b' ids' =>
    obtain ⟨-, hb, h⟩ := h
    obtain ⟨eI, h⟩ := PFw_list PFw_nat ids ids' _ _ ⟨he.2.1, he.2.2⟩ ⟨he'.2.1, he'.2.2⟩ h
    exact ⟨by rw [w64_inj_lt he.1 he'.1 hb, eI], h⟩
  case takeSync.takeSync b b' =>
    obtain ⟨-, hb, h⟩ := h
    exact ⟨by rw [w64_inj_lt he he' hb], h⟩

/-! ## Decoding -/

open Classical in
/-- **The events of a list of words**, as long as they decode. -/
noncomputable def decodeP (ws : List w64) : List PEv :=
  if h : ∃ e ws', PEvWf e ∧ ws = encP e ++ ws' then
    Classical.choose h :: decodeP (Classical.choose (Classical.choose_spec h))
  else []
termination_by ws.length
decreasing_by
  have h2 := (Classical.choose_spec (Classical.choose_spec h)).2
  have hl := encP_length_pos (Classical.choose h)
  have : ws.length = (encP (Classical.choose h)).length +
      (Classical.choose (Classical.choose_spec h)).length := by
    conv => lhs; rw [h2]
    exact List.length_append
  omega

/-- **Resolving one event's words** leaves the decoding of the rest. -/
theorem decodeP_enc {e : PEv} (he : PEvWf e) (ws : List w64) :
    decodeP (encP e ++ ws) = e :: decodeP ws := by
  have hex : ∃ e' ws', PEvWf e' ∧ encP e ++ ws = encP e' ++ ws' := ⟨e, ws, he, rfl⟩
  rw [decodeP, dif_pos hex]
  have hs := Classical.choose_spec (Classical.choose_spec hex)
  obtain ⟨h1, h2⟩ := encP_inj he hs.1 hs.2
  congr 1
  · exact h1.symm
  · exact congrArg decodeP h2.symm

end sp

end Perennial.github_com.imdea_software.swiftpaxos

end
