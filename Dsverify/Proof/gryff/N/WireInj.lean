/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/WireInj.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N: the message encodings are self-delimiting

Every encoding of `Wire/Enc.lean` used on a peer connection is injective and prefix-free on
well-formed values (`*_app_inj`: `enc a ++ x = enc b ++ y → a = b ∧ x = y`), so a model message's
bytes (`msgWireB`) start with a code that determines its kind, then decode uniquely
(`msgWireB_app_inj`). This is what `msgsWire_prefix` and the listener's decoding rest on.
-/
module

public import Dsverify.Proof.gryff.N.WireDefs
public import Dsverify.Proof.gryff.Wire.Proof.Varint

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.gryff.netN

open model wire

variable [GooseExts]

/-! ## Fields -/

theorem u32_app_inj {a b : w32} {l1 l2 : List w8} (h : u32Le a ++ l1 = u32Le b ++ l2) :
    a = b ∧ l1 = l2 := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [u32Le_length])
  exact ⟨u32Le_inj h1, h2⟩

theorem u64_app_inj {a b : w64} {l1 l2 : List w8} (h : u64Le a ++ l1 = u64Le b ++ l2) :
    a = b ∧ l1 = l2 := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [u64Le_length])
  exact ⟨u64Le_inj h1, h2⟩

theorem byte_app_inj {a b : w8} {l1 l2 : List w8} (h : a :: l1 = b :: l2) :
    a = b ∧ l1 = l2 := List.cons.inj h

-- Peel the leading field of `h : f a ++ x = f b ++ y`, substituting `a := b`.
set_option hygiene false in
macro "peel " _hh:ident : tactic => `(tactic| (first
  | (replace h := u32_app_inj h; obtain ⟨heq, h⟩ := h; subst heq)
  | (replace h := u64_app_inj h; obtain ⟨heq, h⟩ := h; subst heq)
  | (replace h := byte_app_inj h; obtain ⟨heq, h⟩ := h; subst heq)))

theorem tag_app_inj {a b : gryffproto.Tag.Msg} {l1 l2 : List w8}
    (h : gryffproto.Tag.enc a ++ l1 = gryffproto.Tag.enc b ++ l2) : a = b ∧ l1 = l2 := by
  cases a; cases b
  simp only [gryffproto.Tag.enc, List.append_assoc] at h
  peel h; peel h; peel h
  exact ⟨rfl, h⟩

theorem valTag_app_inj {a b : gryffproto.ValTag.Msg} {l1 l2 : List w8}
    (h : gryffproto.ValTag.enc a ++ l1 = gryffproto.ValTag.enc b ++ l2) : a = b ∧ l1 = l2 := by
  cases a; cases b
  simp only [gryffproto.ValTag.enc, state.Value.enc, List.append_assoc] at h
  peel h
  replace h := tag_app_inj h; obtain ⟨rfl, h⟩ := h
  exact ⟨rfl, h⟩

theorem dep_app_inj {a b : gryffproto.Dep.Msg} {l1 l2 : List w8}
    (h : gryffproto.Dep.enc a ++ l1 = gryffproto.Dep.enc b ++ l2) : a = b ∧ l1 = l2 := by
  cases a; cases b
  simp only [gryffproto.Dep.enc, state.Key.enc, List.append_assoc] at h
  peel h
  replace h := valTag_app_inj h; obtain ⟨rfl, h⟩ := h
  exact ⟨rfl, h⟩

theorem cmd_app_inj {a b : state.Command.Msg} {l1 l2 : List w8}
    (h : state.Command.enc a ++ l1 = state.Command.enc b ++ l2) : a = b ∧ l1 = l2 := by
  cases a; cases b
  simp only [state.Command.enc, List.append_assoc, List.cons_append,
    List.nil_append] at h
  peel h; peel h; peel h; peel h
  exact ⟨rfl, h⟩

theorem cmds_flat_inj {xs ys : List state.Command.Msg} {l1 l2 : List w8}
    (hl : xs.length = ys.length)
    (h : xs.flatMap state.Command.enc ++ l1 = ys.flatMap state.Command.enc ++ l2) :
    xs = ys ∧ l1 = l2 := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simpa using h
    | cons _ _ => simp at hl
  | cons a xs ih =>
    cases ys with
    | nil => simp at hl
    | cons b ys =>
      simp only [List.flatMap_cons, List.append_assoc] at h
      replace h := cmd_app_inj h; obtain ⟨rfl, h⟩ := h
      replace h := ih (ys := ys) (by simpa using hl) h; obtain ⟨rfl, h⟩ := h
      exact ⟨rfl, h⟩

/-- Terminated varints are prefix-free. -/
theorem term_app_inj {V1 V2 : List w8} {c1 c2 : w8} {l1 l2 : List w8}
    (h1 : contBytes V1) (h2 : contBytes V2) (hc1 : c1.toNat < 128) (hc2 : c2.toNat < 128)
    (h : V1 ++ c1 :: l1 = V2 ++ c2 :: l2) : V1 = V2 ∧ c1 = c2 ∧ l1 = l2 := by
  induction V1 generalizing V2 with
  | nil =>
    cases V2 with
    | nil => simp only [List.nil_append, List.cons.injEq] at h; exact ⟨rfl, h⟩
    | cons b V2 =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      have := h2 b (by simp); rw [← h.1] at this; omega
  | cons a V1 ih =>
    cases V2 with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      have := h1 a (by simp); rw [h.1] at this; omega
    | cons b V2 =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, r⟩ := ih (fun x hx => h1 x (by simp [hx])) (fun x hx => h2 x (by simp [hx])) h
      exact ⟨rfl, r⟩

theorem uvarint_app_inj {a b : Nat} {l1 l2 : List w8}
    (h : uvarintEnc a ++ l1 = uvarintEnc b ++ l2) : a = b ∧ l1 = l2 := by
  obtain ⟨V1, c1, he1, hv1, hc1, -⟩ := uvarintEnc_spec a
  obtain ⟨V2, c2, he2, hv2, hc2, -⟩ := uvarintEnc_spec b
  rw [he1, he2] at h
  simp only [List.append_assoc, List.singleton_append] at h
  obtain ⟨rfl, rfl, rfl⟩ := term_app_inj hv1 hv2 hc1 hc2 h
  refine ⟨uvarintEnc_inj (by rw [he1, he2]), rfl⟩

theorem len_app_inj {n m : Nat} {l1 l2 : List w8} (hn : n < 2 ^ 63) (hm : m < 2 ^ 63)
    (h : varintEnc (sint.Z (W64 n)) ++ l1 = varintEnc (sint.Z (W64 m)) ++ l2) :
    n = m ∧ l1 = l2 := by
  unfold varintEnc at h
  obtain ⟨he, rfl⟩ := uvarint_app_inj h
  refine ⟨?_, rfl⟩
  have hn' : sint.Z (W64 n) = n := by word
  have hm' : sint.Z (W64 m) = m := by word
  rw [hn', hm'] at he
  unfold zigzag at he
  simp only [Int.natCast_nonneg, ↓reduceIte] at he
  omega

theorem cmds_app_inj {xs ys : List state.Command.Msg} {l1 l2 : List w8}
    (ha : xs.length < 2 ^ 63) (hb : ys.length < 2 ^ 63)
    (h : varintEnc (sint.Z (W64 xs.length)) ++ (xs.flatMap state.Command.enc ++ l1) =
      varintEnc (sint.Z (W64 ys.length)) ++ (ys.flatMap state.Command.enc ++ l2)) :
    xs = ys ∧ l1 = l2 := by
  obtain ⟨hl, h⟩ := len_app_inj ha hb h
  exact cmds_flat_inj hl h

theorem arr_app_inj {a b : GoArray w32 5} {l1 l2 : List w8} (ha : a.arr.length = 5)
    (hb : b.arr.length = 5) (h : arrLe32 a ++ l1 = arrLe32 b ++ l2) : a = b ∧ l1 = l2 := by
  obtain ⟨xs⟩ := a
  obtain ⟨ys⟩ := b
  simp only at ha hb
  match xs, ys, ha, hb with
  | [a0, a1, a2, a3, a4], [b0, b1, b2, b3, b4], _, _ =>
    simp only [arrLe32, show ((5 : Int)).toNat = 5 from rfl, List.range_succ, List.range_zero,
      List.nil_append, List.cons_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, List.append_assoc] at h
    peel h; peel h; peel h; peel h; peel h
    exact ⟨rfl, h⟩

/-! ## Messages -/

open wire.gryffproto wire.epaxosproto

-- Peel every leading field (fixed ones, nested records, arrays, command slices).
set_option hygiene false in
macro "peelAll " _hh:ident : tactic => `(tactic| (repeat (first
  | (replace h := u32_app_inj h; obtain ⟨heq, h⟩ := h; subst heq)
  | (replace h := u64_app_inj h; obtain ⟨heq, h⟩ := h; subst heq)
  | (replace h := tag_app_inj h; obtain ⟨heq, h⟩ := h; subst heq)
  | (replace h := valTag_app_inj h; obtain ⟨heq, h⟩ := h; subst heq)
  | (replace h := dep_app_inj h; obtain ⟨heq, h⟩ := h; subst heq)
  | (replace h := arr_app_inj (by assumption) (by assumption) h; obtain ⟨heq, h⟩ := h; subst heq)
  | (replace h := cmds_app_inj (by assumption) (by assumption) h; obtain ⟨heq, h⟩ := h; subst heq)
  | (replace h := byte_app_inj h; obtain ⟨heq, h⟩ := h; subst heq))))

set_option hygiene false in
macro "encInj " e:ident _hh:ident : tactic => `(tactic| (
  cases a; cases b
  simp only [$e:ident, state.Key.enc, state.Value.enc, List.append_assoc,
    List.cons_append, List.nil_append] at h ⊢
  (try simp only at *)
  peelAll h
  exact ⟨rfl, h⟩))

theorem read1_app_inj {a b : Read1Proxied.Msg} {l1 l2 : List w8}
    (h : Read1Proxied.enc a ++ l1 = Read1Proxied.enc b ++ l2) : a = b ∧ l1 = l2 := by
  encInj Read1Proxied.enc h
theorem read2_app_inj {a b : Read2Proxied.Msg} {l1 l2 : List w8}
    (h : Read2Proxied.enc a ++ l1 = Read2Proxied.enc b ++ l2) : a = b ∧ l1 = l2 := by
  encInj Read2Proxied.enc h
theorem read1Reply_app_inj {a b : Read1Reply.Msg} {l1 l2 : List w8}
    (h : Read1Reply.enc a ++ l1 = Read1Reply.enc b ++ l2) : a = b ∧ l1 = l2 := by
  encInj Read1Reply.enc h
theorem read2Reply_app_inj {a b : Read2Reply.Msg} {l1 l2 : List w8}
    (h : Read2Reply.enc a ++ l1 = Read2Reply.enc b ++ l2) : a = b ∧ l1 = l2 := by
  encInj Read2Reply.enc h
theorem write1_app_inj {a b : Write1Proxied.Msg} {l1 l2 : List w8}
    (h : Write1Proxied.enc a ++ l1 = Write1Proxied.enc b ++ l2) : a = b ∧ l1 = l2 := by
  encInj Write1Proxied.enc h
theorem write2_app_inj {a b : Write2Proxied.Msg} {l1 l2 : List w8}
    (h : Write2Proxied.enc a ++ l1 = Write2Proxied.enc b ++ l2) : a = b ∧ l1 = l2 := by
  encInj Write2Proxied.enc h
theorem write1Reply_app_inj {a b : Write1Reply.Msg} {l1 l2 : List w8}
    (h : Write1Reply.enc a ++ l1 = Write1Reply.enc b ++ l2) : a = b ∧ l1 = l2 := by
  encInj Write1Reply.enc h
theorem write2Reply_app_inj {a b : Write2Reply.Msg} {l1 l2 : List w8}
    (h : Write2Reply.enc a ++ l1 = Write2Reply.enc b ++ l2) : a = b ∧ l1 = l2 := by
  encInj Write2Reply.enc h
theorem preAcceptOK_app_inj {a b : PreAcceptOK.Msg} {l1 l2 : List w8}
    (h : PreAcceptOK.enc a ++ l1 = PreAcceptOK.enc b ++ l2) : a = b ∧ l1 = l2 := by
  encInj PreAcceptOK.enc h
theorem acceptReply_app_inj {a b : AcceptReply.Msg} {l1 l2 : List w8}
    (h : AcceptReply.enc a ++ l1 = AcceptReply.enc b ++ l2) : a = b ∧ l1 = l2 := by
  encInj AcceptReply.enc h
theorem prepare_app_inj {a b : Prepare.Msg} {l1 l2 : List w8}
    (h : Prepare.enc a ++ l1 = Prepare.enc b ++ l2) : a = b ∧ l1 = l2 := by
  encInj Prepare.enc h
theorem executed_app_inj {a b : Executed.Msg} {l1 l2 : List w8}
    (h : Executed.enc a ++ l1 = Executed.enc b ++ l2) : a = b ∧ l1 = l2 := by
  encInj Executed.enc h
theorem preAcceptReply_app_inj {a b : PreAcceptReply.Msg} {l1 l2 : List w8}
    (ha1 : a.Deps'.arr.length = 5) (ha2 : a.CommittedDeps'.arr.length = 5)
    (hb1 : b.Deps'.arr.length = 5) (hb2 : b.CommittedDeps'.arr.length = 5)
    (h : PreAcceptReply.enc a ++ l1 = PreAcceptReply.enc b ++ l2) : a = b ∧ l1 = l2 := by
  encInj PreAcceptReply.enc h
theorem preAccept_app_inj {a b : PreAccept.Msg} {l1 l2 : List w8}
    (ha : PreAccept.wf a) (ha1 : a.Deps.arr.length = 5)
    (hb : PreAccept.wf b) (hb1 : b.Deps.arr.length = 5)
    (h : PreAccept.enc a ++ l1 = PreAccept.enc b ++ l2) : a = b ∧ l1 = l2 := by
  unfold PreAccept.wf at ha hb
  encInj PreAccept.enc h
theorem accept_app_inj {a b : EAccept.Msg} {l1 l2 : List w8}
    (ha : EAccept.wf a) (ha1 : a.Deps.arr.length = 5)
    (hb : EAccept.wf b) (hb1 : b.Deps.arr.length = 5)
    (h : EAccept.enc a ++ l1 = EAccept.enc b ++ l2) : a = b ∧ l1 = l2 := by
  unfold EAccept.wf at ha hb
  encInj EAccept.enc h
theorem commit_app_inj {a b : ECommit.Msg} {l1 l2 : List w8}
    (ha : ECommit.wf a) (ha1 : a.Deps.arr.length = 5)
    (hb : ECommit.wf b) (hb1 : b.Deps.arr.length = 5)
    (h : ECommit.enc a ++ l1 = ECommit.enc b ++ l2) : a = b ∧ l1 = l2 := by
  unfold ECommit.wf at ha hb
  encInj ECommit.enc h
theorem prepareReply_app_inj {a b : PrepareReply.Msg} {l1 l2 : List w8}
    (ha : PrepareReply.wf a) (ha1 : a.Deps.arr.length = 5)
    (hb : PrepareReply.wf b) (hb1 : b.Deps.arr.length = 5)
    (h : PrepareReply.enc a ++ l1 = PrepareReply.enc b ++ l2) : a = b ∧ l1 = l2 := by
  unfold PrepareReply.wf at ha hb
  encInj PrepareReply.enc h

end Perennial.gryff.netN
