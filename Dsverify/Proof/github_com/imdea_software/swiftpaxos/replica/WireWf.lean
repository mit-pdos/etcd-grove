/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/WireWf.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The SwiftPaxos frames decode uniquely (pure; `Spec/swift/Wire.lean`'s formats).

What a replica's listener needs to tie a message it decoded off a stream to the message the
stream's protocol (`sp.inP`/`sp.outQ`, `framesProto`) lists at that position: every frame is a
prefix-free, injective encoding of a well-formed message (`Msg.wf`: hashes of 32 bytes, a
command's value shorter than 2^16, varint lengths below 2^62, an `MSync`'s codec encoding below
2^64 bytes), so if the bytes read so far are the frames of `done` and then the frame of `m`, and
the stream is a prefix of the frames of `ms`, then `ms` is `done`, `m`, then more
(`frames_align`).

`Msg.wf` (Spec/swift/WireWf.lean) is in `framesProto` since change log C9 (HUB-REQUEST R1).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.VarintPure
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.WireWf

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

/-! ## Prefix-free injective encodings -/

/-- `enc` is injective and prefix-free on the values satisfying `wf`. -/
def PF {α : Type} (wf : α → Prop) (enc : α → List w8) : Prop :=
  ∀ a b x y, wf a → wf b → enc a ++ x = enc b ++ y → a = b ∧ x = y

theorem PF.peel {α : Type} {wf : α → Prop} {enc : α → List w8} (h : PF wf enc) {a b : α}
    {x y : List w8} (ha : wf a) (hb : wf b) (he : enc a ++ x = enc b ++ y) : a = b ∧ x = y :=
  h a b x y ha hb he

theorem le32_peel {a b : w32} {x y : List w8} (h : le32 a ++ x = le32 b ++ y) :
    a = b ∧ x = y := by
  have := List.append_inj h (by simp [le32, u32Le_length])
  exact ⟨u32Le_inj this.1, this.2⟩

theorem le64_peel {a b : w64} {x y : List w8} (h : le64 a ++ x = le64 b ++ y) :
    a = b ∧ x = y := by
  have := List.append_inj h (by simp [le64, u64Le_length])
  exact ⟨u64Le_inj this.1, this.2⟩

theorem u64Le_peel {a b : w64} {x y : List w8} (h : u64Le a ++ x = u64Le b ++ y) :
    a = b ∧ x = y := by
  have := List.append_inj h (by simp [u64Le_length])
  exact ⟨u64Le_inj this.1, this.2⟩

theorem byte_peel {a b : w8} {x y : List w8} (h : [a] ++ x = [b] ++ y) : a = b ∧ x = y := by
  simpa using h

/-- Varint lengths below `2^62` (so `2 n < 2^63`). -/
theorem varintLen_peel {a b : Nat} {x y : List w8} (ha : a < 2 ^ 62) (hb : b < 2 ^ 62)
    (h : varintLen a ++ x = varintLen b ++ y) : a = b ∧ x = y := by
  unfold varintLen at h
  obtain ⟨ta, da⟩ := uvarint_term (2 * a) (by omega)
  obtain ⟨tb, db⟩ := uvarint_term (2 * b) (by omega)
  have he := uvTerm_prefix _ _ _ _ ta tb h
  have hab : 2 * a = 2 * b := by rw [← da, ← db, he]
  refine ⟨by omega, ?_⟩
  rw [he] at h; exact List.append_cancel_left h

/-- A list of elements of a prefix-free encoding, its length known. -/
theorem elems_peel {α : Type} {wf : α → Prop} {e : α → List w8} (h : PF wf e) :
    ∀ (l1 l2 : List α) (x y : List w8), l1.length = l2.length → (∀ a ∈ l1, wf a) →
      (∀ a ∈ l2, wf a) → (l1.map e).flatten ++ x = (l2.map e).flatten ++ y → l1 = l2 ∧ x = y
  | [], [], _, _, _, _, _, h' => by simpa using h'
  | a :: l1, b :: l2, x, y, hl, h1, h2, h' => by
    simp only [List.map_cons, List.flatten_cons, List.append_assoc] at h'
    obtain ⟨hab, h''⟩ := h.peel (h1 a (by simp)) (h2 b (by simp)) h'
    obtain ⟨hl', hxy⟩ := elems_peel h l1 l2 x y (by simpa using hl)
      (fun z hz => h1 z (by simp [hz])) (fun z hz => h2 z (by simp [hz])) h''
    exact ⟨by rw [hab, hl'], hxy⟩
  | [], _ :: _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _, _ => by simp at hl

/-- A varint-length-prefixed list of elements of a prefix-free encoding. -/
theorem lenList_peel {α : Type} {wf : α → Prop} {e : α → List w8} (h : PF wf e)
    {l1 l2 : List α} {x y : List w8} (h1 : l1.length < 2 ^ 62 ∧ ∀ a ∈ l1, wf a)
    (h2 : l2.length < 2 ^ 62 ∧ ∀ a ∈ l2, wf a)
    (h' : varintLen l1.length ++ ((l1.map e).flatten ++ x) =
      varintLen l2.length ++ ((l2.map e).flatten ++ y)) : l1 = l2 ∧ x = y := by
  obtain ⟨hl, h'⟩ := varintLen_peel h1.1 h2.1 h'
  exact elems_peel h l1 l2 x y hl h1.2 h2.2 h'

/-! ## The pieces -/

theorem pf_cmdId : PF (fun _ => True) encCmdId := by
  intro a b x y _ _ h
  simp only [encCmdId, List.append_assoc] at h
  obtain ⟨h1, h⟩ := le32_peel h
  obtain ⟨h2, h⟩ := le32_peel h
  cases a; cases b; simp_all

theorem cmdId_peel {a b : CmdId} {x y : List w8} (h : encCmdId a ++ x = encCmdId b ++ y) :
    a = b ∧ x = y := pf_cmdId.peel trivial trivial h


theorem pf_hash : PF Hash.wf id := by
  intro a b x y ha hb h
  exact List.append_inj h (by simp [Hash.wf] at ha hb; simp [ha, hb])


theorem hashes_peel {a b : List Hash} {x y : List w8} (ha : hashesWf a) (hb : hashesWf b)
    (h : encHashes a ++ x = encHashes b ++ y) : a = b ∧ x = y := by
  unfold encHashes at h
  rw [List.append_assoc, List.append_assoc] at h
  have e1 : a.flatten = (a.map id).flatten := by simp
  have e2 : b.flatten = (b.map id).flatten := by simp
  rw [e1, e2] at h
  exact lenList_peel pf_hash ha hb h


theorem dep_peel {a b : List CmdId} {x y : List w8} (ha : depWf a) (hb : depWf b)
    (h : encDep a ++ x = encDep b ++ y) : a = b ∧ x = y := by
  unfold encDep at h
  rw [List.append_assoc, List.append_assoc] at h
  exact lenList_peel pf_cmdId ⟨ha, fun _ _ => trivial⟩ ⟨hb, fun _ _ => trivial⟩ h

theorem value_peel {a b : List w8} {x y : List w8} (ha : a.length < 2 ^ 16)
    (hb : b.length < 2 ^ 16) (h : encValue a ++ x = encValue b ++ y) : a = b ∧ x = y := by
  unfold encValue at h
  simp only [List.cons_append, List.nil_append, List.cons.injEq, List.append_assoc] at h
  obtain ⟨h0, h1, -, -, h⟩ := h
  have hl : a.length = b.length := by
    have e0 := congrArg BitVec.toNat h0
    have e1 := congrArg BitVec.toNat h1
    simp only [W8, BitVec.toNat_ofInt] at e0 e1
    omega
  exact List.append_inj h hl


theorem cmd_peel {a b : Cmd} {x y : List w8} (ha : a.wf) (hb : b.wf)
    (h : encCmd a ++ x = encCmd b ++ y) : a = b ∧ x = y := by
  simp only [encCmd, List.append_assoc] at h
  obtain ⟨h1, h⟩ := byte_peel h
  obtain ⟨h2, h⟩ := le64_peel h
  obtain ⟨h3, h⟩ := value_peel ha hb h
  cases a; cases b; simp_all

theorem bytes_peel {a b : List w8} {x y : List w8} (ha : a.length < 2 ^ 62)
    (hb : b.length < 2 ^ 62) (h : encBytes a ++ x = encBytes b ++ y) : a = b ∧ x = y := by
  unfold encBytes at h
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨hl, h⟩ := varintLen_peel ha hb h
  exact List.append_inj h hl

/-! ## Messages -/


theorem pf_fastAck : PF FastAck.wf FastAck.enc := by
  intro a b x y ha hb h
  simp only [FastAck.enc, List.append_assoc] at h
  obtain ⟨h1, h⟩ := le32_peel h
  obtain ⟨h2, h⟩ := le32_peel h
  obtain ⟨h3, h⟩ := cmdId_peel h
  obtain ⟨h4, h⟩ := dep_peel ha.1 hb.1 h
  obtain ⟨h5, h⟩ := hashes_peel ha.2 hb.2 h
  obtain ⟨h6, h⟩ := le64_peel h
  cases a; cases b; simp_all

theorem pf_slowAck : PF (fun _ => True) SlowAck.enc := by
  intro a b x y _ _ h
  simp only [SlowAck.enc, List.append_assoc] at h
  obtain ⟨h1, h⟩ := le32_peel h
  obtain ⟨h2, h⟩ := le32_peel h
  obtain ⟨h3, h⟩ := cmdId_peel h
  cases a; cases b; simp_all

theorem pf_ack : PF Ack.wf Ack.enc := by
  intro a b x y ha hb h
  simp only [Ack.enc, List.append_assoc] at h
  obtain ⟨h3, h⟩ := cmdId_peel h
  obtain ⟨h4, h⟩ := dep_peel ha.1 hb.1 h
  obtain ⟨h5, h⟩ := hashes_peel ha.2 hb.2 h
  obtain ⟨h6, h⟩ := le64_peel h
  cases a; cases b; simp_all


theorem cU64_peel {a b : w64} {x y : List w8} (h : cU64 a ++ x = cU64 b ++ y) :
    a = b ∧ x = y := u64Le_peel h

theorem sync_body_peel {a b : SyncWire} {x y : List w8} (ha : a.wf) (hb : b.wf)
    (h : gobFrame (KitVal.msync a).encode ++ x = gobFrame (KitVal.msync b).encode ++ y) :
    (KitVal.msync a).encode = (KitVal.msync b).encode ∧ x = y := by
  unfold gobFrame at h
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨hl, h⟩ := u64Le_peel h
  have hl' : (KitVal.msync a).encode.length = (KitVal.msync b).encode.length := by
    have := congrArg BitVec.toNat hl
    unfold SyncWire.wf at ha hb
    simp [W64] at this
    omega
  exact List.append_inj h hl'

/-! ### The codec's encoding of an `MSync` (lengths bounded by the frame's) -/

/-- `f` is injective and prefix-free on encodings that fit in `2^64` bytes. -/
def PFB {α : Type} (f : α → List w8) : Prop :=
  ∀ a b x y, (f a ++ x).length < 2 ^ 64 → f a ++ x = f b ++ y → a = b ∧ x = y

theorem PFB.peel {α : Type} {f : α → List w8} (h : PFB f) {a b : α} {x y : List w8}
    (hl : (f a ++ x).length < 2 ^ 64) (he : f a ++ x = f b ++ y) : a = b ∧ x = y :=
  h a b x y hl he

theorem cI32_peel {a b : w32} {x y : List w8} (h : cI32 a ++ x = cI32 b ++ y) :
    a = b ∧ x = y := by
  obtain ⟨h1, h2⟩ := u64Le_peel h
  refine ⟨?_, h2⟩
  ext i hi
  have := congrArg (fun z => z[i]'(by omega)) h1
  simpa [BitVec.getElem_signExtend, hi] using this

theorem w64_len_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : W64 (a : Int) = W64 (b : Int)) : a = b := by
  have := congrArg BitVec.toNat h
  simp [W64] at this
  omega

theorem cBytes_peel {a b x y : List w8} (hl : (cBytes a ++ x).length < 2 ^ 64)
    (h : cBytes a ++ x = cBytes b ++ y) : a = b ∧ x = y := by
  have hb : (cBytes b ++ y).length < 2 ^ 64 := by rw [← h]; exact hl
  simp only [cBytes, cU64, List.append_assoc, List.length_append, u64Le_length] at h hl hb
  obtain ⟨h1, h⟩ := u64Le_peel h
  have := w64_len_inj (by omega) (by omega) h1
  exact List.append_inj h this

theorem elemsB_peel {α : Type} {f : α → List w8} (hf : PFB f) :
    ∀ (l1 l2 : List α) (x y : List w8), l1.length = l2.length →
      ((l1.map f).flatten ++ x).length < 2 ^ 64 →
      (l1.map f).flatten ++ x = (l2.map f).flatten ++ y → l1 = l2 ∧ x = y
  | [], [], _, _, _, _, h' => by simpa using h'
  | a :: l1, b :: l2, x, y, hl, hb, h' => by
    simp only [List.map_cons, List.flatten_cons, List.append_assoc] at h' hb
    obtain ⟨hab, h''⟩ := hf.peel hb h'
    have hb' : ((l1.map f).flatten ++ x).length < 2 ^ 64 := by
      simp only [List.length_append] at hb ⊢; omega
    obtain ⟨hl', hxy⟩ := elemsB_peel hf l1 l2 x y (by simpa using hl) hb' h''
    exact ⟨by rw [hab, hl'], hxy⟩
  | [], _ :: _, _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _ => by simp at hl

theorem length_le_flatten {α : Type} (f : α → List w8) (hne : ∀ a, 1 ≤ (f a).length) :
    ∀ l : List α, l.length ≤ (l.map f).flatten.length
  | [] => by simp
  | a :: l => by
    have := length_le_flatten f hne l
    have := hne a
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.length_append]; omega

theorem cList_peel {α : Type} {f : α → List w8} (hf : PFB f) (hne : ∀ a, 1 ≤ (f a).length)
    {a b : List α} {x y : List w8} (hl : (cList f a ++ x).length < 2 ^ 64)
    (h : cList f a ++ x = cList f b ++ y) : a = b ∧ x = y := by
  have hb : (cList f b ++ y).length < 2 ^ 64 := by rw [← h]; exact hl
  have la := length_le_flatten f hne a
  have lb := length_le_flatten f hne b
  simp only [cList, cU64, List.append_assoc] at h hl hb
  obtain ⟨h1, h⟩ := u64Le_peel h
  simp only [List.length_append, u64Le_length] at hl hb
  have hab := w64_len_inj (by omega) (by omega) h1
  exact elemsB_peel hf a b x y hab (by simp only [List.length_append]; omega) h

theorem cMapOpt_peel {α : Type} {f : α → List w8} (hf : PFB f) (hne : ∀ a, 1 ≤ (f a).length)
    {a b : Option (List α)} {x y : List w8} (hl : (cMapOpt f a ++ x).length < 2 ^ 64)
    (h : cMapOpt f a ++ x = cMapOpt f b ++ y) : a = b ∧ x = y := by
  cases a <;> cases b <;> simp only [cMapOpt, List.cons_append, List.nil_append,
    List.cons.injEq] at h hl
  · exact ⟨rfl, h.2⟩
  · exact absurd h.1 (by decide)
  · exact absurd h.1 (by decide)
  · obtain ⟨-, h⟩ := h
    simp only [List.length_cons] at hl
    obtain ⟨h1, h2⟩ := cList_peel hf hne (by omega) h
    exact ⟨by rw [h1], h2⟩

theorem pfb_cmdId : PFB cCmdId := by
  intro a b x y _ h
  simp only [cCmdId, List.append_assoc] at h
  obtain ⟨h1, h⟩ := cI32_peel h
  obtain ⟨h2, h⟩ := cI32_peel h
  cases a; cases b; simp_all

theorem cCmdId_len (a : CmdId) : 1 ≤ (cCmdId a).length := by
  simp [cCmdId, cI32, cU64, u64Le_length]

theorem pfb_cmd : PFB cCmd := by
  intro a b x y hl h
  simp only [cCmd, List.append_assoc] at h hl
  obtain ⟨h1, h⟩ := u64Le_peel h
  obtain ⟨h2, h⟩ := u64Le_peel h
  simp only [List.length_append, u64Le_length] at hl
  obtain ⟨h3, h⟩ := cBytes_peel (by simp only [List.length_append] at hl ⊢; omega) h
  have h1' : a.op = b.op := by
    have := congrArg (BitVec.setWidth 8) h1
    simpa using this
  cases a; cases b; simp_all

theorem syncEnc_inj {a b : SyncWire} (ha : a.wf)
    (h : (KitVal.msync a).encode = (KitVal.msync b).encode) : a = b := by
  unfold SyncWire.wf at ha
  simp only [KitVal.encode, KitVal.tag, SyncWire.cEnc, List.append_assoc] at h ha
  obtain ⟨-, h⟩ := u64Le_peel h
  simp only [cU64, List.length_append, u64Le_length] at ha
  obtain ⟨h1, h⟩ := cI32_peel h
  obtain ⟨h2, h⟩ := cI32_peel h
  have hp1 : PFB (fun p : CmdId × w64 => cCmdId p.1 ++ cU64 p.2) := by
    intro p q x y hl h
    simp only [List.append_assoc] at h hl
    obtain ⟨e1, h⟩ := pfb_cmdId.peel hl h
    obtain ⟨e2, h⟩ := u64Le_peel h
    exact ⟨Prod.ext e1 e2, h⟩
  have hp2 : PFB (fun p : CmdId × Cmd => cCmdId p.1 ++ cCmd p.2) := by
    intro p q x y hl h
    simp only [List.append_assoc] at h hl
    obtain ⟨e1, h⟩ := pfb_cmdId.peel hl h
    obtain ⟨e2, h⟩ := pfb_cmd.peel (by
      simp only [List.length_append, cCmdId, cI32, cU64, u64Le_length] at hl ⊢; omega) h
    exact ⟨Prod.ext e1 e2, h⟩
  have hp3 : PFB (fun p : CmdId × List CmdId => cCmdId p.1 ++ cList cCmdId p.2) := by
    intro p q x y hl h
    simp only [List.append_assoc] at h hl
    obtain ⟨e1, h⟩ := pfb_cmdId.peel hl h
    obtain ⟨e2, h⟩ := cList_peel pfb_cmdId cCmdId_len (by
      simp only [List.length_append, cCmdId, cI32, cU64, u64Le_length] at hl ⊢; omega) h
    exact ⟨Prod.ext e1 e2, h⟩
  have n1 : ∀ p : CmdId × w64, 1 ≤ (cCmdId p.1 ++ cU64 p.2).length := fun p => by
    simp [cCmdId, cI32, cU64, u64Le_length]
  have n2 : ∀ p : CmdId × Cmd, 1 ≤ (cCmdId p.1 ++ cCmd p.2).length := fun p => by
    simp only [List.length_append, cCmdId, cI32, cU64, u64Le_length]; omega
  have n3 : ∀ p : CmdId × List CmdId, 1 ≤ (cCmdId p.1 ++ cList cCmdId p.2).length := fun p => by
    simp only [List.length_append, cCmdId, cI32, cU64, u64Le_length]; omega
  have h' := h
  obtain ⟨e3, h⟩ := cMapOpt_peel hp1 n1 (by
    simp only [List.length_append, cI32, cU64, u64Le_length] at ha ⊢; omega) h
  obtain ⟨e4, h⟩ := cMapOpt_peel hp2 n2 (by
    simp only [List.length_append, cI32, cU64, u64Le_length] at ha ⊢; omega) h
  obtain ⟨e5, -⟩ := cMapOpt_peel hp3 n3 (a := a.deps) (b := b.deps) (x := []) (y := [])
    (by simp only [List.length_append, cI32, cU64, u64Le_length, List.length_nil] at ha ⊢; omega)
    (by simpa using h)
  cases a; cases b; simp_all

/-! ### The newLeaderAckN's arrays -/

theorem map_flatten_peel {α β : Type} {wf : β → Prop} {e : β → List w8} (h : PF wf e)
    (f : α → β) {l1 l2 : List α} {x y : List w8} (hl : l1.length = l2.length)
    (h1 : ∀ a ∈ l1, wf (f a)) (h2 : ∀ a ∈ l2, wf (f a))
    (h' : (l1.map (fun a => e (f a))).flatten ++ x = (l2.map (fun a => e (f a))).flatten ++ y) :
    l1.map f = l2.map f ∧ x = y := by
  have e1 : l1.map (fun a => e (f a)) = (l1.map f).map e := by simp [List.map_map]
  have e2 : l2.map (fun a => e (f a)) = (l2.map f).map e := by simp [List.map_map]
  rw [e1, e2] at h'
  exact elems_peel h _ _ x y (by simpa using hl) (by simpa using h1) (by simpa using h2) h'

theorem repEntries_eq {es1 es2 : List RepEntry} (hl : es1.length = es2.length)
    (hi : es1.map (·.id) = es2.map (·.id)) (hp : es1.map (·.phase) = es2.map (·.phase))
    (hc : es1.map (·.cmd) = es2.map (·.cmd)) (hd : es1.map (·.dep) = es2.map (·.dep)) :
    es1 = es2 := by
  apply List.ext_getElem hl
  intro n h1 h2
  have ei := congrArg (·[n]?) hi
  have ep := congrArg (·[n]?) hp
  have ec := congrArg (·[n]?) hc
  have ed := congrArg (·[n]?) hd
  simp only [List.getElem?_map, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
    Option.map_some, Option.some.injEq] at ei ep ec ed
  cases h : es1[n]; cases h' : es2[n]
  simp_all

set_option maxHeartbeats 800000 in
theorem pf_body (a b : Msg) (x y : List w8) (ha : a.wf) (hb : b.wf) (hc : a.code = b.code)
    (h : a.body ++ x = b.body ++ y) : a = b ∧ x = y := by
  cases a <;> cases b <;> simp only [Msg.code, rpcTable] at hc <;>
    (try exact absurd hc (by decide)) <;> simp only [Msg.wf] at ha hb <;>
    simp only [Msg.body, List.append_assoc] at h
  case propose.propose =>
    obtain ⟨h1, h⟩ := le32_peel h
    obtain ⟨h2, h⟩ := le32_peel h
    obtain ⟨h3, h⟩ := cmd_peel ha hb h
    obtain ⟨h4, h⟩ := le64_peel h
    simp_all
  case beacon.beacon =>
    obtain ⟨h1, h⟩ := le64_peel h; simp_all
  case beaconReply.beaconReply =>
    obtain ⟨h1, h⟩ := le64_peel h; simp_all
  case fastAck.fastAck =>
    obtain ⟨h1, h⟩ := pf_fastAck.peel ha hb h; simp_all
  case fastAckClient.fastAckClient =>
    obtain ⟨h1, h⟩ := le32_peel h
    obtain ⟨h2, h⟩ := le32_peel h
    obtain ⟨h3, h⟩ := cmdId_peel h
    obtain ⟨h4, h⟩ := hashes_peel ha hb (by simpa using h)
    simp_all
  case lightSlowAck.lightSlowAck =>
    obtain ⟨h1, h⟩ := pf_slowAck.peel trivial trivial (by simpa using h); simp_all
  case acks.acks =>
    obtain ⟨h1, h⟩ := lenList_peel pf_fastAck ha.1 hb.1 h
    obtain ⟨h2, h⟩ := lenList_peel pf_slowAck ⟨ha.2, fun _ _ => trivial⟩
      ⟨hb.2, fun _ _ => trivial⟩ (by simpa using h)
    simp_all
  case optAcks.optAcks =>
    obtain ⟨h1, h⟩ := le32_peel h
    obtain ⟨h2, h⟩ := le32_peel h
    obtain ⟨h3, h⟩ := lenList_peel pf_ack ha hb (by simpa using h)
    simp_all
  case reply.reply =>
    obtain ⟨h1, h⟩ := le32_peel h
    obtain ⟨h2, h⟩ := le32_peel h
    obtain ⟨h3, h⟩ := cmdId_peel h
    obtain ⟨h4, h⟩ := hashes_peel ha.1 hb.1 h
    obtain ⟨h5, h⟩ := bytes_peel ha.2 hb.2 (by simpa using h)
    simp_all
  case newLeader.newLeader =>
    obtain ⟨h1, h⟩ := le32_peel h
    obtain ⟨h2, h⟩ := le32_peel (by simpa using h)
    simp_all
  case newLeaderAckN.newLeaderAckN r1 b1 c1 es1 r2 b2 c2 es2 =>
    obtain ⟨h1, h⟩ := le32_peel h
    obtain ⟨h2, h⟩ := le32_peel h
    obtain ⟨h3, h⟩ := le32_peel h
    obtain ⟨hl, h⟩ := varintLen_peel ha.1 hb.1 h
    obtain ⟨hi, h⟩ := map_flatten_peel pf_cmdId (·.id) hl (fun _ _ => trivial)
      (fun _ _ => trivial) h
    rw [hl] at h
    obtain ⟨-, h⟩ := List.append_inj h rfl
    have pf64 : PF (fun _ => True) le64 := fun a b x y _ _ h => le64_peel h
    obtain ⟨hp, h⟩ := map_flatten_peel pf64 (·.phase) hl (fun _ _ => trivial)
      (fun _ _ => trivial) h
    simp only [RepEntry.encCmds, List.append_assoc] at h
    rw [hl] at h
    obtain ⟨-, h⟩ := List.append_inj h rfl
    have pfc : PF Cmd.wf encCmd := fun a b x y ha hb h => cmd_peel ha hb h
    obtain ⟨hc', h⟩ := map_flatten_peel pfc (·.cmd) hl (fun e he => (ha.2 e he).1)
      (fun e he => (hb.2 e he).1) h
    try rw [hl] at h
    obtain ⟨-, h⟩ := List.append_inj h rfl
    have pfd : PF depWf encDep := fun a b x y ha hb h => dep_peel ha hb h
    obtain ⟨hd, h⟩ := map_flatten_peel pfd (·.dep) hl (fun e he => (ha.2 e he).2)
      (fun e he => (hb.2 e he).2) (by simpa using h)
    refine ⟨?_, h⟩
    simp only [h1, h2, h3, repEntries_eq hl hi hp hc' hd]
  case sync.sync m1 m2 =>
    obtain ⟨he, h⟩ := sync_body_peel ha hb (by simpa using h)
    exact ⟨by rw [syncEnc_inj ha he], h⟩

/-- Frames of well-formed messages are prefix-free and injective. -/
theorem frame_peel {a b : Msg} {x y : List w8} (ha : a.wf) (hb : b.wf)
    (h : a.frame ++ x = b.frame ++ y) : a = b ∧ x = y := by
  simp only [Msg.frame, List.cons_append, List.cons.injEq] at h
  exact pf_body a b x y ha hb h.1 h.2

/-- **Alignment**: the bytes read are the frames of `done` and then the frame of `m`, the
stream a prefix of the frames of `ms`: `ms` continues `done` with `m`. -/
theorem frames_align {done ms : List Msg} {m : Msg} {u : List w8}
    (hd : ∀ d ∈ done, d.wf) (hms : ∀ x ∈ ms, x.wf) (hm : m.wf)
    (h : framesOf done ++ m.frame ++ u = framesOf ms) : ∃ rest, ms = done ++ m :: rest := by
  induction done generalizing ms with
  | nil =>
    cases ms with
    | nil => simp [framesOf, Msg.frame] at h
    | cons b ms =>
      simp only [framesOf, List.map_nil, List.flatten_nil, List.nil_append, List.map_cons,
        List.flatten_cons] at h
      obtain ⟨rfl, -⟩ := frame_peel hm (hms b (by simp)) h
      exact ⟨ms, rfl⟩
  | cons d done ih =>
    cases ms with
    | nil => simp [framesOf, Msg.frame] at h
    | cons b ms =>
      simp only [framesOf, List.map_cons, List.flatten_cons, List.append_assoc] at h
      obtain ⟨hdb, h2⟩ := frame_peel (hd d (by simp)) (hms b (by simp)) h
      subst hdb
      obtain ⟨rest, hr⟩ := ih (fun z hz => hd z (List.mem_cons_of_mem _ hz))
        (fun z hz => hms z (List.mem_cons_of_mem _ hz)) (by simp only [framesOf, List.append_assoc]; exact h2)
      subst hr
      exact ⟨rest, rfl⟩

/-- The same from a prefix relation with a common head. -/
theorem frames_align_prefix {head : List w8} {done ms : List Msg} {m : Msg}
    (hd : ∀ d ∈ done, d.wf) (hms : ∀ x ∈ ms, x.wf) (hm : m.wf)
    (h : head ++ framesOf done ++ m.frame <+: head ++ framesOf ms) :
    ∃ rest, ms = done ++ m :: rest := by
  obtain ⟨u, hu⟩ := h
  simp only [List.append_assoc] at hu
  have hu' := List.append_cancel_left hu
  exact frames_align hd hms hm (by simpa [List.append_assoc] using hu')

/-- The hello's id is read off its bytes. -/
theorem hello_peel {a b : w32} {x y : List w8} (h : helloBytes a ++ x = helloBytes b ++ y) :
    a = b ∧ x = y := by
  simp only [helloBytes, List.cons_append, List.cons.injEq] at h
  exact le32_peel h.2

end sp

end Perennial.github_com.imdea_software.swiftpaxos

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

/-! ## Decoders: what a reader's `Unmarshal` establishes -/

/-- The bytes `data` read after the type byte `c` decode to `m`: `m` is well formed with type
`c`, and whenever the bytes are a prefix of a well-formed message's body of type `c` (then
more), it is `m` and the bytes are its whole body. (A decoder may accept bytes no encoder
writes, e.g. non-minimal varints or `Value`'s two ignored bytes; on what encoders write it is
exact.) -/
def decodes (c : w8) (data : List w8) (m : Msg) : Prop :=
  m.code = c ∧ m.wf ∧ ∀ (m' : Msg) (u w : List w8), m'.wf → m'.code = c →
    data ++ u = m'.body ++ w → m = m' ∧ data = m'.body

/-- An exact decoder: the bytes are the message's body. -/
theorem decodes_of_body {c : w8} {m : Msg} (hc : m.code = c) (hw : m.wf) :
    decodes c m.body m := by
  refine ⟨hc, hw, fun m' u w hw' hc' h => ?_⟩
  obtain ⟨rfl, -⟩ := pf_body m m' u w hw hw' (hc.trans hc'.symm) h
  exact ⟨rfl, rfl⟩

/-- **Alignment** with a decoder: the bytes read are the frames of `done`, the type byte `c`
and bytes that decode to `m`; the stream is a prefix of the frames of the well-formed `ms`:
`ms` continues `done` with `m`, whose frame is what was read. -/
theorem frames_align_dec {done ms : List Msg} {c : w8} {data : List w8} {m : Msg}
    (hd : ∀ d ∈ done, d.wf) (hms : ∀ x ∈ ms, x.wf) (hm : decodes c data m)
    (h : framesOf done ++ (c :: data) <+: framesOf ms) :
    (∃ rest, ms = done ++ m :: rest) ∧ c :: data = m.frame := by
  obtain ⟨u, hu⟩ := h
  induction done generalizing ms with
  | nil =>
    cases ms with
    | nil => simp [framesOf] at hu
    | cons b ms =>
      simp only [framesOf, List.map_nil, List.flatten_nil, List.nil_append, List.map_cons,
        List.flatten_cons, Msg.frame, List.cons_append, List.cons.injEq] at hu
      obtain ⟨hc, hu⟩ := hu
      obtain ⟨rfl, hb⟩ := hm.2.2 b u _ (hms b (by simp)) hc.symm hu
      refine ⟨⟨ms, rfl⟩, ?_⟩
      simp [Msg.frame, hb, hm.1]
  | cons d done ih =>
    cases ms with
    | nil => simp [framesOf, Msg.frame] at hu
    | cons b ms =>
      simp only [framesOf, List.map_cons, List.flatten_cons, List.append_assoc] at hu
      obtain ⟨hdb, h2⟩ := frame_peel (hd d (by simp)) (hms b (by simp)) hu
      subst hdb
      obtain ⟨⟨rest, hr⟩, hf⟩ := ih (fun z hz => hd z (List.mem_cons_of_mem _ hz))
        (fun z hz => hms z (List.mem_cons_of_mem _ hz))
        (by simp only [framesOf, List.append_assoc]; exact h2)
      subst hr
      exact ⟨⟨rest, rfl⟩, hf⟩

end sp

end Perennial.github_com.imdea_software.swiftpaxos
