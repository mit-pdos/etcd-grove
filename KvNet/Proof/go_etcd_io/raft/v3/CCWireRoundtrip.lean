-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/CCWireRoundtrip.lean` (etc/copy-part.py; rerun it, do not edit).
module

public import KvNet.Proof.go_etcd_io.raft.v3.CCCodecLemmas
public import KvNet.Proof.google_golang_org.protobuf.proto.PbSchema

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace Perennial
namespace EtcdGrove

theorem ccWireV1_unknowns [GooseExts] (pre unknown : List w8) (m : ConfChangeM)
    (wire : ufWire ccSchema unknown) :
    ccWireAt (pre ++ unknown) (ccV1Field (pre ++ unknown)) pre.length m = some m := by
  apply ccWireAt_unknowns ccSchema ccV1Field ccV1Field_advance _ pre unknown m wire
  intro b num wt i j state hwt hr hs
  simp [Routed, ccSchema] at hr
  have h8 : num*8 + wt ≠ 8 := by omega
  have h16 : num*8 + wt ≠ 16 := by omega
  have h24 : num*8 + wt ≠ 24 := by omega
  have h34 : num*8 + wt ≠ 34 := by omega
  unfold ccV1Field
  split <;> first | omega | simp [hs]

theorem ccWireV2_unknowns [GooseExts] (pre unknown : List w8) (m : ConfChangeV2M)
    (wire : ufWire cc2Schema unknown) :
    ccWireAt (pre ++ unknown) (ccV2Field (pre ++ unknown)) pre.length m = some m := by
  apply ccWireAt_unknowns cc2Schema ccV2Field ccV2Field_advance _ pre unknown m wire
  intro b num wt i j state hwt hr hs
  simp [Routed, cc2Schema] at hr
  have h8 : num*8 + wt ≠ 8 := by omega
  have h18 : num*8 + wt ≠ 18 := by omega
  have h26 : num*8 + wt ≠ 26 := by omega
  unfold ccV2Field
  split <;> first | omega | simp [hs]

theorem ccWireSingle_unknowns [GooseExts] (pre unknown : List w8) (m : ConfChangeSingleM)
    (wire : ufWire ccsSchema unknown) :
    ccWireAt (pre ++ unknown) (ccSingleField (pre ++ unknown)) pre.length m = some m := by
  apply ccWireAt_unknowns ccsSchema ccSingleField ccSingleField_advance _ pre unknown m wire
  intro b num wt i j state hwt hr hs
  simp [Routed, ccsSchema] at hr
  have h8 : num*8 + wt ≠ 8 := by omega
  have h16 : num*8 + wt ≠ 16 := by omega
  unfold ccSingleField
  split <;> first | omega | simp [hs]

/-- Read an optional known field as written by the encoder. An absent field
leaves both the message and the cursor unchanged. -/
theorem ccWireAt_encOpt {α β : Type} (num wt : Nat) (tag : w8)
    (valid : TagOk true num wt [tag]) (hwt : wt < 8)
    (field : List w8 → Nat → Nat → α → Option (α × Nat))
    (adv : ∀ b t i m next j, field b t i m = some (next, j) → i ≤ j)
    (enc : β → List w8) (o : Option β) (put : α → β → α)
    (readValue : ∀ (v : β), o = some v → ∀ (pre rest : List w8) (m : α),
      field (pre ++ enc v ++ rest) (num*8 + wt) pre.length m =
        some (put m v, (pre ++ enc v).length))
    (pre rest : List w8) (m : α) :
    let bytes := pre ++ ccEncOpt tag enc o ++ rest
    ccWireAt bytes (field bytes) pre.length m =
      ccWireAt bytes (field bytes) (pre ++ ccEncOpt tag enc o).length ((o.map (put m)).getD m) := by
  cases o with
  | none => simp [ccEncOpt]
  | some v =>
    have ht := ccTagL_wire pre [tag] (enc v ++ rest) true num wt valid hwt
    have hval := readValue v rfl (pre ++ [tag]) rest m
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append,
      List.length_cons, List.length_nil, Nat.zero_add, Nat.add_assoc] at ht hval
    have step := ccWireAt_step (adv _) ht hval
    simpa [ccEncOpt, List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using step

/-- The known fields of an encoded change are followed by its stored extension fields. -/
def CCSingleWireEnc [GooseExts] (c : ConfChangeSingleM) (uf bytes : List w8) : Prop :=
  ∃ known, CCSingleEnc c known ∧ bytes = known ++ uf ∧ ufWire ccsSchema uf

theorem ccWireSingle_enc [GooseExts] (ty : Option w32) (nid : Option w64)
    (uf : List w8) (wire : ufWire ccsSchema uf) :
    ccWireSingle (ccEncodeSingle ty nid ++ uf) = some ⟨ty.getD (W32 0), nid.getD (W64 0)⟩ := by
  let m0 : ConfChangeSingleM := ⟨W32 0, W64 0⟩
  let e1 := ccEncOpt (W8 8) ccEnumEnc ty
  let m1 : ConfChangeSingleM := { m0 with Type' := ty.getD (W32 0) }
  let e2 := ccEncOpt (W8 16) ccVarint nid
  let m2 : ConfChangeSingleM := { m1 with NodeId' := nid.getD (W64 0) }
  have s1 := ccWireAt_encOpt 1 0 (W8 8) (by refine ⟨by decide, by decide, ?_⟩; simp [varintEnc]) (by decide)
    ccSingleField ccSingleField_advance ccEnumEnc ty (fun m a => { m with Type' := a })
    (fun a ha p r m => by simp only [ccSingleField, ccEnumL_enc p r a, List.length_append]; rfl)
    ([]) (e2 ++ uf) m0
  have u1 : (ty.map (fun a => { m0 with Type' := a })).getD m0 = m1 := by cases ty <;> rfl
  rw [u1] at s1
  have s2 := ccWireAt_encOpt 2 0 (W8 16) (by refine ⟨by decide, by decide, ?_⟩; simp [varintEnc]) (by decide)
    ccSingleField ccSingleField_advance ccVarint nid (fun m a => { m with NodeId' := a })
    (fun a ha p r m => by simp only [ccSingleField, ccVarintL_enc p r a, List.length_append]; rfl)
    (e1) (uf) m1
  have u2 : (nid.map (fun a => { m1 with NodeId' := a })).getD m1 = m2 := by cases nid <;> rfl
  rw [u2] at s2
  have fin := ccWireSingle_unknowns (e1 ++ e2) uf m2 wire
  simp only [List.nil_append, List.length_nil, List.append_assoc, List.length_append, Nat.add_assoc] at s1 s2 fin
  unfold ccWireSingle ccEncodeSingle
  simp only [List.append_assoc]
  exact s1.trans (s2.trans (fin))

theorem ccWireV1_enc [GooseExts] (id : Option w64) (ty : Option w32) (nid : Option w64) (ctx : Option (List w8))
    (hctx : ∀ c, ctx = some c → c.length < 2^64)
    (uf : List w8) (wire : ufWire ccSchema uf) :
    ccWireV1 (ccEncodeV1 id ty nid ctx ++ uf) = some ⟨ty.getD (W32 0), nid.getD (W64 0), ctx.getD [], id.getD (W64 0)⟩ := by
  let m0 : ConfChangeM := ⟨W32 0, W64 0, [], W64 0⟩
  let e1 := ccEncOpt (W8 8) ccVarint id
  let m1 : ConfChangeM := { m0 with id := id.getD (W64 0) }
  let e2 := ccEncOpt (W8 16) ccEnumEnc ty
  let m2 : ConfChangeM := { m1 with type := ty.getD (W32 0) }
  let e3 := ccEncOpt (W8 24) ccVarint nid
  let m3 : ConfChangeM := { m2 with nodeId := nid.getD (W64 0) }
  let e4 := ccEncOpt (W8 34) ccBytesEnc ctx
  let m4 : ConfChangeM := { m3 with context := ctx.getD ([]) }
  have s1 := ccWireAt_encOpt 1 0 (W8 8) (by refine ⟨by decide, by decide, ?_⟩; simp [varintEnc]) (by decide)
    ccV1Field ccV1Field_advance ccVarint id (fun m a => { m with id := a })
    (fun a ha p r m => by simp only [ccV1Field, ccVarintL_enc p r a, List.length_append]; rfl)
    ([]) (e2 ++ e3 ++ e4 ++ uf) m0
  have u1 : (id.map (fun a => { m0 with id := a })).getD m0 = m1 := by cases id <;> rfl
  rw [u1] at s1
  have s2 := ccWireAt_encOpt 2 0 (W8 16) (by refine ⟨by decide, by decide, ?_⟩; simp [varintEnc]) (by decide)
    ccV1Field ccV1Field_advance ccEnumEnc ty (fun m a => { m with type := a })
    (fun a ha p r m => by simp only [ccV1Field, ccEnumL_enc p r a, List.length_append]; rfl)
    (e1) (e3 ++ e4 ++ uf) m1
  have u2 : (ty.map (fun a => { m1 with type := a })).getD m1 = m2 := by cases ty <;> rfl
  rw [u2] at s2
  have s3 := ccWireAt_encOpt 3 0 (W8 24) (by refine ⟨by decide, by decide, ?_⟩; simp [varintEnc]) (by decide)
    ccV1Field ccV1Field_advance ccVarint nid (fun m a => { m with nodeId := a })
    (fun a ha p r m => by simp only [ccV1Field, ccVarintL_enc p r a, List.length_append]; rfl)
    (e1 ++ e2) (e4 ++ uf) m2
  have u3 : (nid.map (fun a => { m2 with nodeId := a })).getD m2 = m3 := by cases nid <;> rfl
  rw [u3] at s3
  have s4 := ccWireAt_encOpt 4 2 (W8 34) (by refine ⟨by decide, by decide, ?_⟩; simp [varintEnc]) (by decide)
    ccV1Field ccV1Field_advance ccBytesEnc ctx (fun m a => { m with context := a })
    (fun a ha p r m => by simp only [ccV1Field, ccFieldL_enc p r a (hctx a ha), List.length_append]; rfl)
    (e1 ++ e2 ++ e3) (uf) m3
  have u4 : (ctx.map (fun a => { m3 with context := a })).getD m3 = m4 := by cases ctx <;> rfl
  rw [u4] at s4
  have fin := ccWireV1_unknowns (e1 ++ e2 ++ e3 ++ e4) uf m4 wire
  simp only [List.nil_append, List.length_nil, List.append_assoc, List.length_append, Nat.add_assoc] at s1 s2 s3 s4 fin
  unfold ccWireV1 ccEncodeV1
  simp only [List.append_assoc]
  exact s1.trans (s2.trans (s3.trans (s4.trans (fin))))

theorem ccWireSingle_of [GooseExts] {c : ConfChangeSingleM} {uf bytes : List w8}
    (h : CCSingleWireEnc c uf bytes) : ccWireSingle bytes = some c := by
  obtain ⟨known, ⟨ty, nid, rfl, ht, hn⟩, rfl, hu⟩ := h
  rw [ccWireSingle_enc ty nid uf hu, ht, hn]

/-- Each nested change is read from its own length-delimited field. Repeated
fields extend the list of changes in their original order. -/
theorem ccWireV2_changes [GooseExts] (chs : List (ConfChangeSingleM × List w8)) (encs : List (List w8))
    (h : List.Forall₂ (fun ch e => CCSingleWireEnc ch.1 ch.2 e ∧ e.length < 2^64) chs encs)
    (pre rest : List w8) (m : ConfChangeV2M) :
    let bytes := pre ++ ccEncChanges encs ++ rest
    ccWireAt bytes (ccV2Field bytes) pre.length m =
      ccWireAt bytes (ccV2Field bytes) (pre ++ ccEncChanges encs).length
        {m with changes := m.changes ++ chs.map Prod.fst} := by
  induction h generalizing pre m with
  | nil => simp [ccEncChanges]
  | @cons ch e chs es hc _ ih =>
    let tag := W8 18
    let here := tag :: ccBytesEnc e
    have ht := ccTagL_wire pre [tag] (ccBytesEnc e ++ ccEncChanges es ++ rest) true 2 2
      (by refine ⟨by decide, by decide, ?_⟩; simp [varintEnc, tag]) (by decide)
    have hv := ccFieldL_enc (pre ++ [tag]) (ccEncChanges es ++ rest) e hc.2
    have hn := ccWireSingle_of hc.1
    have hs : ccV2Field (pre ++ [tag] ++ ccBytesEnc e ++ (ccEncChanges es ++ rest)) 18
        (pre ++ [tag]).length m = some ({m with changes := m.changes ++ [ch.1] },
        (pre ++ [tag]).length + (ccBytesEnc e).length) := by
      simp only [ccV2Field, hv]; change (ccWireSingle e).bind _ = _; rw [hn]; rfl
    simp only [List.append_assoc, List.length_append, List.cons_append, List.nil_append,
      List.length_cons, List.length_nil, Nat.zero_add, Nat.add_assoc] at ht hs
    have hstep := ccWireAt_step (ccV2Field_advance _) ht hs
    have htail := ih (pre ++ here) {m with changes := m.changes ++ [ch.1] }
    simp only [here, tag, ccEncChanges, List.map_cons, List.cons_append, List.append_assoc,
      List.length_append, List.length_cons, List.singleton_append, Nat.add_assoc, Nat.add_comm 1] at hstep htail ⊢
    exact hstep.trans htail

theorem ccWireV2_enc [GooseExts] (t : Option w32) (chs : List (ConfChangeSingleM × List w8))
    (encs : List (List w8)) (H : List.Forall₂ (fun ch e => CCSingleWireEnc ch.1 ch.2 e ∧ e.length < 2^64) chs encs)
    (ctx : Option (List w8)) (hctx : ∀ c, ctx = some c → c.length < 2^64)
    (uf : List w8) (wire : ufWire cc2Schema uf) :
    ccWireV2 (ccEncodeV2 t encs ctx ++ uf) = some ⟨t.getD (W32 0), chs.map Prod.fst, ctx.getD []⟩ := by
  let e1 := ccEncOpt (W8 8) ccEnumEnc t
  let e2 := ccEncChanges encs
  let e3 := ccEncOpt (W8 26) ccBytesEnc ctx
  let m0 : ConfChangeV2M := ⟨W32 0, [], []⟩
  let m1 : ConfChangeV2M := {m0 with transition := t.getD (W32 0)}
  let m2 : ConfChangeV2M := {m1 with changes := chs.map Prod.fst}
  let m3 : ConfChangeV2M := {m2 with context := ctx.getD [] }
  have s1 := ccWireAt_encOpt 1 0 (W8 8) (by refine ⟨by decide, by decide, ?_⟩; simp [varintEnc]) (by decide)
    ccV2Field ccV2Field_advance ccEnumEnc t (fun m a => {m with transition := a})
    (fun a _ p r m => by simp only [ccV2Field, ccEnumL_enc p r a, List.length_append]; rfl)
    [] (e2 ++ e3 ++ uf) m0
  have u1 : (t.map (fun a => {m0 with transition := a})).getD m0 = m1 := by cases t <;> rfl
  rw [u1] at s1
  have s2 := ccWireV2_changes chs encs H e1 (e3 ++ uf) m1
  have s3 := ccWireAt_encOpt 3 2 (W8 26) (by refine ⟨by decide, by decide, ?_⟩; simp [varintEnc]) (by decide)
    ccV2Field ccV2Field_advance ccBytesEnc ctx (fun m a => {m with context := a})
    (fun a ha p r m => by simp only [ccV2Field, ccFieldL_enc p r a (hctx a ha), List.length_append]; rfl)
    (e1 ++ e2) uf m2
  have u3 : (ctx.map (fun a => {m2 with context := a})).getD m2 = m3 := by cases ctx <;> rfl
  rw [u3] at s3
  have fin := ccWireV2_unknowns (e1 ++ e2 ++ e3) uf m3 wire
  simp only [List.nil_append, List.length_nil, List.append_assoc, List.length_append, Nat.add_assoc] at s1 s2 s3 fin
  unfold ccWireV2 ccEncodeV2
  simp only [List.append_assoc]
  exact s1.trans (s2.trans (s3.trans fin))

end EtcdGrove
end Perennial
