/-
`node.spill`'s ghost steps (`Proof/go_etcd_io/bbolt/SpillNodeCore.lean`): a written part one
more of the parts (`spPiece_step`), what `node.write` writes (`spPieceWritten_write`), and the
children's tokens after `sort.Sort` (`spSubToks_sort`, `spRtoks_sort`).
-/
module

public import Proof.go_etcd_io.bbolt.SpillNodeStep
public import Proof.go_etcd_io.bbolt.WrittenPage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- The page `pg` (id `x`) is the part `ch` written (leaf or branch). -/
def spPieceWritten (pg : List w8) (leaf : Bool) (ch : List WEntry) (x : Nat) : Prop :=
  pageId pg = x ∧ x < 2 ^ 64 ∧ pageCount pg = ch.length ∧ 0 < ch.length ∧
  (∀ i w, ch[i]? = some w → pageKey pg i = w.key) ∧
  (leaf = true → pageFlags pg = leafPageFlag ∧ leafWF pg pg.length ∧
    ∀ i w, ch[i]? = some w → leafFlags pg i = uint.nat w.flags ∧ leafValue pg i = w.value ∧
      leafKsize pg i = w.key.length) ∧
  (leaf = false → pageFlags pg = branchPageFlag ∧ branchWF pg pg.length (2 ^ 64) ∧
    ∀ i w, ch[i]? = some w → branchPgid pg i = uint.nat w.pgid ∧ branchKsize pg i = w.key.length)

theorem spMapGetD {α : Type} (ch : List WEntry) (f : WEntry → α) (d : α) (i : Nat) (w : WEntry)
    (h : ch[i]? = some w) : (ch.map f).getD i d = f w := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, h]

/-- What `node.write` writes for the inodes `ins` of the entries `ch` (to a page buffer whose
bytes after the elements and the keys and values are `rest`): the part `ch` written. -/
theorem spPieceWritten_write (leaf : Bool) (ins : List Inode) (ch : List WEntry) (rest : List w8)
    (x ov : Nat) (hx : x < 2 ^ 64) (hil : ins.length = ch.length) (hpos : 0 < ch.length)
    (hok : writeOK (ch.map WEntry.key) (ch.map WEntry.value) ins)
    (hfp : ∀ (i : Nat) (it : Inode) (w : WEntry), ins[i]? = some it → ch[i]? = some w →
      it.flags' = w.flags ∧ it.pgid' = w.pgid)
    (hs : ∀ i j, i < j → j < ch.length → go.GoStringLt (wKey ch i) (wKey ch j)) :
    spPieceWritten
      (pageBytes ({ id' := W64 (x : Int), flags' := (if leaf then W16 2 else W16 1), count' := W16 (ins.length : Int), overflow' := W32 (ov : Int) } : Page) ++
        (writtenElems leaf (ch.map WEntry.key) (ch.map WEntry.value) ins ++
          kvBytes (ch.map WEntry.key) (ch.map WEntry.value) ++ rest))
      leaf ch x := by
  let ks := ch.map WEntry.key
  let vs := ch.map WEntry.value
  let m := 16 * ins.length + kvLen ks vs ins.length
  let hdr : Page := { id' := W64 (x : Int), flags' := W16 0, count' := W16 0, overflow' := W32 (ov : Int) }
  have heq : pageBytes ({ id' := W64 (x : Int), flags' := (if leaf then W16 2 else W16 1), count' := W16 (ins.length : Int), overflow' := W32 (ov : Int) } : Page) ++
        (writtenElems leaf ks vs ins ++ kvBytes ks vs ++ rest) =
      writtenPage hdr leaf ks vs ins (List.replicate m (0 : w8) ++ rest) := by
    unfold writtenPage
    rw [List.drop_left' (by simp [m])]
  show spPieceWritten (pageBytes _ ++ (writtenElems leaf ks vs ins ++ kvBytes ks vs ++ rest)) leaf ch x
  rw [heq]
  obtain ⟨-, -, Fid, Ffl, Fc, -, Fl, Fb⟩ := writtenPage_facts hdr leaf ks vs ins (List.replicate m 0 ++ rest) hok
  have hks : ∀ i w, ch[i]? = some w → ks.getD i [] = w.key := fun i w h => spMapGetD ch _ _ i w h
  have hvs : ∀ i w, ch[i]? = some w → vs.getD i [] = w.value := fun i w h => spMapGetD ch _ _ i w h
  have hin : ∀ i w, ch[i]? = some w → ∃ it, ins[i]? = some it ∧
      ins.getD i (zero_val Inode) = it ∧ i < ins.length := by
    intro i w h
    have hi : i < ins.length := by rw [hil]; exact (List.getElem?_eq_some_iff.1 h).1
    exact ⟨ins[i], List.getElem?_eq_getElem hi, by simp [List.getD_eq_getElem?_getD, hi], hi⟩
  have hsk : ∀ i j, i < j → j < ins.length → go.GoStringLt (ks.getD i []) (ks.getD j []) := by
    intro i j hij hj
    have e : ∀ k, ks.getD k [] = wKey ch k := by
      intro k; unfold wKey; simp [ks, List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [e, e]; exact hs i j hij (by omega)
  refine ⟨?_, hx, by rw [Fc, hil], hpos, ?_, ?_, ?_⟩
  · rw [Fid]; show uint.nat (W64 (x : Int)) = x; have := hx; word
  · intro i w hw
    obtain ⟨it, -, hit, hi⟩ := hin i w hw
    unfold pageKey
    cases leaf
    · rw [Ffl]; simp only [Bool.false_eq_true, ite_false]
      rw [if_neg (by unfold branchPageFlag leafPageFlag; decide), (Fb rfl i hi).2.2.1, hks i w hw]
    · rw [Ffl]; simp only [ite_true]
      rw [(Fl rfl i hi).2.2.2.2.1, hks i w hw]
  · intro hl
    subst hl
    refine ⟨by rw [Ffl]; rfl, writtenPage_leafWF hdr ks vs ins _ hok hsk, fun i w hw => ?_⟩
    obtain ⟨it, hit', hit, hi⟩ := hin i w hw
    obtain ⟨F1, F2, -, -, -, F6⟩ := Fl rfl i hi
    refine ⟨by rw [F1, hit, (hfp i it w hit' hw).1], by rw [F6, hvs i w hw], by rw [F2, hks i w hw]⟩
  · intro hl
    subst hl
    refine ⟨by rw [Ffl]; rfl, writtenPage_branchWF hdr ks vs ins _ (2 ^ 64) hok (by omega) hsk
      (fun i _ => (ins.getD i (zero_val Inode)).pgid'.isLt), fun i w hw => ?_⟩
    obtain ⟨it, hit', hit, hi⟩ := hin i w hw
    obtain ⟨F1, -, -, F4⟩ := Fb rfl i hi
    exact ⟨by rw [F4, hit, (hfp i it w hit' hw).2], by rw [F1, hks i w hw]⟩


/-- `spPieceWritten_write`, of the page as `writtenPage` of any header with the id `x`. -/
theorem spPieceWritten_wp (hdr : Page) (leaf : Bool) (ins : List Inode) (ch : List WEntry) (rest : List w8)
    (x : Nat) (hid : uint.nat hdr.id' = x) (hx : x < 2 ^ 64) (hil : ins.length = ch.length)
    (hpos : 0 < ch.length) (hok : writeOK (ch.map WEntry.key) (ch.map WEntry.value) ins)
    (hfp : ∀ (i : Nat) (it : Inode) (w : WEntry), ins[i]? = some it → ch[i]? = some w →
      it.flags' = w.flags ∧ it.pgid' = w.pgid)
    (hs : ∀ i j, i < j → j < ch.length → go.GoStringLt (wKey ch i) (wKey ch j)) :
    spPieceWritten (writtenPage hdr leaf (ch.map WEntry.key) (ch.map WEntry.value) ins rest) leaf ch x := by
  let ks := ch.map WEntry.key
  let vs := ch.map WEntry.value
  show spPieceWritten (writtenPage hdr leaf ks vs ins rest) leaf ch x
  obtain ⟨-, -, Fid, Ffl, Fc, -, Fl, Fb⟩ := writtenPage_facts hdr leaf ks vs ins rest hok
  have hks : ∀ i w, ch[i]? = some w → ks.getD i [] = w.key := fun i w h => spMapGetD ch _ _ i w h
  have hvs : ∀ i w, ch[i]? = some w → vs.getD i [] = w.value := fun i w h => spMapGetD ch _ _ i w h
  have hin : ∀ i w, ch[i]? = some w → ∃ it, ins[i]? = some it ∧
      ins.getD i (zero_val Inode) = it ∧ i < ins.length := by
    intro i w h
    have hi : i < ins.length := by rw [hil]; exact (List.getElem?_eq_some_iff.1 h).1
    exact ⟨ins[i], List.getElem?_eq_getElem hi, by simp [List.getD_eq_getElem?_getD, hi], hi⟩
  have hsk : ∀ i j, i < j → j < ins.length → go.GoStringLt (ks.getD i []) (ks.getD j []) := by
    intro i j hij hj
    have e : ∀ k, ks.getD k [] = wKey ch k := by
      intro k; unfold wKey; simp [ks, List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [e, e]; exact hs i j hij (by omega)
  refine ⟨?_, hx, by rw [Fc, hil], hpos, ?_, ?_, ?_⟩
  · rw [Fid, hid]
  · intro i w hw
    obtain ⟨it, -, hit, hi⟩ := hin i w hw
    unfold pageKey
    cases leaf
    · rw [Ffl]; simp only [Bool.false_eq_true, ite_false]
      rw [if_neg (by unfold branchPageFlag leafPageFlag; decide), (Fb rfl i hi).2.2.1, hks i w hw]
    · rw [Ffl]; simp only [ite_true]
      rw [(Fl rfl i hi).2.2.2.2.1, hks i w hw]
  · intro hl
    subst hl
    refine ⟨by rw [Ffl]; rfl, writtenPage_leafWF hdr ks vs ins _ hok hsk, fun i w hw => ?_⟩
    obtain ⟨it, hit', hit, hi⟩ := hin i w hw
    obtain ⟨F1, F2, -, -, -, F6⟩ := Fl rfl i hi
    refine ⟨by rw [F1, hit, (hfp i it w hit' hw).1], by rw [F6, hvs i w hw], by rw [F2, hks i w hw]⟩
  · intro hl
    subst hl
    refine ⟨by rw [Ffl]; rfl, writtenPage_branchWF hdr ks vs ins _ (2 ^ 64) hok (by omega) hsk
      (fun i _ => (ins.getD i (zero_val Inode)).pgid'.isLt), fun i w hw => ?_⟩
    obtain ⟨it, hit', hit, hi⟩ := hin i w hw
    obtain ⟨F1, -, -, F4⟩ := Fb rfl i hi
    exact ⟨by rw [F4, hit, (hfp i it w hit' hw).2], by rw [F1, hks i w hw]⟩


/-- `spPieceWritten` sees only what `ownFresh` keeps of the entries. -/
theorem spPieceWritten_fresh (pg : List w8) (leaf : Bool) (ws ch : List WEntry) (x : Nat)
    (h : spPieceWritten pg leaf ws x) (he : ws.map ownFresh = ch.map ownFresh) :
    spPieceWritten pg leaf ch x := by
  have hl : ws.length = ch.length := by
    have := congrArg List.length he; simpa using this
  have hget : ∀ (i : Nat) (w : WEntry), ch[i]? = some w → ∃ w' : WEntry, ws[i]? = some w' ∧ w'.key = w.key ∧ w'.flags = w.flags ∧
      w'.value = w.value ∧ w'.pgid = w.pgid := by
    intro i w hw
    have e := congrArg (fun l => l[i]?) he
    simp only [List.getElem?_map, hw] at e
    cases hw' : ws[i]? with
    | none => rw [hw'] at e; cases e
    | some w' =>
      rw [hw'] at e
      simp only [Option.map_some, Option.some.injEq] at e
      have e1 := congrArg WEntry.key e; have e2 := congrArg WEntry.flags e
      have e3 := congrArg WEntry.value e; have e4 := congrArg WEntry.pgid e
      exact ⟨w', rfl, e1, e2, e3, e4⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, by rw [h3, hl], by rw [← hl]; exact h4, fun i w hw => ?_, fun hlf => ?_, fun hlf => ?_⟩
  · obtain ⟨w', hw', e, -⟩ := hget i w hw; rw [h5 i w' hw', e]
  · obtain ⟨a, b, c⟩ := h6 hlf
    refine ⟨a, b, fun i w hw => ?_⟩
    obtain ⟨w', hw', ek, ef, ev, -⟩ := hget i w hw
    obtain ⟨c1, c2, c3⟩ := c i w' hw'
    exact ⟨by rw [c1, ef], by rw [c2, ev], by rw [c3, ek]⟩
  · obtain ⟨a, b, c⟩ := h7 hlf
    refine ⟨a, b, fun i w hw => ?_⟩
    obtain ⟨w', hw', ek, -, -, ep⟩ := hget i w hw
    obtain ⟨c1, c2⟩ := c i w' hw'
    exact ⟨by rw [c1, ep], by rw [c2, ek]⟩

end pure

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `wtreeQ_branch`, with the branch's page and its children's trees' pages among `P'`. -/
theorem spWtreeQ_branchP (γ : GName) (P' : GMap Nat (List w8)) (x : Nat) (pg : List w8)
    (lo hi : Option (List w8)) (kind h : Nat) (hf : pageFlags pg = branchPageFlag)
    (hn : 2 ≤ pageCount pg) (hid : pageId pg = x) (hx : x < 2 ^ 64)
    (hwf : branchWF pg pg.length (2 ^ 64)) (hks : ∀ i < pageCount pg, 0 < branchKsize pg i)
    (hin : ∀ i < pageCount pg, keyIn lo hi (branchKey pg i)) (hxP : P' !! x = some pg) :
    (x ↪[γ] () : IProp GF) ∗
      ([∗list] i ∈ List.range (pageCount pg), ∃ Q cpg H,
        ⌜Q ⊆ P' ∧ Q !! branchPgid pg i = some cpg ∧ 0 < pageCount cpg ∧ pageFlags cpg = kind ∧
          pageKey cpg 0 = branchKey pg i ∧ hiLe H (childHi hi (branchKey pg) (pageCount pg) i) ∧
          qHt Q (branchPgid pg i) h⌝ ∗
        wtreeQ γ Q (branchPgid pg i) (some (branchKey pg i)) H) ⊢
    ∃ Q, ⌜Q ⊆ P' ∧ Q !! x = some pg ∧ qHt Q x (h + 1)⌝ ∗ wtreeQ γ Q x lo hi := by
  iintro ⟨Hx, Hl⟩
  ihave Hl := (BigSepL.bigSepL_mono (PROP := IProp GF)
    (Ψ := fun _ i => iprop(∃ t : GMap Nat (List w8) × List w8 × Option (List w8),
      ⌜brFact pg hi kind h i t ∧ t.1 ⊆ P'⌝ ∗ pgToks γ t.1)) ?_) $$ Hl
  · intro k i _
    iintro ⟨%Q, %cpg, %H, %hc, HQ⟩
    unfold wtreeQ
    icases HQ with ⟨HQ, %hw⟩
    iexists (Q, cpg, H)
    iframe
    ipureintro
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hc
    exact ⟨⟨h1, h2, h3, h4, h5, hw.1, h6⟩, h0⟩
  ihave Hl := bigSepL_range_choose ((∅ : GMap Nat (List w8)), ([] : List w8), (none : Option (List w8)))
    (fun i t => iprop(⌜brFact pg hi kind h i t ∧ t.1 ⊆ P'⌝ ∗ pgToks (GF := GF) γ t.1)) (pageCount pg) $$ Hl
  icases Hl with ⟨%f, Hl⟩
  icases bigSepL_range_pure (fun i => brFact pg hi kind h i (f i) ∧ (f i).1 ⊆ P')
    (fun i => pgToks (GF := GF) γ (f i).1) (pageCount pg) $$ Hl with ⟨%hfs2, Hl⟩
  have hfs : ∀ i < pageCount pg, brFact pg hi kind h i (f i) := fun i hi' => (hfs2 i hi').1
  icases toks_page γ x pg (fun i => (f i).1) (pageCount pg) $$ [Hx Hl] with ⟨%hd, Ht⟩
  · iframe
  have hch : ∀ i, ∃ p : Nat → Nat, i < pageCount pg →
      pageHts (f i).1 p ∧ p (branchPgid pg i) = h := by
    intro i
    by_cases hi' : i < pageCount pg
    · obtain ⟨p, hp, hpv⟩ := (hfs i hi').2.2.2.2.2.2
      exact ⟨p, fun _ => ⟨hp, hpv⟩⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' hi'⟩
  have hq : qHt (pageU x pg (fun i => (f i).1) (pageCount pg)) x (h + 1) :=
    hts_pageU x pg (fun i => (f i).1) (pageCount pg) (h + 1) (fun i => Classical.choose (hch i))
      hd.1 hd.2 (fun i hi' => (Classical.choose_spec (hch i) hi').1)
      (fun i hi' => wtreeF0_closed _ _ _ _ (hfs i hi').2.2.2.2.2.1)
      (fun hl => by rw [hf] at hl; exact absurd hl (by unfold branchPageFlag leafPageFlag; decide))
      (fun _ j hj => ⟨j, hj, by rw [(hfs j hj).1]; rfl,
        by rw [(Classical.choose_spec (hch j) hj).2]⟩)
  iexists (pageU x pg (fun i => (f i).1) (pageCount pg))
  isplitr
  · ipureintro
    refine ⟨fun id v hv => ?_, pageU_x _ _ _ _, hq⟩
    rcases pageU_some x pg _ _ id v hv with ⟨rfl, rfl⟩ | ⟨i, hi', hv'⟩
    · exact hxP
    · exact (hfs2 i hi').2 id v hv'
  unfold wtreeQ
  iframe
  ipureintro
  exact ⟨wtreeF0_branch x pg lo hi kind (fun i => (f i).1) (fun i => (f i).2.2) hf hn hid hx hwf hks hin
    (fun i hi' => ⟨(f i).2.1, (hfs i hi').1, (hfs i hi').2.1, (hfs i hi').2.2.1, (hfs i hi').2.2.2.1⟩)
    (fun i hi' => (hfs i hi').2.2.2.2.1) (fun i hi' => (hfs i hi').2.2.2.2.2.1) hd.1 hd.2, _, hq⟩

theorem spEmpty_sub (P' : GMap Nat (List w8)) : (∅ : GMap Nat (List w8)) ⊆ P' := by
  intro k v h; simp at h

/-- `wtreeQ_leaf`, with the leaf's page and its nested buckets' trees' pages among `P'`. -/
theorem spWtreeQ_leafP (γ : GName) (P' : GMap Nat (List w8)) (x : Nat) (pg : List w8)
    (lo hi : Option (List w8)) (hf : pageFlags pg = leafPageFlag) (hid : pageId pg = x)
    (hx : x < 2 ^ 64) (hwf : leafWF pg pg.length) (hks : ∀ i < pageCount pg, 0 < leafKsize pg i)
    (hin : ∀ i < pageCount pg, keyIn lo hi (leafKey pg i)) (hxP : P' !! x = some pg) :
    (x ↪[γ] () : IProp GF) ∗
      ([∗list] i ∈ List.range (pageCount pg),
        if leafFlags pg i % 2 = bucketLeafFlag then wbktQP γ P' (leafValue pg i) else emp) ⊢
    ∃ Q, ⌜Q ⊆ P' ∧ Q !! x = some pg ∧ qHt Q x 0⌝ ∗ wtreeQ γ Q x lo hi := by
  iintro ⟨Hx, Hl⟩
  ihave Hl := (BigSepL.bigSepL_mono (PROP := IProp GF)
    (Ψ := fun _ i => iprop(∃ Q : GMap Nat (List w8), ⌜lfFact pg i Q ∧ Q ⊆ P'⌝ ∗ pgToks γ Q)) ?_) $$ Hl
  · intro k i _
    by_cases hfi : leafFlags pg i % 2 = bucketLeafFlag
    · rw [if_pos hfi]
      unfold wbktQP
      by_cases hr : inBucketRoot (leafValue pg i) = 0
      · rw [if_pos hr]
        iintro ⟨%hlen, %hig⟩
        iexists (∅ : GMap Nat (List w8))
        isplitr
        · ipureintro
          exact ⟨⟨fun _ => ⟨hlen, fun _ => hig⟩, fun h => absurd hr h.2, fun _ => rfl⟩, spEmpty_sub P'⟩
        · iapply pgToks_emptyT
      · rw [if_neg hr]
        iintro ⟨%hlen, %Q, %hQ, HQ⟩
        unfold wtreeQ
        icases HQ with ⟨HQ, %hw⟩
        iexists Q
        iframe
        ipureintro
        exact ⟨⟨fun _ => ⟨hlen, fun h => absurd h hr⟩, fun _ => hw, fun h => absurd ⟨hfi, hr⟩ h⟩, hQ⟩
    · rw [if_neg hfi]
      iintro _
      iexists (∅ : GMap Nat (List w8))
      isplitr
      · ipureintro
        exact ⟨⟨fun h => absurd h hfi, fun h => absurd h.1 hfi, fun _ => rfl⟩, spEmpty_sub P'⟩
      · iapply pgToks_emptyT
  ihave Hl := bigSepL_range_choose (∅ : GMap Nat (List w8))
    (fun i Q => iprop(⌜lfFact pg i Q ∧ Q ⊆ P'⌝ ∗ pgToks (GF := GF) γ Q)) (pageCount pg) $$ Hl
  icases Hl with ⟨%f, Hl⟩
  icases bigSepL_range_pure (fun i => lfFact pg i (f i) ∧ f i ⊆ P') (fun i => pgToks (GF := GF) γ (f i))
    (pageCount pg) $$ Hl with ⟨%hfs2, Hl⟩
  have hfs : ∀ i < pageCount pg, lfFact pg i (f i) := fun i hi' => (hfs2 i hi').1
  icases toks_page γ x pg f (pageCount pg) $$ [Hx Hl] with ⟨%hd, Ht⟩
  · iframe
  have hch : ∀ i, ∃ p : Nat → Nat, i < pageCount pg → pageHts (f i) p ∧
      ∀ id v, f i !! id = some v → pageFlags v = branchPageFlag →
        ∀ j < pageCount v, (f i !! branchPgid v j).isSome := by
    intro i
    by_cases hi' : i < pageCount pg
    · by_cases hn : leafFlags pg i % 2 = bucketLeafFlag ∧ inBucketRoot (leafValue pg i) ≠ 0
      · have hw := (hfs i hi').2.1 hn
        obtain ⟨-, p, hp, -⟩ := hw.2
        exact ⟨p, fun _ => ⟨hp, wtreeF0_closed _ _ _ _ hw.1⟩⟩
      · have he := (hfs i hi').2.2 hn
        refine ⟨fun _ => 0, fun _ => ⟨fun id v hv => ?_, fun id v hv => ?_⟩⟩ <;>
          rw [he] at hv <;> simp at hv
    · exact ⟨fun _ => 0, fun h' => absurd h' hi'⟩
  have hq : qHt (pageU x pg f (pageCount pg)) x 0 :=
    hts_pageU x pg f (pageCount pg) 0 (fun i => Classical.choose (hch i))
      hd.1 hd.2 (fun i hi' => (Classical.choose_spec (hch i) hi').1)
      (fun i hi' => (Classical.choose_spec (hch i) hi').2)
      (fun _ => rfl)
      (fun hb => by rw [hf] at hb; exact absurd hb (by unfold branchPageFlag leafPageFlag; decide))
  iexists (pageU x pg f (pageCount pg))
  isplitr
  · ipureintro
    refine ⟨fun id v hv => ?_, pageU_x _ _ _ _, hq⟩
    rcases pageU_some x pg _ _ id v hv with ⟨rfl, rfl⟩ | ⟨i, hi', hv'⟩
    · exact hxP
    · exact (hfs2 i hi').2 id v hv'
  unfold wtreeQ
  iframe
  ipureintro
  exact ⟨wtreeF0_leaf x pg lo hi f hf hid hx hwf hks hin (fun i hi' => (hfs i hi').1)
    (fun i hi' => ⟨fun hn => ((hfs i hi').2.1 hn).1, (hfs i hi').2.2⟩) hd.1 hd.2, _, hq⟩

theorem spSepL_toRange {A : Type} (Φ : Nat → A → IProp GF) (Ψ : Nat → IProp GF) (l : List A)
    (h : ∀ i w, l[i]? = some w → Φ i w ⊢ Ψ i) :
    ([∗list] i ↦ w ∈ l, Φ i w) ⊢ [∗list] i ∈ List.range l.length, Ψ i := by
  induction l generalizing Φ Ψ with
  | nil => simp only [List.length_nil, List.range_zero]; exact .rfl
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map]
    refine (BigSepL.bigSepL_cons (PROP := IProp GF)).1.trans ?_
    refine .trans ?_ (BigSepL.bigSepL_cons (PROP := IProp GF)).2
    refine sep_mono (h 0 a rfl) ?_
    rw [BigSepL.bigSepL_map]
    exact ih (fun i w => Φ (i + 1) w) (fun i => Ψ (i + 1)) (fun i w hw => h (i + 1) w (by simpa using hw))

theorem spFlags_odd (f : w32) (h : uint.nat f % 2 = bucketLeafFlag) : ¬ (f &&& W32 1 = W32 0) := by
  intro e
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_and] at this
  unfold bucketLeafFlag at h
  have h1 : (W32 1).toNat = 1 := rfl
  have h0 : (W32 0).toNat = 0 := rfl
  rw [h1, h0, Nat.and_one_is_mod] at this
  have : uint.nat f % 2 = f.toNat % 2 := rfl
  omega

/-- A written part's page (its token), its entries' trees: the part's written tree. -/
theorem spPiece_new (γ : GName) (P P' : GMap Nat (List w8)) (B : BRec) (leaf : Bool)
    (kind h ch0 : Nat) (pg : List w8) (ch : List WEntry) (x : Nat) (lo hi : Option (List w8))
    (hPP : P ⊆ P') (hpg : P' !! x = some pg) (hw : spPieceWritten pg leaf ch x)
    (hh : (leaf = true → h = 0) ∧ (leaf = false → h = ch0 + 1))
    (hk : ∀ w ∈ ch, 0 < w.key.length ∧ keyIn lo hi w.key)
    (hbr : leaf = false → 2 ≤ ch.length ∧ ∀ w ∈ ch, B.nm !! w.pgid = none) :
    (x ↪[γ] () : IProp GF) ∗ ([∗list] i ↦ w ∈ ch, entRes γ P B hi leaf kind ch0 ch i w) ⊢
    ∃ Q, ⌜Q ⊆ P' ∧ Q !! x = some pg ∧ qHt Q x h⌝ ∗ wtreeQ γ Q x lo hi := by
  obtain ⟨hid, hx, hpc, hcl, hkey, hlf, hbf⟩ := hw
  have hget : ∀ i < ch.length, ∃ w, ch[i]? = some w :=
    fun i hi' => ⟨ch[i], List.getElem?_eq_getElem hi'⟩
  cases leaf
  · obtain ⟨hf, hwf, hbp⟩ := hbf rfl
    have hbk : ∀ i w, ch[i]? = some w → branchKey pg i = w.key := by
      intro i w hwi
      have := hkey i w hwi
      unfold pageKey at this
      rw [hf, if_neg (by unfold branchPageFlag leafPageFlag; decide)] at this
      exact this
    have hchi : ∀ i, childHi hi (branchKey pg) ch.length i = childHi hi (wKey ch) ch.length i := by
      intro i
      unfold childHi
      by_cases hlt : i + 1 < ch.length
      · rw [if_pos hlt, if_pos hlt]
        obtain ⟨w', hw'⟩ := hget (i + 1) hlt
        rw [hbk _ _ hw']; unfold wKey; rw [hw']; rfl
      · rw [if_neg hlt, if_neg hlt]
    obtain ⟨hc2, hnm⟩ := hbr rfl
    have hT := spWtreeQ_branchP (GF := GF) γ P' x pg lo hi kind ch0 hf (by rw [hpc]; exact hc2) hid hx hwf
      (fun i hi' => by
        obtain ⟨w, hwi⟩ := hget i (by rw [← hpc]; exact hi')
        rw [(hbp i w hwi).2]; exact (hk w (List.mem_of_getElem? hwi)).1)
      (fun i hi' => by
        obtain ⟨w, hwi⟩ := hget i (by rw [← hpc]; exact hi')
        rw [hbk i w hwi]; exact (hk w (List.mem_of_getElem? hwi)).2) hpg
    rw [hpc] at hT
    rw [hh.2 rfl]
    iintro ⟨Hx, Hl⟩
    iapply hT
    iframe Hx
    iapply spSepL_toRange _ _ ch ?_ $$ Hl
    intro i w hwi
    unfold entRes
    simp only [Bool.false_eq_true, ite_false]
    rw [if_pos (hnm w (List.mem_of_getElem? hwi)), (hbp i w hwi).1, hbk i w hwi, hchi i]
    iintro ⟨%Q, %cpg, %H, %hc, Ht⟩
    iexists Q, cpg, H
    isplitr
    · ipureintro
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hc
      exact ⟨GMap.map_subseteq_trans h1 hPP, h2, h3, h4, h5, h6, h7⟩
    · iexact Ht
  · obtain ⟨hf, hwf, hlp⟩ := hlf rfl
    have hlk : ∀ i w, ch[i]? = some w → leafKey pg i = w.key := by
      intro i w hwi
      have := hkey i w hwi
      unfold pageKey at this
      rw [hf, if_pos rfl] at this
      exact this
    have hT := spWtreeQ_leafP (GF := GF) γ P' x pg lo hi hf hid hx hwf
      (fun i hi' => by
        obtain ⟨w, hwi⟩ := hget i (by rw [← hpc]; exact hi')
        rw [(hlp i w hwi).2.2]; exact (hk w (List.mem_of_getElem? hwi)).1)
      (fun i hi' => by
        obtain ⟨w, hwi⟩ := hget i (by rw [← hpc]; exact hi')
        rw [hlk i w hwi]; exact (hk w (List.mem_of_getElem? hwi)).2) hpg
    rw [hpc] at hT
    rw [hh.1 rfl]
    iintro ⟨Hx, Hl⟩
    iapply hT
    iframe Hx
    iapply spSepL_toRange _ _ ch ?_ $$ Hl
    intro i w hwi
    unfold entRes
    simp only [ite_true]
    rw [(hlp i w hwi).1, (hlp i w hwi).2.1]
    by_cases hb : uint.nat w.flags % 2 = bucketLeafFlag
    · rw [if_pos hb, if_neg (spFlags_odd w.flags hb)]
      exact wbktQP_mono γ P P' hPP w.value
    · rw [if_neg hb]
      by_cases hb' : w.flags &&& W32 1 = W32 0
      · rw [if_pos hb']
      · rw [if_neg hb']
        iintro _
        iempintro

/-- A part written: its page (with the part's entries' trees, the next chunk's tokens) one
more of the parts. -/
theorem spPiece_step (pos : Prop) (γ : GName) (P P' : GMap Nat (List w8)) (B B' : BRec) (leaf : Bool)
    (kind h kd ch0 : Nat) (chs : List (List WEntry)) (hi : Option (List w8))
    (ps : List (w64 × List w8)) (p : w64 × List w8) (pg : List w8) (ch : List WEntry) (x : Nat)
    (hPP : P ⊆ P') (hnm : B'.nm = B.nm) (hch : chs[ps.length]? = some ch) (hx : uint.nat p.1 = x)
    (hpg : P' !! x = some pg) (hw : spPieceWritten pg leaf ch x) (hp2 : p.2 = (wHead ch).key)
    (hkind : kind = if leaf then leafPageFlag else branchPageFlag)
    (hh : (leaf = true → h = 0) ∧ (leaf = false → h = ch0 + 1))
    (hk : ∀ w ∈ ch, 0 < w.key.length ∧ keyIn (some p.2) (hiAt chs hi ps.length) w.key)
    (hbr : leaf = false → 2 ≤ ch.length ∧ ∀ w ∈ ch, B.nm !! w.pgid = none) :
    pieceResP (GF := GF) pos γ P kind h ps (hiAt chs hi (ps.length - 1)) ∗
      chunkToks γ P B leaf kd ch0 chs hi ps.length ∗ (x ↪[γ] () : IProp GF) ⊢
    pieceResP pos γ P' kind h (ps ++ [p]) (hiAt chs hi ((ps ++ [p]).length - 1)) ∗
      chunkToks γ P' B' leaf kd ch0 chs hi (ps ++ [p]).length := by
  have hcl : 0 < ch.length := hw.2.2.2.1
  have hpc : pageCount pg = ch.length := hw.2.2.1
  have hfl : pageFlags pg = kind := by
    rw [hkind]
    cases leaf
    · exact (hw.2.2.2.2.2.2 rfl).1
    · exact (hw.2.2.2.2.2.1 rfl).1
  have hch0 : ch[0]? = some (wHead ch) := by
    unfold wHead
    cases ch with
    | nil => simp at hcl
    | cons a l => rfl
  have hk0 : pageKey pg 0 = p.2 := by rw [hw.2.2.2.2.1 0 _ hch0, hp2]
  have hlen : (ps ++ [p]).length = ps.length + 1 := by simp
  have hpn : pieceHi (ps ++ [p]) (hiAt chs hi ((ps ++ [p]).length - 1)) ps.length =
      hiAt chs hi ps.length := by
    unfold pieceHi
    rw [List.getElem?_eq_none (by rw [hlen]; omega), hlen, Nat.add_sub_cancel]
  have hpo : ∀ j, j < ps.length → pieceHi ps (hiAt chs hi (ps.length - 1)) j =
      pieceHi (ps ++ [p]) (hiAt chs hi ((ps ++ [p]).length - 1)) j := by
    intro j hj
    unfold pieceHi
    by_cases hj1 : j + 1 < ps.length
    · rw [List.getElem?_append_left hj1, List.getElem?_eq_getElem hj1]
    · have e : j + 1 = ps.length := by omega
      rw [List.getElem?_eq_none (by omega : ps.length ≤ j + 1), e,
        List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      simp only [List.getElem?_cons_zero]
      unfold hiAt
      rw [show ps.length - 1 + 1 = ps.length by omega, hch, hp2]
  rw [hlen] at hpo hpn
  unfold chunkToks pieceResP
  rw [drop_cons_of_get chs ps.length ch hch, hlen]
  iintro ⟨Hps, Hcs, Htok⟩
  icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ Hcs with ⟨Hc, Hcs⟩
  icases spPiece_new γ P P' B leaf kd h ch0 pg ch x (some p.2) (hiAt chs hi (ps.length + 0)) hPP hpg hw
    hh hk hbr $$ [Htok Hc] with ⟨%Q, %hQ, Hq⟩
  · iframe
  isplitl [Hps Hq]
  · iapply (BigSepL.bigSepL_snoc (PROP := IProp GF)).2
    isplitl [Hps]
    · iapply (BigSepL.bigSepL_mono (PROP := IProp GF) ?_) $$ Hps
      intro j q hj
      have hjl : j < ps.length := (List.getElem?_eq_some_iff.1 hj).1
      rw [← hpo j hjl]
      iintro ⟨%Q', %pg', %hq', Ht⟩
      iexists Q', pg'
      isplitr
      · ipureintro
        obtain ⟨h1, h2⟩ := hq'
        exact ⟨GMap.map_subseteq_trans h1 hPP, h2⟩
      · iexact Ht
    · iexists Q, pg
      rw [hpn, hx]
      isplitr
      · ipureintro
        exact ⟨hQ.1, hQ.2.1, fun _ => by rw [hpc]; exact hcl, hfl, fun _ => hk0, hQ.2.2⟩
      · iexact Hq
  · iapply (BigSepL.bigSepL_mono (PROP := IProp GF) ?_) $$ Hcs
    intro j c _
    refine BigSepL.bigSepL_mono_of_forall (fun {i w} => ?_)
    rw [show ps.length + (j + 1) = ps.length + 1 + j by omega]
    exact entRes_move γ P P' B B' hPP hnm _ _ leaf kd ch0 c c i i w w rfl rfl rfl rfl (fun _ h => h)

/-- The children's tokens (`node.spill.wp_core`'s precondition) as the children loop starts:
the children sorted to `ys`. -/
theorem spSubToks_sort (γ : GName) (P P' : GMap Nat (List w8)) (B : BRec) (n : Loc) (r : NRec)
    (ys : List Loc) (bnd : Loc → Option (List w8) × Option (List w8)) (kd ht : Loc → Nat)
    (sp : Loc → Bool) (sub : Loc → List Loc) (hP : P' = P) (hperm : ys.Perm r.cs)
    (hns : ∀ c ∈ r.cs, n ∉ sub c) :
    ([∗list] c ∈ r.cs, (if sp c then emp else
        [∗list] l ∈ sub c, ∃ rl, ⌜B.ns !! l = some rl⌝ ∗ rtoks (GF := GF) γ P B (bnd l) (kd l) (ht l - 1) rl)) ⊢
      subToks γ P' (setN B n { r with cs := ys }) bnd kd ht sp sub (ys.drop 0) := by
  subst hP
  unfold subToks
  rw [List.drop_zero]
  refine .trans (BigSepL.bigSepL_mono (fun {k c} hk => ?_)) (BigSepL.bigSepL_perm hperm).2
  have hc : c ∈ r.cs := List.mem_of_getElem? hk
  by_cases hs : sp c
  · simp only [hs, ite_true]; exact .rfl
  · simp only [hs, Bool.false_eq_true, ite_false]
    refine BigSepL.bigSepL_mono (fun {j l} hj => ?_)
    have hl : l ≠ n := fun e => hns c hc (e ▸ List.mem_of_getElem? hj)
    iintro ⟨%rl, %hrl, Hr⟩
    iexists rl
    isplitr
    · ipureintro
      show (<[n := { r with cs := ys }]> B.ns) !! l = some rl
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hl)]; exact hrl
    · have e : rtoks (GF := GF) γ P' B (bnd l) (kd l) (ht l - 1) rl ⊢
          rtoks γ P' (setN B n { r with cs := ys }) (bnd l) (kd l) (ht l - 1) rl := .rfl
      iapply e; iexact Hr

/-- A node's tokens, its children sorted to `ys`. -/
theorem spRtoks_sort (γ : GName) (P P' : GMap Nat (List w8)) (B : BRec) (n : Loc) (r : NRec)
    (ys : List Loc) (b : Option (List w8) × Option (List w8)) (kind ch0 : Nat) (hP : P' = P) :
    rtoks (GF := GF) γ P B b kind ch0 r ⊢
      rtoks γ P' (setN B n { r with cs := ys }) b kind ch0 { r with cs := ys } := by
  subst hP
  exact .rfl

/-- The bucket's root written as an empty leaf (its only part, no parent: `¬ pos`). -/
theorem spPiece_empty (pos : Prop) (hpos : ¬ pos) (γ : GName) (P P' : GMap Nat (List w8)) (B B' : BRec)
    (kind h kd ch0 : Nat) (hi : Option (List w8)) (p : w64 × List w8) (pg : List w8) (x : Nat)
    (hx : uint.nat p.1 = x) (hpg : P' !! x = some pg) (hf : pageFlags pg = leafPageFlag)
    (hid : pageId pg = x) (hx64 : x < 2 ^ 64) (hwf : leafWF pg pg.length) (hcnt : pageCount pg = 0)
    (hkind : kind = leafPageFlag) (hh : h = 0) :
    pieceResP (GF := GF) pos γ P kind h [] (hiAt [[]] hi (([] : List (w64 × List w8)).length - 1)) ∗
      chunkToks γ P B true kd ch0 [[]] hi ([] : List (w64 × List w8)).length ∗ (x ↪[γ] () : IProp GF) ⊢
    pieceResP pos γ P' kind h [p] (hiAt [[]] hi ([p].length - 1)) ∗
      chunkToks γ P' B' true kd ch0 [[]] hi [p].length := by
  unfold chunkToks pieceResP
  iintro ⟨-, -, Htok⟩
  icases spWtreeQ_leafP γ P' x pg (some p.2) (pieceHi [p] (hiAt [[]] hi ([p].length - 1)) 0) hf hid hx64 hwf
    (by rw [hcnt]; intro i hi; omega) (by rw [hcnt]; intro i hi; omega) hpg $$ [Htok] with ⟨%Q, %hQ, Hq⟩
  · rw [hcnt, List.range_zero]
    iframe
    iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hq]
  · iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
    isplitl [Hq]
    · iexists Q, pg
      rw [hx]
      isplitr
      · ipureintro
        exact ⟨hQ.1, hQ.2.1, fun h => absurd h hpos, by rw [hf, hkind], fun h => absurd h hpos,
          by rw [hh]; exact hQ.2.2⟩
      · iexact Hq
    · iapply BigSepL.bigSepL_nil.2; iempintro
  · rw [show List.drop [p].length [[]] = ([] : List (List WEntry)) from rfl]
    iapply BigSepL.bigSepL_nil.2; iempintro

end own

end bbolt
end EtcdGrove
end Perennial
