/-
Lemmas about a writer's cursor (`WriteCursor.lean`): the positions a search reaches in a clean
bucket, and the bytes of a position's page, lent out of the view or the inline page.
-/
module

public import Proof.go_etcd_io.bbolt.WriteCursor
public import Proof.go_etcd_io.bbolt.WriteTxLemmas
public import Spec.go_etcd_io.bbolt.Cursor__keyValue_w

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

theorem treeHas_child (pages : GMap Nat (List w8)) (id : Nat) (pg : List w8)
    (hpg : pages !! id = some pg) (hb : pageFlags pg = branchPageFlag) (i : Nat)
    (hi : i < pageCount pg) (d : Nat) (h : treeHas pages (branchPgid pg i) d) :
    treeHas pages id d :=
  treeHas.sub id pg d hpg (pageHas.child pg i d hb hi h)

theorem treeHas_self (pages : GMap Nat (List w8)) (id : Nat) (pg : List w8)
    (hpg : pages !! id = some pg) : treeHas pages id id := treeHas.root id pg hpg

theorem uint_nat_W64 (n : Nat) (h : n < 2 ^ 64) : uint.nat (W64 (n : Int)) = n := by
  unfold uint.nat; word

theorem branchPgid_lt (pg : List w8) (i : Nat) : branchPgid pg i < 2 ^ 64 := leAt_lt _ _ 8

/-- The page of a non-inline page position. -/
theorem posOK_page (W : WView) (hwm : Nat) (B : BRec) (pid : w64) (hr : B.ib.root' ≠ W64 0)
    (hres : resolve B pid = none) (h : posOK W hwm B pid) :
    ∃ pg, W.pages !! uint.nat pid = some pg ∧
      wpageAt W B pid = some (W.data +ₗ ((uint.nat pid * W.ps : Nat) : Int), pg) ∧
      treeWF W.pages hwm (uint.nat pid) ∧
      (∀ d, treeHas W.pages (uint.nat pid) d → B.nm !! W64 (d : Int) = none) := by
  rcases h.2 with ⟨l, r, h1, -⟩ | ⟨-, ⟨h0, -⟩ | ⟨-, hwf, hfree⟩⟩
  · rw [hres] at h1; cases h1
  · exact absurd h0 hr
  · cases hwf with
    | page _ pg _ hpg _ _ =>
      refine ⟨pg, hpg, ?_, ?_, hfree⟩
      · unfold wpageAt; rw [if_neg hr, hpg]; rfl
      · exact treeWF.page _ pg ‹_› hpg ‹_› ‹_›

/-- A branch page's children are page positions. -/
theorem posOK_page_child (W : WView) (hwm : Nat) (B : BRec) (pid : w64) (pg : List w8)
    (hr : B.ib.root' ≠ W64 0) (hpg : W.pages !! uint.nat pid = some pg)
    (hb : pageFlags pg = branchPageFlag) (hwf : ∀ i < pageCount pg, treeWF W.pages hwm (branchPgid pg i))
    (hfree : ∀ d, treeHas W.pages (uint.nat pid) d → B.nm !! W64 (d : Int) = none)
    (i : Nat) (hi : i < pageCount pg) :
    posOK W hwm B (W64 (branchPgid pg i : Int)) := by
  have hl := branchPgid_lt pg i
  refine ⟨fun h => absurd h hr, Or.inr ?_⟩
  refine ⟨?_, Or.inr ⟨hr, ?_, ?_⟩⟩
  · unfold resolve; rw [if_neg hr]
    have := hfree _ (treeHas_child _ _ pg hpg hb i hi _ (by
      cases hwf i hi with
      | page _ pg' _ hpg' _ _ => exact treeHas_self _ _ pg' hpg'))
    exact this
  · rw [uint_nat_W64 _ hl]; exact hwf i hi
  · intro d hd
    rw [uint_nat_W64 _ hl] at hd
    exact hfree d (treeHas_child _ _ pg hpg hb i hi d hd)

/-- A branch node's children are positions of a clean bucket. -/
theorem posOK_node_child (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (nl : Loc) (r : NRec)
    (hc : bktClean W hwm bl B) (hr : B.ns !! nl = some r) (hb : r.nv.isLeaf' = false)
    (i : Nat) (w : WEntry) (hw : r.ws[i]? = some w) : posOK W hwm B w.pgid := by
  obtain ⟨-, -, -, -, -, -, hleafs, hnodes, -, hfree⟩ := hc
  have hroot : B.ib.root' ≠ W64 0 := by
    intro h0; have := hleafs h0 nl r hr; rw [hb] at this; cases this
  have hn := hnodes nl r hr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hbr, -⟩ := hn
  obtain ⟨-, -, hkids⟩ := hbr hb
  obtain ⟨-, hsome, hnone⟩ := hkids w (List.mem_of_getElem? hw)
  cases hk : B.nm !! w.pgid with
  | some l' =>
    obtain ⟨r', hr', -⟩ := hsome l' hk
    refine ⟨fun h => absurd h hroot, Or.inl ?_⟩
    exact ⟨l', r', by unfold resolve; rw [if_neg hroot]; exact hk, hr'⟩
  | none =>
    refine ⟨fun h => absurd h hroot, Or.inr ?_⟩
    refine ⟨by unfold resolve; rw [if_neg hroot]; exact hk, Or.inr ⟨hroot, hnone hk, ?_⟩⟩
    exact hfree nl i w.pgid ⟨r, w, hr, hb, hw, rfl, hk⟩

/-- A page of a well-formed tree: its header, and a leaf or a branch whose children's trees are
well-formed. -/
theorem treeWF_page (pages : GMap Nat (List w8)) (hwm id : Nat) (pg : List w8)
    (h : treeWF pages hwm id) (hpg : pages !! id = some pg) :
    16 ≤ pg.length ∧ pageId pg = id ∧ id < hwm ∧
    ((pageFlags pg = leafPageFlag ∧ leafWF pg pg.length ∧
        ∀ i < pageCount pg, leafFlags pg i % 2 = bucketLeafFlag → bucketWF pages hwm (leafValue pg i)) ∨
     (pageFlags pg = branchPageFlag ∧ branchWF pg pg.length hwm ∧
        ∀ i < pageCount pg, treeWF pages hwm (branchPgid pg i))) := by
  cases h with
  | page _ pg' hlt hpg' hid hpt =>
    rw [hpg] at hpg'; cases hpg'
    cases hpt with
    | leaf _ _ hfl hw hb =>
      refine ⟨?_, hid, hlt, Or.inl ⟨hfl, hw, hb⟩⟩
      have := hw.2.1; unfold elemOff at this; omega
    | branch _ _ hfl hw hk =>
      refine ⟨?_, hid, hlt, Or.inr ⟨hfl, hw, hk⟩⟩
      have := hw.2.2.1; unfold elemOff at this; omega

theorem validPageFlags_of (pg : List w8)
    (h : pageFlags pg = leafPageFlag ∨ pageFlags pg = branchPageFlag) :
    validPageFlags (W16 (pageFlags pg : Int)) := by
  rcases h with h | h <;> rw [h] <;> unfold validPageFlags <;> decide

/-- The root of a clean bucket is a position. -/
theorem posOK_root (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B) :
    posOK W hwm B B.ib.root' := by
  obtain ⟨hinl, hfile, hempty, hrootn, hnm, -, -, -, -, -⟩ := hc
  refine ⟨fun h => h, ?_⟩
  by_cases hrn : B.bv.rootNode' = null
  · obtain ⟨-, hnm0⟩ := hempty hrn
    right
    by_cases hr : B.ib.root' = W64 0
    · refine ⟨by unfold resolve; rw [if_pos hr, if_pos hrn], Or.inl ⟨hr, hr, ?_⟩⟩
      exact hinl hr hrn
    · refine ⟨by unfold resolve; rw [if_neg hr, hnm0]; rfl, Or.inr ⟨hr, (hfile hr).2 hrn, ?_⟩⟩
      intro d _; rw [hnm0]; rfl
  · left
    obtain ⟨-, r, hr', -⟩ := hnm _ _ (hrootn hrn)
    refine ⟨B.bv.rootNode', r, ?_, hr'⟩
    unfold resolve
    split
    · simp [hrn]
    · exact hrootn hrn

/-- The last element of a path of a clean bucket is a leaf position. -/
theorem wpath_last (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B) :
    ∀ (es : List elemRef) (pid : w64), wpath W B pid es → posOK W hwm B pid →
    ∃ pid' r ks, es.getLast? = some r ∧ refAt W B pid' r ∧ posOK W hwm B pid' ∧
      kidsAt W B pid' = some (true, ks) ∧ 0 ≤ sint.Z r.index' := by
  intro es
  induction es with
  | nil => intro pid h; exact absurd h (by simp [wpath])
  | cons r rs ih =>
    intro pid h hpos
    cases rs with
    | nil =>
      obtain ⟨hr, hi, ks, hk⟩ := h
      exact ⟨pid, r, ks, rfl, hr, hpos, hk, hi⟩
    | cons r2 rs' =>
      obtain ⟨hr, hi, ks, c, hk, hc', hrest⟩ := h
      have hcpos : posOK W hwm B c := by
        unfold kidsAt at hk
        rcases hpos.2 with ⟨l, rr, hres, hrr⟩ | ⟨hres, hpg⟩
        · rw [hres] at hk
          simp only [hrr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
          obtain ⟨hleaf, rfl⟩ := hk
          rw [List.getElem?_map] at hc'
          obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 hc'
          exact posOK_node_child W hwm bl B l rr hc hrr hleaf _ w hw
        · rw [hres] at hk
          rcases hpg with ⟨h0, -, -, -, hinl⟩ | ⟨hr0, hwf, hfree⟩
          · have hp0 := hpos.1 h0
            simp only [wpageAt, h0, hp0, ↓reduceIte, Option.map_some, Option.some.injEq,
              Prod.mk.injEq] at hk
            obtain ⟨hleaf, -⟩ := hk
            exfalso; revert hleaf; simp [hinl.2.1]
          · obtain ⟨pg, hpg, hpa, -, -⟩ := posOK_page W hwm B pid hr0 hres hpos
            simp only [hpa, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hk
            obtain ⟨hleaf, rfl⟩ := hk
            obtain ⟨-, -, -, hkind⟩ := treeWF_page _ _ _ pg hwf hpg
            rcases hkind with ⟨hfl, -⟩ | ⟨hfl, -, hkids⟩
            · exfalso; revert hleaf; simp [hfl]
            · rw [List.getElem?_map] at hc'
              obtain ⟨i, hi', rfl⟩ := Option.map_eq_some_iff.1 hc'
              have hil := (List.mem_range.1 (List.mem_of_getElem? hi'))
              exact posOK_page_child W hwm B pid pg hr0 hpg hfl hkids hfree _ hil
      obtain ⟨pid', r', ks', hl, h1, h2, h3, h4⟩ := ih c hrest hcpos
      exact ⟨pid', r', ks', by simpa using hl, h1, h2, h3, h4⟩

/-- Where a key a writer's cursor returns is: nil, an entry's key of a node of the bucket, or bytes
of a page of the bucket (`kvResW`). -/
def keySrcOK (W : WView) (B : BRec) (k : GoSlice) : Prop :=
  k = slice.nil ∨
  (∃ (l : Loc) (r : NRec) (i : Nat) (it : Inode) (w : WEntry), B.ns !! l = some r ∧
    r.ins[i]? = some it ∧ r.ws[i]? = some w ∧ it.key' = k ∧
    w.ks ≠ Src.stale) ∨
  (∃ (pid : w64) (p : Loc) (pg : List w8) (off n : Nat), wpageAt W B pid = some (p, pg) ∧
    (B.ib.root' = W64 0 → B.bv.page' ≠ null ∧ B.isrc ≠ Src.stale) ∧ 16 ≤ pg.length ∧
    off + n ≤ pg.length ∧ n < 2 ^ 32 ∧ k = sliceAt p off n)

theorem kvResult_keySrc (W : WView) (B : BRec) (pid : w64) (p : Loc) (pg : List w8) (i : Int)
    (hpa : wpageAt W B pid = some (p, pg))
    (hinl : B.ib.root' = W64 0 → B.bv.page' ≠ null ∧ B.isrc ≠ Src.stale) (hlen : 16 ≤ pg.length)
    (hwf : leafWF pg pg.length) :
    keySrcOK W B (kvResult p pg i).1 := by
  unfold kvResult
  split
  · exact Or.inl rfl
  · rename_i hc
    right; right
    have hi : i.toNat < pageCount pg := by omega
    have hb := (hwf.2.2.1 _ hi).1
    exact ⟨pid, p, pg, elemOff i.toNat + leafPos pg i.toNat, leafKsize pg i.toNat, hpa, hinl, hlen,
      by omega, leAt_lt _ _ 4, rfl⟩

theorem nodeKV_keySrc (W : WView) (B : BRec) (l : Loc) (r : NRec) (i : Int)
    (hr : B.ns !! l = some r) (hlive : wsLive r.ws) (hlen : r.ins.length = r.ws.length) :
    keySrcOK W B (nodeKV r.ins i).1 := by
  unfold nodeKV
  split
  · exact Or.inl rfl
  · rename_i hc
    cases hit : r.ins[i.toNat]? with
    | none => exact Or.inl rfl
    | some it =>
      have hl := (List.getElem?_eq_some_iff.1 hit).1
      obtain ⟨w, hw⟩ : ∃ w, r.ws[i.toNat]? = some w := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      exact Or.inr (Or.inl ⟨l, r, i.toNat, it, w, hr, hit, hw, rfl,
        (hlive w (List.mem_of_getElem? hw)).1⟩)

/-- A writer's cursor's facts: the view's, the bucket clean, no dirty page of the view's. -/
def wctxOK (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (txl : Loc) (pm : GMap w64 Loc) : Prop :=
  viewOK W ∧ bktClean W hwm bl B ∧ B.bv.tx' = txl ∧
  ∀ id, (W.pages !! uint.nat id).isSome → pm !! id = none

end pure

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The bytes of a position's page, out of the view or the inline page (and back). -/
theorem wpageAt_acc (W : WView) (B : BRec) (pid : w64) (p : Loc) (pg : List w8)
    (hc : W.data.locCar ≠ 0) (hpa : wpageAt W B pid = some (p, pg))
    (hinl : B.ib.root' = W64 0 → B.bv.page' ≠ null ∧ B.isrc ≠ Src.stale) (hne : pg ≠ []) :
    pagesView (GF := GF) W.data W.ps W.q W.pages ∗ pageOwn W B ⊢ ∃ dq,
      ⌜p.locCar ≠ 0⌝ ∗ bytesPointsto p dq pg ∗
      (bytesPointsto p dq pg -∗ pagesView W.data W.ps W.q W.pages ∗ pageOwn W B) := by
  iintro ⟨Hpv, Hpo⟩
  unfold wpageAt at hpa
  by_cases hr : B.ib.root' = W64 0
  · rw [if_pos hr] at hpa
    split at hpa
    · cases hpa
      obtain ⟨hpn, hns⟩ := hinl hr
      unfold pageOwn
      rw [if_neg hpn]
      cases hs : B.isrc with
      | stale => exact absurd hs hns
      | view =>
        simp only [hs]
        icases Hpo with %Hin
        icases viewLoc_acc (GF := GF) W _ _ Hin $$ Hpv with ⟨Hb, Hback⟩
        iexists DFrac.own W.q
        isplitr
        · ipureintro
          obtain ⟨id, PG, o, -, -, -, Hp⟩ := Hin
          rw [Hp]; simpa [Loc.add] using hc
        iframe Hb
        iintro Hb
        ihave Hpv := Hback $$ Hb
        iframe
        ipureintro; exact Hin
      | own d =>
        simp only [hs]
        ihave %Hcar := bytesPointsto_car _ _ _ hne $$ Hpo
        iexists d
        isplitr
        · ipureintro; exact Hcar
        iframe Hpo
        iintro Hb
        iframe
    · cases hpa
  · rw [if_neg hr] at hpa
    obtain ⟨pg', hpg, heq⟩ := Option.map_eq_some_iff.1 hpa
    cases heq
    icases viewLoc_acc (GF := GF) W _ _ (inViewLoc_page W _ pg hpg) $$ Hpv with ⟨Hb, Hback⟩
    iexists DFrac.own W.q
    isplitr
    · ipureintro; simpa [Loc.add] using hc
    iframe Hb
    iintro Hb
    ihave Hpv := Hback $$ Hb
    iframe

end own

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- What a writer's cursor reads: the bucket, the view, and the transaction's page cache and
database. -/
def wctx (W : WView) (bl : Loc) (B : BRec) (txl : Loc) (pmap : GoMap) (pm : GMap w64 Loc)
    (dqp : DFrac) : IProp GF :=
  iprop(bktOwn W bl B ∗ wView W ∗ structFieldRef Tx go!"pages" txl ↦{dqp} pmap ∗
    pmap ↦${dqp} pm ∗ structFieldRef Tx go!"db" txl ↦{dqp} W.dbl)

end defs

section acc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- A key a writer's cursor returned (`keySrcOK`), its bytes lent out (and back). -/
theorem keySrc_acc (W : WView) (bl : Loc) (B : BRec) (txl : Loc) (pmap : GoMap)
    (pm : GMap w64 Loc) (dqp : DFrac) (k : GoSlice) (hc : W.data.locCar ≠ 0)
    (h : keySrcOK W B k) :
    wctx (GF := GF) W bl B txl pmap pm dqp ⊢ ∃ (dq : DFrac) (bs : List w8), k ↦*{dq} bs ∗
      (k ↦*{dq} bs -∗ wctx W bl B txl pmap pm dqp) := by
  iintro Hctx
  rcases h with rfl | ⟨l, r, i, it, w, hr, hit, hw, rfl, hns⟩ | ⟨pid, p, pg, off, n, hpa, hinl, hlen, hb, hn, rfl⟩
  · iexists DFrac.own 1, []
    isplitl []
    · iapply ownSlice_nil
    iintro -; iexact Hctx
  · unfold wctx
    icases Hctx with ⟨Hb, Hv, Hpf, Hpm, Hdb⟩
    isimp only [wView] at Hv
    icases Hv with ⟨Hdata, #Hps, #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
    icases bktOwn_node_acc W bl B l r hr $$ Hb with ⟨Hn, Hback⟩
    isimp only [nodeOwn] at Hn
    icases Hn with ⟨Hn, Hins, Hicap, Hents, Hch, Hchcap, Hkey⟩
    icases BigSepL2.bigSepL2_lookup_acc (Φ := fun _ it w => wOwn (GF := GF) W it w) hit hw $$ Hents
      with ⟨Hi, Hentsback⟩
    isimp only [wOwn] at Hi
    icases Hi with ⟨%Hfp, Hk, Hvv⟩
    icases srcBorrow W hc W.q it.key' w.ks w.key hns $$ [Hpv Hk] with ⟨%dq, -, Hk, Hkback⟩
    · iframe
    iexists dq, w.key
    iframe Hk
    iintro Hk
    ihave Hk := Hkback $$ Hk
    icases Hk with ⟨Hpv, Hk⟩
    ihave Hents := Hentsback $$ [Hk Hvv]
    · unfold wOwn; iframe; ipureintro; exact Hfp
    ihave Hb := Hback $$ %r [Hn Hins Hicap Hents Hch Hchcap Hkey]
    · unfold nodeOwn; iframe
    rw [bktOwn_insert_same W bl B l r hr]
    iframe
    unfold wView; iframe; iframe #; ipureintro; exact Hlgv
  · unfold wctx
    icases Hctx with ⟨Hb, Hv, Hpf, Hpm, Hdb⟩
    isimp only [wView] at Hv
    icases Hv with ⟨Hdata, #Hps, #Hlg, Hfli, #Hdl, %Hlgv, Hpv⟩
    isimp only [bktOwn] at Hb
    icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpo, Hns⟩
    have Hne : pg ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    icases wpageAt_acc W B pid p pg hc hpa hinl Hne $$ [Hpv Hpo] with ⟨%dq, %Hc, Hpg, Hpgback⟩
    · iframe
    icases bytes_slice_acc (hG := hG) p dq pg off n hb hn Hc $$ Hpg with ⟨Hk, Hkback⟩
    iexists dq, bytesAt pg off n
    iframe Hk
    iintro Hk
    ihave Hpg := Hkback $$ Hk
    ihave Hpg := Hpgback $$ Hpg
    icases Hpg with ⟨Hpv, Hpo⟩
    unfold bktOwn wView; iframe; iframe #; ipureintro; exact Hlgv

end acc

end bbolt
end EtcdGrove
end Perennial
