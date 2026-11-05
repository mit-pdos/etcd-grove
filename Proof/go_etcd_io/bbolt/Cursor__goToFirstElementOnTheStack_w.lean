/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__goToFirstElementOnTheStack_w.lean` (U6z/U6aa,
`notes/bbolt-proof-plan.md`, "Writer reads at a fraction"): the stack's registry is first replaced by
the writer's (`WGoFirst.nlX`, agreeing on the stack's nodes); the loop keeps a prefix (`sPrefix`)
whose leaf page, once a path, holds its bounds' entries. Its top is a registered live node
(`WGoFirst.top_node`: read through `objOwn`), the inline root page (its bytes from `wInlOwn`, a
leaf by `inlineGood`) or a view page (`WGoFirst.top_page`); a leaf ends the loop (the prefix a
path), a branch pushes the reference `pageNode_w` returns for its entry's child (`WGoFirst.push`,
its registry fragment from `nlFrags`).
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__goToFirstElementOnTheStack_w
public import Spec.go_etcd_io.bbolt.Bucket__pageNode_w
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsLeafPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__BranchPageElement
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__Pgid
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Pgid
public import Proof.go_etcd_io.bbolt.Read.WGoFirst
public import Proof.go_etcd_io.bbolt.Read.Bytes
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Cursor.goToFirstElementOnTheStack_w.wp_proofQ
    (hpn : Bucket.pageNode_w.specQ (GF := GF) (hG := hG))
    (hIL : internal.common.Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (hBE : internal.common.Page.BranchPageElement.spec (GF := GF) (hG := hG))
    (hBP : internal.common.branchPageElement.Pgid.spec (GF := GF) (hG := hG))
    (hIP : internal.common.Inode.Pgid.spec (GF := GF) (hG := hG)) :
    Cursor.goToFirstElementOnTheStack_w.specQ (GF := GF) (hG := hG) := by
  intro K tx r m q X n bl rt ipg nl c stk els pids hc hpre hlok
  wp_start as ⟨Hw, Hc, Hs, Hcap, #Ho⟩
  obtain ⟨B, hB⟩ := WGoFirst.wCurCtx_B X n bl rt hc
  icases wtxWQ_pkgInit K tx r m q X $$ Hw with ⟨Hw, #Hpkg⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  icases WGoFirst.wtxWQ_wStkOwn_agree K tx r m q X nl X.v rt ipg els $$ [Hw Ho] with ⟨Hw, %Hag⟩
  · iframe; iframe #
  have hpre' := WGoFirst.sPrefix_congr nl (WGoFirst.nlX X) X.v bl rt els pids Hag hpre
  have hlok' : sPathR (WGoFirst.nlX X) X.v bl rt els pids → sLeafOK X.v ipg (wEs X n) pids els :=
    fun h => hlok (WGoFirst.sPathR_congr _ nl X.v bl rt els pids
      (fun e he hn => (Hag e he hn).symm) h)
  ihave #Ho' := WGoFirst.wStkOwn_congr r nl (WGoFirst.nlX X) X.v rt ipg els Hag $$ Ho
  wp_auto
  ihave IH : (∃ (stk1 : GoSlice) (R : List elemRef) (Q : List Nat),
      "Hw" ∷ wtxWQ K tx r m q X ∗ "Hc" ∷ c_ptr ↦ c ∗ "Hcc" ∷ c ↦ Cursor.mk bl stk1 ∗
      "Hs" ∷ stk1 ↦* (els ++ R) ∗ "Hcap" ∷ ownSliceCap elemRef stk1 (DFrac.own 1) ∗
      "Ho" ∷ wStkOwn r (WGoFirst.nlX X) X.v rt ipg (els ++ R) ∗
      "%Hinv" ∷ ⌜sPrefix (WGoFirst.nlX X) X.v bl rt (els ++ R) (pids ++ Q) ∧
        (sPathR (WGoFirst.nlX X) X.v bl rt (els ++ R) (pids ++ Q) →
          sLeafOK X.v ipg (wEs X n) (pids ++ Q) (els ++ R)) ∧ sAllFirst R⌝ : IProp GF)
      $$ [Hw c Hc Hs Hcap]
  · iexists stk, [], []
    simp only [named, List.append_nil]
    iframe; iframe #
    ipureintro; exact ⟨hpre', hlok', fun x hx => by cases hx⟩
  wp_for IH
  obtain ⟨hp1, hlk1, haf1⟩ := Hinv
  obtain ⟨S0, e1, hS⟩ : ∃ S0 e1, els ++ R = S0 ++ [e1] := by
    rcases List.eq_nil_or_concat (els ++ R) with h | h
    · exact absurd h hp1.1
    · obtain ⟨a, b, h⟩ := h; exact ⟨a, b, by simpa using h⟩
  obtain ⟨P0, p1, hP⟩ : ∃ P0 p1, pids ++ Q = P0 ++ [p1] := by
    rcases List.eq_nil_or_concat (pids ++ Q) with h | h
    · have := hp1.2.1; rw [h] at this; exact absurd (List.length_eq_zero_iff.1 this.symm) hp1.1
    · obtain ⟨a, b, h⟩ := h; exact ⟨a, b, by simpa using h⟩
  have he1 : (els ++ R).getLast? = some e1 := by rw [hS]; simp
  have hp1l : (pids ++ Q).getLast? = some p1 := by rw [hP]; simp
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  rw [hS] at Hsl
  have hidx : sint.Z (stk1.len - W64 1) = (S0.length : Int) := by
    simp only [List.length_append, List.length_singleton] at Hsl; word
  rw [if_pos (by rw [hidx]; word)]
  rw [hS]
  icases ownSlice_elem_acc (sint.Z (stk1.len - W64 1)) e1 _ _ (S0 ++ [e1]) (by omega)
    (by rw [hidx]; simp) $$ Hs with ⟨He, Hsback⟩
  rw [hidx]
  wp_auto
  wp_method_call; wp_call
  wp_auto
  by_cases hn : e1.node' = null
  · -- a page reference
    rw [hn]
    wp_auto
    icases wtxWQ_cells_acc K tx r m q X $$ Hw with ⟨%Hbase, Hcells, Hwb⟩
    -- its bytes, through a source
    obtain ⟨pg, hpg16, hsrcF⟩ : ∃ pg, 16 ≤ pg.length ∧
        ((p1 = 0 ∧ els ++ R = [e1] ∧ sPathR (WGoFirst.nlX X) X.v bl rt (els ++ R) (pids ++ Q) ∧
          pageFlags pg = leafPageFlag ∧ rt = 0 ∧ ipg = pg) ∨
         (p1 ≠ 0 ∧ B.ib.root' ≠ W64 0 ∧ e1.page' = pageLoc X.v p1 ∧ X.v.pages !! p1 = some pg ∧
          ((pageFlags pg = leafPageFlag ∧ sPathR (WGoFirst.nlX X) X.v bl rt (els ++ R) (pids ++ Q)) ∨
           (pageFlags pg = branchPageFlag ∧ e1.index'.toNat < pageCount pg)))) := by
      rcases WGoFirst.top_page X n bl rt B hc hB _ _ hp1 e1 p1 he1 hp1l hn with
        ⟨hp0, hels, hrt, -, hpath⟩ | ⟨hp0, h0, hloc, pg, hpg, hk⟩
      · obtain ⟨pg, hlp, -, -, hg⟩ := hlk1 hpath e1 p1 he1 hp1l hn
        subst hp0
        unfold leafPgAt at hlp; rw [if_pos rfl] at hlp; cases hlp
        have hg := hg rfl
        exact ⟨ipg, hg.2.2.2.1, Or.inl ⟨rfl, hels, hpath, hg.2.1, hrt, rfl⟩⟩
      · have h4 := (Read.viewWF_page _ hc.1.2.2.2.2.2.2.2 _ _ hpg).2.2.1
        exact ⟨pg, by omega, Or.inr ⟨hp0, h0, hloc, hpg, hk⟩⟩
    icases Ho with #Ho
    ihave Hsrc : (∃ s, srcLoc X.v e1.page' s pg : IProp GF) $$ []
    · rcases hsrcF with ⟨-, hels, -, -, hrt, rfl⟩ | ⟨-, -, hloc, hpg, -⟩
      · rw [hS] at hels
        isimp only [hels, wStkOwn, wInlOwn, hrt, hn, and_self, ↓reduceIte] at Ho
        icases Ho with ⟨-, Hi⟩
        iapply WGoFirst.locOwn_srcLoc $$ Hi
      · iclear Ho
        iexists Src.view
        rw [hloc]
        iapply srcLoc_view_page X.v p1 pg hpg
    icases Hsrc with ⟨%src, #Hsrc⟩
    icases Write.srcLoc_acc (QpMul q wq) X.v e1.page' src pg $$ [Hcells] with ⟨%dq, Hp, Hpb⟩
    · iframe; iframe #
    icases Read.bytesPointsto_bounds e1.page' dq pg (by intro h; simp [h] at hpg16) $$ Hp
      with ⟨Hp, %Hlb⟩
    icases bytesPointsto_view_read (V := Page) e1.page' dq pg 0 e1.page' (by simp) (by omega) Hlb.1
      $$ Hp with ⟨Hh, Hhb⟩
    rw [show (decode (List.take 16 (List.drop 0 pg)) : Page) = pageHdr pg from rfl]
    obtain ⟨hd, hH⟩ : ∃ hd, pageHdr pg = hd := ⟨_, rfl⟩
    have hfz : pageFlags pg = hd.flags'.toNat := by unfold pageFlags; rw [hH]
    rw [hH]
    wp_apply hIL e1.page' hd dq $$ [Hh] as Hh
    · iexact Hh
    ihave Hp := Hhb $$ Hh
    have hleafE : pageFlags pg = leafPageFlag →
        sPathR (WGoFirst.nlX X) X.v bl rt (els ++ R) (pids ++ Q) := by
      intro hl
      rcases hsrcF with ⟨-, -, hpath, -⟩ | ⟨-, -, -, -, ⟨-, hpath⟩ | ⟨hb, -⟩⟩
      · exact hpath
      · exact hpath
      · exact (WGoFirst.flag_ne hb hl).elim
    by_cases hlf : pageFlags pg = leafPageFlag
    · -- a leaf page: done
      have hf2 : hd.flags' = W16 2 := by
        apply BitVec.eq_of_toNat_eq; rw [← hfz, hlf]; rfl
      rw [hf2]
      wp_auto
      wp_for_post
      ihave Hcells := Hpb $$ Hp
      ihave Hw := Hwb $$ Hcells
      ihave Hs := Hsback $$ He
      rw [show (S0 ++ [e1]).set (↑S0.length : Int).toNat e1 = S0 ++ [e1] by simp]
      iapply HΦ
      iexists stk1, R, Q, WGoFirst.nlX X
      rw [hS]
      iframe; iframe #
      ipureintro
      rw [← hS]
      have hpath := hleafE hlf
      exact ⟨hpath, hlk1 hpath, haf1⟩
    · -- a branch page: its entry's child
      obtain ⟨h0, hpg, hf, hi⟩ : B.ib.root' ≠ W64 0 ∧ X.v.pages !! p1 = some pg ∧
          pageFlags pg = branchPageFlag ∧ e1.index'.toNat < pageCount pg := by
        rcases hsrcF with ⟨-, -, -, hl, -⟩ | ⟨-, h0, -, hpg, ⟨hl, -⟩ | ⟨hb, hi⟩⟩
        · exact absurd hl hlf
        · exact absurd hl hlf
        · exact ⟨h0, hpg, hb, hi⟩
      have hf1 : hd.flags' ≠ W16 2 := by
        intro h; apply hlf; rw [hfz, h]; rfl
      rw [decide_eq_false hf1]
      wp_auto
      rw [hn]
      wp_auto
      obtain ⟨_, hbw⟩ := WGoFirst.viewWF_branchWF _ hc.1.2.2.2.2.2.2.2 _ _ hpg hf
      obtain ⟨-, -, hcnt, -, -⟩ := hbw
      have hcnt16 : pageCount pg < 2 ^ 16 := by unfold pageCount; exact BitVec.isLt _
      have hu : uint.Z (W16 (sint.Z e1.index')) = (e1.index'.toNat : Int) := by
        have : e1.index'.toNat < 2 ^ 16 := by omega
        word
      wp_apply hBE e1.page' (W16 (sint.Z e1.index')) Hlb.1
        (by rw [hu]; unfold elemOff at hcnt; omega)
      rw [hu]
      have hoff : (16 + 16 * (e1.index'.toNat : Int)) = ((elemOff e1.index'.toNat : Nat) : Int) := by
        unfold elemOff; push_cast; rfl
      rw [hoff]
      icases bytesPointsto_view_read (V := branchPageElement) e1.page' dq pg (elemOff e1.index'.toNat)
        (e1.page' +ₗ ((elemOff e1.index'.toNat : Nat) : Int)) rfl
        (by unfold elemOff at hcnt ⊢; omega) Hlb.1 $$ Hp with ⟨Hel, Helb⟩
      rw [show (decode (List.take 16 (List.drop (elemOff e1.index'.toNat) pg)) : branchPageElement) =
        branchElem pg e1.index'.toNat from rfl]
      obtain ⟨be, hbe⟩ : ∃ be, branchElem pg e1.index'.toNat = be := ⟨_, rfl⟩
      rw [hbe]
      wp_apply hBP (e1.page' +ₗ ((elemOff e1.index'.toNat : Nat) : Int)) be dq $$ [Hel] as Hel
      · iexact Hel
      ihave Hp := Helb $$ Hel
      ihave Hcells := Hpb $$ Hp
      ihave Hw := Hwb $$ Hcells
      have hchild : be.pgid' = W64 (branchPgid pg e1.index'.toNat : Int) := by
        unfold branchPgid; rw [hbe]; exact (WBridge.w64_cast_toNat _).symm
      rw [hchild]
      try wp_auto
      ihave Hs := Hsback $$ He
      rw [show (S0 ++ [e1]).set (↑S0.length : Int).toNat e1 = S0 ++ [e1] by simp]
      icases wtxWQ_nodes_nonnull K tx r m q X bl B hB $$ Hw with ⟨Hw, %Hnodes⟩
      ihave %Hmax := wtxWQ_page_maxMap K tx r m q X $$ Hw
      obtain ⟨pgc, hpgc⟩ : ∃ pgc, X.v.pages !! branchPgid pg e1.index'.toNat = some pgc :=
        WBridge.viewWF_child _ hc.1.2.2.2.2.2.2.2 _ _ hpg hf _ hi
      obtain ⟨hlive, hz, hnmnn, hpnpre⟩ := WGoFirst.pn_pre X n bl rt B hc hB Hmax h0 _ pgc hpgc
        (WBridge.branchPgid_lt _ _)
      wp_apply hpn K tx r m q X bl B _ hB hlive hz (fun h => absurd h Hnodes) hnmnn hpnpre $$ [Hw]
        as %pp %nd ⟨Hw, %Hpn⟩
      · iexact Hw
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl] as %s1 ⟨Hs, Hcap, -⟩
      try wp_auto
      wp_for_post
      have hpush := WGoFirst.push X n bl rt B hc hB Hbase ipg (els ++ R) (pids ++ Q) hp1 e1 p1 he1
        hp1l pg hpg hf hi h0 { page' := pp, node' := nd, index' := W64 0 } rfl Hpn
      icases (show wtxWQ K tx r m q X ⊢ wtxWQ K tx r m q X ∗
          nodeLoc r (WGoFirst.nlX X) ({ page' := pp, node' := nd, index' := W64 0 } : elemRef) by
          unfold nodeLoc
          by_cases hnd : nd = null
          · simp only [hnd, ↓reduceIte]; iintro Hw; iframe
          · simp only [hnd, ↓reduceIte]
            have h1 : (els ++ R ++ [({ page' := pp, node' := nd, index' := W64 0 } : elemRef)])[(els ++ R).length]? =
                some { page' := pp, node' := nd, index' := W64 0 } := by simp
            have h2 : (pids ++ Q ++ [branchPgid pg e1.index'.toNat])[(els ++ R).length]? =
                some (branchPgid pg e1.index'.toNat) := by rw [← hp1.2.1]; simp
            have hx : X.nloc !! nd = some (bl, branchPgid pg e1.index'.toNat) :=
              (hpush.1.2.2.2 _ _ _ h1 h2).1 hnd
            iintro Hw
            icases WGoFirst.wtxWQ_nlFrag K tx r m q X nd _ hx $$ Hw with ⟨Hw, #Hy⟩
            iframe
            iexists _
            iframe #
            ipureintro; exact hx) $$ Hw with ⟨Hw, Hne⟩
      ihave Ho2 := WGoFirst.wStkOwn_snoc r (WGoFirst.nlX X) X.v rt ipg (S0 ++ [e1])
        { page' := pp, node' := nd, index' := W64 0 } (by simp) $$ [Ho Hne]
      · iframe
        iexact Ho
      isplitl [HΦ]
      · iexact HΦ
      iexists s1, R ++ [{ page' := pp, node' := nd, index' := W64 0 }],
        Q ++ [branchPgid pg e1.index'.toNat]
      simp only [named, ← List.append_assoc]
      rw [hS]
      iframe
      ipureintro
      rw [← hS]
      refine ⟨hpush.1, hpush.2, fun x hx => ?_⟩
      rcases List.mem_append.1 hx with h | h
      · exact haf1 x h
      · simp at h; rw [h]; rfl

  · -- a node reference
    obtain ⟨rn, hrn, hlv, hleafT, hbrF⟩ := WGoFirst.top_node X n bl rt B hc hB _ _ hp1 e1 p1 he1 hp1l hn
    rw [decide_eq_false hn]
    wp_auto
    icases wtxWQ_node_cells_acc K tx r m q X bl B e1.node' rn hB hrn hlv $$ Hw
      with ⟨%Hbase, Hob, Hcells, Hwb⟩
    isimp only [objOwn] at Hob
    icases Hob with ⟨Hn, Hins, Hcapn, Hws, Hch, Hchcap, Hnk⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
    iStructNamed Hn
    wp_auto
    ihave Hn : (e1.node' ↦{DFrac.own q} rn.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hob : objOwn X.v e1.node' (DFrac.own q) true (.node bl rn) $$ [Hn Hins Hcapn Hws Hch Hchcap Hnk]
    · simp only [objOwn]; iframe
    cases hleaf : rn.nv.isLeaf'
    · -- a branch node: its entry's child
      obtain ⟨h0, pg, hpg, hf, hi, hwl, hwp⟩ := hbrF hleaf
      wp_auto
      rw [decide_eq_false hn]
      wp_auto
      isimp only [objOwn] at Hob
      icases Hob with ⟨Hn, Hins, Hcapn, Hws, Hch, Hchcap, Hnk⟩
      iStructNamed Hn
      wp_auto
      ihave Hn : (e1.node' ↦{DFrac.own q} rn.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ihave %Hinl := ownSlice_len _ _ _ $$ Hins
      ihave %Hwl := BigSepL2.bigSepL2_length $$ Hws
      have hcnt16 : pageCount pg < 2 ^ 16 := by unfold pageCount; exact BitVec.isLt _
      have hix : sint.Z e1.index' = (e1.index'.toNat : Int) := by
        have : e1.index'.toNat < 2 ^ 16 := by omega
        word
      have Hlen : sint.Z rn.nv.inodes'.len = (rn.ws.length : Int) := by word
      rw [if_pos (show 0 ≤ sint.Z e1.index' ∧ sint.Z e1.index' < sint.Z rn.nv.inodes'.len by
        rw [hix, Hlen]; omega)]
      list_elem rn.ins (sint.Z e1.index').toNat as it
      list_elem rn.ws (sint.Z e1.index').toNat as w
      icases ownSlice_elem_acc (sint.Z e1.index') it _ _ rn.ins (by omega) Hit_lookup $$ Hins
        with ⟨Hit, Hsb⟩
      wp_apply hIP $$ [$Hit] as Hit
      icases BigSepL2.bigSepL2_lookup_acc Hit_lookup Hw_lookup $$ Hws with ⟨Hw1, Hwsback⟩
      isimp only [wOwn] at Hw1
      icases Hw1 with ⟨%Hfp, Hwr⟩
      ihave Hws := Hwsback $$ [Hwr]
      · isimp only [wOwn]; iframe; ipureintro; exact Hfp
      ihave Hins := Hsb $$ Hit
      rw [list_set_lookup_self _ _ _ Hit_lookup]
      ihave Hob : objOwn X.v e1.node' (DFrac.own q) true (.node bl rn) $$ [Hn Hins Hcapn Hws Hch Hchcap Hnk]
      · simp only [objOwn]; iframe
      ihave Hw := Hwb $$ Hob Hcells
      have hwc : w.pgid = W64 (branchPgid pg e1.index'.toNat : Int) := by
        have := hwp _ w Hw_lookup; rw [show (sint.Z e1.index').toNat = e1.index'.toNat by omega] at this
        exact this
      rw [Hfp.2, hwc]
      ihave Hs := Hsback $$ He
      rw [show (S0 ++ [e1]).set (↑S0.length : Int).toNat e1 = S0 ++ [e1] by simp]
      icases wtxWQ_nodes_nonnull K tx r m q X bl B hB $$ Hw with ⟨Hw, %Hnodes⟩
      ihave %Hmax := wtxWQ_page_maxMap K tx r m q X $$ Hw
      obtain ⟨pgc, hpgc⟩ : ∃ pgc, X.v.pages !! branchPgid pg e1.index'.toNat = some pgc :=
        WBridge.viewWF_child _ hc.1.2.2.2.2.2.2.2 _ _ hpg hf _ hi
      obtain ⟨hlive, hz, hnmnn, hpnpre⟩ := WGoFirst.pn_pre X n bl rt B hc hB Hmax h0 _ pgc hpgc
        (WBridge.branchPgid_lt _ _)
      wp_apply hpn K tx r m q X bl B _ hB hlive hz (fun h => absurd h Hnodes) hnmnn hpnpre $$ [Hw]
        as %pp %nd ⟨Hw, %Hpn⟩
      · iexact Hw
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl] as %s1 ⟨Hs, Hcap, -⟩
      try wp_auto
      wp_for_post
      have hpush := WGoFirst.push X n bl rt B hc hB Hbase ipg (els ++ R) (pids ++ Q) hp1 e1 p1 he1
        hp1l pg hpg hf hi h0 { page' := pp, node' := nd, index' := W64 0 } rfl Hpn
      icases (show wtxWQ K tx r m q X ⊢ wtxWQ K tx r m q X ∗
          nodeLoc r (WGoFirst.nlX X) ({ page' := pp, node' := nd, index' := W64 0 } : elemRef) by
          unfold nodeLoc
          by_cases hnd : nd = null
          · simp only [hnd, ↓reduceIte]; iintro Hw; iframe
          · simp only [hnd, ↓reduceIte]
            have h1 : (els ++ R ++ [({ page' := pp, node' := nd, index' := W64 0 } : elemRef)])[(els ++ R).length]? =
                some { page' := pp, node' := nd, index' := W64 0 } := by simp
            have h2 : (pids ++ Q ++ [branchPgid pg e1.index'.toNat])[(els ++ R).length]? =
                some (branchPgid pg e1.index'.toNat) := by rw [← hp1.2.1]; simp
            have hx : X.nloc !! nd = some (bl, branchPgid pg e1.index'.toNat) :=
              (hpush.1.2.2.2 _ _ _ h1 h2).1 hnd
            iintro Hw
            icases WGoFirst.wtxWQ_nlFrag K tx r m q X nd _ hx $$ Hw with ⟨Hw, #Hy⟩
            iframe
            iexists _
            iframe #
            ipureintro; exact hx) $$ Hw with ⟨Hw, Hne⟩
      ihave Ho2 := WGoFirst.wStkOwn_snoc r (WGoFirst.nlX X) X.v rt ipg (S0 ++ [e1])
        { page' := pp, node' := nd, index' := W64 0 } (by simp) $$ [Ho Hne]
      · iframe
      isplitl [HΦ]
      · iexact HΦ
      iexists s1, R ++ [{ page' := pp, node' := nd, index' := W64 0 }],
        Q ++ [branchPgid pg e1.index'.toNat]
      simp only [named, ← List.append_assoc]
      rw [hS]
      iframe
      ipureintro
      rw [← hS]
      refine ⟨hpush.1, hpush.2, fun x hx => ?_⟩
      rcases List.mem_append.1 hx with h | h
      · exact haf1 x h
      · simp at h; rw [h]; rfl

    · -- a leaf node: done
      wp_auto
      wp_for_post
      ihave Hw := Hwb $$ Hob Hcells
      ihave Hs := Hsback $$ He
      rw [show (S0 ++ [e1]).set (↑S0.length : Int).toNat e1 = S0 ++ [e1] by simp]
      iapply HΦ
      iexists stk1, R, Q, WGoFirst.nlX X
      rw [hS]
      iframe
      ipureintro
      rw [← hS]
      have hpath := hleafT hleaf
      exact ⟨hpath, hlk1 hpath, haf1⟩

end proof

end bbolt
end EtcdGrove
end Perennial
