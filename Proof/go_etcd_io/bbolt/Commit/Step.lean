/-
**`Commit`'s commit point** (U10 of `notes/bbolt-proof-plan.md`; design §3.11, Commit step 7, D22):
`writeMeta`'s `commitStep` for a commit. Under `metalock`, with the writer's ghost state and meta
shares, the new tree's slots and the client's update: the meta slot's bytes and cells go to the
write; given back with `j` bytes written,
- `j = 4096` (the page whole, whatever `WriteAt` returned): the store publishes `C'`
  (`store_publish`), the update fires (`au_commit_fire`), the meta cells and bytes are `C'`'s
  (`meta_put`), and `metalock`'s resource holds `C'` (`metaOk_parity_write`);
- `j = 0`: everything as it was, the update unfired.
-/
module

public import Proof.go_etcd_io.bbolt.Tx__writeMeta
public import Proof.go_etcd_io.bbolt.Commit.MetaBytes
public import Proof.go_etcd_io.bbolt.Commit.Fire

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

/-- The summed meta's txid is the meta's. Proved by unfolding first: `rfl` alone makes the kernel
compare `metaSummed mv` with `mv` (the projections' arguments), which unfolds the checksum
(`metaSum`) and fails with "deep recursion detected"; so does any cast between the two
(`simp only [metaSummed]` on a hypothesis). Rewrite with this lemma instead. -/
theorem metaSummed_txid [GooseExts] (mv : Meta) : (metaSummed mv).txid' = mv.txid' := by
  unfold metaSummed; rfl

section step
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The writer's resources the commit point works on, at the committed state `C` (`wdbCoreG`'s
ghost state, its `opened` half and meta shares; the data's writer quarter at `D`), its store
state `(v, w, pb, wl)`. -/
def cpRes (K : BC) (C : CommitSt) (fl : FLPg) (b : Loc) (l : Nat) (v : View) (w : Nat)
    (pb wl : Bool) (D : Data) : IProp GF :=
  iprop(ghostVar K.B.out (1 : Qp).half false ∗ ghostVar K.B.cur (1 : Qp).half.half C ∗
    ghostVar K.B.fl (1 : Qp).half fl ∗ ghostVar K.B.map (1 : Qp).half (some (b, l) : MapSt) ∗
    ghostVar K.B.wv (1 : Qp).half ((some v, some w, pb, wl) : WSt) ∗
    K.db.[DB, go!"opened"] ↦{DFrac.own (1 : Qp).half} true ∗
    metaCellsQ (1 : Qp).half.half (some (b, l)) C ∗ metaOsBytes K.p (DFrac.own (1 : Qp).half) C ∗
    ghostVar K.B.st (1 : Qp).half.half D)

/-- The client's update of a commit from `Db` to `Dn`. -/
def commitAU (K : BC) (N' : Namespace) (Db Dn : Data) (Q : IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (D' : Data), boltStateDef K.B 1 D' }> @ ⊤ \ ↑N', ∅
    <{ ⌜D' = Db⌝ ∗ boltStateDef K.B 1 Dn, COMM Q }>)

/-- **After the commit point**: published at `C'` with the update fired (`j = 4096`), or unchanged
with the update's carrier `A` (U11i: the caller's resource that gives the update, `Commit_err`'s
`P`) and the new slots back (`j = 0`). -/
def cpPost (K : BC) (C C' : CommitSt) (fl : FLPg) (b : Loc) (l : Nat)
    (v : View) (wl : Bool) (S : List Nat) (bs : Nat → List w8) (Fb : GMap Nat (List w8))
    (Dn : Data) (Q A : IProp GF) (j : Nat) : IProp GF :=
  iprop((⌜j = 4096⌝ ∗ cpRes K C' fl b l v (C.txid + 1) true wl Dn ∗ receipt 1 ∗ Q) ∨
    (⌜j = 0⌝ ∗ cpRes K C fl b l v (C.txid + 1) false wl (treeData C) ∗
      slotsOwn (some (b, l)) K.p S bs ∗
      fbTok K.B C fl ((some v, some (C.txid + 1), false, wl) : WSt) Fb ∗ A))

omit package_sem in
/-- **`writeMeta`'s commit step for a commit** (see the file header). The premises are
`store_publish`'s for `C' = C.publish (metaBuf mv) (metaSummed mv) pages` (spill's and
`commitFreelist`'s posts), the meta's validity, and the new data `Dn = treeData C'`. -/
theorem commitStep_commit (K : BC) (N' : Namespace) (C : CommitSt) (fl : FLPg) (b : Loc) (l : Nat)
    (v : View) (wl : Bool) (S : List Nat) (bs : Nat → List w8) (Fb : GMap Nat (List w8))
    (mv : Meta) (pages : Pages) (Dn : Data) (Q A : IProp GF)
    (hA : A ⊢ commitAU K N' (treeData C) Dn Q)
    (htx : mv.txid'.toNat = C.txid + 1) (hval : metaValid (metaSummed mv))
    (hps : (metaSummed mv).pageSize'.toNat = 4096)
    (hDn : treeData (C.publish (metaBuf mv) (metaSummed mv) pages) = Dn)
    (htree : treeOK (C.publish (metaBuf mv) (metaSummed mv) pages))
    (hhwm : (C.publish (metaBuf mv) (metaSummed mv) pages).hwm ≤ 2 ^ 62)
    (hdrop : ∀ s ∈ treeSlots C, s ∉ treeSlots (C.publish (metaBuf mv) (metaSummed mv) pages) →
      s ∈ pendSlots fl)
    (hS : ∀ s, s ∈ S ↔ s ∈ treeSlots (C.publish (metaBuf mv) (metaSummed mv) pages) ∧
      s ∉ slotsOf C fl)
    (hbytes : ∀ id pg, (C.publish (metaBuf mv) (metaSummed mv) pages).pages !! id = some pg →
      C.pages !! id = some pg ∨
      ((∀ j < 1 + pageOverflow pg, id + j ∈ S) ∧
        pg = (List.range' id (1 + pageOverflow pg)).flatMap bs))
    (hfl : flBelow fl (C.publish (metaBuf mv) (metaSummed mv) pages) (some (C.txid + 1)))
    (hnp : ∀ s ∈ treeSlots (C.publish (metaBuf mv) (metaSummed mv) pages), s ∉ pendSlots fl)
    (hSb : ∀ s ∈ S, (bs s).length = 4096 ∧ W64 (s : Int) ∉ fl.free ∧
      (∀ b' l', (some (b, l) : MapSt) = some (b', l') → s < l' / 4096) ∧ 2 ≤ s) :
    K.core (GF := GF) ∗ cpRes K C fl b l v (C.txid + 1) false wl (treeData C) ∗
      slotsOwn (some (b, l)) K.p S bs ∗
      fbTok K.B C fl ((some v, some (C.txid + 1), false, wl) : WSt) Fb ∗
      A ⊢
    commitStep K (mv.txid'.toNat % 2) b (metaBuf mv)
      (cpPost K C (C.publish (metaBuf mv) (metaSummed mv) pages) fl b l v wl S bs Fb Dn Q A) := by
  have hs2 : mv.txid'.toNat % 2 < 2 := Nat.mod_lt _ (by omega)
  have hsl : ∀ i, (C.publish (metaBuf mv) (metaSummed mv) pages).slot i =
      if i % 2 = mv.txid'.toNat % 2 then metaBuf mv else C.slot i := by
    intro i; rw [publish_slot, metaSummed_txid]
  have hother : (mv.txid'.toNat % 2 + 1) % 2 ≠ mv.txid'.toNat % 2 := by omega
  have hself : mv.txid'.toNat % 2 % 2 = mv.txid'.toNat % 2 := Nat.mod_mod _ _
  iintro ⟨#Hcore, Hres, HS, Hfb, Hau⟩
  ihave #Hcore' : isBoltCoreP K.B K.N K.db K.p K.sp K.t0 $$ []
  · unfold BC.core; iexact Hcore
  unfold isBoltCoreP
  icases Hcore' with ⟨-, -, -, -, -, -, -, -, -, #Hpi, -⟩
  iunfold cpRes at Hres
  icases Hres with ⟨Hout, Hcurq, Hfl, Hmap, Hwv, Hopw, Hmcw, Hobw, Hstw⟩
  unfold commitStep
  iintro HR
  iunfold metaR at HR
  icases HR with ⟨%C0, %F, %cl, %fli, %wa, Hcur, Hst, Hcls, Hop, Hfli, Hwa, Hob, Hmlk, Hfa, Hro,
    %Hok, %HF⟩
  icombine Hcur Hcurq gives % ⟨_, hC0⟩
  subst C0
  icombine Hop Hopw gives %hop
  have hcl : cl = false := by
    cases cl
    · rfl
    · simp only [Bool.not_true] at hop; exact absurd hop (by simp)
  subst hcl
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
  obtain ⟨hmok, htok, htx1⟩ := Hok rfl
  imod meta_take K.B K.N K.p ⊤ CoPset.subseteq_top C (some (b, l)) $$ [Hpi Hout Hmlk Hcurq Hmap]
    with ⟨Hmcl, Hout, Hcurq, Hmap⟩
  · iframe; iframe #
  icases metaCells_take C b l _ hs2 $$ [Hmcw Hmcl] with ⟨Hold, Hoth⟩
  · iframe
  icases metaOsBytes_take K.p C _ hs2 hmok.1 hmok.2.1 $$ [Hob Hobw] with ⟨%xa, %xb, Hxa, Hxb, %hxab⟩
  · iframe
  have hslotlen : ∀ i, (C.slot i).length = 4096 := by
    intro i; unfold CommitSt.slot; split
    · exact hmok.1
    · exact hmok.2.1
  imodintro
  iexists xa, C.slot (mv.txid'.toNat % 2)
  iframe Hxa Hold
  isplitr
  · ipureintro
    have := congrArg List.length hxab.1
    simp only [List.length_map] at this
    exact ⟨this.trans (hslotlen _), hslotlen _⟩
  iintro %j %ys %hj Hys Hnew Hrc
  obtain ⟨hj01, hys⟩ := hj
  rcases hj01 with rfl | rfl
  · -- nothing written: everything back, the update unfired
    simp only [↓reduceIte] at hys
    icases metaOsBytes_put K.p C _ hs2 hmok.1 hmok.2.1 ys xb (hys.trans hxab.1) hxab.2
      $$ [Hys Hxb] with ⟨Hob, Hobw⟩
    · iframe
    ihave Hnew : bytesPointsto (b +ₗ ((4096 * (mv.txid'.toNat % 2) : Nat) : Int))
        (DFrac.own (1 : Qp).half) (C.slot (mv.txid'.toNat % 2)) $$ [Hnew]
    · rw [hys, hxab.1]; iexact Hnew
    icases metaCells_put C b l _ hs2 $$ [Hnew Hoth] with ⟨Hmcw, Hmcl⟩
    · iframe
    imod meta_put K.B K.N K.p ⊤ CoPset.subseteq_top C (some (b, l)) $$ [Hpi Hout Hmcl Hcurq Hmap]
      with ⟨Hout, Hmlk, Hcurq, Hmap⟩
    · iframe; iframe #
    imodintro
    isplitl [Hcur Hst Hcls Hop Hfli Hwa Hob Hmlk Hfa Hro]
    · iunfold metaR
      iexists C, F, false, fli, wa
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      iframe
      ipureintro; exact ⟨fun _ => ⟨hmok, htok, htx1⟩, HF⟩
    unfold cpPost
    iright
    isplitr
    · ipureintro; rfl
    iunfold cpRes
    iframe
  · -- the page written whole: the commit point
    simp only [show (4096 : Nat) ≠ 0 from by decide, ↓reduceIte] at hys
    have hmeta : (C.publish (metaBuf mv) (metaSummed mv) pages).metaOk :=
      metaOk_parity_write C (metaBuf mv) (metaSummed mv) pages hmok (metaBuf_length mv)
        (metaOf_metaBuf mv) hval (by rw [metaSummed_txid]; exact htx) hps (metaBuf_probes mv)
    have htx' : (C.publish (metaBuf mv) (metaSummed mv) pages).txid = C.txid + 1 := by
      simp only [CommitSt.publish, metaSummed_txid]; exact htx
    imod store_publish K.B K.N K.p ⊤ CoPset.subseteq_top C _ fl (some (b, l)) v (C.txid + 1) wl S bs
      Fb htx' hmeta htree hhwm hdrop hS hbytes hfl hnp hSb (by simp)
      $$ [Hpi Hcur Hcurq Hfl Hmap Hwv HS Hout Hfb] with ⟨Hcur, Hcurq, Hfl, Hmap, Hwv, Hout⟩
    · iframe; iframe #
      iapply (ghostVar_split_half K.B.cur (1 : Qp).half C).1 $$ Hcur
    ihave Hau := hA $$ Hau
    iunfold commitAU at Hau
    imod au_commit_fire K.B N' (treeData C) Dn Q $$ [Hst Hstw Hau] with ⟨Hst, Hstw, HQ⟩
    · iframe
    have hlen' : ∀ i, ((C.publish (metaBuf mv) (metaSummed mv) pages).slot i).length = 4096 := by
      intro i; rw [hsl]; split
      · exact metaBuf_length mv
      · exact hslotlen i
    ihave Hnew : bytesPointsto (b +ₗ ((4096 * (mv.txid'.toNat % 2) : Nat) : Int))
        (DFrac.own (1 : Qp).half)
        ((C.publish (metaBuf mv) (metaSummed mv) pages).slot (mv.txid'.toNat % 2)) $$ [Hnew]
    · rw [hsl, ite_eq_left hself, ← hys]; iexact Hnew
    ihave Hoth : bytesPointsto (b +ₗ ((4096 * (1 - mv.txid'.toNat % 2) : Nat) : Int))
        (DFrac.own (1 : Qp).half)
        ((C.publish (metaBuf mv) (metaSummed mv) pages).slot (mv.txid'.toNat % 2 + 1)) $$ [Hoth]
    · rw [hsl, ite_eq_right hother]; iexact Hoth
    have hm0' : (C.publish (metaBuf mv) (metaSummed mv) pages).m0.length = 4096 := hmeta.1
    have hm1' : (C.publish (metaBuf mv) (metaSummed mv) pages).m1.length = 4096 := hmeta.2.1
    icases metaOsBytes_put K.p _ _ hs2 hm0' hm1' ys xb
      (by rw [hsl, ite_eq_left hself]; exact hys) (by rw [hsl, ite_eq_right hother]; exact hxab.2)
      $$ [Hys Hxb] with ⟨Hob, Hobw⟩
    · iframe
    icases metaCells_put _ b l _ hs2 $$ [Hnew Hoth] with ⟨Hmcw, Hmcl⟩
    · iframe
    imod meta_put K.B K.N K.p ⊤ CoPset.subseteq_top _ (some (b, l)) $$ [Hpi Hout Hmcl Hcurq Hmap]
      with ⟨Hout, Hmlk, Hcurq, Hmap⟩
    · iframe; iframe #
    imodintro
    isplitl [Hcur Hst Hcls Hop Hfli Hwa Hob Hmlk Hfa Hro]
    · iunfold metaR
      iexists (C.publish (metaBuf mv) (metaSummed mv) pages), F, false, fli, wa
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      rw [hDn]
      iframe
      ipureintro
      refine ⟨fun _ => ⟨hmeta, htree, by omega⟩, fun k t h => ?_⟩
      have := HF k t h
      omega
    unfold cpPost
    ileft
    isplitr
    · ipureintro; rfl
    iunfold cpRes
    iframe


end step

end bbolt
end EtcdGrove
end Perennial
