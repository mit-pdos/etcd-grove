/-
The write transaction during `Commit`'s spill, as a whole (`spillR`, `spillG`).

**Resources** (`spillR`): the database (`dbWR`), the transaction's objects with its nodes
without their inodes' capacities (`ownWriteTxGX`) and those apart (`capsOwn`, `K` the nodes
without one), the view, the ghost map's authority (its domain: the view's pages and the dirty
ones), and the stash of freed pages' tokens.

**Facts** (`spillG`): the view's (strict, slot-disjoint, below its high-water mark), the dirty
pages' (`spillDirty`) and what an allocation may take (`allocUnseen`), the freed pages
(`freedOK`), and what `dereference` needs of every bucket (`derefReadyX`), so that every
allocation may remap.

**An allocation** (`spill_alloc`, over `Tx.allocate.xspec`): the dirty page's buffer, its
header lent out (`dirtyHdr`), its token fresh from the authority; on an error, what `Commit`'s
rollback needs (`spillErr`: the transaction's objects as `ownWriteTxG`, the nodes without a
capacity dropped).
-/
module

public import Proof.go_etcd_io.bbolt.SpillDirty
public import Proof.go_etcd_io.bbolt.SpillTree
public import Proof.go_etcd_io.bbolt.RebalanceDefs
public import Proof.go_etcd_io.bbolt.SpillDeref

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The transaction `T` (at `txl`) during the spill: its facts (see the module doc), its txid
`txid`, the database `ρ`, the stash `F`. -/
def spillG (W : WView) (txl : Loc) (txid : w64) (T : WTx) (ρ : DBState)
    (F : GMap Nat (List w8)) : Prop :=
  viewOK W ∧ pagesDisjoint W.pages ∧ (∀ id pg, W.pages !! id = some pg → id < W.hwm) ∧
  W.hwm ≤ uint.nat T.mv.pgid' ∧ uint.Z T.mv.pgid' * W.ps < 2 ^ 48 ∧ T.mv.txid' = txid ∧
  T.t.writable' = true ∧ T.t.db' = W.dbl ∧ W.dbl ≠ null ∧
  (∀ bl B, T.bs !! bl = some B → B.bv.tx' = txl) ∧
  spillDirty ρ W T ∧ allocUnseen ρ W.hwm ∧ freedOK W ρ.fl txid F ∧
  derefReadyX T (structFieldRef Tx go!"root" txl)


/-- Reachable buckets survive a dereference (it keeps every bucket's cache). -/
theorem bktReach_rel (T T0 : WTx) (rl : Loc) (h : derefRelX T T0) (bl : Loc)
    (hr : bktReach T rl bl) : bktReach T0 rl bl := by
  induction hr with
  | root => exact .root
  | child bl B name c _ hB hc ih =>
    obtain ⟨B0, hB0⟩ := Option.isSome_iff_exists.1 ((h.2.2.2.2.1 bl).1 (by rw [hB]; rfl))
    have hd := h.2.2.2.2.2 bl B B0 hB hB0
    exact .child bl B0 name c ih hB0 (by rw [hd.2.2.2.1]; exact hc)

/-- `derefReadyX` survives a dereference (`derefRelX`). -/
theorem derefReadyX_rel (T T0 : WTx) (rl : Loc) (h : derefRelX T T0) (hr : derefReadyX T rl) :
    derefReadyX T0 rl := by
  obtain ⟨h1, h2, ⟨dep, hdep⟩, h4⟩ := hr
  have hdom := h.2.2.2.2.1
  have hb := h.2.2.2.2.2
  refine ⟨(hdom rl).1 h1, fun bl hbl => ?_, ⟨dep, fun bl B0 name c hB0 hc => ?_⟩, fun bl B0 hB0 => ?_⟩
  · have := h2 bl ((hdom bl).2 hbl)
    exact bktReach_rel T T0 rl h bl this
  · obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 ((hdom bl).2 (by rw [hB0]; rfl))
    have hd := hb bl B B0 hB hB0
    exact hdep bl B name c hB (by rw [← hd.2.2.2.1]; exact hc)
  · obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 ((hdom bl).2 (by rw [hB0]; rfl))
    have hd := hb bl B B0 hB hB0
    obtain ⟨hn, hc⟩ := h4 bl B hB
    refine ⟨derefBktX_ready bl B B0 hn hd, fun name c hc0 => ?_⟩
    exact (hdom c).1 (hc name c (by rw [← hd.2.2.2.1]; exact hc0))

theorem bktReach_bs (T T' : WTx) (rl : Loc) (h : T'.bs = T.bs) (bl : Loc)
    (hr : bktReach T rl bl) : bktReach T' rl bl := by
  induction hr with
  | root => exact .root
  | child bl B name c _ hB hc ih => exact .child bl B name c ih (by rw [h]; exact hB) hc

/-- `derefReadyX` depends on the buckets only. -/
theorem derefReadyX_bs (T T' : WTx) (rl : Loc) (h : T'.bs = T.bs) (hr : derefReadyX T rl) :
    derefReadyX T' rl := by
  obtain ⟨h1, h2, ⟨dep, hdep⟩, h4⟩ := hr
  refine ⟨by rw [h]; exact h1, fun bl hbl => bktReach_bs T T' rl h bl (h2 bl (by rw [← h]; exact hbl)),
    ⟨dep, fun bl B name c hB hc => hdep bl B name c (by rw [← h]; exact hB) hc⟩,
    fun bl B hB => ?_⟩
  obtain ⟨a, b⟩ := h4 bl B (by rw [← h]; exact hB)
  exact ⟨a, fun name c hc => by rw [h]; exact b name c hc⟩

/-- An allocation keeps the pending pages. -/
theorem allocOK_pending (σ σ' : DBState) (w : Reader) (mv mv' : internal.common.Meta)
    (txid id : w64) (n : Nat) (h : allocOK σ σ' w mv mv' txid id n) :
    σ'.fl.pending = σ.fl.pending := by
  obtain ⟨-, -, -, -, -, -, h⟩ := h
  rcases h with ⟨-, rfl, -⟩ | ⟨-, -, rfl | ⟨d', sz', -, rfl⟩⟩ <;> rfl

theorem freedOK_pending (W W' : WView) (fl fl' : FLState) (txid : w64) (F : GMap Nat (List w8))
    (hp : W'.pages = W.pages) (hf : fl'.pending = fl.pending) (h : freedOK W fl txid F) :
    freedOK W' fl' txid F := by
  unfold freedOK at *
  rw [hp, hf]; exact h

end pure

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The transaction during the spill, as resources (see the module doc). -/
def spillR (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) : IProp GF :=
  iprop(dbWR I γd W txl txid ρ ∗ ownWriteTxGX W txl T ∗ wView W ∗ capsOwn T K ∗
    (∃ M : GMap Nat Unit, ghostMapAuth γ 1 M ∗
      ⌜∀ id, (M !! id).isSome ↔ (spillPages W T !! id).isSome⌝) ∗
    pgToks γ F)

/-- What is left after an error: what `Commit`'s rollback needs (`Tx.rollback.wspec`), or,
the database lost in a failed remap, what `Tx.rollback.lspec` needs. -/
def spillErr (I : FLImpl (GF := GF)) (γd : DBNames) (txl : Loc) (txid : w64) : IProp GF :=
  iprop((∃ (W : WView) (ρ : DBState) (T : WTx), dbWR I γd W txl txid ρ ∗ ownWriteTxG W txl T ∗
      wView W ∗ ⌜T.t.writable' = true ∧ T.t.db' = W.dbl ∧
        (T.bs !! structFieldRef Tx go!"root" txl).isSome ∧ T.mv.txid' = txid⌝) ∨
    (∃ (W : WView) (fl : FLState) (T : WTx), dbLost I W.dbl txl txid fl ∗ ownWriteTxG W txl T ∗
      ⌜T.t.writable' = true ∧ T.t.db' = W.dbl ∧
        (T.bs !! structFieldRef Tx go!"root" txl).isSome ∧ T.mv.txid' = txid⌝))

/-- The transaction with only its nodes outside `K` (those with a capacity). -/
def dropCaps (T : WTx) (K : Loc → Bool) : WTx :=
  ⟨T.t, T.mv, T.pm, T.bufs, Iris.Std.PartialMap.map
      (fun B : BRec => ({ B with ns := Iris.Std.PartialMap.filter (fun l _ => !K l) B.ns } : BRec)) T.bs⟩

theorem bktOwn_dropCaps (W : WView) (bl : Loc) (B : BRec) (K : Loc → Bool) :
    bktOwnX (GF := GF) W bl B ∗ ([∗map] l ↦ r ∈ B.ns, if K l then iprop(emp) else capOwn r) ⊢
      bktOwn W bl { B with ns := Iris.Std.PartialMap.filter (fun l _ => !K l) B.ns } := by
  unfold bktOwnX bktOwn
  iintro ⟨⟨Hbv, Hib, Hnm, Hbm, Hpg, Hns⟩, Hc⟩
  rw [show pageOwn (GF := GF) W { B with ns := Iris.Std.PartialMap.filter (fun l _ => !K l) B.ns } =
    pageOwn W B from rfl]
  iframe Hbv Hib Hnm Hbm Hpg
  rw [BigSepM.bigSepM_filter_cond (M := GMap Loc)]
  ihave Hb := (BiEntails.of_eq (BigSepM.bigSepM_sep_eq (M := GMap Loc)
    (Φ := fun l r => nodeOwnX (GF := GF) W l r)
    (Ψ := fun l r => if K l then iprop(emp) else capOwn (GF := GF) r) (m := B.ns))).2 $$ [Hns Hc]
  · iframe
  iapply (BigSepM.bigSepM_mono (M := GMap Loc) ?_) $$ Hb
  intro l r _
  cases hk : K l
  · simp only [Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
    exact (nodeOwn_X W l r).2
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    iintro -
    iempintro

theorem ownWriteTxG_dropCaps (W : WView) (txl : Loc) (T : WTx) (K : Loc → Bool) :
    ownWriteTxGX (GF := GF) W txl T ∗ capsOwn T K ⊢ ownWriteTxG W txl (dropCaps T K) := by
  unfold ownWriteTxGX ownWriteTxG capsOwn dropCaps
  iintro ⟨⟨Ht, Hm, Hpm, Hbufs, Hbs⟩, Hc⟩
  iframe Ht Hm Hpm Hbufs
  simp only
  rw [BigSepM.bigSepM_map (M := GMap Loc)]
  ihave Hb := (BiEntails.of_eq (BigSepM.bigSepM_sep_eq (M := GMap Loc)
    (Φ := fun bl B => bktOwnX (GF := GF) W bl B)
    (Ψ := fun _ B => iprop([∗map] l ↦ r ∈ B.ns, if K l then iprop(emp) else capOwn (GF := GF) r))
    (m := T.bs))).2 $$ [Hbs Hc]
  · iframe
  iapply (BigSepM.bigSepM_mono (M := GMap Loc) ?_) $$ Hb
  intro bl B _
  exact bktOwn_dropCaps W bl B K


/-- What a dereference keeps of the transaction (or none happened). -/
theorem rel0_facts (T T0 : WTx) (rl txl : Loc) (h : T0 = T ∨ (derefRelX T T0 ∧ derefKeep T T0))
    (hd : derefReadyX T rl) (htx : ∀ bl B, T.bs !! bl = some B → B.bv.tx' = txl) :
    T0.t.writable' = T.t.writable' ∧ T0.t.db' = T.t.db' ∧ T0.mv = T.mv ∧ T0.bufs = T.bufs ∧
    T0.pm = T.pm ∧ (∀ k, (T0.bs !! k).isSome ↔ (T.bs !! k).isSome) ∧ derefReadyX T0 rl ∧
    (∀ bl B, T0.bs !! bl = some B → B.bv.tx' = txl) := by
  rcases h with rfl | ⟨hr, -⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ => Iff.rfl, hd, htx⟩
  obtain ⟨ht, hmv, hpm, hbufs, hdom, hb⟩ := hr
  refine ⟨by rw [ht], by rw [ht], hmv, hbufs, hpm, fun k => (hdom k).symm,
    derefReadyX_rel T T0 rl ⟨ht, hmv, hpm, hbufs, hdom, hb⟩ hd, fun bl B0 hB0 => ?_⟩
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 ((hdom bl).2 (by rw [hB0]; rfl))
  rw [(hb bl B B0 hB hB0).1]; exact htx bl B hB

theorem dropCaps_isSome (T : WTx) (K : Loc → Bool) (k : Loc) :
    ((dropCaps T K).bs !! k).isSome = (T.bs !! k).isSome := by
  unfold dropCaps
  change (Iris.Std.PartialMap.get? (Iris.Std.PartialMap.map _ T.bs) _).isSome = _
  rw [Iris.Std.LawfulPartialMap.get?_map (M := GMap Loc)]
  change ((T.bs !! _).map _).isSome = _
  cases T.bs !! k <;> rfl

/-- The transaction's objects keep only the nodes with a capacity: `ownWriteTxG`. -/
theorem spillR_err (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool)
    (hg : spillG (hG := hG) W txl txid T ρ F) (hr : (T.bs !! structFieldRef Tx go!"root" txl).isSome) :
    spillR (GF := GF) I γd γ W txl txid T ρ F K ⊢ spillErr I γd txl txid := by
  obtain ⟨-, -, -, -, -, hmtx, hwr, hdb, -⟩ := hg
  unfold spillR spillErr
  iintro ⟨Hdb, Hg, Hv, Hc, -, -⟩
  ileft
  iexists W, ρ, (dropCaps T K)
  iframe Hdb Hv
  isplitl [Hg Hc]
  · iapply (ownWriteTxG_dropCaps W txl T K) $$ [Hg Hc]
    iframe
  ipureintro
  refine ⟨hwr, hdb, ?_, hmtx⟩
  unfold dropCaps
  simp only
  change (Iris.Std.PartialMap.get? (Iris.Std.PartialMap.map _ T.bs) _).isSome = true
  rw [Iris.Std.LawfulPartialMap.get?_map (M := GMap Loc)]
  change ((T.bs !! _).map _).isSome = true
  cases h : T.bs !! structFieldRef Tx go!"root" txl with
  | none => rw [h] at hr; cases hr
  | some _ => rfl

/-- The header of the dirty page `id` (at `p`, its bytes `b`: the header `hdr`, then `rest`),
lent out of the transaction's page buffers. -/
theorem dirtyHdr (W : WView) (txl : Loc) (T : WTx) (id : w64) (p : Loc) (b : List w8)
    (hp : T.pm !! id = some p) (hb : T.bufs !! id = some b) (h16 : 16 ≤ b.length)
    (hc : p.locCar ≠ 0) :
    ownWriteTxGX (GF := GF) W txl T ⊢
      (p ↦ pageOf b : IProp GF) ∗ bytesPointsto (p +ₗ 16) (DFrac.own 1) (b.drop 16) ∗
      (∀ (hdr : Page) (rest : List w8), (p ↦ hdr : IProp GF) -∗ bytesPointsto (p +ₗ 16) (DFrac.own 1) rest -∗
        ownWriteTxGX W txl { T with bufs := <[id := pageBytes hdr ++ rest]> T.bufs }) := by
  unfold ownWriteTxGX
  iintro ⟨Ht, Hm, Hpm, Hbufs, Hbs⟩
  icases (BigSepM.bigSepM_delete (M := GMap w64)
      (Φ := fun i q => iprop(∃ bs, ⌜T.bufs !! i = some bs⌝ ∗ bytesPointsto (GF := GF) q (DFrac.own 1) bs))
      (show Std.get? T.pm id = some p from hp)).1 $$ Hbufs with ⟨⟨%bs, %Hbs', Hp⟩, Hrest⟩
  rw [hb] at Hbs'
  cases Hbs'
  icases (page_header_bytes p (DFrac.own 1) b h16 hc).1 $$ Hp with ⟨Hh, Hr⟩
  iframe Hh Hr
  iintro %hdr %rest Hh Hr
  iframe Ht Hm Hpm Hbs
  iapply (BigSepM.bigSepM_delete (M := GMap w64)
      (Φ := fun i q => iprop(∃ bs, ⌜(<[id := pageBytes hdr ++ rest]> T.bufs) !! i = some bs⌝ ∗
        bytesPointsto (GF := GF) q (DFrac.own 1) bs))
      (show Std.get? T.pm id = some p from hp)).2
  isplitl [Hh Hr]
  · iexists (pageBytes hdr ++ rest)
    isplitr
    · ipureintro; exact GMap.lookup_insert _ _ _
    iapply (bytesPointsto_app _ _ _ _).2
    have hl : (pageBytes hdr).length = 16 := by unfold pageBytes; simp [leBytes_length']
    rw [hl]
    ihave Hh := (Page_bytes (hG := hG) p hdr (DFrac.own 1) hc).1 $$ Hh
    iframe
  iapply (BigSepM.bigSepM_mono (M := GMap w64)
    (Φ := fun i q => iprop(∃ bs, ⌜T.bufs !! i = some bs⌝ ∗ bytesPointsto (GF := GF) q (DFrac.own 1) bs))
    (Ψ := fun i q => iprop(∃ bs, ⌜(<[id := pageBytes hdr ++ rest]> T.bufs) !! i = some bs⌝ ∗
        bytesPointsto (GF := GF) q (DFrac.own 1) bs)) ?_) $$ Hrest
  intro i q hi
  have hne : i ≠ id := by
    intro e; subst e
    change (GMap.delete i T.pm) !! i = some q at hi
    rw [GMap.lookup_delete] at hi; cases hi
  iintro ⟨%bs, %hbs, H⟩
  iexists bs
  iframe
  ipureintro
  rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact hbs

theorem dbWR_car (I : FLImpl (GF := GF)) (γd : DBNames) (W : WView) (txl : Loc) (txid : w64)
    (ρ : DBState) :
    dbWR I γd W txl txid ρ ⊢ ⌜W.data.locCar ≠ 0⌝ := by
  iintro H
  icases (persistent_entails_left (dbWR_facts I γd W txl txid ρ)) $$ H with ⟨H, %hf⟩
  unfold dbWR
  icases H with ⟨-, %hd⟩
  ipureintro
  obtain ⟨⟨v0, v1, hok⟩, -⟩ := hf
  rw [← hd.2.2.1]; exact hok.2.2.2.2.1

/-- A big separating conjunction over a map, carried to another whose entries come from it. -/
theorem bigSepM_transfer {V V2 : Type} (Φ : Loc → V → IProp GF) (Ψ : Loc → V2 → IProp GF)
    (m₁ : GMap Loc V) (m₂ : GMap Loc V2)
    (h : ∀ k y, m₂ !! k = some y → ∃ x, m₁ !! k = some x ∧ (Φ k x ⊢ Ψ k y)) :
    ([∗map] k ↦ x ∈ m₁, Φ k x) ⊢ [∗map] k ↦ y ∈ m₂, Ψ k y := by
  iintro H
  ihave Hr := (BigSepM.bigSepM_impl_strong (M := GMap Loc) (M₂ := GMap Loc) (Φ := Φ) (Ψ := Ψ)
    (m₁ := m₁) (m₂ := m₂)) $$ [H]
  · isplitl [H]
    · iexact H
    imodintro
    iintro %k %y Hx %hy
    obtain ⟨x, hx, hxy⟩ := h k y hy
    rw [show Iris.Std.PartialMap.get? m₁ k = some x from hx]
    simp only [Option.elim]
    iapply hxy
    iexact Hx
  icases Hr with ⟨Hr, -⟩
  iexact Hr

/-- The capacities survive a dereference keeping the nodes' structs. -/
theorem capsOwn_deref (T T0 : WTx) (K : Loc → Bool)
    (h : T0 = T ∨ (derefRelX T T0 ∧ derefKeep T T0)) :
    capsOwn (GF := GF) T K ⊢ capsOwn T0 K := by
  rcases h with rfl | ⟨hr, hk⟩
  · exact .rfl
  unfold capsOwn
  refine bigSepM_transfer _ _ _ _ (fun bl B0 hB0 => ?_)
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 ((hr.2.2.2.2.1 bl).2 (by rw [hB0]; rfl))
  refine ⟨B, hB, bigSepM_transfer _ _ _ _ (fun l r0 hr0 => ?_)⟩
  obtain ⟨r, hr', -⟩ := (hr.2.2.2.2.2 bl B B0 hB hB0).2.2.2.2.2.2.1 l r0 hr0
  refine ⟨r, hr', ?_⟩
  have he := hk bl B B0 l r r0 hB hB0 hr' hr0
  have hi : r0.nv.inodes' = r.nv.inodes' := by rw [he]
  unfold capOwn
  rw [hi]

/-- The bytes of a dirty page say where it is: not at null. -/
theorem bufs_car (W : WView) (txl : Loc) (T : WTx) (id : w64) (p : Loc) (b : List w8)
    (hp : T.pm !! id = some p) (hb : T.bufs !! id = some b) (hne : b ≠ []) :
    ownWriteTxGX (GF := GF) W txl T ⊢ ⌜p.locCar ≠ 0⌝ := by
  unfold ownWriteTxGX
  iintro ⟨-, -, -, Hbufs, -⟩
  icases (BigSepM.bigSepM_delete (M := GMap w64)
      (Φ := fun i q => iprop(∃ bs, ⌜T.bufs !! i = some bs⌝ ∗ bytesPointsto (GF := GF) q (DFrac.own 1) bs))
      (show Iris.Std.PartialMap.get? T.pm id = some p from hp)).1 $$ Hbufs with ⟨⟨%bs, %Hbs', Hp⟩, -⟩
  rw [hb] at Hbs'
  cases Hbs'
  iapply bytesPointsto_car p (DFrac.own 1) _ hne
  iexact Hp

variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- `tx.allocate(count)` during the spill (see the module doc): the new dirty page `id`, its
token, the transaction possibly dereferenced first (`T0`). -/
theorem spill_alloc (hAlloc : Tx.allocate.xspec (GF := GF) (hG := hG))
    (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc) (txid : w64)
    (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (count : w64)
    (hg : spillG (hG := hG) W txl txid T ρ F) (hc0 : 0 < sint.Z count) (hc1 : sint.Z count ≤ 2 ^ 32)
    (hc2 : sint.Z count * W.ps < 2 ^ 47) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ spillR I γd γ W txl txid T ρ F K }}
      (App (Val (txl @!! go.GoType.PointerType Tx.ty @!! go!"allocate")) (Val #count))
    {{ (p : Loc) (err : GoInterface), RET (PairV #p #err);
        (⌜err = interface.nil⌝ ∗ ∃ (data' : Loc) (T0 T' : WTx) (ρ' : DBState) (id : w64)
            (st : TxStats),
          spillR I γd γ { W with data := data' } txl txid T' ρ' F K ∗ (uint.nat id ↪[γ] () : IProp GF) ∗
          ⌜spillG (hG := hG) { W with data := data' } txl txid T' ρ' F ∧
            (T0 = T ∨ (derefRelX T T0 ∧ derefKeep T T0)) ∧
            T' = allocT T0 st T'.mv.pgid' id p (freshPage id (uint.nat count) W.ps) ∧
            T0.mv = T.mv ∧ T0.bufs = T.bufs ∧ T0.pm = T.pm ∧
            T.pm !! id = none ∧ W.pages !! uint.nat id = none ∧ 2 ≤ uint.nat id ∧
            uint.nat id + uint.nat count ≤ uint.nat T'.mv.pgid' ∧
            uint.nat T.mv.pgid' ≤ uint.nat T'.mv.pgid' ∧ p.locCar ≠ 0⌝) ∨
        (⌜err ≠ interface.nil⌝ ∗ spillErr I γd txl txid) }} := by
  obtain ⟨hv, hvd, hvb, hhwm, hps48, hmtx, hwr, hdb, hdbn, htx, hdirty, hau, hfr, hdr⟩ := hg
  subst hmtx
  iintro %Φ ⟨#Hpkg, Hs⟩ HΦ
  unfold spillR
  icases Hs with ⟨Hdb, Hg, Hv, Hc, ⟨%M, Ha, %HM⟩, HF⟩
  icases (persistent_entails_left (dbWR_facts I γd W txl T.mv.txid' ρ)) $$ Hdb with ⟨Hdb, %Hf⟩
  obtain ⟨hok, hρps, w, hw, hwp, hwh⟩ := Hf
  have h16 : 16 ≤ W.ps := by have := hv.2.1; omega
  iapply wp_fupd
  wp_apply hAlloc I γd W txl T ρ count hc0 hc1 hc2 hps48 hhwm hdr hdb hv.1 htx h16
    $$ [Hdb Hg Hv] as %p %err Hpost
  · iframe
  icases Hpost with (⟨%ρ', %data', %T0, %T', Hdb, Hg, Hv, %Hres⟩ | ⟨%Herr, %T0, %HrelL, Hlost, Hg⟩)
  · obtain ⟨Hd0, Hcase⟩ := Hres
    have Hk0 : T0 = T ∨ (derefRelX T T0 ∧ derefKeep T T0) := by
      rcases Hd0 with ⟨h, -⟩ | ⟨h1, h2, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2⟩
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := rel0_facts T T0 _ txl Hk0 hdr htx
    ihave Hc := capsOwn_deref T T0 K Hk0 $$ Hc
    rcases Hcase with ⟨hne, hT', hρ'⟩ | ⟨herr, id0, st0, w0, hw0, hok0, hT0⟩
    · subst T' ρ'
      imodintro
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact hne
      unfold spillErr
      ileft
      iexists { W with data := data' }, ρ, (dropCaps T0 K)
      ihave Hg := ownWriteTxG_dropCaps _ txl T0 K $$ [Hg Hc]
      · iframe
      iframe
      ipureintro
      refine ⟨by rw [show (dropCaps T0 K).t = T0.t from rfl, f1]; exact hwr,
        by rw [show (dropCaps T0 K).t = T0.t from rfl, f2]; exact hdb, ?_,
        by rw [show (dropCaps T0 K).mv = T0.mv from rfl, f3]⟩
      rw [dropCaps_isSome]; exact (f6 _).2 hdr.1
    · subst herr
      have hc0' : 0 < uint.nat count := by unfold uint.nat; word
      have hc32' : uint.nat count ≤ 2 ^ 32 := by unfold uint.nat; word
      obtain ⟨hdirty', hau', id, st, hT', h0pm, h0bufs, hwid, hid2, hidc, hpg, hps48', hrd, hwr', hps'⟩ :=
        spillDirty_alloc ρ ρ' W T T0 T' count p data' hc0' hc32' h16 hok hρps
          (fun w' hw' => by rw [hw] at hw'; cases hw'; exact hwp)
          (fun w' hw' => by rw [hw] at hw'; cases hw'; exact hwh) hdirty hau hhwm ⟨Hd0, Or.inr ⟨rfl, id0, st0, w0, hw0, hok0, hT0⟩⟩
      -- the new page's token
      have hid64 : uint.nat id < 2 ^ 64 := by unfold uint.nat; have := id.isLt; omega
      have hidw : W64 ((uint.nat id : Nat) : Int) = id := by unfold uint.nat; word
      have hM0 : M.lookup (uint.nat id) = none := by
        cases hm : M.lookup (uint.nat id) with
        | none => rfl
        | some _ =>
          have h1 := (HM (uint.nat id)).1 (by change (M !! _).isSome = true; rw [show M !! uint.nat id = M.lookup (uint.nat id) from rfl, hm]; rfl)
          unfold spillPages at h1
          rw [GMap.lookup_union, hwid, bufsN_lookup, if_pos hid64, hidw, ← f4, h0bufs] at h1
          simp at h1
      imod ghost_map_insert (GF := GF) (γ := γ) (uint.nat id) () hM0 $$ Ha with ⟨Ha, Htok⟩
      -- the page is not at null
      have hpT : T'.pm !! id = some p := by rw [hT']; exact GMap.lookup_insert _ _ _
      have hbT : T'.bufs !! id = some (freshPage id (uint.nat count) W.ps) := by
        rw [hT']; exact GMap.lookup_insert _ _ _
      have hne : freshPage id (uint.nat count) W.ps ≠ [] := by
        intro h; have := congrArg List.length h; simp [freshPage, leBytes_length'] at this
      icases (persistent_entails_left (bufs_car { W with data := data' } txl T' id p _ hpT hbT hne))
        $$ Hg with ⟨Hg, %hpc⟩
      icases (persistent_entails_left (dbWR_car I γd { W with data := data' } txl T.mv.txid' ρ'))
        $$ Hdb with ⟨Hdb, %hcar⟩
      imodintro
      iapply HΦ
      ileft
      isplitr
      · ipureintro; rfl
      iexists data', T0, T', ρ', id, st
      have hcaps : capsOwn (GF := GF) T' K = capsOwn T0 K := by rw [hT']; rfl
      rw [hcaps]
      iframe Hdb Hg Hv Hc HF Htok
      isplitl [Ha]
      · iexists (M.insert (uint.nat id) ())
        iframe
        ipureintro
        intro n
        unfold spillPages
        change (M.insert (uint.nat id) () |>.lookup n).isSome = true ↔ _
        rw [GMap.lookup_union]
        by_cases hn : n = uint.nat id
        · subst hn
          simp only [GMap.insert, Option.isSome_some, true_iff]
          rw [bufsN_lookup, if_pos hid64, hidw, hbT]
          cases W.pages !! uint.nat id <;> rfl
        · have hl : (M.insert (uint.nat id) ()).lookup n = M.lookup n := by
            simp only [GMap.insert]; rw [if_neg (Ne.symm hn)]
          rw [hl]
          have hb' : bufsN T'.bufs !! n = bufsN T.bufs !! n := by
            rw [bufsN_lookup, bufsN_lookup]
            by_cases h64 : n < 2 ^ 64
            · rw [if_pos h64, if_pos h64, hT']
              show (<[id := _]> T0.bufs) !! W64 (n : Int) = _
              rw [GMap.lookup_insert_ne _ _ (by intro e; apply hn; rw [e]; unfold uint.nat; word), f4]
            · rw [if_neg h64, if_neg h64]
          rw [hb']
          have := HM n
          unfold spillPages at this
          rw [GMap.lookup_union] at this
          exact this
      ipureintro
      have hmv' : T'.mv.txid' = T.mv.txid' := by rw [hT']; show T0.mv.txid' = _; rw [f3]
      have ht' : T'.t = { T0.t with stats' := st } := by rw [hT']; rfl
      refine ⟨⟨⟨hcar, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2⟩, hvd, hvb, by show W.hwm ≤ _; omega, hps48', hmv',
        by rw [ht']; exact f1.trans hwr, by rw [ht']; exact f2.trans hdb, hdbn,
        by rw [hT']; exact f8, hdirty', hau',
        freedOK_pending W _ ρ.fl ρ'.fl _ F rfl
          (allocOK_pending ρ ρ' w0 T.mv T'.mv T.mv.txid' id0 _ hok0) hfr,
        derefReadyX_bs T0 T' _ (by rw [hT']; rfl) f7⟩,
        Hk0, hT', f3, f4, f5, by rw [← f5]; exact h0pm, hwid, hid2, hidc, hpg, hpc⟩
  · imodintro
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact Herr
    unfold spillErr
    iright
    obtain ⟨Hrel, Hkeep, -⟩ := HrelL
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := rel0_facts T T0 _ txl (Or.inr ⟨Hrel, Hkeep⟩) hdr htx
    ihave Hc := capsOwn_deref T T0 K (Or.inr ⟨Hrel, Hkeep⟩) $$ Hc
    iexists W, ρ.fl, (dropCaps T0 K)
    iframe Hlost
    isplitl [Hg Hc]
    · iapply (ownWriteTxG_dropCaps W txl T0 K) $$ [Hg Hc]
      iframe
    ipureintro
    refine ⟨by rw [show (dropCaps T0 K).t = T0.t from rfl, f1]; exact hwr,
      by rw [show (dropCaps T0 K).t = T0.t from rfl, f2]; exact hdb, ?_,
      by rw [show (dropCaps T0 K).mv = T0.mv from rfl, f3]⟩
    rw [dropCaps_isSome]; exact (f6 _).2 hdr.1

end own

end bbolt
end EtcdGrove
end Perennial
