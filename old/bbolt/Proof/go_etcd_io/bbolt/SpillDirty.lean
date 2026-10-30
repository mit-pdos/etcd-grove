/-
The dirty pages during the spill (`spillDirty`): what `Tx.write` will need of them
(`DBWrite.lean`'s `dirtyOK`, but for the slots being inside the file, which `Commit`'s `grow`
gives), and what keeps a later allocation off them. Their slots are seen by no view
(`slotUnseen`), are no page of the writer's view, and are not free; distinct ones are disjoint.

An allocation takes free slots, or slots at the high-water mark and above, all seen by no view
(`allocUnseen`, from the database's facts: `dbWR_allocUnseen`); so its page is new to the dirty
ones and to the view (`spillDirty_alloc`). A free (`Free`: pending, not free) keeps it all
(`spillDirty_free`); `node.write` rewrites a dirty page keeping its length, id and overflow
(`spillDirty_write`).
-/
module

public import Proof.go_etcd_io.bbolt.SpillDefs
public import Proof.go_etcd_io.bbolt.DBWrite
public import Spec.go_etcd_io.bbolt.Tx__allocate_x
public import Proof.go_etcd_io.bbolt.MetaInj
public import Proof.go_etcd_io.bbolt.DBRemap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The slots an allocation may take are seen by no view: the free ones, and those from the
high-water mark `h` on (which are not free); slots 0 and 1 (the metas) aside. -/
def allocUnseen (ρ : DBState) (h : Nat) : Prop :=
  (∀ s : Nat, 2 ≤ s → s < 2 ^ 64 → W64 (s : Int) ∈ ρ.fl.free → slotUnseen ρ s) ∧
  (∀ s, h ≤ s → (2 ≤ s → slotUnseen ρ s) ∧ (s < 2 ^ 64 → W64 (s : Int) ∉ ρ.fl.free))

/-- The dirty pages of `T` (see the module doc), the view `W`, the database `ρ`. -/
def spillDirty (ρ : DBState) (W : WView) (T : WTx) : Prop :=
  (∀ id, (T.pm !! id).isSome ↔ (T.bufs !! id).isSome) ∧
  (∀ id b, T.bufs !! id = some b →
    b.length = dspan b * W.ps ∧ pageId b = uint.nat id ∧ 2 ≤ uint.nat id ∧
    uint.nat id + dspan b ≤ uint.nat T.mv.pgid' ∧
    ∀ k < dspan b, slotUnseen ρ (uint.nat id + k) ∧
      (∀ v0 v1, dbOK ρ v0 v1 → ¬ inFlPage ρ v0 v1 (uint.nat id + k)) ∧
      ¬ coversSlot W.pages (uint.nat id + k) ∧ W64 ((uint.nat id + k : Nat) : Int) ∉ ρ.fl.free) ∧
  ∀ i1 b1 i2 b2, T.bufs !! i1 = some b1 → T.bufs !! i2 = some b2 → i1 ≠ i2 →
    uint.nat i1 + dspan b1 ≤ uint.nat i2 ∨ uint.nat i2 + dspan b2 ≤ uint.nat i1

/-! ### Helpers -/

theorem dspan_pos (b : List w8) : 1 ≤ dspan b := by unfold dspan; omega

/-- Two runs with no common slot are apart. -/
theorem runs_apart (x n1 y n2 : Nat) (h1 : 1 ≤ n1) (h2 : 1 ≤ n2)
    (h : ∀ a < n1, ∀ b < n2, x + a ≠ y + b) : x + n1 ≤ y ∨ y + n2 ≤ x := by
  by_cases hxy : x ≤ y
  · left
    refine Classical.byContradiction fun hc => ?_
    exact h (y - x) (by omega) 0 (by omega) (by omega)
  · right
    refine Classical.byContradiction fun hc => ?_
    exact h 0 (by omega) (x - y) (by omega) (by omega)

/-- The metas of the database's facts are the bytes'. -/
theorem dbOK_metas_eq (σ σ' : DBState) (v0 v1 v0' v1' : internal.common.Meta)
    (h : dbOK σ v0 v1) (h' : dbOK σ' v0' v1') (hbs : σ'.bs = σ.bs) (hps : σ'.ps = σ.ps) :
    v0' = v0 ∧ v1' = v1 := by
  obtain ⟨-, -, -, -, -, h0, h1, -⟩ := h
  obtain ⟨-, -, -, -, -, h0', h1', -⟩ := h'
  unfold metaIn at h0 h1 h0' h1'
  rw [hbs, hps] at h0' h1'
  exact ⟨metaBytes_inj _ _ (h0'.symm.trans h0), metaBytes_inj _ _ (h1'.symm.trans h1)⟩

/-- A slot no view sees stays unseen in a state with the same bytes, page size, readers and
writer (another freelist, another mapping). -/
theorem slotUnseen_congr (σ σ' : DBState) (hbs : σ'.bs = σ.bs) (hps : σ'.ps = σ.ps)
    (hrd : σ'.readers = σ.readers) (hwr : σ'.wr = σ.wr) (hok : ∃ v0 v1, dbOK σ v0 v1) (s : Nat)
    (h : slotUnseen σ s) : slotUnseen σ' s := by
  obtain ⟨h2, hr, hw, hc⟩ := h
  refine ⟨h2, fun k r hk => hr k r (by rw [← hrd]; exact hk),
    fun w hw' => hw w (by rw [← hwr]; exact hw'), fun v0' v1' hok' => ?_⟩
  obtain ⟨v0, v1, hok0⟩ := hok
  obtain ⟨e0, e1⟩ := dbOK_metas_eq σ σ' v0 v1 v0' v1' hok0 hok' hbs hps
  rw [e0, e1]
  have : curPages σ' v0 v1 = curPages σ v0 v1 := by unfold curPages; rw [hbs, hps]
  rw [this]; exact hc v0 v1 hok0

/-- A slot off the current freelist page stays off it in a state with the same bytes and page
size. -/
theorem spNotFl_congr (σ σ' : DBState) (hbs : σ'.bs = σ.bs) (hps : σ'.ps = σ.ps)
    (hok : ∃ v0 v1, dbOK σ v0 v1) (s : Nat)
    (h : ∀ v0 v1, dbOK σ v0 v1 → ¬ inFlPage σ v0 v1 s) :
    ∀ v0 v1, dbOK σ' v0 v1 → ¬ inFlPage σ' v0 v1 s := by
  intro v0' v1' hok'
  obtain ⟨v0, v1, hok0⟩ := hok
  obtain ⟨e0, e1⟩ := dbOK_metas_eq σ σ' v0 v1 v0' v1' hok0 hok' hbs hps
  rw [e0, e1]
  unfold inFlPage
  rw [hbs, hps]
  exact h v0 v1 hok0

/-- A view whose pages are the file's, ending below `H`, covers only slots below `H`. -/
theorem covers_lt (bs : List w8) (ps : Nat) (hps : 16 ≤ ps) (P : GMap Nat (List w8)) (n H s : Nat)
    (hin : ∀ id pg, P !! id = some pg → pageAt bs ps id = pg ∧ id + pageSpan bs ps id ≤ min n H)
    (hc : coversSlot P s) : s < H := by
  obtain ⟨id, pg, hid, h1, h2⟩ := hc
  obtain ⟨ha, hb⟩ := hin id pg hid
  have := span_of_pageAt bs ps id pg hps ha.symm
  have : min n H ≤ H := Nat.min_le_right _ _
  omega

/-- The database's facts give the slots an allocation may take, unseen (readers no newer than
the writer's high-water mark: `hrh`). -/
theorem allocUnseen_of_dbOK (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (w : Reader) (hw : σ.wr = some w) (H : Nat) (hwh : w.hwm = H)
    (hrh : ∀ k r, σ.readers !! k = some r → r.hwm ≤ H) : allocUnseen σ H := by
  have hok := h
  obtain ⟨hps, -, -, -, -, -, -, -, hcur, hrd, hmv, -, -, -, -, hwr⟩ := h
  obtain ⟨-, -, cin, -, cfree, cbelow, -⟩ := hcur
  obtain ⟨b1, -, -, b4, -, -, -⟩ := cbelow
  have hb4 := (b4 w hw).1
  have hps16 : 16 ≤ σ.ps := by omega
  have hwo := writer_readerOK σ v0 v1 hok w hw
  have hwm := (hwr.2 w hw).2
  -- the current tree's metas: those of the facts
  have hcm : ∀ v0' v1', dbOK σ v0' v1' → v0' = v0 ∧ v1' = v1 :=
    fun v0' v1' h' => dbOK_metas_eq σ σ v0 v1 v0' v1' hok h' rfl rfl
  refine ⟨fun s hs2 hs64 hfree => ⟨hs2, fun k r hk hc => ?_, fun w' hw' hc => ?_,
    fun v0' v1' h' hc => ?_⟩, fun s hs => ⟨fun hs2 => ⟨hs2, fun k r hk hc => ?_, fun w' hw' hc => ?_,
    fun v0' v1' h' hc => ?_⟩, fun hs64 hfree => ?_⟩⟩
  · exact ((hmv k r hk).2 s hc).2.1 hfree
  · rw [hw] at hw'; cases hw'
    exact (hwm.2 s hc).2.1 hfree
  · obtain ⟨rfl, rfl⟩ := hcm v0' v1' h'
    exact (cfree s hc).2.1 hfree
  · have := covers_lt σ.bs σ.ps hps16 r.pages σ.nslots r.hwm s (hrd k r hk).2.2 hc
    have := hrh k r hk
    omega
  · rw [hw] at hw'; cases hw'
    have := covers_lt σ.bs σ.ps hps16 w.pages σ.nslots w.hwm s hwo.2.2 hc
    omega
  · obtain ⟨rfl, rfl⟩ := hcm v0' v1' h'
    unfold curPages at hc
    obtain ⟨id, pg, hid, h1, h2⟩ := hc
    have hpg := filePages_some _ _ _ _ _ (treePages_lookup _ _ id pg hid)
    have := span_of_pageAt σ.bs σ.ps id pg hps16 hpg
    have := cin id pg hid
    have : min σ.nslots (uint.nat (if metaPick v0' v1' then v1' else v0').pgid') ≤
      uint.nat (if metaPick v0' v1' then v1' else v0').pgid' := Nat.min_le_right _ _
    omega
  · have := b1 _ hfree
    have e : uint.Z (W64 (s : Int)) = (s : Int) := uint_Z_W64 _ (by omega) (by omega)
    rw [e] at this
    have : (uint.nat (if metaPick v0 v1 then v1 else v0).pgid' : Int) =
        uint.Z (if metaPick v0 v1 then v1 else v0).pgid' := rfl
    omega

/-- The writer's view and facts out of the database. -/
theorem dbWR_facts (I : FLImpl (GF := GF)) (γ : DBNames) (W : WView) (txl : Loc) (txid : w64)
    (ρ : DBState) :
    dbWR I γ W txl txid ρ ⊢ ⌜(∃ v0 v1, dbOK ρ v0 v1) ∧ ρ.ps = W.ps ∧
      ∃ w, ρ.wr = some w ∧ w.pages = W.pages ∧ w.hwm = W.hwm⌝ := by
  unfold dbWR
  iintro ⟨Hdb, %Hd⟩
  obtain ⟨-, -, -, hps, -, w, hw, hwp, -, hwh, -, -⟩ := Hd
  isimp only [ownDB] at Hdb
  iNamed Hdb
  ipureintro
  exact ⟨⟨v0, v1, Hok⟩, hps, w, hw, hwp, hwh⟩

/-- No dirty page yet. -/
theorem spillDirty_empty (ρ : DBState) (W : WView) (T : WTx) (hpm : T.pm = ∅)
    (hb : T.bufs = ∅) : spillDirty ρ W T := by
  refine ⟨fun id => ?_, fun id b h => ?_, fun i1 b1 i2 b2 h1 => ?_⟩
  · rw [hpm, hb]; rfl
  · rw [hb] at h; cases h
  · rw [hb] at h1; cases h1

/-- The database's facts give the slots an allocation may take, unseen, if no reader is newer
than the writer's view's high-water mark (`hrh`: not a fact of `dbOK`). -/
theorem dbWR_allocUnseen (I : FLImpl (GF := GF)) (γ : DBNames) (W : WView) (txl : Loc) (txid : w64)
    (ρ : DBState) (hrh : ∀ k r, ρ.readers !! k = some r → r.hwm ≤ W.hwm) :
    dbWR I γ W txl txid ρ ⊢ ⌜allocUnseen ρ W.hwm⌝ := by
  unfold dbWR
  iintro ⟨Hdb, %Hd⟩
  obtain ⟨-, -, -, -, -, w, hw, -, -, hwh, -, -⟩ := Hd
  isimp only [ownDB] at Hdb
  iNamed Hdb
  ipureintro
  exact allocUnseen_of_dbOK ρ v0 v1 Hok w hw W.hwm hwh hrh

/-- The page `Tx.allocate` returns: its length, id and slots. -/
theorem freshPage_facts (id : w64) (n ps : Nat) (hn : 0 < n) (h32 : n ≤ 2 ^ 32) (hps : 16 ≤ ps) :
    (freshPage id n ps).length = n * ps ∧ pageId (freshPage id n ps) = uint.nat id ∧
      dspan (freshPage id n ps) = n := by
  have h16 : 16 ≤ n * ps := Nat.le_trans hps (Nat.le_mul_of_pos_left _ hn)
  refine ⟨?_, ?_, ?_⟩
  · unfold freshPage; simp only [List.length_append, leBytes_length', List.length_replicate]; omega
  · unfold freshPage pageId
    rw [List.append_assoc, List.append_assoc,
      leAt_app_left _ _ 0 8 (by rw [leBytes_length']; omega),
      show uint.Z id = ((uint.nat id : Nat) : Int) from rfl,
      leAt_leBytes 8 _ (by have := id.isLt; simpa using this)]
  · unfold dspan freshPage pageOverflow
    have := leAt_leBytes_app (leBytes 8 (uint.Z id) ++ leBytes 4 0)
      (List.replicate (n * ps - 16) (0 : w8)) 4 (n - 1) (by omega)
    simp only [List.length_append, leBytes_length'] at this
    rw [this]; omega

/-- An allocation (`Tx.allocate.xspec`'s `xallocRes`, without an error) keeps the dirty pages'
facts, and its page `id` is new: no page of the view, no dirty page. -/
theorem spillDirty_alloc (ρ ρ' : DBState) (W : WView) (T T0 T' : WTx) (count : w64) (p : Loc)
    (data' : Loc) (hc0 : 0 < uint.nat count) (hc32 : uint.nat count ≤ 2 ^ 32) (hps : 16 ≤ W.ps)
    (hok : ∃ v0 v1, dbOK ρ v0 v1) (hρps : ρ.ps = W.ps)
    (hwv : ∀ w, ρ.wr = some w → w.pages = W.pages)
    (hwhw : ∀ w, ρ.wr = some w → w.hwm = W.hwm)
    (hd : spillDirty ρ W T) (hu : allocUnseen ρ W.hwm) (hwh : W.hwm ≤ uint.nat T.mv.pgid')
    (hr : xallocRes W T T0 T' count p interface.nil data' ρ ρ') :
    spillDirty ρ' { W with data := data' } T' ∧ allocUnseen ρ' W.hwm ∧
    ∃ (id : w64) (st : TxStats), T' = allocT T0 st T'.mv.pgid' id p (freshPage id (uint.nat count) W.ps) ∧
      T0.pm !! id = none ∧ T0.bufs !! id = none ∧ W.pages !! uint.nat id = none ∧
      2 ≤ uint.nat id ∧ uint.nat id + uint.nat count ≤ uint.nat T'.mv.pgid' ∧
      uint.nat T.mv.pgid' ≤ uint.nat T'.mv.pgid' ∧ uint.Z T'.mv.pgid' * W.ps < 2 ^ 48 ∧
      ρ'.readers = ρ.readers ∧ ρ'.wr = ρ.wr ∧ ρ'.ps = ρ.ps := by
  obtain ⟨hT0, hres⟩ := hr
  rcases hres with ⟨hne, -⟩ | ⟨-, id, st, w, hw, hal, hT'⟩
  · exact absurd rfl hne
  have hT0e : T0.bufs = T.bufs ∧ T0.pm = T.pm ∧ T0.mv = T.mv := by
    rcases hT0 with ⟨rfl, -⟩ | ⟨⟨-, hmv, hpm, hbufs, -⟩, -, -⟩
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨hbufs, hpm, hmv⟩
  obtain ⟨hT0b, hT0p, hT0m⟩ := hT0e
  have hwp := hwv w hw
  have hnfl : ∀ k < uint.nat count, ∀ v0' v1', dbOK ρ' v0' v1' →
      ¬ inFlPage ρ' v0' v1' (uint.nat id + k) := by
    obtain ⟨v0, v1, hok0⟩ := hok
    have hmv0 : w.hwm ≤ uint.nat T.mv.pgid' := by rw [hwhw w hw]; exact hwh
    exact fun k hk v0' v1' h' => (allocOK_unseen' ρ ρ' v0 v1 hok0 w hw T.mv T'.mv T.mv.txid' id
      (uint.nat count) hmv0 hal k hk v0' v1' h').2
  obtain ⟨hid2, hslots, hmv', hle, h48, hidn, hcases⟩ := hal
  have hfacts := freshPage_facts id (uint.nat count) W.ps hc0 hc32 hps
  generalize uint.nat count = n at *
  generalize hfpe : freshPage id n W.ps = fp at *
  obtain ⟨fpl, fpi, fps⟩ := hfacts
  have hb' : T'.bufs = <[id := fp]> T.bufs := by rw [← hT0b]; exact congrArg WTx.bufs hT'
  have hp' : T'.pm = <[id := p]> T.pm := by rw [← hT0p]; exact congrArg WTx.pm hT'
  have hpgZ : uint.Z T'.mv.pgid' < 2 ^ 64 := uint_Z_lt _
  have z1 : uint.Z id = ((uint.nat id : Nat) : Int) := rfl
  have z2 : uint.Z T.mv.pgid' = ((uint.nat T.mv.pgid' : Nat) : Int) := rfl
  have z3 : uint.Z T'.mv.pgid' = ((uint.nat T'.mv.pgid' : Nat) : Int) := rfl
  have hid64 : uint.nat id + n < 2 ^ 64 := by
    have : (uint.nat id : Int) + n ≤ uint.Z T'.mv.pgid' := hidn
    omega
  have hle' : uint.nat T.mv.pgid' ≤ uint.nat T'.mv.pgid' := by
    have : uint.Z T.mv.pgid' ≤ uint.Z T'.mv.pgid' := hle
    omega
  have hidn' : uint.nat id + n ≤ uint.nat T'.mv.pgid' := by
    have : (uint.nat id : Int) + n ≤ uint.Z T'.mv.pgid' := hidn
    omega
  have hw64 : ∀ k < n, uint.Z (W64 ((uint.nat id + k : Nat) : Int)) = ((uint.nat id + k : Nat) : Int) :=
    fun k hk => uint_Z_W64 _ (by omega) (by omega)
  -- the database after: the same bytes, readers, writer; fewer free ids; the new slots
  obtain ⟨hbs, hpss, hrds, hwrs, hsub, hnew⟩ : ρ'.bs = ρ.bs ∧ ρ'.ps = ρ.ps ∧
      ρ'.readers = ρ.readers ∧ ρ'.wr = ρ.wr ∧ (∀ x, x ∈ ρ'.fl.free → x ∈ ρ.fl.free) ∧
      ∀ k < n, (W64 ((uint.nat id + k : Nat) : Int) ∈ ρ.fl.free ∨ uint.nat T.mv.pgid' ≤ uint.nat id + k) ∧
        W64 ((uint.nat id + k : Nat) : Int) ∉ ρ'.fl.free := by
    rcases hcases with ⟨hcan, rfl, -⟩ | ⟨hidm, -, hρ'⟩
    · refine ⟨rfl, rfl, rfl, rfl, fun x hx => (List.mem_filter.1 hx).1, fun k hk => ⟨Or.inl ?_, ?_⟩⟩
      · apply hcan.2; unfold inRun; rw [hw64 k hk]; omega
      · intro hx
        have := (List.mem_filter.1 hx).2
        simp only [decide_eq_true_eq] at this
        apply this; unfold inRun; rw [hw64 k hk]; omega
    · have hk : ∀ k < n, uint.nat T.mv.pgid' ≤ uint.nat id + k := by
        intro k _; rw [hidm]; omega
      have hnf : ∀ k < n, W64 ((uint.nat id + k : Nat) : Int) ∉ ρ.fl.free := fun k hk' =>
        (hu.2 _ (Nat.le_trans hwh (hk k hk'))).2 (by omega)
      rcases hρ' with rfl | ⟨d', sz', -, rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl, fun x hx => hx, fun k hk' => ⟨Or.inr (hk k hk'), hnf k hk'⟩⟩
      · exact ⟨rfl, rfl, rfl, rfl, fun x hx => hx, fun k hk' => ⟨Or.inr (hk k hk'), hnf k hk'⟩⟩
  have hcong := slotUnseen_congr ρ ρ' hbs hpss hrds hwrs hok
  have hcongF := spNotFl_congr ρ ρ' hbs hpss hok
  obtain ⟨hd1, hd2, hd3⟩ := hd
  -- a new slot is no old dirty slot
  have hnotold : ∀ i b, T.bufs !! i = some b → ∀ k1 < dspan b, ∀ k < n,
      uint.nat i + k1 ≠ uint.nat id + k := by
    intro i b hib k1 hk1 k hk heq
    obtain ⟨-, -, -, hend, hsl⟩ := hd2 i b hib
    rcases (hnew k hk).1 with hf | hge
    · apply (hsl k1 hk1).2.2.2; rw [heq]; exact hf
    · omega
  have hnewU : ∀ k < n, slotUnseen ρ (uint.nat id + k) := by
    intro k hk
    have h2 : 2 ≤ uint.nat id + k := by have : (2 : Int) ≤ uint.nat id := hid2; omega
    rcases (hnew k hk).1 with hf | hge
    · exact hu.1 _ h2 (by omega) hf
    · exact (hu.2 _ (Nat.le_trans hwh hge)).1 h2
  have hid0 : W64 ((uint.nat id : Nat) : Int) = id := by simp [uint.nat]
  have hidb : T.bufs !! id = none := by
    cases hb : T.bufs !! id with
    | none => rfl
    | some b =>
      exact absurd rfl (hnotold id b hb 0 (dspan_pos b) 0 hc0)
  refine ⟨⟨fun i => ?_, fun i b hib => ?_, fun i1 b1 i2 b2 h1 h2 hne => ?_⟩, ⟨fun s hs2 hs64 hf =>
    hcong s (hu.1 s hs2 hs64 (hsub _ hf)), fun s hs => ⟨fun hs2 => hcong s ((hu.2 s hs).1 hs2),
    fun hs64 hf => (hu.2 s hs).2 hs64 (hsub _ hf)⟩⟩, id, st, by rw [hfpe]; exact hT', ?_⟩
  · rw [hb', hp']
    by_cases e : i = id
    · subst e; simp
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e), GMap.lookup_insert_ne _ _ (Ne.symm e)]
      exact hd1 i
  · rw [hb'] at hib
    by_cases e : i = id
    · subst e
      rw [GMap.lookup_insert] at hib; cases hib
      refine ⟨by rw [fpl, fps], fpi, by have : (2 : Int) ≤ uint.nat i := hid2; omega,
        by rw [fps]; exact hidn', fun k hk => ?_⟩
      rw [fps] at hk
      refine ⟨hcong _ (hnewU k hk), hnfl k hk, ?_, (hnew k hk).2⟩
      show ¬ coversSlot W.pages _
      rw [← hwp]; exact hslots k hk
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hib
      obtain ⟨a1, a2, a3, a4, a5⟩ := hd2 i b hib
      refine ⟨a1, a2, a3, Nat.le_trans a4 hle', fun k hk => ?_⟩
      obtain ⟨c1, c0, c2, c3⟩ := a5 k hk
      exact ⟨hcong _ c1, hcongF _ c0, c2, fun hx => c3 (hsub _ hx)⟩
  · rw [hb'] at h1 h2
    by_cases e1 : i1 = id
    · subst e1
      rw [GMap.lookup_insert] at h1; cases h1
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hne).symm] at h2
      rw [fps]
      rcases runs_apart (uint.nat i2) (dspan b2) (uint.nat i1) n (dspan_pos b2) hc0
        (fun a ha b hb => hnotold i2 b2 h2 a ha b hb) with h | h
      · right; exact h
      · left; exact h
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e1)] at h1
      by_cases e2 : i2 = id
      · subst e2
        rw [GMap.lookup_insert] at h2; cases h2
        rw [fps]
        exact runs_apart (uint.nat i1) (dspan b1) (uint.nat i2) n (dspan_pos b1) hc0
          (fun a ha b hb => hnotold i1 b1 h1 a ha b hb)
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm e2)] at h2
        exact hd3 i1 b1 i2 b2 h1 h2 hne
  · refine ⟨?_, by rw [hT0b]; exact hidb, ?_, by have : (2 : Int) ≤ uint.nat id := hid2; omega,
      hidn', hle', by rw [← hρps]; exact h48, hrds, hwrs, hpss⟩
    · rw [hT0p]
      cases hp : T.pm !! id with
      | none => rfl
      | some _ =>
        have := (hd1 id).1 (by rw [hp]; rfl)
        rw [hidb] at this; cases this
    · cases hpg : W.pages !! uint.nat id with
      | none => rfl
      | some pg =>
        exfalso
        have := hslots 0 hc0
        rw [hwp] at this
        exact this ⟨uint.nat id, pg, hpg, by omega, by omega⟩

/-- A free of a page of the view keeps them. -/
theorem spillDirty_free (ρ : DBState) (W : WView) (T : WTx) (txid id : w64) (n : Nat)
    (hok : ∃ v0 v1, dbOK ρ v0 v1)
    (hd : spillDirty ρ W T) (hu : allocUnseen ρ W.hwm) :
    spillDirty { ρ with fl := ρ.fl.freePages txid id n } W T ∧
      allocUnseen { ρ with fl := ρ.fl.freePages txid id n } W.hwm := by
  have hcong := slotUnseen_congr ρ { ρ with fl := ρ.fl.freePages txid id n } rfl rfl rfl rfl hok
  have hcongF := spNotFl_congr ρ { ρ with fl := ρ.fl.freePages txid id n } rfl rfl hok
  have hfree : ({ ρ with fl := ρ.fl.freePages txid id n } : DBState).fl.free = ρ.fl.free := rfl
  obtain ⟨hd1, hd2, hd3⟩ := hd
  refine ⟨⟨hd1, fun i b hib => ?_, hd3⟩, fun s hs2 hs64 hf => hcong s (hu.1 s hs2 hs64 (by rw [hfree] at hf; exact hf)),
    fun s hs => ⟨fun hs2 => hcong s ((hu.2 s hs).1 hs2), fun hs64 => by rw [hfree]; exact (hu.2 s hs).2 hs64⟩⟩
  obtain ⟨a1, a2, a3, a4, a5⟩ := hd2 i b hib
  refine ⟨a1, a2, a3, a4, fun k hk => ?_⟩
  obtain ⟨c1, c0, c2, c3⟩ := a5 k hk
  exact ⟨hcong _ c1, hcongF _ c0, c2, by rw [hfree]; exact c3⟩

/-- A dirty page rewritten with the same length, id and overflow keeps them. -/
theorem spillDirty_write (ρ : DBState) (W : WView) (T : WTx) (id : w64) (b b' : List w8)
    (hd : spillDirty ρ W T) (hb : T.bufs !! id = some b) (hl : b'.length = b.length)
    (hi : pageId b' = pageId b) (ho : pageOverflow b' = pageOverflow b) :
    spillDirty ρ W { T with bufs := <[id := b']> T.bufs } := by
  have hds : dspan b' = dspan b := by unfold dspan; rw [ho]
  obtain ⟨hd1, hd2, hd3⟩ := hd
  have hlk : ∀ i, (<[id := b']> T.bufs) !! i = if i = id then some b' else T.bufs !! i := by
    intro i
    by_cases e : i = id
    · subst e; rw [GMap.lookup_insert, if_pos rfl]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e), if_neg e]
  have hlk' : ∀ i c, (<[id := b']> T.bufs) !! i = some c →
      ∃ c0, T.bufs !! i = some c0 ∧ c.length = c0.length ∧ pageId c = pageId c0 ∧ dspan c = dspan c0 := by
    intro i c h
    rw [hlk] at h
    split at h
    · rename_i e; subst e; cases h; exact ⟨b, hb, hl, hi, hds⟩
    · exact ⟨c, h, rfl, rfl, rfl⟩
  refine ⟨fun i => ?_, fun i c hc => ?_, fun i1 c1 i2 c2 h1 h2 hne => ?_⟩
  · show ((T.pm !! i).isSome ↔ ((<[id := b']> T.bufs) !! i).isSome)
    rw [hd1 i, hlk]
    split
    · rename_i e; subst e; rw [hb]; rfl
    · rfl
  · obtain ⟨c0, hc0, e1, e2, e3⟩ := hlk' i c hc
    obtain ⟨a1, a2, a3, a4, a5⟩ := hd2 i c0 hc0
    exact ⟨by rw [e1, e3]; exact a1, by rw [e2]; exact a2, a3, by rw [e3]; exact a4,
      fun k hk => a5 k (by rw [← e3]; exact hk)⟩
  · obtain ⟨d1, hd1', -, -, f1⟩ := hlk' i1 c1 h1
    obtain ⟨d2, hd2', -, -, f2⟩ := hlk' i2 c2 h2
    rw [f1, f2]; exact hd3 i1 d1 i2 d2 hd1' hd2' hne

theorem bufsN_lookup (bufs : GMap w64 (List w8)) (n : Nat) :
    bufsN bufs !! n = if n < 2 ^ 64 then bufs !! W64 (n : Int) else none := rfl

/-- The view and the dirty pages share no slot (the view's pages being disjoint), and are below
the transaction's high-water mark. -/
theorem spillPages_disjoint (ρ : DBState) (W : WView) (T : WTx) (hd : spillDirty ρ W T)
    (hv : pagesDisjoint W.pages) (hvb : ∀ id pg, W.pages !! id = some pg → id < W.hwm)
    (hwh : W.hwm ≤ uint.nat T.mv.pgid') :
    pagesDisjoint (spillPages W T) ∧
      ∀ id pg, spillPages W T !! id = some pg → id < uint.nat T.mv.pgid' := by
  obtain ⟨-, hd2, hd3⟩ := hd
  -- a page of `spillPages`: the view's, or a dirty one (at its id)
  have hcase : ∀ id pg, spillPages W T !! id = some pg →
      W.pages !! id = some pg ∨ (W.pages !! id = none ∧ id < 2 ^ 64 ∧ T.bufs !! W64 (id : Int) = some pg) := by
    intro id pg h
    unfold spillPages at h
    rw [GMap.lookup_union] at h
    cases hw : W.pages !! id with
    | some pg' => rw [hw] at h; left; simpa using h
    | none =>
      rw [hw] at h
      simp only [Option.none_or] at h
      rw [bufsN_lookup] at h
      split at h
      · right; exact ⟨rfl, by assumption, h⟩
      · cases h
  have hnat : ∀ id : Nat, id < 2 ^ 64 → uint.nat (W64 (id : Int)) = id := by
    intro id h; show (BitVec.ofInt 64 (id : Int)).toNat = id
    rw [BitVec.toNat_ofInt]; omega
  refine ⟨fun i1 p1 i2 p2 h1 h2 hne => ?_, fun id pg h => ?_⟩
  · rcases hcase i1 p1 h1 with h1 | ⟨-, hl1, h1⟩ <;> rcases hcase i2 p2 h2 with h2 | ⟨-, hl2, h2⟩
    · exact hv i1 p1 i2 p2 h1 h2 hne
    · -- a view page and a dirty one: the dirty slots are no view slot
      obtain ⟨-, -, -, -, a5⟩ := hd2 _ p2 h2
      rw [hnat i2 hl2] at a5
      have hds : dspan p2 = 1 + pageOverflow p2 := rfl
      rw [hds] at a5
      rcases runs_apart i1 (1 + pageOverflow p1) i2 (1 + pageOverflow p2) (by omega) (by omega)
        (fun a ha b hb heq => (a5 b hb).2.2.1 ⟨i1, p1, h1, by omega, by omega⟩) with h | h
      · left; exact h
      · right; exact h
    · obtain ⟨-, -, -, -, a5⟩ := hd2 _ p1 h1
      rw [hnat i1 hl1] at a5
      have hds : dspan p1 = 1 + pageOverflow p1 := rfl
      rw [hds] at a5
      exact runs_apart i1 (1 + pageOverflow p1) i2 (1 + pageOverflow p2) (by omega) (by omega)
        (fun a ha b hb heq => (a5 a ha).2.2.1 ⟨i2, p2, h2, by omega, by omega⟩)
    · have hne' : W64 (i1 : Int) ≠ W64 (i2 : Int) := by
        intro e; apply hne
        have := congrArg (fun x : w64 => uint.nat x) e
        rw [hnat i1 hl1, hnat i2 hl2] at this; exact this
      have := hd3 _ p1 _ p2 h1 h2 hne'
      rw [hnat i1 hl1, hnat i2 hl2] at this
      exact this
  · rcases hcase id pg h with h | ⟨-, hl, h⟩
    · have := hvb id pg h; omega
    · obtain ⟨-, -, -, a4, -⟩ := hd2 _ pg h
      rw [hnat id hl] at a4
      have := dspan_pos pg
      omega


/-- The dirty pages' facts are what `Tx.write` needs (`dirtyOK`), once their slots are inside
the file (`Commit`'s `grow`). -/
theorem spillDirty_dirtyOK (ρ : DBState) (W : WView) (T : WTx) (hd : spillDirty ρ W T)
    (hps : ρ.ps = W.ps)
    (hin : ∀ id b, T.bufs !! id = some b → ∀ k < dspan b, uint.nat id + k < ρ.nslots) :
    dirtyOK ρ T := by
  obtain ⟨hd1, hd2, hd3⟩ := hd
  refine ⟨fun id b _ hb => ?_, fun i1 b1 i2 b2 _ h1 _ h2 hne => hd3 i1 b1 i2 b2 h1 h2 hne⟩
  obtain ⟨a1, a2, -, -, a5⟩ := hd2 id b hb
  exact ⟨by rw [hps]; exact a1, a2, fun k hk => ⟨hin id b hb k hk, (a5 k hk).1, (a5 k hk).2.1⟩⟩

end pure

end bbolt
end EtcdGrove
end Perennial
