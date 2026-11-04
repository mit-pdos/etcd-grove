/-
`Tx.allocate` over `DB.allocate` (U4c, `notes/bbolt-proof-plan.md`): `db.allocate(tx.meta.Txid(),
count)`, its error logged and returned; the page added to `tx.pages`, the statistics counted.

`Tx.allocate.spec` (U0b's, `Spec/go_etcd_io/bbolt/Tx__allocate.lean`) cannot be proved as stated
(reported): it does not say that the transaction's meta copy holds the writer's txid
(`X.t.mv.txid' = w.wtxid`, which `allocate` passes to the freelist, whose ghost step is for
`w.wtxid`) nor that the high-water mark's pages are inside the mapping (without it `minsz` wraps and
`allocRes`' `id + count < 2^62` is unknown), and its `X'.v = X.v → w' = w.withFl w'.fl` fails for
a remap that maps at the same address. `Tx.allocate.spec'` is the statement proved here: those two
premises, the mark kept inside the new mapping, and a remap or not as a disjunction.
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.Alloc
public import Spec.go_etcd_io.bbolt.Tx__allocate
public import Spec.go_etcd_io.bbolt.TxStats__IncPageCount
public import Spec.go_etcd_io.bbolt.TxStats__IncPageAlloc
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Txid

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section txalloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`tx.allocate(count)`**, as proved (see the header): `Tx.allocate.spec` with the writer's txid
in its meta copy and its high-water mark's pages inside the mapping, kept. -/
abbrev Tx.allocate.spec' : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (count : w64),
  0 < sint.Z count → sint.nat count * 4096 < 2 ^ 62 → X.t.mv.txid' = w.wtxid →
  X.t.mv.pgid'.toNat * 4096 ≤ mapLen w.ms → derefPre X → liveFresh X → liveReach X →
  {{ wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"allocate")) (Val #count))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err);
      (⌜err = interface.nil⌝ ∗ ∃ (X' : WX) (w' : WDb) (id : w64),
        wtxW K tx r m X' ∗ wdbW K tx X'.v w' ∗
        ⌜allocRes X X' w.fl w'.fl w.wtxid (sint.nat count) p id ∧
          w'.C = w.C ∧ X'.t.mv.pgid'.toNat * 4096 ≤ mapLen w'.ms ∧
          (w' = w.withFl w'.fl ∨ wdbRemap w w')⌝) ∨
      (⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∗
        ((wtxW K tx r m X ∗ wdbW K tx X.v w) ∨
         (∃ (X' : WX) (w' : WDb), wtxLost K tx r m X' ∗ wdbLost K tx X'.v w' ∗
           ⌜(∃ Xd b, derefRel X Xd ∧ X' = Xd.rebase b) ∧ w'.C = w.C ∧ w'.fl = w.fl⌝))) }}

omit [GooseSemantics] [GooseInterp] go_gctx hos sem package_sem in
/-- **`DB.allocate`'s success as `Tx.allocate`'s** (`allocRes`, the page added to the cache). -/
theorem txAlloc_res (X Xr : WX) (w w' : WDb) (n : Nat) (p : Loc) (id hwm : w64) (hn : 0 < n)
    (hp : p ≠ null) (h : dbAllocRes X Xr w w' w.wtxid n id hwm) :
    allocRes X (Xr.addPage id p n hwm) w.fl w'.fl w.wtxid n p id ∧ w'.C = w.C ∧
      hwm.toNat * 4096 ≤ mapLen w'.ms ∧ (w' = w.withFl w'.fl ∨ wdbRemap w w') := by
  obtain ⟨hC, hb, hcase⟩ := h
  rcases hcase with ⟨rfl, hcan, rfl, rfl⟩ | ⟨rfl, hlt, rfl, hr⟩
  · exact ⟨⟨hn, hp, Xr, .inl rfl, .inl ⟨hcan, rfl, rfl⟩⟩, hC, hb, .inl rfl⟩
  · rcases hr with ⟨rfl, rfl⟩ | ⟨Xd, b, hd, rfl, hrm⟩
    · exact ⟨⟨hn, hp, Xr, .inl rfl, .inr ⟨rfl, rfl, hlt, rfl⟩⟩, hC, hb, .inl rfl⟩
    · exact ⟨⟨hn, hp, Xd.rebase b, .inr ⟨Xd, b, hd, rfl⟩, .inr ⟨rfl, hrm.2.1, hlt, rfl⟩⟩, hC, hb,
        .inr hrm⟩

omit hos in
/-- A `Txid` is formatted as its integer (a named `uint64` without methods). -/
theorem txid_argWf (v : w64) : _root_.Perennial.fmt.ArgWf (interface.mk Txid.ty #v) := by
  have hu : underlying Txid.ty = go.uint64 := go.IsUnderlying.is_underlying
  have hni : ¬ _root_.Perennial.fmt.IsIntType Txid.ty := by
    simp [_root_.Perennial.fmt.IsIntType, Txid.ty, go.int, go.int64, go.int32, go.int16, go.int8,
      go.uint, go.uint64, go.uint32, go.uint16, go.uint8]
  have hint : _root_.Perennial.fmt.IsIntType (underlying Txid.ty) := by
    rw [hu]; simp [_root_.Perennial.fmt.IsIntType]
  have hnf := _root_.Perennial.fmt.NoFmtMethods.of_methodSetIs_nil Txid.ty
  refine ⟨fun h => ?_, fun _ => ⟨uint.Z v, .named _ _ _ hni hint hnf ?_⟩, Or.inr (Or.inr ⟨hint, hnf⟩)⟩
  · simp [Txid.ty, go.string] at h
  · show _root_.Perennial.fmt.IntArgValue (interface.mk (underlying Txid.ty) #v) (uint.Z v)
    rw [hu]; exact .uint64 v

omit package_sem in
/-- The transaction's `db` field's share out of `wtxW` (and its registration, statistics token
and facts, persistent or read only), back. -/
theorem wtxW_db_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ ⌜r.db = K.db⌝ ∗ reg tx K.B r ∗
      tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} r.db ∗ statsTok r m 1 ∗
      (tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} r.db -∗ statsTok r m 1 -∗ wtxW K tx r m X) := by
  unfold wtxW wtxCore
  iintro ⟨⟨#Hpkg, #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩, Hcells, Hmap⟩
  iframe Hdbf Hst
  isplitr
  · ipureintro; exact Hr.1
  iframe #
  iintro Hdbf Hst
  iframe; iframe #
  ipureintro; exact Hr

omit package_sem in
/-- The transaction's `db` field's share, its `meta` field and its meta copy out of `wtxW`, back. -/
theorem wtxW_read_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ ⌜r.db = K.db⌝ ∗
      tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} r.db ∗ tx.[Tx, go!"meta"] ↦ X.t.t.meta' ∗
      X.t.t.meta' ↦ X.t.mv ∗
      (tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} r.db -∗ tx.[Tx, go!"meta"] ↦ X.t.t.meta' -∗
        X.t.t.meta' ↦ X.t.mv -∗ wtxW K tx r m X) := by
  unfold wtxW wtxCore wtxHeap txFields
  iintro ⟨⟨#Hpkg, #Hcore, %Hr, #Hreg, ⟨%Hok, ⟨Hf1, Hf2, Hmeta, Hpages, Hf5, Hf6, Hmv, Hpm, Hbufs⟩,
    Hroot, Hobjs, Hbobjs⟩, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩, Hcells, Hmap⟩
  iframe Hdbf Hmeta Hmv
  isplitr
  · ipureintro; exact Hr.1
  iintro Hdbf Hmeta Hmv
  iframe; iframe #
  ipureintro; exact ⟨Hr, Hok⟩

omit hos package_sem in
/-- **The page cache's buffers with a new page** `id` at `p` (an old buffer at `id`, if any,
dropped). -/
theorem bufs_insert (pm : GMap w64 Loc) (bufs : GMap w64 (List w8)) (id : w64) (p : Loc)
    (bs : List w8) :
    ([∗map] k ↦ pl ∈ pm, ∃ b, ⌜bufs !! k = some b⌝ ∗ bytesPointsto (GF := GF) pl (DFrac.own 1) b) ∗
      bytesPointsto (GF := GF) p (DFrac.own 1) bs ⊢
    [∗map] k ↦ pl ∈ pm.insert id p,
      ∃ b, ⌜(bufs.insert id bs) !! k = some b⌝ ∗ bytesPointsto (GF := GF) pl (DFrac.own 1) b := by
  refine Entails.trans ?_ (BigSepM.bigSepM_insert_delete (M := GMap w64)).2
  iintro ⟨Hm, Hp⟩
  isplitl [Hp]
  · iexists bs
    iframe
    ipureintro; exact GMap.lookup_insert _ _ _
  ihave Hm : [∗map] k ↦ pl ∈ GMap.delete id pm, ∃ b, ⌜bufs !! k = some b⌝ ∗
      bytesPointsto (GF := GF) pl (DFrac.own 1) b $$ [Hm]
  · cases hl : pm !! id with
    | none => rw [GMap.delete_notin _ _ hl]; iexact Hm
    | some x =>
      icases (BigSepM.bigSepM_delete (M := GMap w64) hl).1 $$ Hm with ⟨-, Hm⟩
      iexact Hm
  iapply BigSepM.bigSepM_mono ?_ $$ Hm
  intro k v hk
  have hne : id ≠ k := by
    intro h; subst h
    have h0 : Std.get? (GMap.delete id pm) id = none := GMap.lookup_delete pm id
    rw [h0] at hk; cases hk
  iintro ⟨%b, %hb, H⟩
  iexists b
  iframe
  ipureintro
  rw [GMap.lookup_insert_ne _ _ hne]; exact hb

omit package_sem in
/-- **The page cache and the statistics' resources out of `wtxW`** (`tx.pages[id] = p` and the
statistics' increments): `tx.db`'s share, the statistics' token, the `pages` field, its map and
buffers; back with a new map and buffers. -/
theorem wtxW_pages_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (Y : WX) :
    wtxW (GF := GF) K tx r m Y ⊢ ⌜r.db = K.db⌝ ∗ reg tx K.B r ∗
      tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} r.db ∗ statsTok r m 1 ∗
      tx.[Tx, go!"pages"] ↦ Y.t.t.pages' ∗ Y.t.t.pages' ↦$ Y.t.pm ∗
      ([∗map] id ↦ pl ∈ Y.t.pm, ∃ bs, ⌜Y.t.bufs !! id = some bs⌝ ∗ bytesPointsto pl (DFrac.own 1) bs) ∗
      (∀ (pm : GMap w64 Loc) (bufs : GMap w64 (List w8)),
        tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} r.db -∗ statsTok r m 1 -∗
        tx.[Tx, go!"pages"] ↦ Y.t.t.pages' -∗ Y.t.t.pages' ↦$ pm -∗
        ([∗map] id ↦ pl ∈ pm, ∃ bs, ⌜bufs !! id = some bs⌝ ∗ bytesPointsto pl (DFrac.own 1) bs) -∗
        wtxW K tx r m { Y with t := { Y.t with pm := pm, bufs := bufs } }) := by
  unfold wtxW wtxCore wtxHeap txFields
  iintro ⟨⟨#Hpkg, #Hcore, %Hr, #Hreg, ⟨%Hok, ⟨Hf1, Hf2, Hmeta, Hpages, Hf5, Hf6, Hmv, Hpm, Hbufs⟩,
    Hroot, Hobjs, Hbobjs⟩, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩, Hcells, Hmap⟩
  iframe Hdbf Hst Hpages Hpm Hbufs
  isplitr
  · ipureintro; exact Hr.1
  iframe #
  iintro %pm %bufs Hdbf Hst Hpages Hpm Hbufs
  iframe; iframe #
  ipureintro; exact ⟨Hr, Hok⟩

omit package_sem in
/-- The transaction's `meta` field and meta copy out of `allocate`'s error state, back. -/
theorem errState_meta_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) :
    ((wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w) ∨
      (∃ (X' : WX) (w' : WDb), wtxLost K tx r m X' ∗ wdbLost K tx X'.v w' ∗
        ⌜(∃ Xd b, derefRel X Xd ∧ X' = Xd.rebase b) ∧ w'.C = w.C ∧ w'.fl = w.fl⌝)) ⊢
    ∃ (ml : Loc) (mv : Meta), tx.[Tx, go!"meta"] ↦ ml ∗ ml ↦ mv ∗
      (tx.[Tx, go!"meta"] ↦ ml -∗ ml ↦ mv -∗
        ((wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w) ∨
         (∃ (X' : WX) (w' : WDb), wtxLost K tx r m X' ∗ wdbLost K tx X'.v w' ∗
           ⌜(∃ Xd b, derefRel X Xd ∧ X' = Xd.rebase b) ∧ w'.C = w.C ∧ w'.fl = w.fl⌝))) := by
  iintro (⟨Hw, Hdb⟩ | ⟨%X', %w', Hw, Hdb, %h⟩)
  · icases wtxW_read_acc K tx r m X $$ Hw with ⟨-, Htdb, Hmeta, Hmv, Hb⟩
    iexists X.t.t.meta', X.t.mv
    iframe Hmeta Hmv
    iintro Hmeta Hmv
    ileft
    iframe Hdb
    iapply Hb $$ Htdb Hmeta Hmv
  · unfold wtxLost wtxCore wtxHeap txFields
    icases Hw with ⟨⟨#Hpkg, #Hcore, %Hr, #Hreg, ⟨%Hok, ⟨Hf1, Hf2, Hmeta, Hpages, Hf5, Hf6, Hmv, Hpm,
      Hbufs⟩, Hroot, Hobjs, Hbobjs⟩, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩, Hmap⟩
    iexists X'.t.t.meta', X'.t.mv
    iframe Hmeta Hmv
    iintro Hmeta Hmv
    iright
    iexists X', w'
    iframe; iframe #
    ipureintro; exact ⟨⟨Hr, Hok⟩, h⟩

theorem Tx.allocate.wp_proof' (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hAlloc : DB.allocate.spec (GF := GF) (hG := hG))
    (hTxid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
    (hId : internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (hCount : TxStats.IncPageCount.spec (GF := GF) (hG := hG))
    (hPAlloc : TxStats.IncPageAlloc.spec (GF := GF) (hG := hG)) :
    Tx.allocate.spec' (GF := GF) (hG := hG) := by
  intro K tx r m X w count hc0 hc htx hhwm hdp hlf hlr
  wp_start as ⟨Hw, Hdb⟩
  icases wtxW_core K tx r m X $$ Hw with ⟨#Hcore, Hw⟩
  icases BC.core_allocFields K $$ Hcore with ⟨#Hps, #Has, ⟨%mx, #Hmx⟩, ⟨%lg, #Hlg, #Hlgok⟩,
    #Hfix, #Hpkg, %Hdb, #Hpinv⟩
  icases wtxW_read_acc K tx r m X $$ Hw with ⟨%Hrdb, Htdb, Hmeta, Hmv, Hwb⟩
  rw [Hrdb]
  wp_auto
  wp_apply hLogger K.db lg Hdb $$ []
  · iframe #
  try wp_auto
  wp_apply hTxid $$ [Hmv] as Hmv
  · iframe
  try wp_auto
  ihave Hw := Hwb $$ [Htdb] [Hmeta] [Hmv]
  · iexact Htdb
  · iexact Hmeta
  · iexact Hmv
  rw [htx]
  wp_apply hAlloc K tx r m X w w.wtxid count rfl hc0 hc hhwm hdp hlf hlr $$ [Hw Hdb] as %p %err Hres
  · iframe
  try wp_auto
  icases Hres with (⟨%he, %Xr, %w', %id, %hwm, Hw, Hdb, Hp, %hres⟩ | ⟨%hne, #HeOk, Hcase⟩)
  · subst he
    wp_auto
    icases wtxW_pages_acc K tx r m (Xr.withHwm hwm) $$ Hw with ⟨%Hrdb', #Hreg, Htdb, Hst, Hpages, Hpm,
      Hbufs, Hwb⟩
    unfold allocBuf
    icases (bytesPointsto_app _ _ _ _).1 $$ Hp with ⟨Hh, Hz⟩
    ihave %Hpp := bytesPointsto_pos _ _ _
      (List.ne_nil_of_length_pos (by rw [ByteEncoding.encode_length]; decide)) $$ Hh
    icases (typedPointsto_bytes (V := Page) _ _ _ Hpp).2 $$ Hh with Hh
    try wp_auto
    wp_apply hId $$ [Hh] as Hh
    · iframe
    try wp_auto
    simp only [WX.withHwm]
    wp_apply (wp_mapInsert Pgid.ty Xr.t.t.pages' Xr.t.pm id p) $$ [Hpm] as Hpm
    · iexact Hpm
    try wp_auto
    wp_apply hCount K tx r m 1 _ $$ [Hst] as %n1 Hst
    · iframe; iframe #
    try wp_auto
    rw [Hrdb']
    wp_auto
    wp_apply hPAlloc K tx r m 1 _ $$ [Hst] as %n2 Hst
    · iframe; iframe #
    try wp_auto
    ihave Hbufs := bufs_insert Xr.t.pm Xr.t.bufs id p _ $$ [Hbufs Hh Hz]
    · iframe Hbufs
      iapply (bytesPointsto_app _ _ _ _).2
      isplitl [Hh]
      · iapply (typedPointsto_bytes (V := Page) _ _ _ Hpp).1 $$ Hh
      · rw [ByteEncoding.encode_length]; iexact Hz
    ihave Hw := Hwb $$ %(Xr.t.pm.insert id p) %(Xr.t.bufs.insert id (allocBuf id (sint.nat count)))
      Htdb Hst Hpages Hpm [Hbufs]
    · unfold allocBuf; iexact Hbufs
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists Xr.addPage id p (sint.nat count) hwm, w', id
    rw [WX.addPage_eq]
    simp only [WX.withHwm]
    iframe Hw
    iframe Hdb
    ipureintro
    exact txAlloc_res X Xr w w' (sint.nat count) p id hwm (by have : sint.nat count = (sint.Z count).toNat := rfl; omega) hres.1 hres.2
  -- the error: logged, returned
  cases err with
  | nil => exact absurd rfl hne
  | ok ii =>
  icases errState_meta_acc K tx r m X w $$ Hcase with ⟨%ml, %mv, Hmeta, Hmv, Hcase⟩
  wp_auto
  wp_apply hTxid $$ [Hmv] as Hmv
  · iframe
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  try wp_auto
  cases lg with
  | nil => unfold boltLogger; iexfalso; iexact Hlgok
  | ok li =>
  simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl,
    show sint.nat (W64 (0 + 1 + 1)) = 2 from rfl, List.set_cons_succ, List.set_cons_zero]
  wp_apply wp_boltLog li _ _ [W8 100, W8 100, W8 118] _
    [interface.mkOk Txid.ty #mv.txid', interface.mkOk go.int #count, GoInterface.ok ii] _ iprop(True) _
    (by decide) (by decide) rfl $$ Hlgok [Hsl] [] [] as Hsl -
  · iframe
  · simp only [List.zip_cons_cons, List.zip_nil_left, Iris.BI.BigSepL.bigSepL_cons,
      Iris.BI.BigSepL.bigSepL_nil]
    isplitr
    · iapply logArgOk_of_argWf; exact txid_argWf _
    isplitr
    · iapply logArgOk_of_argWf
      apply Perennial.EtcdGrove.fmt.argWf_of_argsWf
      exact .cons_int _ _ _ (.int _) .nil
    isplitr
    · iapply logArgOk_of_fmtErrorOk
      · simp [methodVerbs]
      iexact HeOk
    iempintro
  try wp_auto
  iapply HΦ
  iright
  isplitr
  · ipureintro; exact hne
  iframe HeOk
  iapply Hcase $$ Hmeta Hmv

end txalloc

end bbolt
end EtcdGrove
end Perennial
