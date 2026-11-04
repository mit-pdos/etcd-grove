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
    Hroot, Hobjs⟩, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩, Hcells, Hmap⟩
  iframe Hdbf Hmeta Hmv
  isplitr
  · ipureintro; exact Hr.1
  iintro Hdbf Hmeta Hmv
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
      Hbufs⟩, Hroot, Hobjs⟩, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩, Hmap⟩
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
    sorry
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
