/-
The proof of `Spec/go_etcd_io/bbolt/Open.lean` (U11g, `notes/bbolt-proof-plan.md`; design §3.11
"Open"): the fields `Open` sets, the file opened and locked, initialized when empty (`DB.init`)
or its page size read (`getPageSize`), the page pool, the mapping (`mmapUnlocked`, owned), the
freelist loaded (`DB.loadFreelist.spec_open`: the core phase, `Open/Core`), the writer phase
(`Open/Core.open_writer`), and, for a file with no synced freelist, a write transaction committed
unchanged (`Begin`, `Commit`, over the client's `boltState` it then returns).
-/
module

public import Spec.go_etcd_io.bbolt.Open
public import Spec.go_etcd_io.bbolt.Options__String
public import Spec.go_etcd_io.bbolt.DB__Begin_err
public import Spec.go_etcd_io.bbolt.Tx__Commit_err
public import Spec.go_etcd_io.bbolt.DB__Close
public import Spec.os.OpenFile
public import Spec.os.File__Name
public import Proof.go_etcd_io.bbolt.Options
public import Proof.go_etcd_io.bbolt.DB__loadFreelist
public import Proof.go_etcd_io.bbolt.DB__init
public import Proof.go_etcd_io.bbolt.Open.MmapOwn
public import Proof.go_etcd_io.bbolt.Open.FileFacts
public import Proof.go_etcd_io.bbolt.Open.Close
public import Proof.go_etcd_io.bbolt.Open.Flock
public import Proof.go_etcd_io.bbolt.Open.Logger
public import Proof.go_etcd_io.bbolt.Open.PageSize
public import Proof.go_etcd_io.bbolt.Open.MetasZero
public import Proof.go_etcd_io.bbolt.Open.MetaNonzero
public import Proof.go_etcd_io.bbolt.Open.FileModeString
public import Proof.go_etcd_io.bbolt.Open.LogFmt
public import Proof.go_etcd_io.bbolt.Inv.LoggerOk
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`os.OpenFile` with its error formattable** (maintainer 8's pending 37.10: `os.OpenFile.spec`'s
post gains `fmtErrorOkOrNil err`; `Open` logs the error with `%v`). Assumed here until it lands. -/
abbrev os.OpenFile.specE : Prop :=
  ∀ (path : GoString) (perm : w32) (q : DFrac) (mo : Option OsMeta),
  (mo = none → q = DFrac.own 1) →
  {{ osInv (GF := GF) ∗ osMeta (GF := GF) path q mo }}
    (App (App (App (Val (@! os.OpenFile)) (Val #path)) (Val #(W64 0x42))) (Val #perm))
  {{ (f : Loc) (err : GoInterface), RET (PairV #f #err);
      ((∃ fd : w64, ⌜err = interface.nil ∧ 0 ≤ fd.toInt⌝ ∗ os.ownFile f fd path (DFrac.own 1) ∗
          osFd fd (DFrac.own 1) ⟨path, true, true⟩ ∗ osMeta path q (openMeta mo true)) ∨
      (⌜err ≠ interface.nil ∧ f = null⌝ ∗
        ∃ mo' : Option OsMeta, ⌜mo' = mo ∨ mo' = openMeta mo true⌝ ∗ osMeta path q mo')) ∗
      fmtErrorOkOrNil err }}

variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`db.Begin(true)` with no transaction on an error** (`DB.Begin_err.spec` at `w = true`, with
`tx = nil` on an error: `beginRWTx` returns `nil, err` on each of its errors). `Open` calls
`tx.Commit()` only if `tx != nil`; `DB.Begin_err.spec` does not say that an error's `tx` is nil
(reported). Assumed here until the shared spec says it. -/
abbrev DB.Begin_err.spec_w : Prop :=
  ∀ (db : Loc) (γ : BoltName),
  {{ isBolt (GF := GF) db γ }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Begin")) (Val #true))
  {{ (tx : Loc) (err : GoInterface), RET (PairV #tx #err);
      (⌜err = GoInterface.nil⌝ ∗ txDB tx γ db ∗ ∃ D : Data, boltTx tx γ 1 (TxView.wr D)) ∨
      (⌜err ≠ GoInterface.nil ∧ tx = null⌝ ∗ fmtErrorOk err) }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`lg != discardLogger`** (as `DB__Begin_err.wp_logger_ne_discard`, which `Open` does not
import: `DB__Begin_err` is a proof module of another unit). -/
theorem wp_logger_ne_discard_open (lg : GoInterface) (hty : logPtrTyped lg) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ boltLogger lg }}
      (App (Val (GoInstruction (Convert go.untypedBool go.bool)))
        (App (Val (GoInstruction (GoUnOp GoNot go.bool)))
          (App (Val (GoInstruction (GoOp GoEquals Logger.ty)))
            (Pair (Val #lg) (App (Val (GoInstruction (GoLoad Logger.ty)))
              (Val #(globalAddr discardLogger)))))))
    {{ (b : Bool), RET #b; True }} := by
  wp_start as -
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt $$ []
  · iPkgInit
  icases bboltRootInit_discard $$ Hpkg with ⟨%l, #Hd⟩
  wp_auto
  cases lg with
  | nil =>
    simp only [interface.mkOk]
    wp_auto
    iapply HΦ; itrivial
  | ok ii =>
    simp only [interface.mkOk]
    by_cases h : ii.ty = go.GoType.PointerType nopLogger.ty
    · obtain ⟨l', hl⟩ := hty ii rfl _ h
      rw [if_pos h, h, hl]
      wp_auto
      iapply HΦ; itrivial
    · rw [if_neg h]
      wp_auto
      iapply HΦ; itrivial

end proof

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

set_option hygiene false in
/-- Read an untracked field of the options (`optsAt_*_rd`), giving `optsAt` back. -/
macro "opt_rd" ax:term : tactic => `(tactic| (
  icases ($ax) $$ Hopts with ⟨%dqx, %x, Hx, Hback⟩
  try wp_auto
  ihave Hopts := Hback $$ Hx))

set_option hygiene false in
/-- Read a tracked field of the options (`optsAt_*_rd`), giving `optsAt` back. -/
macro "opt_rdt" ax:term : tactic => `(tactic| (
  icases ($ax) $$ Hopts with ⟨%dqx, Hx, Hback⟩
  try wp_auto
  ihave Hopts := Hback $$ Hx))

theorem Open.wp_proof
    (hOpenFile : ∀ [HasExt osFsExt], os.OpenFile.specE (GF := GF) (hG := hG))
    (hName : os.File.Name.spec (GF := GF) (hG := hG))
    (hFlock : ∀ [HasExt osFsExt], flock.spec (GF := GF) (hG := hG))
    (hStat : ∀ [HasExt osFsExt], os.File.Stat.spec (GF := GF) (hG := hG))
    (hSize : os.fileStat.Size.spec (GF := GF) (hG := hG))
    (hMZ : ∀ [HasExt osFsExt], DB.metasZero.spec_own (GF := GF) (hG := hG))
    (hInit : ∀ [HasExt osFsExt], DB.init.spec (GF := GF) (hG := hG))
    (hGPS : ∀ [HasExt osFsExt], DB.getPageSize.spec_own (GF := GF) (hG := hG))
    (hMmap : ∀ [HasExt osFsExt], DB.mmapUnlocked.spec_own (GF := GF) (hG := hG))
    (hLoad : ∀ [HasExt osFsExt], DB.loadFreelist.spec_open (GF := GF) (hG := hG))
    (hSync : ∀ [HasExt osFsExt], DB.hasSyncedFreelist.spec (GF := GF) (hG := hG))
    (hBegin : ∀ [HasExt osFsExt], DB.Begin_err.spec_w (GF := GF) (hG := hG))
    (hCommit : ∀ [HasExt osFsExt], Tx.Commit_err.spec (GF := GF) (hG := hG))
    (hClose : DB.Close.spec (GF := GF) (hG := hG))
    (hclose : ∀ [HasExt osFsExt], DB.close.spec_owned (GF := GF) (hG := hG))
    (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hOptStr : Options.String.spec (GF := GF) (hG := hG))
    (hModeStr : fs.FileMode.String.spec (GF := GF) (hG := hG)) :
    Open.spec (GF := GF) (hG := hG) := by
  intro _ _ _ N path mode opts dq o D
  wp_start as ⟨#Hos, %HN, Hfh, Hopts, %Hok, Hlgr⟩
  ihave %Hoptnn := optsAt_nonnull _ _ _ $$ Hopts
  unfold fileHolds
  icases fileHolds_openRest path D $$ Hfh with ⟨%mo, Hfm, Hfr⟩
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨«$r0», %Hdbnn⟩
  irename path => Hpathv
  irename mode => Hmodev
  irename options => Hoptsv
  iStructNamed «$r0»
  generalize «$r0_ptr» = dbl at *
  ipersist Hoptsv
  ipersist Hmodev
  ipersist Hpathv
  rw [decide_eq_false Hoptnn]
  try wp_auto
  opt_rd (optsAt_bool_rd opts dq o go!"NoSync" (by decide))
  opt_rd (optsAt_bool_rd opts dq o go!"NoGrowSync" (by decide))
  opt_rdt (optsAt_mmapFlags_rd opts dq o)
  opt_rd (optsAt_bool_rd opts dq o go!"NoFreelistSync" (by decide))
  opt_rd (optsAt_bool_rd opts dq o go!"PreLoadFreelist" (by decide))
  opt_rd (optsAt_freelist_rd opts dq o)
  opt_rdt (optsAt_mlock_rd opts dq o)
  opt_rd (optsAt_int_rd opts dq o go!"MaxSize" (by decide))
  simp only [internal.common.DefaultMaxBatchSize, internal.common.DefaultMaxBatchDelay,
    internal.common.DefaultAllocSize]
  try wp_auto
  -- the statistics
  icases (optsAt_bool_rd opts dq o go!"NoStatistics" (by decide)) $$ Hopts with
    ⟨%dqx, %nst, Hx, Hback⟩
  wp_join iprop((∃ sp : Loc, dbl.[DB, go!"stats"] ↦ sp ∗ Ps sp 1) ∗
      opts.[Options, go!"NoStatistics"] ↦{dqx} nst ∗ db_ptr ↦ dbl) at next with [stats Hx db]
      as ⟨⟨%sp, stats, Hps⟩, Hx, db⟩
  · cases nst
    · wp_auto
      icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨«$r0», %Hspnn⟩
      isplitr
      · ipureintro; rfl
      iframe Hx db
      iexists «$r0_ptr»
      iframe stats
      unfold Ps; rw [if_neg Hspnn]; iexists _; iexact «$r0»
    · wp_auto
      isplitr
      · ipureintro; rfl
      iframe Hx db
      iexists null
      iframe stats
      unfold Ps; simp only [↓reduceIte]; iempintro
  ihave Hopts := Hback $$ Hx
  -- the logger
  icases (optsAt_logger_rd opts dq o) $$ Hopts with ⟨%dqx, Hx, Hback⟩
  wp_join iprop((∃ lg : GoInterface, dbl.[DB, go!"logger"] ↦ lg ∗ boltLogger lg ∗
      ⌜logPtrTyped lg⌝) ∗ opts.[Options, go!"Logger"] ↦{dqx} (o.logger : Logger) ∗ db_ptr ↦ dbl)
      at next with [logger Hx Hlgr db] as ⟨⟨%lg, logger, #Hlgok, %Hlgty⟩, Hx, db⟩
  · have hpt := OptsM.ok_logPtrTyped o Hok
    rcases hlo : o.logger with li | _
    · simp only [hlo] at hpt ⊢
      icases Hlgr with (%h | #Hb)
      · cases h
      wp_auto
      isplitr
      · ipureintro; rfl
      iframe Hx db
      iexists _
      iframe logger
      iframe Hb
      ipureintro; exact hpt
    · simp only [hlo] at hpt ⊢
      wp_auto
      wp_apply getDiscardLogger.wp_spec as %lg ⟨#Hd, #Hb, %Ht⟩
      isplitr
      · ipureintro; rfl
      iframe Hx db
      iexists lg
      iframe logger Hb
      ipureintro; exact Ht
  ihave Hopts := Hback $$ Hx
  ipersist logger
  wp_apply hLogger dbl lg Hdbnn $$ []
  · iframe #
  try wp_auto
  rcases lg with li | _
  rotate_left
  · unfold boltLogger; iexfalso; iexact Hlgok
  ipersist lg
  -- `lg != discardLogger`: the deferred log call, as a deferred function `dv` that logs the result
  wp_apply wp_logger_ne_discard_open (.ok li) Hlgty $$ [] as %b -
  · iframe #
  wp_join iprop((∃ dv : GoFunc, defer ↦ dv ∗ □ (∀ (e : GoInterface) (Ψ : val → IProp GF),
      err_ptr ↦ e -∗ fmtErrorOkOrNil e -∗ (err_ptr ↦ e -∗ Ψ #()) -∗
      WP (App (Val #dv) (Val #())) {{ Ψ }})) ∗ optsAt opts dq o)
      at next with [Hdefer Hopts] as ⟨⟨%dv, Hdefer, #Hdef⟩, Hopts⟩
  · cases b
    · wp_auto
      isplitr
      · ipureintro; rfl
      iframe Hopts
      iexists _; iframe Hdefer
      imodintro; iintro %e %Ψ Herr #Hek HΨ; wp_auto; iapply HΨ $$ Herr
    · wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl,
        show sint.nat (W64 (0 + 1 + 1)) = 2 from rfl, List.set]
      try wp_auto
      wp_apply wp_boltLog li _ _ [W8 115, W8 115, W8 115] _
        [interface.mkOk go.string #path, interface.mkOk os.FileMode.ty #mode,
          interface.mkOk (go.GoType.PointerType Options.ty) #opts] _ (optsAt opts dq o) _
        infof_mem fmtVerbs_opening rfl $$ Hlgok [Hsl] [] [Hopts] as Hsl Hopts
      · iexact Hsl
      · simp only [List.zip_cons_cons, List.zip_nil_left, BigSepL.bigSepL_cons,
          BigSepL.bigSepL_nil]
        isplitr
        · iapply logArgOk_of_argWf
          apply fmt.argWf_of_argsWf
          exact .cons_string _ _ .nil
        isplitr
        · iapply fileMode_logArgOk hModeStr _ _ (by simp [methodVerbs])
        isplitr
        · iapply options_logArgOk hOptStr opts dq o Hok.2.2.2.2.2
        iempintro
      · iexact Hopts
      isplitr
      · ipureintro; rfl
      iframe Hopts
      iexists _; iframe Hdefer
      imodintro
      iintro %e %Ψ Herr #Hek HΨ
      wp_auto
      cases e with
      | ok ei =>
        ihave #Hek' := fmtErrorOkOrNil_ne (GF := GF) (.ok ei) (by simp) $$ Hek
        wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨Hsl, -⟩
        simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl, List.set]
        try wp_auto
        wp_apply wp_boltLog li _ _ [W8 115, W8 118] _
          [interface.mkOk go.string #path, GoInterface.ok ei] _ iprop(True) _
          errorf_mem' fmtVerbs_failed rfl $$ Hlgok [Hsl] [] [] as Hsl -
        · iexact Hsl
        · log_args_ok
        iapply HΨ $$ Herr
      | nil =>
        wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨Hsl, -⟩
        try wp_auto
        wp_apply wp_boltLog li _ _ [W8 115] _
          [interface.mkOk go.string #path] _ iprop(True) _
          infof_mem fmtVerbs_success rfl $$ Hlgok [Hsl] [] [] as Hsl -
        · iexact Hsl
        · log_args_ok
        iapply HΨ $$ Herr
  sorry

end proof

end bbolt
end EtcdGrove
end Perennial
