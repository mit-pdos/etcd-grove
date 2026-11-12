/-
The proof of `Spec/go_etcd_io/bbolt/Open.lean` (U11g, `notes/bbolt-proof-plan.md`; design §3.11
"Open"): the fields `Open` sets, the file opened and locked, initialized when empty (`DB.init`)
or its page size read (`getPageSize`), the page pool, the mapping (`mmapUnlocked`, owned), the
freelist loaded (`DB.loadFreelist.spec_open`: the core phase, `Open/Core`), the writer phase
(`Open/Core.open_writer`), unless `NoSync` the file synced (`fdatasync`, bbolt `ea4cab52`:
issues/bbolt-open-unsynced-meta-kill-then-power-loss.md; the writer side's file metadata changes,
`Open/SyncAcc.wdbCore_file_acc`; on an error, `db.Close()` over the database the writer phase
made), and, for a file with no synced freelist, a write transaction committed unchanged (`Begin`,
`Commit`, over the client's `boltState` it then returns).

Every error exit closes the database (`DB.close.spec_owned`, or `DB.Close` once the transaction
began), logs, and returns through the deferred log (`Hdef`, the deferred function's spec).
The page pool's `New` reads the named result `db`, which the returns write: it borrows the cell
from the protocol `Open/PoolNew.dpProt` against its caller's lease (U11j).
A local assumption until the method is translated: `fs.FileMode.String.spec`.
-/
module

public import Spec.go_etcd_io.bbolt.Open
public import Spec.go_etcd_io.bbolt.Options__String
public import Spec.go_etcd_io.bbolt.DB__Begin_err
public import Spec.go_etcd_io.bbolt.Tx__Commit_err
public import Spec.go_etcd_io.bbolt.DB__Close
public import Spec.go_etcd_io.bbolt.fdatasync
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
public import Proof.go_etcd_io.bbolt.Open.SyncAcc
public import Proof.go_etcd_io.bbolt.Inv.LoggerOk
public import Proof.go_etcd_io.bbolt.Open.PoolNew
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

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

/-- The arguments of `Open`'s log calls: strings, a `bool`, errors (`fmtErrorOk` in the context). -/
macro "open_args" : tactic => `(tactic| (
  try simp only [List.zip_cons_cons, List.zip_nil_left, List.zip_nil_right,
    Iris.BI.BigSepL.bigSepL_cons, Iris.BI.BigSepL.bigSepL_nil]
  repeat' (first
    | isplitr
    | itrivial
    | iapply Perennial.EtcdGrove.bbolt.logArgOk_bool
    | (simp only [Perennial.EtcdGrove.bbolt.logArgOk]; itrivial)
    | (iapply Perennial.EtcdGrove.bbolt.logArgOk_of_argWf
       apply Perennial.EtcdGrove.fmt.argWf_of_argsWf
       exact .cons_string _ _ .nil)
    | (iapply Iris.BI.BigSepL.bigSepL_nil.2; iempintro)
    | (iapply Perennial.EtcdGrove.bbolt.logArgOk_of_fmtErrorOk
       · simp [Perennial.EtcdGrove.bbolt.methodVerbs]
       iassumption))))

set_option hygiene false in
/-- An error exit after `db.close()`: `lg.Errorf(fmtS, …)` (`hv` its verbs), the `return nil, err`,
the deferred log (`Hdef`), and `Open`'s error post. -/
macro "open_exit" hv:term:max xs:term:max : tactic => `(tactic| (
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl,
    show sint.nat (W64 (0 + 1 + 1)) = 2 from rfl, List.set]
  try wp_auto
  wp_apply wp_boltLog li _ _ _ _ $xs _ iprop(True) _ errorf_mem' $hv rfl $$ Hlgok [Hsl] [] []
    as Hsl -
  · iexact Hsl
  · open_args
  try wp_auto
  wp_bind (App (Val #dv) (Val #()))
  iapply Hdef $$ [err]
  · iexact err
  · first | iassumption | (simp only [fmtErrorOkOrNil]; iassumption)
  iintro err
  try wp_auto
  iapply HΦ
  iframe Hopts
  iright; ipureintro; intro h; cases h))

set_option hygiene false in
/-- An error exit inside the joined branch (`init`/`getPageSize`): log, `return nil, err`, and the
join's error case (`err` an `ok ei` with `Hek : fmtErrorOk`). -/
macro "open_exit_j" hv:term:max xs:term:max : tactic => `(tactic| (
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl,
    show sint.nat (W64 (0 + 1 + 1)) = 2 from rfl, List.set]
  try wp_auto
  wp_apply wp_boltLog li _ _ _ _ $xs _ iprop(True) _ errorf_mem' $hv rfl $$ Hlgok [Hsl] [] []
    as Hsl -
  · iexact Hsl
  · open_args
  try wp_auto
  iright
  iexists (GoInterface.ok ei)
  simp only [fmtErrorOkOrNil]
  iframe; iframe #
  ipureintro
  first | exact ⟨rfl, fun h => nomatch h⟩ | exact ⟨trivial, fun h => nomatch h⟩ | simp))

/-- **`Open`'s last write of `db` begins** (U11i, U11j; `Open/PoolNew.dp_lock`): the whole
validity token of the client's `boltState` lent to the protocol, which gives back the cell's
other half around one step of `Open`'s (`open_step`). -/
theorem open_lock [HasExt osFsExt] (B : BNs) (N : Namespace) (γs : GName) (D : Data)
    (dp db : Loc) :
    dpProt (GF := GF) N γs B.bq dp db ∗ ghostVar γs (1 : Qp).half 0 ∗
      boltState (GF := GF) ⟨mkGs B, N⟩ 1 D ⊢
    ghostVar B.st (1 : Qp).half D ∗ (|={⊤, ⊤ \ ↑(dpN N)}=> ▷ |={⊤ \ ↑(dpN N), ⊤}=>
      ghostVar γs (1 : Qp).half 1 ∗ dp ↦{DFrac.own (1 : Qp).half} db) := by
  iintro ⟨#Hinv, Hs, Hst⟩
  unfold boltState boltStateDef
  rw [bnsOf_mkGs]
  icases Hst with ⟨Hst, Hbq⟩
  iframe Hst
  iapply dp_lock N γs B.bq dp db $$ [Hinv Hs Hbq]
  iframe; iframe #

/-- **`Open`'s last write of `db` done, on success**: the token back, `db` persistent. -/
theorem open_unlock [HasExt osFsExt] (B : BNs) (N : Namespace) (γs : GName) (D : Data)
    (dp db : Loc) :
    dpProt (GF := GF) N γs B.bq dp db ∗ ghostVar γs (1 : Qp).half 1 ∗ dp ↦ db ∗
      ghostVar B.st (1 : Qp).half D ⊢
    |={⊤}=> dp ↦□ db ∗ boltState (GF := GF) ⟨mkGs B, N⟩ 1 D := by
  iintro ⟨#Hinv, Hs, Hdp, Hst⟩
  imod dp_unlock N γs B.bq dp db $$ [Hinv Hs Hdp] with ⟨Hbq, #Hdp⟩
  · iframe; iframe #
  imodintro
  iframe Hdp
  unfold boltState boltStateDef
  rw [bnsOf_mkGs]
  iframe

set_option hygiene false in
/-- `Open`'s next operation (before its write of `db`) with the page pool's lock `Hlk`
(`open_lock`) taken around it (`wp_step_fupd`): the cell's other half back, joined to `Open`'s
(`db`), and the protocol's tag `Hs` at `1`. -/
macro "open_step" : tactic => `(tactic| (
  try wp_pures
  wp_bind
  iapply (wp_step_fupd (E₂ := ⊤ \ ↑(dpN N)) (by rfl) CoPset.subseteq_top) $$ Hlk
  try wp_auto
  iintro ⟨Hs, Hdp'⟩
  ihave db := (typedPointsto_half_split db_ptr dbl 1).2 $$ [db Hdp']
  · iframe
  imodintro))

set_option hygiene false in
/-- `Open`'s success exit (`return db, nil`) with the client's state `Hst'`: `db` written under
the page pool's protocol (`open_lock`, `open_unlock`), the deferred log (`Hdef`), and the
database. -/
macro "open_ret" : tactic => `(tactic| (
  ihave ⟨Hstq, Hlk⟩ := open_lock B N γs _ db_ptr dbl $$ [Hdpi Hs Hst']
  · iframe; iframe #
  open_step
  try wp_auto
  wp_bind (App (Val #dv) (Val #()))
  iapply Hdef $$ [err]
  · iexact err
  · iexact Herrok
  iintro err
  imod open_unlock B N γs _ db_ptr dbl $$ [Hdpi Hs db Hstq] with ⟨#db, Hst'⟩
  · iframe; iframe #
  try wp_auto
  iapply HΦ
  iframe Hopts
  ileft
  isplitr
  · ipureintro; rfl
  iexists ⟨mkGs B, N⟩
  isplitr
  · ipureintro; rfl
  iframe Hst'
  unfold isBolt
  rw [bnsOf_mkGs]
  iexact Hbolt))

set_option hygiene false in
/-- `Open`'s success exit from the core phase's state `Hstate`. -/
macro "open_ok" : tactic => `(tactic| (
  ihave Hst' : boltState (GF := GF) ⟨mkGs B, N⟩ 1 D $$ [Hstate]
  · unfold boltState; rw [bnsOf_mkGs, ← hCD]; iexact Hstate
  open_ret))

set_option hygiene false in
/-- The transaction's error exit (`Begin` or `Commit` failed with `ok ei`, `Hek`): log, `db.Close()`,
`return nil, txErr`, the deferred log. -/
macro "open_tx_exit" : tactic => `(tactic| (
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  try wp_auto
  wp_apply wp_boltLog li _ _ [W8 118] _ [GoInterface.ok ei] _ iprop(True) _ errorf_mem'
    fmtVerbs_txErr rfl $$ Hlgok [Hsl] [] [] as Hsl -
  · iexact Hsl
  · open_args
  try wp_auto
  wp_apply hClose dbl ⟨mkGs B, N⟩ $$ []
  · unfold isBolt; rw [bnsOf_mkGs]; iexact Hbolt
  iintro %cerr -
  ihave ⟨-, Hlk⟩ := open_lock B N γs _ db_ptr dbl $$ [Hdpi Hs Hst']
  · iframe; iframe #
  open_step
  try wp_auto
  wp_bind (App (Val #dv) (Val #()))
  iapply Hdef $$ [err]
  · iexact err
  · simp only [fmtErrorOkOrNil]; iexact Hek
  iintro err
  try wp_auto
  iapply HΦ
  iframe Hopts
  iright; ipureintro; intro h; cases h))

set_option maxHeartbeats 4000000 in
theorem Open.wp_proof [sync.Assumptions]
    (hOpenFile : ∀ [HasExt osFsExt], os.OpenFile.spec (GF := GF) (hG := hG))
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
    (hFds : ∀ [HasExt osFsExt], fdatasync.spec (GF := GF) (hG := hG))
    (hBegin : ∀ [HasExt osFsExt], DB.Begin_err.spec (GF := GF) (hG := hG))
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
  icases (optsAt_bool_rd opts dq o go!"NoSync" (by decide)) $$ Hopts with
    ⟨%dqx, %nos, Hx, Hback⟩
  try wp_auto
  ihave Hopts := Hback $$ Hx
  opt_rd (optsAt_bool_rd opts dq o go!"NoGrowSync" (by decide))
  opt_rdt (optsAt_mmapFlags_rd opts dq o)
  icases (optsAt_bool_rd opts dq o go!"NoFreelistSync" (by decide)) $$ Hopts with
    ⟨%dqx, %nfs, Hx, Hback⟩
  try wp_auto
  ihave Hopts := Hback $$ Hx
  opt_rd (optsAt_bool_rd opts dq o go!"PreLoadFreelist" (by decide))
  opt_rd (optsAt_freelist_rd opts dq o)
  opt_rdt (optsAt_mlock_rd opts dq o)
  opt_rd (optsAt_int_rd opts dq o go!"MaxSize" (by decide))
  try simp only [internal.common.DefaultMaxBatchSize, internal.common.DefaultMaxBatchDelay,
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
      · simp only [List.zip_cons_cons, List.zip_nil_left]
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
  -- the file
  obtain ⟨hro, hps0, hof, hml0, hmf0, hlp⟩ := Hok
  icases (optsAt_readOnly_rd opts dq o) $$ Hopts with ⟨%dqx, Hx, Hback⟩
  simp only [hro, _root_.Perennial.os.O_RDWR, _root_.Perennial.os.O_RDONLY,
    _root_.Perennial.os.O_CREATE]
  try wp_auto
  ihave Hopts := Hback $$ Hx
  icases (optsAt_openFile_rd opts dq o) $$ Hopts with ⟨%dqx, Hx, Hback⟩
  simp only [hof]
  try wp_auto
  ihave Hopts := Hback $$ Hx
  rw [show (W64 2 ||| W64 64 : w64) = W64 0x42 from rfl]
  iStructNamed ops
  ihave Hmf : mapFields (GF := GF) dbl (DFrac.own 1) none $$ [dataref data meta0 meta1]
  · simp only [mapFields]; iframe
  wp_apply hOpenFile path mode (DFrac.own 1) mo (fun _ => rfl) $$ [Hfm] as %f %err
    ⟨(⟨%fd, %Hfd, Hf, Hfdo, Hfm⟩ | ⟨%Herr, %mo', -, -⟩), #Herrok⟩
  · iframe; iframe #
  rotate_left
  · -- the file did not open
    obtain ⟨Herr, rfl⟩ := Herr
    cases err with
    | nil => exact absurd rfl Herr
    | ok ei =>
    ihave #Hek := fmtErrorOkOrNil_ne (GF := GF) (.ok ei) (by simp) $$ Herrok
    try wp_auto
    wp_apply hclose dbl (.ok li) (DFrac.own 1) GoInterface.nil func.nil _ none path null Hdbnn $$
      [readOnly opened freelist writeAt path Hmf datasz file] as %cerr ⟨readOnly, -⟩
    · iframe; iframe #
      isplitr
      · unfold closeMapRes; iempintro
      ileft; ipureintro; rfl
    open_exit fmtVerbs_openErr [interface.mkOk go.string #path, GoInterface.ok ei]
  -- the file opened
  obtain ⟨rfl, hfd0⟩ := Hfd
  icases openRest_opened path D mo $$ [Hfm Hfr] with ⟨%m, %xs, Hfm, Hxs, %Hm⟩
  · iframe
  try wp_auto
  wp_apply hName f fd path (DFrac.own 1) $$ [Hf] as Hf
  · iexact Hf
  icases (optsAt_timeout_rd opts dq o) $$ Hopts with ⟨%dqx, %tmo, Hx, Hback⟩
  try wp_auto
  ihave Hopts := Hback $$ Hx
  rw [← fileOwn_eq] at *
  wp_apply hFlock dbl f fd path _ (DFrac.own 1) true tmo $$ [file Hf Hfdo] as %ferr
    ⟨file, Hf, Hfdo, #Hfe⟩
  · iframe; iframe #
  cases ferr with
  | ok ei =>
    ihave #Hek := fmtErrorOkOrNil_ne (GF := GF) (.ok ei) (by simp) $$ Hfe
    try wp_auto
    wp_apply hclose dbl (.ok li) (DFrac.own 1) GoInterface.nil func.nil _ none path f Hdbnn $$
      [readOnly opened freelist writeAt path Hmf datasz file Hf Hfdo] as %cerr ⟨readOnly, -⟩
    · iframe; iframe #
      isplitr
      · unfold closeMapRes; iempintro
      iright; iexists fd, path, _; iframe
    open_exit fmtVerbs_lockErr
      [interface.mkOk go.string #path, interface.mkOk go.bool #false, GoInterface.ok ei]
  | nil =>
  try wp_auto
  -- the page size
  icases (optsAt_pageSize_rd opts dq o) $$ Hopts with ⟨%dqx, Hx, Hback⟩
  simp only [hps0]
  try wp_auto
  ihave Hopts := Hback $$ Hx
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  ihave #Hdps : globalAddr internal.common.DefaultPageSize ↦□ (W64 4096) $$ [Hcom]
  · ihave #H := isPkgInit_access (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ Hcom
    iexact H
  try wp_auto
  -- the file's size
  obtain ⟨hmaps, hxl, hsz, hbr⟩ := Hm
  wp_apply hStat f fd path (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) ⟨path.ino, true, true⟩ m $$
    [Hf Hfdo Hfm] as %fi %serr ⟨Hf, Hfdo, Hfm, Hfi, #Hse, -⟩
  · rw [← fileOwn_eq]; iframe; iframe #
  rw [← fileOwn_eq]
  icases Hfi with (⟨%fs, %Hfi, Hfs⟩ | %Hfi)
  rotate_left
  · obtain ⟨Herr, rfl⟩ := Hfi
    cases serr with
    | nil => exact absurd rfl Herr
    | ok ei =>
    try wp_auto
    wp_apply hclose dbl (.ok li) (DFrac.own 1) GoInterface.nil _ _ none path f Hdbnn $$
      [readOnly opened freelist writeAt path Hmf datasz file Hf Hfdo] as %cerr ⟨readOnly, -⟩
    · iframe; iframe #
      isplitr
      · unfold closeMapRes; iempintro
      iright; iexists fd, path, _; iframe
    open_exit fmtVerbs_statErr [interface.mkOk go.string #path, GoInterface.nil]
  obtain ⟨rfl, rfl⟩ := Hfi
  try wp_auto
  wp_apply hSize fs (W64 m.size) $$ [Hfs] as Hfs
  · iexact Hfs
  try wp_auto
  rw [← hxl]
  wp_apply hMZ dbl f fd path (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) (DFrac.own 1)
    ⟨path.ino, true, true⟩ xs rfl rfl (by omega) $$ [file pageSize Hf Hfdo Hxs]
    as %z %zerr ⟨file, pageSize, Hf, Hfdo, Hxs, Hz⟩
  · iframe; iframe #
  icases Hz with (%Hz | ⟨%Hzerr, #Hze⟩)
  rotate_left
  · cases zerr with
    | nil => exact absurd rfl Hzerr
    | ok ei =>
    try wp_auto
    wp_apply hclose dbl (.ok li) (DFrac.own 1) GoInterface.nil _ _ none path f Hdbnn $$
      [readOnly opened freelist writeAt path Hmf datasz file Hf Hfdo] as %cerr ⟨readOnly, -⟩
    · iframe; iframe #
      isplitr
      · unfold closeMapRes; iempintro
      iright; iexists fd, path, _; iframe
    open_exit fmtVerbs_metaErr [interface.mkOk go.string #path, GoInterface.ok ei]
  obtain ⟨rfl, hz⟩ := Hz
  try wp_auto
  -- a new file is initialized, an existing one's page size read
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗
      ∃ (m' : OsMeta) (xs' : List ByteG) (C : CommitSt),
        osMeta path.ino (DFrac.own 1) m' ∗ osBytes path.ino 0 (DFrac.own 1) xs' ∗
        ⌜m'.maps = ∅ ∧ xs'.length = m'.size ∧ m'.size < 2 ^ 62 ∧ openOK C D m' xs'⌝ ∗
        dbl.[DB, go!"file"] ↦ f ∗ (∃ dqp, dbl.[DB, go!"pageSize"] ↦{dqp} W64 4096) ∗
        (dbl.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦
          methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #f ∗
        fileOwn f fd path (DFrac.own 1) ∗ osFd fd (DFrac.own 1) ⟨path.ino, true, true⟩ ∗
        dbl.[DB, go!"readOnly"] ↦ false ∗ dbl.[DB, go!"opened"] ↦ true ∗
        dbl.[DB, go!"freelist"] ↦ GoInterface.nil ∗ dbl.[DB, go!"path"] ↦ path ∗
        mapFields dbl (DFrac.own 1) none ∗ dbl.[DB, go!"datasz"] ↦ W64 0 ∗
        err_ptr ↦ GoInterface.nil ∗ db_ptr ↦ dbl ∗ defer ↦ dv) ∨
    (∃ e : GoInterface, ⌜v = returnVal #() ∧ e ≠ GoInterface.nil⌝ ∗ err_ptr ↦ e ∗
      fmtErrorOkOrNil e ∗ db_ptr ↦ null ∗ defer ↦ dv)))
    at next with [Hfm Hxs Hfs file pageSize writeAt Hf Hfdo readOnly opened freelist path Hmf
      datasz err db Hdefer zero]
  · try wp_auto
    wp_apply hSize fs _ $$ [Hfs] as Hfs
    · iexact Hfs
    by_cases h0 : m.size = 0
    · -- a new file: `init`
      have hx0 : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hx0
      have hD : D = ∅ := by
        rcases hbr with h | ⟨C, hC⟩
        · exact h.2
        · have := openOK_size C D m [] hC; omega
      subst hD
      try wp_auto
      ipersist pageSize
      wp_apply hInit dbl f fd path (.ok li) m (DFrac.own 1) (DFrac.own 1) Hdbnn h0 hmaps $$
        [writeAt file Hf Hfdo Hfm Hxs] as %ierr ⟨writeAt, file, Hf, Hfdo, Hir⟩
      · iframe; iframe #
      icases Hir with (⟨%Hie, %m', %xs', Hfm, Hxs, %Hx'⟩ | ⟨%Hie, #Hek, %m', Hfm⟩)
      · subst Hie
        try wp_auto
        ileft
        isplitr
        · ipureintro; rfl
        iexists m', xs', initC
        obtain ⟨hm1, hm2, hm3⟩ := Hx'
        have hl : xs'.length = 16384 := by rw [← List.length_map Prod.fst, hm3, initImg_length]
        iframe; iframe #
        ipureintro
        exact ⟨hm1, hm2, by omega, openOK_init m' xs' hm3 hm2⟩
      · cases ierr with
        | nil => exact absurd rfl Hie
        | ok ei =>
        try wp_auto
        wp_apply hclose dbl (.ok li) (DFrac.own 1) GoInterface.nil _ _ none path f Hdbnn $$
          [readOnly opened freelist writeAt path Hmf datasz file Hf Hfdo] as %cerr ⟨readOnly, -⟩
        · iframe; iframe #
          isplitr
          · unfold closeMapRes; iempintro
          iright; iexists fd, path, _; iframe
        open_exit_j fmtVerbs_initErr [interface.mkOk go.string #path, GoInterface.ok ei]
    · -- an existing file: its page size
      obtain ⟨C, hC⟩ : ∃ C, openOK C D m xs := by
        rcases hbr with h | h
        · exact absurd h.1 h0
        · exact h
      have hzf : z = false := by
        cases z
        · rfl
        · exact absurd (hz.1 rfl) (fileImage_metas_nonzero _ C hC.1 hC.2.1)
      subst hzf
      have hne : W64 (xs.length : Int) ≠ W64 0 := by
        intro h; apply h0
        have := congrArg BitVec.toNat h
        simp at this; omega
      try rw [decide_eq_false hne]
      try wp_auto
      have h8 := openOK_size C D m xs hC
      wp_apply hGPS dbl f fd path (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) (DFrac.own 1)
        (DFrac.own 1) ⟨path.ino, true, true⟩ m xs C rfl rfl hxl (by omega) hsz hC.2.1 hC.1.1 hC.1.2.1
        $$ [file pageSize Hf Hfdo Hfm Hxs] as %gsz %gerr ⟨file, pageSize, Hf, Hfdo, Hfm, Hxs, Hg⟩
      · iframe; iframe #
      icases Hg with (%Hg | ⟨%Hge, #Hek⟩)
      · obtain ⟨rfl, rfl⟩ := Hg
        try wp_auto
        ileft
        isplitr
        · ipureintro; rfl
        iexists m, xs, C
        iframe
        ipureintro
        exact ⟨hmaps, hxl, hsz, hC⟩
      · cases gerr with
        | nil => exact absurd rfl Hge
        | ok ei =>
        try wp_auto
        wp_apply hclose dbl (.ok li) (DFrac.own 1) GoInterface.nil _ _ none path f Hdbnn $$
          [readOnly opened freelist writeAt path Hmf datasz file Hf Hfdo] as %cerr ⟨readOnly, -⟩
        · iframe; iframe #
          isplitr
          · unfold closeMapRes; iempintro
          iright; iexists fd, path, _; iframe
        open_exit_j fmtVerbs_psErr [interface.mkOk go.string #path, GoInterface.ok ei]
  iintro (⟨%Hv, %m', %xs', %C, Hfm, Hxs, %HC, file, ⟨%dqp, pageSize⟩, writeAt, Hf, Hfdo, readOnly,
    opened, freelist, path, Hmf, datasz, err, db, Hdefer⟩ | ⟨%e, %He, err, #Hek, db, Hdefer⟩)
  rotate_left
  · obtain ⟨rfl, hne⟩ := He
    try wp_auto
    wp_bind (App (Val #dv) (Val #()))
    iapply Hdef $$ [err]
    · iexact err
    · iexact Hek
    iintro err
    try wp_auto
    iapply HΦ
    iframe Hopts
    iright; ipureintro; exact hne
  subst Hv
  ipersist pageSize
  try wp_auto
  rw [recv_eq_func_mk BAnon BAnon]
  try wp_auto
  -- the mapping
  obtain ⟨hmaps', hxl', hsz', hC⟩ := HC
  icases (optsAt_int_rd opts dq o go!"InitialMmapSize" (by decide)) $$ Hopts with
    ⟨%dqx, %minsz, Hx, Hback⟩
  try wp_auto
  ihave Hopts := Hback $$ Hx
  simp only [hml0]
  ipersist Mlock
  ipersist MmapFlags
  have hmf' : o.mmapFlags = W64 0 ∨ o.mmapFlags = W64 0x8000 := by
    unfold mapPopulate at hmf0
    rcases hmf0 with h | h
    · left; apply BitVec.eq_of_toNat_eq; simpa using h
    · right; apply BitVec.eq_of_toNat_eq; simpa using h
  wp_apply hMmap dbl f fd path (.ok li) o.mmapFlags _ (DFrac.own 1) m' xs' minsz Hdbnn hmaps' hxl'
    (by omega) hmf' (fun _ => openOK_meta C D m' xs' hC) $$
    [MaxSize rwtx file Hf Hfdo Hfm Hxs Hmf datasz] as %merr ⟨Hfix, file, Hf, Hfdo, Hxs, Hmr⟩
  · unfold mmapOwnFix; iframe; iframe #
  unfold mmapOwnFix
  icases Hfix with ⟨-, -, -, MaxSize, -, -, rwtx⟩
  icases Hmr with (⟨%Hme, %base, %L, %HL, Hmf, datasz, Hfm, Hbp, %vf, Hcells⟩ |
    ⟨%Hme, #Hek, Hmf, datasz, %m'', Hfm⟩)
  rotate_left
  · cases merr with
    | nil => exact absurd rfl Hme
    | ok ei =>
    try wp_auto
    wp_apply hclose dbl (.ok li) (DFrac.own 1) GoInterface.nil _ _ none path f Hdbnn $$
      [readOnly opened freelist writeAt path Hmf datasz file Hf Hfdo] as %cerr ⟨readOnly, -⟩
    · iframe; iframe #
      isplitr
      · unfold closeMapRes; iempintro
      iright; iexists fd, path, _; iframe
    open_exit fmtVerbs_mapErr [interface.mkOk go.string #path, GoInterface.ok ei]
  subst Hme
  try wp_auto
  -- the database's fixed fields
  ipersist stats
  ipersist readOnly
  ipersist StrictMode
  ipersist NoSync
  ipersist NoGrowSync
  ipersist NoFreelistSync
  ipersist PreLoadFreelist
  ipersist FreelistType
  ipersist MaxBatchSize
  ipersist MaxBatchDelay
  ipersist AllocSize
  ipersist MaxSize
  ipersist openFile
  ipersist batch
  imod sync.init_Mutex iprop(True) ⊤ _ $$ batchMu [] with #HbatchMu
  · inext; itrivial
  -- the page pool (U11i, `Open/PoolNew`): its `New` reads `Open`'s named result `db`, which
  -- every `return` writes; a `Get` caller lends it a `poolR γbq N P` (the whole `boltState`
  -- validity token `γbq` excluded), and `Open`'s writes hold that token (`dp_lock`)
  imod ghostVar_alloc (GF := GF) () with ⟨%γbq, Hbq⟩
  imod ghostVar_alloc (GF := GF) (0 : Nat) with ⟨%γs, Hs⟩
  icases (ghostVar_split_half γs 1 (0 : Nat)).1 $$ Hs with ⟨Hs, Hs'⟩
  icases (typedPointsto_half_split db_ptr dbl 1).1 $$ db with ⟨db, Hdp⟩
  imod dp_init ⊤ N γs γbq db_ptr dbl $$ [Hs' Hdp] with #Hdpi
  · iframe
  imod init_Pool_all _ _ (poolR γbq N) pageBuf ⊤ $$ [pagePool] with #Hp
  · iframe pagePool
    isplitl
    · iintro !> %P
      unfold sync.newSpec
      iright
      wp_start as HR
      wp_auto
      -- the read `![*DB] #db_ptr` (non-atomic) on a loan of the protocol's (U11j,
      -- `dp_borrow`): the persistent cell (state 2), or a fraction against the lease `P`,
      -- given back after the read (`wp_load_loan`, `P` under two laters the next steps take off)
      unfold poolR
      icases HR with ⟨HP, #Href⟩
      imod dp_borrow N γs γbq db_ptr dbl P $$ [HP] with (⟨#Hdp, HP⟩ | ⟨%q, Hdp, Hloan⟩)
      · iframe; iframe #
      · wp_auto
        wp_apply wp_slice_make2 (V := w8) $$ [] as %sl ⟨Hsl, -⟩
        · ipureintro; decide
        try wp_auto
        iapply HΦ
        iframe HP; iframe #
        unfold pageBuf
        iexists sl
        rw [show (zero_val w8 : w8) = W8 0 from rfl] at *
        iframe Hsl
        ipureintro; rfl
      · wp_apply (wp_load_loan N γs γbq db_ptr dbl P q) $$ [Hdp Hloan] as HP
        · iframe
        wp_apply wp_slice_make2 (V := w8) $$ [] as %sl ⟨Hsl, -⟩
        · ipureintro; decide
        try wp_auto
        iapply HΦ
        iframe HP; iframe #
        unfold pageBuf
        iexists sl
        rw [show (zero_val w8 : w8) = W8 0 from rfl] at *
        iframe Hsl
        ipureintro; rfl
    · ipureintro; rfl
  ihave #Hpool : (∃ pf : GoFunc,
      (∀ P : IProp GF, sync.isPool dbl.[DB, go!"pagePool"] pf (poolR γbq N P) pageBuf) ∗
      ⌜pf ≠ func.nil⌝) $$ []
  · iexists _
    iframe Hp
    ipureintro; intro h; injection h with _ _ h3; cases h3
  ihave #Hfix : dbFixed (GF := GF) γbq N dbl sp $$ []
  · unfold dbFixed dbLogger
    iframe #
    isplitr
    · ipureintro; exact hmf'
    ipureintro; exact Hlgty
  -- the freelist, the core and the writer phase (`DB.loadFreelist.spec_open`)
  wp_apply hLoad γbq N dbl sp f fd path C base L _ xs'
    (openOK_lfOK N dbl C D m' xs' base L hC hxl' hsz' HL.2.1 HN Hdbnn) hfd0 $$
    [metalock mmaplock statlock opened freelist writeAt rwtx file path datasz Hmf Hfm Hf Hfdo Hps
      Hxs Hbp Hcells freelistLoad Hbq] as Hlf
  · unfold lfPre
    rw [← hxl']
    iframe; iframe #
    done
  iunfold lfPost at Hlf
  icases Hlf with ⟨%B, %fl, %fli, #Hcore, #Hpl, Hw, Hst, Hflo, Hsp, Hcls, Hstate, Hopn, ⟨%Hwok, %HBbq⟩⟩
  subst HBbq
  have hCD : treeData C = D := hC.2.2.2.2.2.2.2
  -- the writer side `W`: `loadFreelist`'s, or with the file's metadata after the sync below
  have hWC : (lfW C base L { m' with maps := GMap.singleton base L } xs' f fd fl fli).C = C := rfl
  have hWms : (lfW C base L { m' with maps := GMap.singleton base L } xs' f fd fl fli).ms =
    some (base, L) := rfl
  have hWfl : (lfW C base L { m' with maps := GMap.singleton base L } xs' f fd fl fli).fl = fl :=
    rfl
  have hWfli : (lfW C base L { m' with maps := GMap.singleton base L } xs' f fd fl fli).fli =
    fli := rfl
  generalize lfW C base L { m' with maps := GMap.singleton base L } xs' f fd fl fli = W
    at Hwok hWC hWms hWfl hWfli ⊢
  try wp_auto
  -- `if !db.NoSync { fdatasync(db) }` (bbolt `ea4cab52`): on an error, `db.Close()` (the
  -- database is shared with its locks by now, as for the transaction's error exit)
  cases nos
  case' false =>
    try wp_auto
    icases wdbCore_file_acc (GF := GF) B dbl path W $$ Hw with ⟨Hf, Hfo, Hfd, Hosm, Hwb⟩
    wp_apply hFds dbl W.f W.fd path W.m (DFrac.own 1) (DFrac.own 1) $$ [Hf Hfo Hfd Hosm]
      as %serr ⟨Hf, Hfo, Hfd, ⟨%m2, Hosm, %hm2⟩, Hsr⟩
    · iframe; iframe #
    ihave Hw := Hwb $$ %m2 %hm2.1 Hf Hfo Hfd Hosm
    have Hwok2 := wdbOK_withMeta W m2 hm2.1 hm2.2 Hwok
    have hWC2 : ({ W with m := m2 } : WDb).C = C := hWC
    have hWms2 : ({ W with m := m2 } : WDb).ms = some (base, L) := hWms
    have hWfl2 : ({ W with m := m2 } : WDb).fl = fl := hWfl
    have hWfli2 : ({ W with m := m2 } : WDb).fli = fli := hWfli
    clear Hwok hWC hWms hWfl hWfli hm2
    generalize ({ W with m := m2 } : WDb) = W at Hwok2 hWC2 hWms2 hWfl2 hWfli2 ⊢
    icases Hsr with (%Hse | ⟨%Hse, #Hek⟩)
    rotate_left
    · cases serr with
      | nil => exact absurd rfl Hse
      | ok ei =>
      try wp_auto
      have hOW := open_writer (GF := GF) ⊤ B N dbl path sp _ Hwok2
      rw [hWC2, hWfl2, hWfli2] at hOW
      imod hOW $$ [Hcore Hpl rwlock Hw Hst Hflo Hsp Hcls Hopn] with #Hbolt
      · iframe; iframe #
      ihave Hst' : boltState (GF := GF) ⟨mkGs B, N⟩ 1 D $$ [Hstate]
      · unfold boltState; rw [bnsOf_mkGs, ← hCD]; iexact Hstate
      wp_apply hClose dbl ⟨mkGs B, N⟩ $$ []
      · unfold isBolt; rw [bnsOf_mkGs]; iexact Hbolt
      iintro %cerr -
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      simp only [show sint.nat (W64 (0 + 1)) = 1 from rfl, List.set]
      try wp_auto
      -- (`+noauto`: `open_step` takes the step before the write of `db`)
      wp_apply +noauto wp_boltLog li _ _ _ _ [interface.mkOk go.string #path, GoInterface.ok ei] _
        iprop(True) _ errorf_mem' fmtVerbs_syncErr rfl $$ Hlgok [Hsl] [] [] as Hsl -
      · iexact Hsl
      · open_args
      ihave ⟨-, Hlk⟩ := open_lock B N γs _ db_ptr dbl $$ [Hdpi Hs Hst']
      · iframe; iframe #
      open_step
      try wp_auto
      wp_bind (App (Val #dv) (Val #()))
      iapply Hdef $$ [err]
      · iexact err
      · simp only [fmtErrorOkOrNil]; iexact Hek
      iintro err
      try wp_auto
      iapply HΦ
      iframe Hopts
      iright; ipureintro; intro h; cases h
    subst Hse
    have Hwok := Hwok2
    have hWC := hWC2
    have hWms := hWms2
    have hWfl := hWfl2
    have hWfli := hWfli2
    clear Hwok2 hWC2 hWms2 hWfl2 hWfli2
  -- both branches: the writer side `W`
  all_goals
    try wp_auto
    cases nfs
    rotate_left
    · -- `NoFreelistSync`: done
      have hOW := open_writer (GF := GF) ⊤ B N dbl path sp _ Hwok
      rw [hWC, hWfl, hWfli] at hOW
      imod hOW $$ [Hcore Hpl rwlock Hw Hst Hflo Hsp Hcls Hopn] with #Hbolt
      · iframe; iframe #
      open_ok
    -- `hasSyncedFreelist()`
    have hacc := wdbCore_meta_acc (GF := GF) B dbl path W
    rw [hWms, hWC] at hacc
    icases hacc $$ Hw with ⟨Hmf, Hmq, Hwb⟩
    try wp_auto
    wp_apply hSync dbl base L C (DFrac.own (1 : Qp).half) (1 : Qp).half.half hC.2.1 $$ [Hmf Hmq]
      as ⟨Hmf, Hmq⟩
    · iframe
    ihave Hw := Hwb $$ Hmf Hmq
    have hOW := open_writer (GF := GF) ⊤ B N dbl path sp _ Hwok
    rw [hWC, hWfl, hWfli] at hOW
    imod hOW $$ [Hcore Hpl rwlock Hw Hst Hflo Hsp Hcls Hopn] with #Hbolt
    · iframe; iframe #
    by_cases hfl : C.flpg = none
    rotate_left
    · rw [decide_eq_false hfl]
      open_ok
    rw [decide_eq_true hfl]
    try wp_auto
    -- no synced freelist: a write transaction, committed unchanged
    ihave Hst' : boltState (GF := GF) ⟨mkGs B, N⟩ 1 D $$ [Hstate]
    · unfold boltState; rw [bnsOf_mkGs, ← hCD]; iexact Hstate
    wp_apply hBegin dbl ⟨mkGs B, N⟩ true (fun _ => iprop(emp)) $$ [] as %tx %txErr Hb
    · simp only [↓reduceIte]; unfold isBolt; rw [bnsOf_mkGs]
      isplitl
      · iexact Hbolt
      iempintro
    try simp only [↓reduceIte]
    icases Hb with (⟨%Hte, #Htxdb, %D', Htx⟩ | ⟨%Hte, #Hek, -⟩)
    rotate_left
    · obtain ⟨Hne, rfl⟩ := Hte
      cases txErr with
      | nil => exact absurd rfl Hne
      | ok ei =>
      open_tx_exit
    subst Hte
    icases persistent_entails_left (boltTx_base tx ⟨mkGs B, N⟩ 1 1 (TxView.wr D') D) $$
      [Htx Hst'] with ⟨⟨Htx, Hst'⟩, %Hbase⟩
    · iframe
    have hD' : D' = D := Hbase rfl
    subst hD'
    icases persistent_entails_left (boltTx_nonnull tx ⟨mkGs B, N⟩ 1 (TxView.wr D')) $$ Htx
      with ⟨Htx, %Htxnn⟩
    try wp_auto
    rw [decide_eq_false Htxnn]
    try wp_auto
    -- the update's carrier is the whole state itself, back on every exit (U11i)
    wp_apply hCommit tx ⟨mkGs B, N⟩ (TxView.wr D') (boltState ⟨mkGs B, N⟩ 1 D')
        (boltState ⟨mkGs B, N⟩ 1 D')
        (by simp only [TxView.wr]; exact boltState_commit_au _ _ _) $$ [Htx Hst']
      as %cerr ⟨-, Hc⟩
    · iframe
      ipureintro; rfl
    icases Hc with (⟨%Hce, Hst'⟩ | ⟨%Hce, #Hek, Hor⟩)
    rotate_left
    · cases cerr with
      | nil => exact absurd rfl Hce
      | ok ei =>
      ihave Hst' : boltState (GF := GF) ⟨mkGs B, N⟩ 1 D' $$ [Hor]
      · icases Hor with (H | H) <;> iexact H
      open_tx_exit
    subst Hce
    open_ret

end proof

end bbolt
end EtcdGrove
end Perennial
