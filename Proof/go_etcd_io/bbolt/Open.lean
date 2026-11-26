/-
The proof of `Spec/go_etcd_io/bbolt/Open.lean` (U11g, `notes/bbolt-proof-plan.md`; design §3.11
"Open"): the fields `Open` sets, the file opened and locked, initialized when empty (`DB.init`)
or its page size read (`getPageSize`), unless `NoSync` the whole file synced with its bytes
(`fdatasync.specS`; bbolt `c5a6065`, before the mapping since `2f6fcff`:
issues/bbolt-open-unsynced-meta-kill-then-power-loss.md; on an error, `db.close()`), the page pool,
the mapping (`mmapUnlocked`, owned), the freelist loaded (`DB.loadFreelist.spec_open`: the core
phase, `Open/Core`), the writer phase (`Open/Core.open_writer`), and, for a file with no synced
freelist, a write transaction committed unchanged (`Begin`, `Commit`, over the client's
`boltState` it then returns).

Every error exit closes the database (`DB.close.spec_owned`, or `DB.Close` once the transaction
began), logs, and returns through the deferred log (`Hdef`, the deferred function's spec).
The page pool's `New` reads the named result `db`, which the returns write: it borrows the cell
from the protocol `Open/PoolNew.dpProt` against its caller's lease (U11j).
`fs.FileMode.String.spec` (`Spec/io/fs/FileMode__String.lean`) is a hypothesis, linked to its proof.
-/
module

public import Spec.go_etcd_io.bbolt.Open
public import Spec.go_etcd_io.bbolt.Options__String
public import Spec.go_etcd_io.bbolt.DB__Begin
public import Proof.go_etcd_io.bbolt.Tx__Commit_err
public import Proof.go_etcd_io.bbolt.Open.CloseTok
public import Spec.go_etcd_io.bbolt.fdatasync
public import Proof.go_etcd_io.bbolt.Open.FdatasyncW
public import Spec.os.File__Stat
public import Spec.os.OpenFileS
public import Proof.os.WriteFileLemmas
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
public import Spec.go_etcd_io.bbolt.DB__needsInit
public import Proof.go_etcd_io.bbolt.Open.InitPartial
public import Proof.go_etcd_io.bbolt.Open.FileModeString
public import Proof.go_etcd_io.bbolt.Open.LogFmt
public import Proof.go_etcd_io.bbolt.Open.SyncAcc
public import Proof.go_etcd_io.bbolt.Inv.LoggerOk
public import Proof.go_etcd_io.bbolt.Open.PoolNew
public import Proof.ReceiptTactics
public import Proof.go_etcd_io.bbolt.Open.Congr
public import Proof.go_etcd_io.bbolt.Open.Mode
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt
open Fs

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
  iframe Hopts HW
  iexists V'
  iframe Ht
  iright; ipureintro; exact ⟨(fun h => by cases h), by assumption⟩))

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
  first | exact ⟨rfl, (fun h => nomatch h), by assumption⟩ | exact ⟨trivial, (fun h => nomatch h), by assumption⟩))

/-- **`Open`'s last write of `db` begins** (U11i, U11j; `Open/PoolNew.dp_lock`): the whole
validity token of the client's `boltState` lent to the protocol, which gives back the cell's
other half around one step of `Open`'s (`open_step`). -/
theorem open_lock [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (B : BNs) (N : Namespace) (γs : GName) (D : Data)
    (dp db : Loc) :
    dpProt (GF := GF) N γs B.bq dp db ∗ ghostVar γs (1 : Qp).half 0 ∗
      boltState (GF := GF) ⟨mkGs B, N⟩ 1 D ⊢
    (∃ ν : Nat, ghostVar B.st (1 : Qp).half (D, ν) ∗ crashPart B 1 D ν) ∗
      (|={⊤, ⊤ \ ↑(dpN N)}=> ▷ |={⊤ \ ↑(dpN N), ⊤}=>
      ghostVar γs (1 : Qp).half 1 ∗ dp ↦{DFrac.own (1 : Qp).half} db) := by
  iintro ⟨#Hinv, Hs, Hst⟩
  unfold boltState boltStateDef boltStateVDef
  rw [bnsOf_mkGs]
  icases Hst with ⟨%ν, Hst, Hbq, Hcp⟩
  isplitl [Hst Hcp]
  · iexists ν; iframe
  iapply dp_lock N γs B.bq dp db $$ [Hinv Hs Hbq]
  iframe; iframe #

/-- **`Open`'s last write of `db` done, on success**: the token back, `db` persistent. -/
theorem open_unlock [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (B : BNs) (N : Namespace) (γs : GName) (D : Data)
    (dp db : Loc) :
    dpProt (GF := GF) N γs B.bq dp db ∗ ghostVar γs (1 : Qp).half 1 ∗ dp ↦ db ∗
      (∃ ν : Nat, ghostVar B.st (1 : Qp).half (D, ν) ∗ crashPart B 1 D ν) ⊢
    |={⊤}=> dp ↦□ db ∗ boltState (GF := GF) ⟨mkGs B, N⟩ 1 D := by
  iintro ⟨#Hinv, Hs, Hdp, ⟨%ν, Hst, Hcp⟩⟩
  imod dp_unlock N γs B.bq dp db $$ [Hinv Hs Hdp] with ⟨Hbq, #Hdp⟩
  · iframe; iframe #
  imodintro
  iframe Hdp
  unfold boltState boltStateDef boltStateVDef
  rw [bnsOf_mkGs]
  iexists ν
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
  iframe Hopts HW
  iexists V'
  iframe Ht
  ileft
  isplitr
  · ipureintro; rfl
  iexists ⟨mkGs B, N⟩, p.ino
  isplitr
  · ipureintro; exact ⟨rfl, hl⟩
  iframe Hst'
  unfold isBolt boltIno boltCloser
  rw [bnsOf_mkGs]
  iframe Hclo
  isplitr
  · iexact Hbolt
  iexists _
  iapply isBoltCoreP_t0At $$ Hcore))

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
  wp_apply hClose dbl ⟨mkGs B, N⟩ $$ [Hclo]
  · unfold isBolt boltCloser; rw [bnsOf_mkGs]; iframe Hclo; iexact Hbolt
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
  iframe Hopts HW
  iexists V'
  iframe Ht
  iright; ipureintro; exact ⟨(fun h => by cases h), by assumption⟩))

/-- **`Open`, generic in how the file is opened** (S3a: the tree's `os.OpenFile` for `Open.spec`,
the shared mode's `os.OpenFile.specCreateS` for `Open.specS`): the opening's resources `Pre`, given
back as `Back x` for some `x` (the tree, or the claim on the name, after the open) on every exit,
and on success the file's inode `i` with `Good x i` (it is the file at the path in `x`) and its
contents `openedF i D`. Everything after the open is this proof's. -/
private abbrev openFileDb.spec [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] {X : Type} (Ek : Prop)
    (B : Nat → Prop) (Pre : IProp GF)
    (Back : X → IProp GF) (Good : X → Ino → Prop) (path : GoString) (perm : w32) (D : Data) : Prop :=
  {{ osInv (GF := GF) ∗ Pre }}
    (App (App (App (Val (@! os.OpenFile)) (Val #path)) (Val #(W64 0x42))) (Val #perm))
  {{ (f : Loc) (err : GoInterface), RET (PairV #f #err); ∃ x : X, Back x ∗
      ((∃ (fd : w64) (i : Ino), ⌜err = interface.nil ∧ 0 ≤ fd.toInt ∧ Good x i⌝ ∗
          os.ownFile f fd path (DFrac.own 1) ∗ osFd fd (DFrac.own 1) ⟨i, true, true, none, none⟩ ∗
          openedF i D B) ∨
       ⌜err ≠ interface.nil ∧ f = null ∧ Ek⌝) ∗
      fmtErrorOkOrNil err }}

/-- An opened file's facts hold of it synced: a sync changes no byte's value (each becomes
`durB` of it) and not the size. -/
theorem openOK_synced [ExtSemantics fsExt] [FsSemOk] (C : CommitSt) (D : Data) (m : OsMeta)
    (xs : List ByteG) (h : openOK C D m xs) : openOK C D m.synced (xs.map fun x => durB x.1) := by
  have e : (xs.map fun x => durB x.1).map Prod.fst = xs.map Prod.fst := by
    rw [List.map_map]; rfl
  unfold openOK at *
  rw [e]
  exact h

set_option maxHeartbeats 4000000 in
private theorem Open.wp_proofG [sync.Assumptions] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
    [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 62)]
    (hName : os.File.Name.spec (GF := GF) (hG := hG))
    (hFlock : flock.spec (GF := GF) (hG := hG))
    (hStat : os.File.Stat.spec (GF := GF) (hG := hG))
    (hSize : os.fileStat.Size.spec (GF := GF) (hG := hG))
    (hNI : DB.needsInit.spec (GF := GF) (hG := hG))
    (hInit : DB.init.spec (GF := GF) (hG := hG))
    (hGPS : DB.getPageSize.spec_own (GF := GF) (hG := hG))
    (hMmap : DB.mmapUnlocked.spec_own (GF := GF) (hG := hG))
    (hLoad : DB.loadFreelist.spec_open (GF := GF) (hG := hG))
    (hSync : DB.hasSyncedFreelist.spec (GF := GF) (hG := hG))
    (hFds : fdatasync.specS (GF := GF) (hG := hG))
    (hBegin : DB.Begin.spec (GF := GF) (hG := hG))
    (hCommit : Tx.Commit_err.spec (GF := GF) (hG := hG))
    (hClose : DB.Close.specTok (GF := GF) (hG := hG))
    (hclose : DB.close.spec_owned (GF := GF) (hG := hG))
    (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hOptStr : Options.String.spec (GF := GF) (hG := hG))
    (hModeStr : fs.FileMode.String.spec (GF := GF) (hG := hG))
    {X : Type} (Pre : IProp GF) (Back : X → IProp GF) (Good : X → Ino → Prop)
    (N : Namespace) (path : GoString) (mode : w32) (opts : Loc) (dq : DFrac) (o : OptsM) (D : Data)
    (Ek : Prop) (B : Nat → Prop) (W : IProp GF)
    (hFs : ¬ FsNoErr → Ek) (hB : ∀ n, B n → Ek ∨ n ≤ 0xFFFFFFFFFFFF)
    (hWto : ∀ dqx (x : time.Duration),
      W ∗ opts.[Options, go!"Timeout"] ↦{dqx} x ⊢ ⌜Ek ∨ x = W64 0⌝)
    (hWnf : ∀ dqx (x : Bool),
      W ∗ opts.[Options, go!"NoFreelistSync"] ↦{dqx} x ⊢ ⌜x = true⌝)
    (hWms : ∀ dqx (x : w64),
      W ∗ opts.[Options, go!"InitialMmapSize"] ↦{dqx} x ⊢ ⌜Ek ∨ sint.Z x ≤ 0xFFFFFFFFFFFF⌝)
    (hOF : openFileDb.spec (GF := GF) (hG := hG) Ek B Pre Back Good path mode D) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv ∗ ⌜↑N ## ↑osN⌝ ∗ Pre ∗
        optsAt opts dq o ∗ W ∗ ⌜o.ok⌝ ∗ (⌜o.logger = GoInterface.nil⌝ ∨ boltLogger o.logger) }}
      (App (App (App (Val (@! go_etcd_io.bbolt.Open)) (Val #path)) (Val #mode)) (Val #opts))
    {{ (db : Loc) (err : GoInterface), RET (PairV #db #err); optsAt opts dq o ∗ W ∗
        (∃ x : X, Back x ∗
          ((⌜err = GoInterface.nil⌝ ∗ ∃ (γ : BoltName) (i : Ino),
              ⌜γ.ns = N ∧ Good x i⌝ ∗ isBolt db γ ∗ boltIno γ i ∗ boltState γ 1 D ∗
              boltCloser γ) ∨
           ⌜err ≠ GoInterface.nil ∧ Ek⌝)) }} := by
  wp_start as ⟨#Hos, %HN, Hph, Hopts, HW, %Hok, Hlgr⟩
  ihave %Hoptnn := optsAt_nonnull _ _ _ $$ Hopts
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
  icases persistent_entails_left (hWnf dqx nfs) $$ [HW Hx] with ⟨⟨HW, Hx⟩, %hnfs⟩
  · iframe
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
        · iapply (options_logArgOk hOptStr opts dq o Hok.2.2.2.2.2) $$ Hpkg
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
  wp_apply hOF $$ [Hph] as %f %err
    ⟨%V', Ht, (⟨%fd, %i, %Hfd, Hf, Hfdo, Hop⟩ | %Herr), #Herrok⟩
  · iframe; iframe #
  rotate_left
  · -- the file did not open
    obtain ⟨Herr, rfl, hk⟩ := Herr
    cases err with
    | nil => exact absurd rfl Herr
    | ok ei =>
    ihave #Hek := fmtErrorOkOrNil_ne (GF := GF) (.ok ei) (by simp) $$ Herrok
    try wp_auto
    wp_apply hclose dbl (.ok li) (DFrac.own 1) GoInterface.nil func.nil _ none { path := path, ino := 0 } null Hdbnn $$
      [readOnly opened freelist writeAt path Hmf datasz file] as %cerr ⟨readOnly, -⟩
    · iframe; iframe #
      isplitr
      · unfold closeMapRes; iempintro
      ileft; ipureintro; rfl
    open_exit fmtVerbs_openErr [interface.mkOk go.string #path, GoInterface.ok ei]
  -- the file opened
  obtain ⟨rfl, hfd0, hl⟩ := Hfd
  -- the database's file: its path and inode
  obtain ⟨p, rfl, rfl, hpcs⟩ : ∃ p : BFile, p.path = path ∧ p.ino = i ∧ p.cs = none :=
    ⟨{ path := path, ino := i }, rfl, rfl, rfl⟩
  -- (outside a crash invariant until `Open/Mode` chooses the file's mode, before `loadFreelist`)
  unfold openedF
  icases Hop with ⟨%m, %xs, Hfm, Hxs, %Hm, %HBm, #Hrcf⟩
  have hBm := hB _ HBm
  try wp_auto
  wp_apply +noauto hName f fd p.path (DFrac.own 1) $$ [Hf] as Hf
  · iexact Hf
  icases (optsAt_timeout_rd opts dq o) $$ Hopts with ⟨%dqx, %tmo, Hx, Hback⟩
  icases persistent_entails_left (hWto dqx tmo) $$ [HW Hx] with ⟨⟨HW, Hx⟩, %htmo⟩
  · iframe
  -- a persistent receipt of one step (session bbolt-inv: an initialized file's txid, 1, is
  -- `metaR`'s `⧖`), from `flock`'s resolution
  imod preceipt_zero (GF := GF) with #Hrc1
  wp_raise_receipt Hrc1
  ihave Hopts := Hback $$ Hx
  rw [← fileOwn_eq] at *
  wp_apply hFlock dbl f fd p ⟨p.ino, true, true, none, none⟩ (DFrac.own 1) true tmo rfl $$ [file Hf Hfdo] as %ferr
    ⟨file, Hf, #Hfe, Hlk⟩
  · iframe; iframe #
  cases ferr with
  | ok ei =>
    icases Hlk with (⟨%hn, -⟩ | ⟨%hfl, Hfdo⟩)
    · exact absurd hn (by simp)
    have hk : Ek := by
      rcases hfl.2 with h | h
      · exact hFs h
      · rcases htmo with h' | h'
        · exact h'
        · exact absurd h' h
    ihave #Hek := fmtErrorOkOrNil_ne (GF := GF) (.ok ei) (by simp) $$ Hfe
    try wp_auto
    wp_apply hclose dbl (.ok li) (DFrac.own 1) GoInterface.nil func.nil _ none p f Hdbnn $$
      [readOnly opened freelist writeAt path Hmf datasz file Hf Hfdo] as %cerr ⟨readOnly, -⟩
    · iframe; iframe #
      isplitr
      · unfold closeMapRes; iempintro
      iright; iexists fd, p.path, _; iframe; iapply lockToks_unlocked <;> rfl
    open_exit fmtVerbs_lockErr
      [interface.mkOk go.string #(p.path), interface.mkOk go.bool #false, GoInterface.ok ei]
  | nil =>
  icases Hlk with (⟨-, Hfdo, Htok⟩ | ⟨%hn, -⟩)
  rotate_left
  · exact absurd rfl hn.1
  -- (the file-lock semantics, 2026-11-15) the descriptor holds `flock`'s exclusive lock: its token
  -- rides with the `path` field (`dbPathLk`) until `close`
  have hsl : (⟨p.ino, true, true, none, none⟩ : OsFd).setLk .flock (some true) = dbFd p.ino := rfl
  ihave Hfdo : osFd fd (DFrac.own 1) (dbFd p.ino) $$ [Hfdo]
  · rw [← hsl]; iexact Hfdo
  ihave Htok : lockTok .flock fd (dbFd p.ino) $$ [Htok]
  · rw [← hsl]; iexact Htok
  ihave Htok : osLock .flock p.ino fd $$ [Htok]
  · iapply (lockTok_some .flock fd (dbFd p.ino) rfl).1 $$ Htok
  ihave path : dbPathLk dbl p fd $$ [path Htok]
  · unfold dbPathLk; iframe; iapply bSyncs_none hpcs
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
  wp_apply hStat f fd p.path (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) (dbFd p.ino) m $$
    [Hf Hfdo Hfm] as %fi %serr ⟨Hf, Hfdo, Hfm, Hfi, #Hse, -⟩
  · rw [← fileOwn_eq]; iframe; iframe #
  rw [← fileOwn_eq]
  icases Hfi with (⟨%fs, %Hfi, Hfs⟩ | %Hfi)
  rotate_left
  · obtain ⟨Herr, rfl, hfs⟩ := Hfi
    have hk : Ek := hFs hfs
    cases serr with
    | nil => exact absurd rfl Herr
    | ok ei =>
    try wp_auto
    iunfold dbPathLk at path
    icases path with ⟨path, Htok, -⟩
    wp_apply hclose dbl (.ok li) (DFrac.own 1) GoInterface.nil _ _ none p f Hdbnn $$
      [readOnly opened freelist writeAt path Hmf datasz file Hf Hfdo Htok] as %cerr ⟨readOnly, -⟩
    · iframe; iframe #
      isplitr
      · unfold closeMapRes; iempintro
      iright; iexists fd, p.path, _; iframe; iapply dbFd_lockToks $$ Htok
    open_exit fmtVerbs_statErr [interface.mkOk go.string #(p.path), GoInterface.nil]
  obtain ⟨rfl, rfl⟩ := Hfi
  try wp_auto
  wp_apply hSize fs (W64 m.size) $$ [Hfs] as Hfs
  · iexact Hfs
  try wp_auto
  rw [← hxl]
  wp_apply hNI dbl f fd p (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) (DFrac.own 1)
    (dbFd p.ino) false xs rfl rfl (by omega) $$ [file pageSize readOnly Hf Hfdo Hxs]
    as %z %zerr ⟨file, pageSize, readOnly, Hf, Hfdo, Hxs, Hz⟩
  · iframe; iframe #
  icases Hz with (%Hz | ⟨%Hzerr, #Hze⟩)
  rotate_left
  · have hk : Ek := hFs Hzerr.2
    cases zerr with
    | nil => exact absurd rfl Hzerr.1
    | ok ei =>
    try wp_auto
    iunfold dbPathLk at path
    icases path with ⟨path, Htok, -⟩
    wp_apply hclose dbl (.ok li) (DFrac.own 1) GoInterface.nil _ _ none p f Hdbnn $$
      [readOnly opened freelist writeAt path Hmf datasz file Hf Hfdo Htok] as %cerr ⟨readOnly, -⟩
    · iframe; iframe #
      isplitr
      · unfold closeMapRes; iempintro
      iright; iexists fd, p.path, _; iframe; iapply dbFd_lockToks $$ Htok
    open_exit fmtVerbs_metaErr [interface.mkOk go.string #(p.path), GoInterface.ok ei]
  obtain ⟨rfl, hz0, hzi⟩ := Hz
  try wp_auto
  -- a new file, or one an interrupted `init` left, is initialized; an existing one's page size
  -- read
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗
      ∃ (m' : OsMeta) (xs' : List ByteG) (C : CommitSt),
        osMeta p.ino (DFrac.own 1) m' ∗ osBytes p.ino 0 (DFrac.own 1) xs' ∗
        ⌜m'.maps = ∅ ∧ xs'.length = m'.size ∧ (m'.size < 2 ^ 62 ∧ m'.size % 4096 = 0) ∧
          openOK C D m' xs' ∧ (Ek ∨ m'.size ≤ 0xFFFFFFFFFFFF)⌝ ∗ ⧖ C.txid ∗
        dbl.[DB, go!"file"] ↦ f ∗ (∃ dqp, dbl.[DB, go!"pageSize"] ↦{dqp} W64 4096) ∗
        (dbl.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦
          methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #f ∗
        fileOwn f fd p.path (DFrac.own 1) ∗ osFd fd (DFrac.own 1) (dbFd p.ino) ∗
        dbl.[DB, go!"readOnly"] ↦ false ∗ dbl.[DB, go!"opened"] ↦ true ∗
        dbl.[DB, go!"freelist"] ↦ GoInterface.nil ∗ dbPathLk dbl p fd ∗
        mapFields dbl (DFrac.own 1) none ∗ dbl.[DB, go!"datasz"] ↦ W64 0 ∗
        err_ptr ↦ GoInterface.nil ∗ db_ptr ↦ dbl ∗ defer ↦ dv) ∨
    (∃ e : GoInterface, ⌜v = returnVal #() ∧ e ≠ GoInterface.nil ∧ Ek⌝ ∗ err_ptr ↦ e ∗
      fmtErrorOkOrNil e ∗ db_ptr ↦ null ∗ defer ↦ dv)))
    at next with [Hfm Hxs Hfs file pageSize writeAt Hf Hfdo readOnly opened freelist path Hmf
      datasz err db Hdefer]
  · try wp_auto
    cases z
    · -- an existing file: its page size
      have hne : xs.length ≠ 0 := fun h => absurd (hz0 h) Bool.false_ne_true
      have h0 : m.size ≠ 0 := by omega
      obtain ⟨C, hC⟩ : ∃ C, openOK C D m xs := by
        rcases hbr with h | h
        · exact absurd h.1 h0
        · exact h
      try wp_auto
      have h8 := openOK_size C D m xs hC
      wp_apply hGPS dbl f fd p (DFrac.own 1) (DFrac.own 1) (DFrac.own 1) (DFrac.own 1)
        (DFrac.own 1) (dbFd p.ino) m xs C rfl rfl hxl (by omega) hsz.1 hC.2.1 hC.1.1 hC.1.2.1
        $$ [file pageSize Hf Hfdo Hfm Hxs] as %gsz %gerr ⟨file, pageSize, Hf, Hfdo, Hfm, Hxs, Hg⟩
      · iframe; iframe #
      icases Hg with (%Hg | ⟨%Hge, #Hek⟩)
      · obtain ⟨rfl, rfl⟩ := Hg
        try wp_auto
        ileft
        isplitr
        · ipureintro; rfl
        iexists m, xs, C
        ihave #HrcC := fileRcpt_get _ C hC.1 hC.2.1 $$ Hrcf
        iframe HrcC
        iframe
        ipureintro
        exact ⟨hmaps, hxl, hsz, hC, hBm⟩
      · have hk : Ek := hFs Hge.2
        cases gerr with
        | nil => exact absurd rfl Hge.1
        | ok ei =>
        try wp_auto
        iunfold dbPathLk at path
        icases path with ⟨path, Htok, -⟩
        wp_apply hclose dbl (.ok li) (DFrac.own 1) GoInterface.nil _ _ none p f Hdbnn $$
          [readOnly opened freelist writeAt path Hmf datasz file Hf Hfdo Htok] as %cerr ⟨readOnly, -⟩
        · iframe; iframe #
          isplitr
          · unfold closeMapRes; iempintro
          iright; iexists fd, p.path, _; iframe; iapply dbFd_lockToks $$ Htok
        open_exit_j fmtVerbs_psErr [interface.mkOk go.string #(p.path), GoInterface.ok ei]
    · -- a new file, or one an interrupted `init` left (`initPartial`): `init`; a well-formed
      -- one holds no data (`openOK_initPartial`)
      have hD : D = ∅ := by
        rcases hbr with h | ⟨C, hC⟩
        · exact h.2
        · rcases hzi rfl with h | h
          · have := openOK_size C D m xs hC; omega
          · exact openOK_initPartial C D m xs hC hxl h
      subst hD
      have hm16 : m.size ≤ 16384 := by
        rcases hzi rfl with h | h
        · omega
        · have := h.1; rw [List.length_map] at this; omega
      try wp_auto
      ipersist pageSize
      wp_apply hInit dbl f fd p (.ok li) m xs (DFrac.own 1) (DFrac.own 1) Hdbnn hm16 hxl hmaps $$
        [writeAt file Hf Hfdo Hfm Hxs] as %ierr ⟨writeAt, file, Hf, Hfdo, Hir⟩
      · iframe; iframe #
      icases Hir with (⟨%Hie, %m', %xs', Hfm, Hxs, %Hx'⟩ | ⟨%Hie2, #Hek, %m', Hfm⟩)
      · subst Hie
        try wp_auto
        ileft
        isplitr
        · ipureintro; rfl
        iexists m', xs', initC
        obtain ⟨hm1, hm2, hm3⟩ := Hx'
        have hl : xs'.length = 16384 := by rw [← List.length_map Prod.fst, hm3, initImg_length]
        ihave #Hrci : ⧖ initC.txid $$ []
        · iapply (preceipt_mono (GF := GF) (show initC.txid ≤ 0 + 1 by simp [initC])) $$ Hrc1
        iframe Hrci
        iframe; iframe #
        ipureintro
        exact ⟨hm1, hm2, ⟨by omega, by omega⟩, openOK_init m' xs' hm3 hm2, Or.inr (by omega)⟩
      · have hk : Ek := hFs Hie2.2
        cases ierr with
        | nil => exact absurd rfl Hie2.1
        | ok ei =>
        try wp_auto
        iunfold dbPathLk at path
        icases path with ⟨path, Htok, -⟩
        wp_apply hclose dbl (.ok li) (DFrac.own 1) GoInterface.nil _ _ none p f Hdbnn $$
          [readOnly opened freelist writeAt path Hmf datasz file Hf Hfdo Htok] as %cerr ⟨readOnly, -⟩
        · iframe; iframe #
          isplitr
          · unfold closeMapRes; iempintro
          iright; iexists fd, p.path, _; iframe; iapply dbFd_lockToks $$ Htok
        open_exit_j fmtVerbs_initErr [interface.mkOk go.string #(p.path), GoInterface.ok ei]
  iintro (⟨%Hv, %m', %xs', %C, Hfm, Hxs, %HC, #HrcC, file, ⟨%dqp, pageSize⟩, writeAt, Hf, Hfdo, readOnly,
    opened, freelist, path, Hmf, datasz, err, db, Hdefer⟩ | ⟨%e, %He, err, #Hek, db, Hdefer⟩)
  rotate_left
  · obtain ⟨rfl, hne, hk⟩ := He
    try wp_auto
    wp_bind (App (Val #dv) (Val #()))
    iapply Hdef $$ [err]
    · iexact err
    · iexact Hek
    iintro err
    try wp_auto
    iapply HΦ
    iframe Hopts HW
    iexists V'
    iframe Ht
    iright; ipureintro; exact ⟨hne, hk⟩
  subst Hv
  ipersist pageSize
  ipersist NoSync
  try wp_auto
  -- `if !db.readOnly && !db.NoSync { fdatasync(db) }` (bbolt `c5a6065`, moved before the mapping
  -- by `2f6fcff`): the whole file synced, its bytes with it (`fdatasync.specS`); on an error,
  -- `db.close()` (no lock or mapping is held yet)
  obtain ⟨hmaps', hxl', hsz', hC, hBm'⟩ := HC
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗
      ∃ (m2 : OsMeta) (xs2 : List ByteG),
        osMeta p.ino (DFrac.own 1) m2 ∗ osBytes p.ino 0 (DFrac.own 1) xs2 ∗
        ⌜m2.maps = ∅ ∧ xs2.length = m2.size ∧ (m2.size < 2 ^ 62 ∧ m2.size % 4096 = 0) ∧
          openOK C D m2 xs2 ∧ (Ek ∨ m2.size ≤ 0xFFFFFFFFFFFF) ∧
          (nos = false → m2 = m'.synced ∧ xs2 = xs'.map (fun x => durB x.1))⌝ ∗
        dbl.[DB, go!"file"] ↦ f ∗
        (dbl.[DB, go!"ops"]).[dbOps, go!"writeAt"] ↦
          methods (go.GoType.PointerType os.File.ty) go!"WriteAt" #f ∗
        fileOwn f fd p.path (DFrac.own 1) ∗ osFd fd (DFrac.own 1) (dbFd p.ino) ∗
        dbl.[DB, go!"readOnly"] ↦ false ∗ dbl.[DB, go!"opened"] ↦ true ∗
        dbl.[DB, go!"freelist"] ↦ GoInterface.nil ∗ dbPathLk dbl p fd ∗
        mapFields dbl (DFrac.own 1) none ∗ dbl.[DB, go!"datasz"] ↦ W64 0 ∗
        err_ptr ↦ GoInterface.nil ∗ db_ptr ↦ dbl ∗ defer ↦ dv) ∨
    (∃ e : GoInterface, ⌜v = returnVal #() ∧ e ≠ GoInterface.nil ∧ Ek⌝ ∗ err_ptr ↦ e ∗
      fmtErrorOkOrNil e ∗ db_ptr ↦ null ∗ defer ↦ dv)))
    at next with [Hfm Hxs file writeAt Hf Hfdo readOnly opened freelist path Hmf datasz err db
      Hdefer]
  · try wp_auto
    cases nos
    · -- `NoSync` false: the sync
      try wp_auto
      wp_apply hFds dbl f fd p p.ino m' xs' (DFrac.own 1) (DFrac.own 1)
        (OsMeta.covers_whole m' hxl') $$ [file Hf Hfdo Hfm Hxs]
        as %serr ⟨file, Hf, Hfdo, Hsr⟩
      · iframe file Hf Hfdo Hfm Hxs; iframe #
      icases Hsr with (⟨%Hse, Hfm, Hxs⟩ | ⟨%Hse, #Hek, Hfm, Hxs⟩)
      · subst Hse
        try wp_auto
        ileft
        isplitr
        · ipureintro; rfl
        iexists m'.synced, xs'.map (fun x => durB x.1)
        iframe Hfm Hxs file writeAt Hf Hfdo readOnly opened freelist path Hmf datasz err db Hdefer
        ipureintro
        refine ⟨hmaps', by simp only [List.length_map]; exact hxl', hsz', openOK_synced C D m' xs' hC,
          hBm', fun _ => ⟨rfl, rfl⟩⟩
      · have hk : Ek := hFs Hse.2
        cases serr with
        | nil => exact absurd rfl Hse.1
        | ok ei =>
        try wp_auto
        iunfold dbPathLk at path
        icases path with ⟨path, Htok, -⟩
        wp_apply hclose dbl (.ok li) (DFrac.own 1) GoInterface.nil _ _ none p f Hdbnn $$
          [readOnly opened freelist writeAt path Hmf datasz file Hf Hfdo Htok] as %cerr ⟨readOnly, -⟩
        · iframe; iframe #
          isplitr
          · unfold closeMapRes; iempintro
          iright; iexists fd, p.path, _; iframe; iapply dbFd_lockToks $$ Htok
        open_exit_j fmtVerbs_syncErr [interface.mkOk go.string #(p.path), GoInterface.ok ei]
    · -- `NoSync` true: no sync
      try wp_auto
      ileft
      isplitr
      · ipureintro; rfl
      iexists m', xs'
      iframe Hfm Hxs file writeAt Hf Hfdo readOnly opened freelist path Hmf datasz err db Hdefer
      ipureintro
      exact ⟨hmaps', hxl', hsz', hC, hBm', fun h => nomatch h⟩
  -- **the file synced** (unless `NoSync`): `Hfm`/`Hxs` the whole file, with `hsync` (`m'.synced`,
  -- every byte `durB`, when `nos = false`); nothing has carved it yet (W1 allocates its crash
  -- invariant here)
  iintro (⟨%Hv, %m', %xs', Hfm, Hxs, %HC, file, writeAt, Hf, Hfdo, readOnly, opened, freelist,
    path, Hmf, datasz, err, db, Hdefer⟩ | ⟨%e, %He, err, #Hek, db, Hdefer⟩)
  rotate_left
  · obtain ⟨rfl, hne, hk⟩ := He
    try wp_auto
    wp_bind (App (Val #dv) (Val #()))
    iapply Hdef $$ [err]
    · iexact err
    · iexact Hek
    iintro err
    try wp_auto
    iapply HΦ
    iframe Hopts HW
    iexists V'
    iframe Ht
    iright; ipureintro; exact ⟨hne, hk⟩
  subst Hv
  obtain ⟨hmaps', hxl', hsz', hC, hBm', hsync⟩ := HC
  try wp_auto
  rw [recv_eq_func_mk BAnon BAnon]
  try wp_auto
  -- the mapping
  icases (optsAt_int_rd opts dq o go!"InitialMmapSize" (by decide)) $$ Hopts with
    ⟨%dqx, %minsz, Hx, Hback⟩
  icases persistent_entails_left (hWms dqx minsz) $$ [HW Hx] with ⟨⟨HW, Hx⟩, %hms⟩
  · iframe
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
  wp_apply hMmap dbl f fd p (.ok li) o.mmapFlags _ (DFrac.own 1) m' xs' minsz Hdbnn hmaps' hxl'
    (by omega) hmf' (fun _ => openOK_meta C D m' xs' hC) $$
    [MaxSize rwtx file Hf Hfdo Hfm Hxs Hmf datasz] as %merr ⟨Hfix, file, Hf, Hfdo, Hxs, Hmr⟩
  · unfold mmapOwnFix; iframe; iframe #
  unfold mmapOwnFix
  icases Hfix with ⟨-, -, -, MaxSize, -, -, rwtx⟩
  icases Hmr with (⟨%Hme, %base, %L, %HL, Hmf, datasz, Hfm, Hbp, %vf, Hcells⟩ |
    ⟨%Hme, #Hek, Hmf, datasz, %m'', Hfm⟩)
  rotate_left
  · have hk : Ek := by
      rcases Hme.2 with h | h | h
      · exact hFs h
      · have := openOK_size C D m' xs' hC; omega
      · rcases hBm' with h1 | h1
        · exact h1
        rcases hms with h2 | h2
        · exact h2
        exfalso
        have h3 := mmapSizeOf_none_gt _ h
        have e2 : sint.nat minsz = (sint.Z minsz).toNat := rfl
        omega
    cases merr with
    | nil => exact absurd rfl Hme.1
    | ok ei =>
    try wp_auto
    iunfold dbPathLk at path
    icases path with ⟨path, Htok, -⟩
    wp_apply hclose dbl (.ok li) (DFrac.own 1) GoInterface.nil _ _ none p f Hdbnn $$
      [readOnly opened freelist writeAt path Hmf datasz file Hf Hfdo Htok] as %cerr ⟨readOnly, -⟩
    · iframe; iframe #
      isplitr
      · unfold closeMapRes; iempintro
      iright; iexists fd, p.path, _; iframe; iapply dbFd_lockToks $$ Htok
    open_exit fmtVerbs_mapErr [interface.mkOk go.string #(p.path), GoInterface.ok ei]
  subst Hme
  try wp_auto
  -- the database's fixed fields
  ipersist stats
  ipersist readOnly
  ipersist StrictMode
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
  ihave #HNFS : dbl.[DB, go!"NoFreelistSync"] ↦□ true $$ []
  · rw [← hnfs]; iexact NoFreelistSync
  ihave #Hfix : dbFixed (GF := GF) γbq N dbl sp $$ []
  · unfold dbFixed dbLogger
    iframe #
    isplitr
    · ipureintro; exact hmf'
    ipureintro; exact Hlgty
  iclear HNFS
  -- the file's mode (W1, `Open/Mode`): crash mode iff `NoSync` and `NoGrowSync` are off and the
  -- file system does not fail; the file's bytes as bbolt's invariants hold them
  ihave #Hngs0 : (∃ b : Bool, dbl.[DB, go!"NoGrowSync"] ↦□ b) $$ []
  · iexists _; iexact NoGrowSync
  icases Hngs0 with ⟨%ngs, #Hngs⟩
  iapply wp_open_mode _ _ _ _ rfl γbq N dbl p fd C { m' with maps := GMap.singleton base L } xs'
    nos ngs hxl' (fun hfs hnos hngs => by
      obtain ⟨hms, hxss⟩ := hsync hnos
      have hone : XsOne m' := by rw [hms]; exact xsOne_synced _
      have hdur : ∀ y ∈ xs', y = durB y.1 := by
        rw [hxss]; intro y hy; obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy; rfl
      refine ⟨by show m'.dhi ≤ m'.dlo; rw [hms]; exact Nat.le_refl _, hdur,
        fun l hl x hx => hone l hl x hx, ?_⟩
      exact open_bDur C D m' _ xs' hC rfl hxl' HL.2.2.2.1 hdur
        (by show m'.lo = m'.size; rw [hms]; rfl) (by show m'.hi = m'.size; rw [hms]; rfl)
        (by show m'.xs = some [m'.size]; rw [hms]; rfl) hsz'.2)
  iframe NoSync Hngs path Hfm Hxs HrcC
  iintro %cs %gcn %m'' %Hm'' #Hmode Hseed path Hfm Hxs
  -- the freelist, the core and the writer phase (`DB.loadFreelist.spec_open`)
  wp_apply hLoad γbq gcn N dbl sp f fd { p with cs := cs } C base L m'' xs'
    (lfOK_congr (openOK_lfOK N dbl C D m' xs' base L hC hxl' hsz' HL.2.1 HL.2.2.2.2 HN Hdbnn)
      Hm''.1 Hm''.2) hfd0 $$
    [metalock mmaplock statlock opened freelist writeAt rwtx file path datasz Hmf Hfm Hf Hfdo Hps
      Hxs Hbp Hcells freelistLoad Hbq Hseed HrcC Hmode] as Hlf
  · unfold lfPre
    rw [← hxl']
    iframe; iframe #
    done
  iunfold lfPost at Hlf
  icases Hlf with ⟨%B, %fl, %fli, #Hcore, #Hpl, Hw, Hst, Hflo, Hsp, Hcls, Hstate, Hopn, Hclo, ⟨%Hwok, %HBbq⟩⟩
  subst HBbq
  have hCD : treeData C = D := hC.2.2.2.2.2.2.2
  -- the writer side `W`: `loadFreelist`'s, or with the file's metadata after the sync below
  have hWC : (lfW C base L m'' xs' f fd fl fli).C = C := rfl
  have hWms : (lfW C base L m'' xs' f fd fl fli).ms = some (base, L) := rfl
  have hWfl : (lfW C base L m'' xs' f fd fl fli).fl = fl := rfl
  have hWfli : (lfW C base L m'' xs' f fd fl fli).fli = fli := rfl
  generalize lfW C base L m'' xs' f fd fl fli = W
    at Hwok hWC hWms hWfl hWfli ⊢
  try wp_auto
  -- the writer side `W`
  try wp_auto
  cases nfs
  · exact absurd hnfs (by decide)
  · -- `NoFreelistSync` (`Open.spec`'s options): done, no `hasSyncedFreelist()` call
    have hOW := open_writer (GF := GF) ⊤ B N dbl { p with cs := cs } sp _ Hwok
    rw [hWC, hWfl, hWfli] at hOW
    imod hOW $$ [Hcore Hpl rwlock Hw Hst Hflo Hsp Hcls Hopn] with #Hbolt
    · iframe; iframe #
    open_ok

/-! ## The shared mode's open, and `Open.spec` (session S3f: the one spec of `Open`) -/

section canon
variable [go.BasicIntoValInj] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]

/-- The name holds no directory. -/
private theorem nameHolds_notDir (h : NamesH) (b : GoString) (D : Data) :
    nameHolds (GF := GF) h b D ⊢ nameHolds h b D ∗ ⌜∀ J, h.cur !! b ≠ some (.dir J)⌝ := by
  unfold nameHolds
  iintro (⟨%i, %hi, H⟩ | %hn)
  · isplitl
    · ileft; iexists i; iframe H; ipureintro; exact hi
    · ipureintro; intro J hJ; rw [hi] at hJ; cases hJ
  · isplitl
    · iright; ipureintro; exact hn
    · ipureintro; intro J hJ; rw [hn.1] at hJ; cases hJ

/-- **The mappable file the open left at the name, opened** (the existing file holding `D`, or the
created one, empty). -/
private theorem nameHolds_opened (j : Ino) (h : NamesH) (b : GoString) (D : Data)
    (o : Option (Nat × Nat × Ino)) (i : Ino) (hcr : crIno b h o i) :
    nameHolds (GF := GF) h b D ∗ crOut j b h (DFrac.own 1) o ∗ crMeta o ⊢
      crOut j b h (DFrac.own 1) o ∗ openedF i D (· ≤ 0xFFFFFFFFFFFF) := by
  unfold nameHolds
  cases o with
  | none =>
    dsimp only [crIno] at hcr
    dsimp only [crMeta]
    iintro ⟨(⟨%i0, %hi0, Hf⟩ | %hn), Ho, -⟩
    · rw [hcr] at hi0; cases hi0
      iframe Ho
      unfold fileHoldsM
      iapply fileHoldsM_opened $$ Hf
    · rw [hcr] at hn; exact absurd hn.1 (by simp)
  | some xsi =>
    obtain ⟨x, s, i1⟩ := xsi
    dsimp only [crIno] at hcr
    subst hcr
    dsimp only [crMeta, crOut]
    iintro ⟨(⟨%i0, %hi0, -⟩ | %hn), ⟨%hh, Hl, Hn⟩, Hm⟩
    · rw [hh.1] at hi0; cases hi0
    · obtain ⟨-, rfl⟩ := hn
      iframe Hl Hn
      isplitr
      · ipureintro; exact hh
      iapply new_opened _ (· ≤ 0xFFFFFFFFFFFF) (Nat.zero_le _) $$ Hm

/-- `O_RDWR|O_CREATE` with `O_CLOEXEC` is a valid create, without `O_TRUNC`. -/
private theorem boltOpenFlag_create :
    OpenFlagsOk (W64 0x42 ||| W64 0x80000).toNat ∧ (W64 0x42 ||| W64 0x80000).toNat / O_CREAT % 2 = 1 ∧
      (W64 0x42 ||| W64 0x80000).toNat / O_TRUNC % 2 = 0 := by
  unfold OpenFlagsOk O_CREAT O_TRUNC O_CLOEXEC
  decide

private theorem boltOpenFd (i : Ino) :
    openFd i (W64 0x42 ||| W64 0x80000) = ⟨i, true, true, none, none⟩ := by
  have h1 : (W64 0x42 ||| W64 0x80000).toNat % 4 = 2 := by decide
  simp only [openFd, h1, O_WRONLY, O_RDONLY]; rfl

/-- **The shared mode's open of the database file** as `openFileDb.spec` at
`Ek := ¬ FsNoErr ∨ ¬ PathFits (child d b)`: `os.OpenFile.specCreateS` (an error carries it); the claim's halves, the trivial update, the outcome's claim back
whole; the file the open left at the name, mappable. -/
private theorem openFileDb_shared
    (hCS : os.OpenFile.specCreateS (GF := GF) (hG := hG))
    (R : Roots) (d b : GoString) (dq : DFrac) (j : Ino) (qc : Qp) (h : NamesH) (perm : w32)
    (D : Data) (hb : NameOk b) :
    openFileDb.spec (GF := GF) (hG := hG) (¬ FsNoErr ∨ ¬ PathFits (child d b)) (· ≤ 0xFFFFFFFFFFFF)
      iprop(isPkgInit (PROP := IProp GF) pkg_id.os ∗ osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗
        osNames j (.only [b]) (DFrac.own 1) h ∗ nameHolds h b D)
      (fun oc : Option (Nat × Nat × Ino) =>
        iprop(osPathS (GF := GF) R d dq j ∗ osCallPerm (callKey R d) qc ∗ crOut j b h (DFrac.own 1) oc))
      (fun oc i => crIno b h oc i) (child d b) perm D := by
  iintro %Φ ⟨#Hos, #Hospkg, #Hsi, Hp, Hperm, Hn, Hnh⟩ HΦ
  obtain ⟨hfl, hcr, htr⟩ := boltOpenFlag_create
  icases nameHolds_notDir h b D $$ Hnh with ⟨Hnh, %hnd⟩
  icases (osNames_join j _ _ _ h (Qp.half_add_half 1)).2 $$ Hn with ⟨Hn, Hr⟩
  ihave Hau := os.osAU_triv (A := Option (Nat × Nat × Ino))
    (osNames (GF := GF) j (.only [b]) (DFrac.own (1 : Qp).half) h)
    (crOut j b h (DFrac.own (1 : Qp).half)) $$ Hr
  wp_apply hCS d b (W64 0x42) perm R j dq h (1 : Qp).half (1 : Qp).half qc
    (crOut j b h (DFrac.own (1 : Qp).half)) hfl hcr htr hb hnd (Qp.half_add_half 1)
    $$ [$Hospkg $Hos $Hsi $Hp $Hperm $Hn $Hau]
    as %f %err ⟨Hp, Hperm, %oc, Ho1, Ho2, Hm, Hr⟩
  ihave Ho := os.crOut_join j b h oc $$ [$Ho1 $Ho2]
  iapply HΦ
  iexists oc
  dsimp only
  icases Hr with (⟨%fd, %i, %hres, Hf, -, Hfd⟩ | ⟨%herr, #Hok⟩)
  · obtain ⟨rfl, hfd, hi⟩ := hres
    icases nameHolds_opened j h b D oc i hi $$ [$Hnh $Ho $Hm] with ⟨Ho, Hop⟩
    iframe Hp Hperm Ho
    isplitl [Hf Hfd Hop]
    · ileft
      iexists fd, i
      iframe Hf Hop
      isplitr
      · ipureintro; exact ⟨rfl, hfd, hi⟩
      rw [boltOpenFd] at *
      iexact Hfd
    · iapply fmtErrorOkOrNil_nil
  · iframe Hp Hperm Ho Hok
    iright; ipureintro; exact herr

/-- Half of a discardable fraction (`dfHalf dq • dfHalf dq = dq`). -/
private def dfHalf : DFrac → DFrac
  | .own q => .own q.half
  | .discard => .discard
  | .ownDiscard q => .ownDiscard q.half

private theorem dfHalf_op (dq : DFrac) : dfHalf dq • dfHalf dq = dq := by
  cases dq with
  | own q => show DFrac.own (q.half + q.half) = _; rw [Qp.half_add_half]
  | discard => rfl
  | ownDiscard q => show DFrac.ownDiscard (q.half + q.half) = _; rw [Qp.half_add_half]

private theorem pt_join_half (l : Loc) (v : go_etcd_io.bbolt.Options) (dq : DFrac) :
    (l ↦{dfHalf dq} v : IProp GF) ∗ l ↦{dfHalf dq} v ⊢ l ↦{dq} v := by
  have h := (typedPointsto_dfractional (GF := GF) l v).dfractional (dfHalf dq) (dfHalf dq)
  rw [dfHalf_op] at h
  exact h.2

private theorem pt_split_half (l : Loc) (v : go_etcd_io.bbolt.Options) (dq : DFrac) :
    (l ↦{dq} v : IProp GF) ⊢ l ↦{dfHalf dq} v ∗ l ↦{dfHalf dq} v := by
  have h := (typedPointsto_dfractional (GF := GF) l v).dfractional (dfHalf dq) (dfHalf dq)
  rw [dfHalf_op] at h
  exact h.1

private theorem optsAt_intro' (l : Loc) (dq : DFrac) (o : OptsM) (v : go_etcd_io.bbolt.Options)
    (h : optsVal v o) : (l ↦{dq} v : IProp GF) ⊢ optsAt l dq o := by
  unfold optsAt; iintro H; iexists v; iframe H; ipureintro; exact h

private theorem optsAt_elim' (l : Loc) (dq : DFrac) (o : OptsM) :
    optsAt (GF := GF) l dq o ⊢ ∃ v : go_etcd_io.bbolt.Options, l ↦{dq} v := by
  unfold optsAt; iintro ⟨%v, H, -⟩; iexists v; iexact H

private theorem optsAtNoErr_intro' (l : Loc) (dq : DFrac) (o : OptsM) (v : go_etcd_io.bbolt.Options)
    (h : optsVal v o ∧ optsNoErr v) : (l ↦{dq} v : IProp GF) ⊢ optsAtNoErr l dq o := by
  unfold optsAtNoErr; iintro H; iexists v; iframe H; ipureintro; exact h

private theorem optsAtNoErr_elim' (l : Loc) (dq : DFrac) (o : OptsM) :
    optsAtNoErr (GF := GF) l dq o ⊢
      ∃ v : go_etcd_io.bbolt.Options, l ↦{dq} v ∗ ⌜optsVal v o ∧ optsNoErr v⌝ := by
  unfold optsAtNoErr; exact .rfl

/-- The witness half of the options agrees with a field `Open` reads: `Timeout`. -/
private theorem optsW_timeout (Ek : Prop) (opts : Loc) (dq : DFrac) (v : go_etcd_io.bbolt.Options)
    (hv : optsNoErr v) (dqx : DFrac) (x : time.Duration) :
    (opts ↦{dq} v : IProp GF) ∗ opts.[Options, go!"Timeout"] ↦{dqx} x ⊢ ⌜Ek ∨ x = W64 0⌝ := by
  iintro ⟨Hv, Hx⟩
  icases (optsPt_eq opts v dq).1 $$ Hv with ⟨⟨H1, -⟩, -⟩
  ihave %h := typedPointsto_agree_wand _ _ _ _ _ $$ H1 Hx
  ipureintro; right; rw [← h]; exact hv.1

private theorem optsW_nfs (Ek : Prop) (opts : Loc) (dq : DFrac) (v : go_etcd_io.bbolt.Options)
    (hv : optsNoErr v) (dqx : DFrac) (x : Bool) :
    (opts ↦{dq} v : IProp GF) ∗ opts.[Options, go!"NoFreelistSync"] ↦{dqx} x ⊢
      ⌜x = true⌝ := by
  iintro ⟨Hv, Hx⟩
  icases (optsPt_eq opts v dq).1 $$ Hv with ⟨⟨-, -, H3, -⟩, -⟩
  ihave %h := typedPointsto_agree_wand _ _ _ _ _ $$ H3 Hx
  ipureintro; rw [← h]; exact hv.2.1

private theorem optsW_mmap (Ek : Prop) (opts : Loc) (dq : DFrac) (v : go_etcd_io.bbolt.Options)
    (hv : optsNoErr v) (dqx : DFrac) (x : w64) :
    (opts ↦{dq} v : IProp GF) ∗ opts.[Options, go!"InitialMmapSize"] ↦{dqx} x ⊢
      ⌜Ek ∨ sint.Z x ≤ 0xFFFFFFFFFFFF⌝ := by
  iintro ⟨Hv, Hx⟩
  icases (optsPt_eq opts v dq).1 $$ Hv with ⟨⟨-, -, -, -, -, -, -, H8, -⟩, -⟩
  ihave %h := typedPointsto_agree_wand _ _ _ _ _ $$ H8 Hx
  ipureintro; right; rw [← h]; exact hv.2.2

omit [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] in
set_option maxHeartbeats 4000000 in
/-- **`Open.spec`**: `Open.wp_proofG` at `Ek := ¬ FsNoErr ∨ ¬ PathFits (child d b)` (every callee's
error arm witnesses `¬ FsNoErr`, the open's either),
the file mappable (`nameHolds`), the options' witness half of `optsAtNoErr`'s points-to. -/
theorem Open.wp_proof [sync.Assumptions]
    (hCS : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt],
      os.OpenFile.specCreateS (GF := GF) (hG := hG))
    (hName : os.File.Name.spec (GF := GF) (hG := hG))
    (hFlock : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], flock.spec (GF := GF) (hG := hG))
    (hStat : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], os.File.Stat.spec (GF := GF) (hG := hG))
    (hSize : os.fileStat.Size.spec (GF := GF) (hG := hG))
    (hNI : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.needsInit.spec (GF := GF) (hG := hG))
    (hInit : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.init.spec (GF := GF) (hG := hG))
    (hGPS : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.getPageSize.spec_own (GF := GF) (hG := hG))
    (hMmap : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.mmapUnlocked.spec_own (GF := GF) (hG := hG))
    (hLoad : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.loadFreelist.spec_open (GF := GF) (hG := hG))
    (hSync : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.hasSyncedFreelist.spec (GF := GF) (hG := hG))
    (hFds : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], fdatasync.specS (GF := GF) (hG := hG))
    (hBegin : DB.Begin.spec (GF := GF) (hG := hG))
    (hCommit : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], Tx.Commit_err.spec (GF := GF) (hG := hG))
    (hClose : DB.Close.specTok (GF := GF) (hG := hG))
    (hclose : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], DB.close.spec_owned (GF := GF) (hG := hG))
    (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hOptStr : Options.String.spec (GF := GF) (hG := hG))
    (hModeStr : fs.FileMode.String.spec (GF := GF) (hG := hG)) :
    Open.spec (GF := GF) (hG := hG) := by
  intro _ _ _ _ _ N R d b dq j qc h mode opts dqo o D hb
  iintro %Φ ⟨#Hpkg, #Hos, %HN, #Hsi, Hp, Hperm, Hn, Hnh, Hopts, %Hok, Hlgr⟩ HΦ
  icases optsAtNoErr_elim' opts dqo o $$ Hopts with ⟨%v, Hv, %hv⟩
  icases pt_split_half opts v dqo $$ Hv with ⟨Hv1, Hv2⟩
  iapply Open.wp_proofG hName hFlock hStat hSize hNI hInit hGPS hMmap hLoad hSync hFds hBegin
    hCommit hClose hclose hLogger hOptStr hModeStr _ _ _ N (child d b) mode opts (dfHalf dqo) o D
    (¬ FsNoErr ∨ ¬ PathFits (child d b)) (· ≤ 0xFFFFFFFFFFFF) (opts ↦{dfHalf dqo} v) Or.inl
    (fun _ hn => Or.inr hn)
    (optsW_timeout _ opts (dfHalf dqo) v hv.2)
    (optsW_nfs (¬ FsNoErr ∨ ¬ PathFits (child d b)) opts (dfHalf dqo) v hv.2)
    (optsW_mmap _ opts (dfHalf dqo) v hv.2)
    (openFileDb_shared hCS R d b dq j qc h mode D hb) $$ [Hp Hperm Hn Hnh Hv1 Hv2 Hlgr]
  · iframe; iframe #
    isplitr
    · ipureintro; exact HN
    isplitr
    · iPkgInit
    isplitl [Hv1]
    · iapply optsAt_intro' opts (dfHalf dqo) o v hv.1 $$ Hv1
    ipureintro; exact Hok
  inext
  iintro %db %err ⟨Hopts, Hv2, %oc, ⟨Hp, Hperm, Ho⟩, Hr⟩
  icases optsAt_elim' opts (dfHalf dqo) o $$ Hopts with ⟨%v', Hv1⟩
  ihave %hvv := typedPointsto_agree_wand _ _ _ _ _ $$ Hv1 Hv2
  subst hvv
  iapply HΦ
  iframe Hp Hperm
  isplitl [Hv1 Hv2]
  · iapply optsAtNoErr_intro' opts dqo o v' hv
    iapply pt_join_half opts v' dqo $$ [Hv1 Hv2]
    iframe
  iexists oc
  iframe Ho Hr

end canon

end proof

end bbolt
end EtcdGrove
end Perennial
