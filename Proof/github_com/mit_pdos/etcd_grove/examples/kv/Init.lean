/- Lean-first (no Rocq counterpart).

# The store's package initialization (2026-10-19)

`kv.wp_initialize'`: running the package's `initialize'` from `ownInitializing` initializes its
imports (`proto`, `encoding/binary`, `raftpb`, raft, `time`, `sync`, `context`, lintest,
`primitive`, porcupine, in the translation's order) and then the package (no package-level
variable), and gives its `isPkgInit` with `context`'s `isClosedchanInit`, which `Main.spec`
takes.

`isClosedchanInit` (`closedchan` closed, an invariant) is not part of `context`'s `isPkgInit`
and Perennial's `context.wp_initialize'` drops it, so it must come from `context`'s first
initialization, `context_wp_initialize'_closedchan` (`Proof/github_com/anishathalye/porcupine/
Init.lean`), at a table whose entry for `context` carries it. Here the first package to
initialize `context` is raft (the store's initializer runs `proto`'s, `binary`'s, `raftpb`'s,
then raft's, which imports `context`), and raft's `wp_initialize'`
(`Proof/go_etcd_io/raft/v3/Init.lean`) takes `GetIsPkgInitProp raft`, whose entry for `context`
is its bare `isPkgInit`. So this file proves raft's initialization again,
`go_etcd_io.raft.v3.wp_initialize'_closedchan`: the same proof, at a table (`CCInitTable`)
whose entry for `context` carries `isClosedchanInit`, running `context_wp_initialize'_closedchan`
in place of Perennial's. (The clean fix is Perennial's, as porcupine's `Init.lean` says:
`context`'s `isPkgInit` including `isClosedchanInit`.)

The store's table (`KVInitTable`): the entries of the store, lintest, porcupine and `context`
(the packages that import `context`, but raft) carry `isClosedchanInit`; raft's and every other
package's are their `isPkgInit`.

The premises are raft's (`Proof/go_etcd_io/raft/v3/Init.lean`): the method-set facts
`context.ErrorStringIsError`, `context.DeadlineExceededIsError` and the model of `log.New`,
`log.NewModel`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Base
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Init
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace go_etcd_io.raft.v3

section raft_init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [context.ErrorStringIsError] [context.DeadlineExceededIsError] [log.NewModel]

/-- What raft's initialization needs of `get_is_pkg_init` when `context`'s entry carries
`isClosedchanInit` (see the file header): raft's entry is its `isPkgInit`, `context`'s is
`isPkgInit context ∗ isClosedchanInit`, every other package raft (or `context`) imports has its
`GetIsPkgInitProp`. -/
structure CCInitTable (get_is_pkg_init : GoString → IProp GF) : Prop where
  self : get_is_pkg_init pkg_id.go_etcd_io.raft.v3 =
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3
  context : get_is_pkg_init pkg_id.context =
    iprop(isPkgInit (PROP := IProp GF) pkg_id.context ∗ context.isClosedchanInit)
  errors : GetIsPkgInitProp pkg_id.errors get_is_pkg_init
  proto : GetIsPkgInitProp pkg_id.google_golang_org.protobuf.proto get_is_pkg_init
  raftpb : GetIsPkgInitProp pkg_id.go_etcd_io.raft.v3.raftpb get_is_pkg_init
  fmt : GetIsPkgInitProp pkg_id.fmt get_is_pkg_init
  io : GetIsPkgInitProp pkg_id.io get_is_pkg_init
  log : GetIsPkgInitProp pkg_id.log get_is_pkg_init
  os : GetIsPkgInitProp pkg_id.os get_is_pkg_init
  sync : GetIsPkgInitProp pkg_id.sync get_is_pkg_init
  bytes : GetIsPkgInitProp pkg_id.bytes get_is_pkg_init
  rand : GetIsPkgInitProp pkg_id.crypto.rand get_is_pkg_init
  math : GetIsPkgInitProp pkg_id.math get_is_pkg_init
  big : GetIsPkgInitProp pkg_id.math.big get_is_pkg_init
  slices : GetIsPkgInitProp pkg_id.slices get_is_pkg_init
  strings : GetIsPkgInitProp pkg_id.strings get_is_pkg_init
  confchange : GetIsPkgInitProp pkg_id.go_etcd_io.raft.v3.confchange get_is_pkg_init
  quorum : GetIsPkgInitProp pkg_id.go_etcd_io.raft.v3.quorum get_is_pkg_init
  tracker : GetIsPkgInitProp pkg_id.go_etcd_io.raft.v3.tracker get_is_pkg_init
  binary : GetIsPkgInitProp pkg_id.encoding.binary get_is_pkg_init
  atomic : GetIsPkgInitProp pkg_id.sync.atomic get_is_pkg_init
  time : GetIsPkgInitProp pkg_id.time get_is_pkg_init

/-- Raft's initialization at a table whose entry for `context` carries `isClosedchanInit`
(see the file header): the proof of `wp_initialize'` (`Proof/go_etcd_io/raft/v3/Init.lean`),
with `context`'s initialization by `context_wp_initialize'_closedchan`. -/
theorem wp_initialize'_closedchan (get_is_pkg_init : GoString → IProp GF)
    (Ht : CCInitTable get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Ht.self) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoArray Bool 23) isResponseMsg _ as HisResp
  wp_apply wp_GlobalAlloc (V := GoArray Bool 23) isLocalMsg _ as HisLocal
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrSnapshotTemporarilyUnavailable go.error as HESU
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrUnavailable go.error as HEU
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrSnapOutOfDate go.error as _
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrCompacted go.error as HEC
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrStepPeerNotFound go.error as HESP
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrStepLocalMsg go.error as HESL
  wp_apply wp_GlobalAlloc (V := GoInterface) errBreak go.error as HEB
  wp_apply wp_GlobalAlloc (V := GoArray GoString 4) stmap _ as _
  wp_apply wp_GlobalAlloc (V := Loc) globalRand _ as HGR
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrProposalDropped go.error as HEPD
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrStopped go.error as HES
  wp_apply wp_GlobalAlloc (V := Loc) emptyState _ as HEmpty
  wp_apply wp_GlobalAlloc (V := GoInterface) raftLogger Logger.ty as _
  wp_apply wp_GlobalAlloc (V := sync.Mutex) raftLoggerMu _ as _
  wp_apply wp_GlobalAlloc (V := Loc) discardLogger _ as _
  wp_apply wp_GlobalAlloc (V := Loc) defaultLogger _ as _
  wp_apply encoding.binary.wp_initialize' _ Ht.binary $$ Hown as ⟨Hown, #Hd18⟩
  wp_apply go_etcd_io.raft.v3.tracker.wp_initialize' _ Ht.tracker $$ Hown as ⟨Hown, #Hd17⟩
  wp_apply go_etcd_io.raft.v3.quorum.wp_initialize' _ Ht.quorum $$ Hown as ⟨Hown, #Hd16⟩
  wp_apply go_etcd_io.raft.v3.confchange.wp_initialize' _ Ht.confchange $$ Hown as ⟨Hown, #Hd15⟩
  wp_apply strings.wp_initialize' _ Ht.strings $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply slices.wp_initialize' _ Ht.slices $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply math.big.wp_initialize' _ Ht.big $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply math.wp_initialize' _ Ht.math $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply crypto.rand.wp_initialize' _ Ht.rand $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply bytes.wp_initialize' _ Ht.bytes $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply context_wp_initialize'_closedchan _ Ht.context Ht.errors Ht.sync Ht.atomic Ht.time
    $$ Hown as ⟨Hown, #Hd8, -⟩
  wp_apply sync.wp_initialize' _ Ht.sync $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply os.wp_initialize' _ Ht.os $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply log.wp_initialize' _ Ht.log $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply io.wp_initialize' _ Ht.io $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply fmt.wp_initialize' _ Ht.fmt $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply go_etcd_io.raft.v3.raftpb.wp_initialize' _ Ht.raftpb $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply google_golang_org.protobuf.proto.wp_initialize' _ Ht.proto $$ Hown as ⟨Hown, #Hdp⟩
  wp_apply errors.wp_initialize' _ Ht.errors $$ Hown as ⟨Hown, #Hd1⟩
  icases os_isPkgInit_Stderr $$ Hd6 with ⟨%stderr, #Hstderr⟩
  icases io_isPkgInit_Discard $$ Hd4 with ⟨%discard, #Hdiscard⟩
  iapply wp_fupd
  repeat (first
    | (wp_apply log.wp_New as %_ _)
    | (wp_apply _root_.Perennial.context.wp_New_errorString as %_ #_)
    | wp_auto)
  iStructNamed «$r0»
  imod sync.init_Mutex iprop(True) ⊤ («$r0_ptr».[lockedRand, go!"mu"]) $$ mu [] with #Hmu
  · inext
    itrivial
  ihave %HesNN := typedPointsto_not_null $$ «$r0»
  icases typedPointsto_split _ _ _ $$ «$r0» with Hes
  simp only [TypedPointsto.typedPointstoDef]
  icases Hes with ⟨Hst, HeT, HeV, HeC, Heuf, Hesc, -⟩
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod inv_alloc (nroot.@"protobuf") ⊤
      iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState) (sc : w32) (us : GoSlice),
        _.[raftpb.HardState, go!"state"] ↦ st ∗ _.[raftpb.HardState, go!"sizeCache"] ↦ sc ∗
          _.[raftpb.HardState, go!"unknownFields"] ↦ us ∗ us ↦* ([] : List w8))
      $$ [Hst Heuf Hesc Hnil] with #HesPb
  · inext
    iexists _, _, _
    iframe Hst Hesc Heuf Hnil
  ipersist HES
  ipersist HEPD
  ipersist HGR
  ipersist HEmpty
  ipersist HeT
  ipersist HeV
  ipersist HeC
  ipersist HEC
  ipersist HEU
  ipersist HESU
  ipersist HESP
  ipersist HESL
  ipersist HEB
  ipersist HisLocal
  ipersist HisResp
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold isInitialized isLockedRand
  iexists _, _, _, _, _, _, _, _, _, _
  ihave #HEB' : iprop(∃ eb : GoInterface, (globalAddr errBreak ↦□ eb : IProp GF) ∗
      ⌜eb ≠ interface.nil ∧ IsNewError eb⌝) $$ [HEB]
  · iexists _
    iframe HEB
    ipureintro
    exact ⟨nofun, ⟨_, _, rfl⟩⟩
  ihave #HEmpty' : iprop(∃ es : Loc, (globalAddr emptyState ↦□ es : IProp GF) ∗ ⌜es ≠ null⌝ ∗
      (es.[raftpb.HardState, go!"Term"] ↦□ null : IProp GF) ∗
      (es.[raftpb.HardState, go!"Vote"] ↦□ null : IProp GF) ∗
      (es.[raftpb.HardState, go!"Commit"] ↦□ null : IProp GF) ∗
      inv (nroot.@"protobuf") iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState)
          (sc : w32) (us : GoSlice),
        es.[raftpb.HardState, go!"state"] ↦ st ∗ es.[raftpb.HardState, go!"sizeCache"] ↦ sc ∗
          es.[raftpb.HardState, go!"unknownFields"] ↦ us ∗ us ↦* ([] : List w8)))
      $$ [HEmpty HeT HeV HeC HesPb]
  · iexists _
    iframe HEmpty HeT HeV HeC HesPb
    ipureintro; exact HesNN
  iframe HES HEPD HGR HEmpty' HEC HEU HESU HESP HESL HisLocal HisResp Hmu HEB'
  simp only [named, EtcdGrove.errorsNewVar]
  iframe #
  ipureintro
  exact ⟨nofun, nofun, ⟨_, _, rfl⟩, nofun, nofun,
    ⟨_, _, rfl⟩, ⟨_, _, rfl⟩, nofun⟩

end raft_init

end go_etcd_io.raft.v3

namespace github_com.mit_pdos.etcd_grove.examples.kv

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [context.ErrorStringIsError] [context.DeadlineExceededIsError] [log.NewModel]

/-- What the store's initialization needs of `get_is_pkg_init` (see the file header): the
store's and lintest's entries carry `isClosedchanInit`, as porcupine's and `context`'s
(`PorcupineInitTable`); raft's table (`CCInitTable`) covers raft and the packages it imports;
`primitive`'s is its `isPkgInit`. -/
structure KVInitTable (get_is_pkg_init : GoString → IProp GF) : Prop where
  self : get_is_pkg_init pkg_id.github_com.mit_pdos.etcd_grove.examples.kv =
    iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗
      context.isClosedchanInit)
  lintest : get_is_pkg_init pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest =
    iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest ∗
      context.isClosedchanInit)
  porcupine : github_com.anishathalye.porcupine.PorcupineInitTable get_is_pkg_init
  raft : go_etcd_io.raft.v3.CCInitTable get_is_pkg_init
  primitive : GetIsPkgInitProp pkg_id.github_com.goose_lang.primitive get_is_pkg_init

/-- The store's initialization, returning `context`'s `isClosedchanInit` (see the file
header). -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Ht : KVInitTable get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        (isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗
          context.isClosedchanInit) }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Ht.self) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply google_golang_org.protobuf.proto.wp_initialize' _ Ht.raft.proto $$ Hown
    as ⟨Hown, #H10⟩
  wp_apply encoding.binary.wp_initialize' _ Ht.raft.binary $$ Hown as ⟨Hown, #H9⟩
  wp_apply go_etcd_io.raft.v3.raftpb.wp_initialize' _ Ht.raft.raftpb $$ Hown as ⟨Hown, #H8⟩
  wp_apply go_etcd_io.raft.v3.wp_initialize'_closedchan _ Ht.raft $$ Hown as ⟨Hown, #H7⟩
  wp_apply time.wp_initialize' _ Ht.raft.time $$ Hown as ⟨Hown, #H6⟩
  wp_apply sync.wp_initialize' _ Ht.raft.sync $$ Hown as ⟨Hown, #H5⟩
  wp_apply context_wp_initialize'_closedchan _ Ht.raft.context Ht.raft.errors Ht.raft.sync
    Ht.raft.atomic Ht.raft.time $$ Hown as ⟨Hown, #H4, #Hcc⟩
  wp_apply github_com.mit_pdos.etcd_grove.examples.lintest.wp_initialize' _ Ht.porcupine
    Ht.lintest $$ Hown as ⟨Hown, #H3, -⟩
  wp_apply github_com.goose_lang.primitive.wp_initialize' _ Ht.primitive $$ Hown
    as ⟨Hown, #H2⟩
  wp_apply github_com.anishathalye.porcupine.wp_initialize' _ Ht.porcupine $$ Hown
    as ⟨Hown, #H1, -⟩
  iframe Hown
  imodintro
  iframe #
  is_pkg_init_finish

end init

end github_com.mit_pdos.etcd_grove.examples.kv

end Perennial
