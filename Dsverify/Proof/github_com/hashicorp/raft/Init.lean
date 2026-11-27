/-
Package initialization of `github_com.hashicorp.raft`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`pkgGlobals`, `Base.lean`, the lab's): its error variables (translated `errors.New`
calls) hold pairwise distinct errors, each `errors.newVar` of its message (`errVals`), the three
stable-store keys read-only bytes, and `nextObserverID` an invariant. Its initializer allocates its
variables, initializes its imports and runs their translated initializers; the proof is the lab's
`initialize.lean` (its lemmas: `InitLemmas.lean`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.Base
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Perennial.Proof.errors.NewVar
public import Dsverify.Proof.github_com.hashicorp.raft.InitLemmas
public import Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.github_com.hashicorp.raft.Assumptions]

namespace github_com.hashicorp.raft

set_option maxHeartbeats 8000000 in
theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.hashicorp.raft get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrPipelineReplicationNotSupported _ as HErrPipelineReplicationNotSupported
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrLogNotFound _ as HErrLogNotFound
  wp_apply wp_GlobalAlloc (V := GoSlice) keyLastVoteCand _ as HkeyLastVoteCand
  wp_apply wp_GlobalAlloc (V := GoSlice) keyLastVoteTerm _ as HkeyLastVoteTerm
  wp_apply wp_GlobalAlloc (V := GoSlice) keyCurrentTerm _ as HkeyCurrentTerm
  wp_apply wp_GlobalAlloc (V := w64) nextObserverID _ as HnextObserverID
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrPipelineShutdown _ as HErrPipelineShutdown
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrTransportShutdown _ as HErrTransportShutdown
  wp_apply wp_GlobalAlloc (V := GoInterface) errShortBuffer _ as HerrShortBuffer
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrIncompatibleLogStore _ as HErrIncompatibleLogStore
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrLeadershipTransferInProgress _ as HErrLeadershipTransferInProgress
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrCantBootstrap _ as HErrCantBootstrap
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrUnsupportedProtocol _ as HErrUnsupportedProtocol
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrNothingNewToSnapshot _ as HErrNothingNewToSnapshot
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrEnqueueTimeout _ as HErrEnqueueTimeout
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrRaftShutdown _ as HErrRaftShutdown
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrAbortedByRestore _ as HErrAbortedByRestore
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrLeadershipLost _ as HErrLeadershipLost
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrNotVoter _ as HErrNotVoter
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrNotLeader _ as HErrNotLeader
  wp_apply wp_GlobalAlloc (V := GoInterface) ErrLeader _ as HErrLeader
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.github_com.goose_lang.primitive _root_.Perennial.github_com.goose_lang.primitive.initialize'
      EtcdGrove.ExternalInit.github_com_goose_lang_primitive _root_.Perennial.github_com.goose_lang.primitive.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.bytes _root_.Perennial.bytes.initialize'
      EtcdGrove.ExternalInit.bytes _root_.Perennial.bytes.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync.atomic _root_.Perennial.sync.atomic.initialize'
      EtcdGrove.ExternalInit.sync_atomic _root_.Perennial.sync.atomic.wp_initialize' _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strconv _root_.Perennial.strconv.initialize'
      EtcdGrove.ExternalInit.strconv _root_.Perennial.strconv.wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.errors _root_.Perennial.errors.initialize'
      EtcdGrove.ExternalInit.errors _root_.Perennial.errors.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of ErrLeader))
  try wp_auto
  wp_apply wp_New_excl as %xErrLeader ⟨#SErrLeader, #EErrLeader, XErrLeader⟩
  -- translated initializer of ErrNotLeader))
  try wp_auto
  wp_apply wp_New_excl as %xErrNotLeader ⟨#SErrNotLeader, #EErrNotLeader, XErrNotLeader⟩
  -- translated initializer of ErrNotVoter))
  try wp_auto
  wp_apply wp_New_excl as %xErrNotVoter ⟨#SErrNotVoter, #EErrNotVoter, XErrNotVoter⟩
  -- translated initializer of ErrLeadershipLost))
  try wp_auto
  wp_apply wp_New_excl as %xErrLeadershipLost ⟨#SErrLeadershipLost, #EErrLeadershipLost, XErrLeadershipLost⟩
  -- translated initializer of ErrAbortedByRestore))
  try wp_auto
  wp_apply wp_New_excl as %xErrAbortedByRestore ⟨#SErrAbortedByRestore, #EErrAbortedByRestore, XErrAbortedByRestore⟩
  -- translated initializer of ErrRaftShutdown))
  try wp_auto
  wp_apply wp_New_excl as %xErrRaftShutdown ⟨#SErrRaftShutdown, #EErrRaftShutdown, XErrRaftShutdown⟩
  -- translated initializer of ErrEnqueueTimeout))
  try wp_auto
  wp_apply wp_New_excl as %xErrEnqueueTimeout ⟨#SErrEnqueueTimeout, #EErrEnqueueTimeout, XErrEnqueueTimeout⟩
  -- translated initializer of ErrNothingNewToSnapshot))
  try wp_auto
  wp_apply wp_New_excl as %xErrNothingNewToSnapshot ⟨#SErrNothingNewToSnapshot, #EErrNothingNewToSnapshot, XErrNothingNewToSnapshot⟩
  -- translated initializer of ErrUnsupportedProtocol))
  try wp_auto
  wp_apply wp_New_excl as %xErrUnsupportedProtocol ⟨#SErrUnsupportedProtocol, #EErrUnsupportedProtocol, XErrUnsupportedProtocol⟩
  -- translated initializer of ErrCantBootstrap))
  try wp_auto
  wp_apply wp_New_excl as %xErrCantBootstrap ⟨#SErrCantBootstrap, #EErrCantBootstrap, XErrCantBootstrap⟩
  -- translated initializer of ErrLeadershipTransferInProgress))
  try wp_auto
  wp_apply wp_New_excl as %xErrLeadershipTransferInProgress ⟨#SErrLeadershipTransferInProgress, #EErrLeadershipTransferInProgress, XErrLeadershipTransferInProgress⟩
  -- translated initializer of ErrIncompatibleLogStore))
  try wp_auto
  wp_apply wp_New_excl as %xErrIncompatibleLogStore ⟨#SErrIncompatibleLogStore, #EErrIncompatibleLogStore, XErrIncompatibleLogStore⟩
  -- translated initializer of errShortBuffer))
  try wp_auto
  wp_apply wp_New_excl as %xerrShortBuffer ⟨#SerrShortBuffer, #EerrShortBuffer, XerrShortBuffer⟩
  -- translated initializer of ErrTransportShutdown))
  try wp_auto
  wp_alloc_anon
  try wp_auto
  wp_apply wp_New_excl as %xErrTransportShutdown ⟨#SErrTransportShutdown, #EErrTransportShutdown, XErrTransportShutdown⟩
  -- translated initializer of ErrPipelineShutdown))
  try wp_auto
  wp_apply wp_New_excl as %xErrPipelineShutdown ⟨#SErrPipelineShutdown, #EErrPipelineShutdown, XErrPipelineShutdown⟩
  -- translated initializer of keyCurrentTerm))
  try wp_auto
  wp_alloc_anon
  try wp_auto
  wp_apply wp_string_to_bytes go!"CurrentTerm" as %skeyCurrentTerm ⟨SkeyCurrentTerm, -⟩
  try wp_auto
  wp_apply wp_string_to_bytes go!"LastVoteTerm" as %skeyLastVoteTerm ⟨SkeyLastVoteTerm, -⟩
  try wp_auto
  wp_apply wp_string_to_bytes go!"LastVoteCand" as %skeyLastVoteCand ⟨SkeyLastVoteCand, -⟩
  try wp_auto
  -- translated initializer of keyLastVoteTerm))
  -- translated initializer of keyLastVoteCand))
  -- translated initializer of ErrLogNotFound))
  try wp_auto
  wp_apply wp_New_excl as %xErrLogNotFound ⟨#SErrLogNotFound, #EErrLogNotFound, XErrLogNotFound⟩
  -- translated initializer of ErrPipelineReplicationNotSupported))
  try wp_auto
  wp_apply wp_New_excl as %xErrPipelineReplicationNotSupported ⟨#SErrPipelineReplicationNotSupported, #EErrPipelineReplicationNotSupported, XErrPipelineReplicationNotSupported⟩
  try wp_auto
  ipersist HErrLeader
  ipersist HErrNotLeader
  ipersist HErrNotVoter
  ipersist HErrLeadershipLost
  ipersist HErrAbortedByRestore
  ipersist HErrRaftShutdown
  ipersist HErrEnqueueTimeout
  ipersist HErrNothingNewToSnapshot
  ipersist HErrUnsupportedProtocol
  ipersist HErrCantBootstrap
  ipersist HErrLeadershipTransferInProgress
  ipersist HErrIncompatibleLogStore
  ipersist HErrTransportShutdown
  ipersist HErrPipelineShutdown
  ipersist HErrLogNotFound
  ipersist HErrPipelineReplicationNotSupported
  ipersist HerrShortBuffer
  ipersist SkeyCurrentTerm
  ipersist HkeyCurrentTerm
  ipersist SkeyLastVoteTerm
  ipersist HkeyLastVoteTerm
  ipersist SkeyLastVoteCand
  ipersist HkeyLastVoteCand
  imod inv_alloc nextObserverIDN ⊤ (∃ n : w64, globalAddr nextObserverID ↦ n) $$ [HnextObserverID]
    with #Hobs
  · inext; iexists _; iexact HnextObserverID
  let g : RaftErr → Loc := fun c =>
    match c with
      | .leader => xErrLeader
      | .notLeader => xErrNotLeader
      | .notVoter => xErrNotVoter
      | .leadershipLost => xErrLeadershipLost
      | .abortedByRestore => xErrAbortedByRestore
      | .raftShutdown => xErrRaftShutdown
      | .enqueueTimeout => xErrEnqueueTimeout
      | .nothingNewToSnapshot => xErrNothingNewToSnapshot
      | .unsupportedProtocol => xErrUnsupportedProtocol
      | .cantBootstrap => xErrCantBootstrap
      | .leadershipTransferInProgress => xErrLeadershipTransferInProgress
      | .incompatibleLogStore => xErrIncompatibleLogStore
      | .shortBuffer => xerrShortBuffer
      | .transportShutdown => xErrTransportShutdown
      | .pipelineShutdown => xErrPipelineShutdown
      | .logNotFound => xErrLogNotFound
      | .pipelineReplicationNotSupported => xErrPipelineReplicationNotSupported
  ihave %Hnd := exclS_nodup g RaftErr.all $$ [XErrLeader XErrNotLeader XErrNotVoter XErrLeadershipLost XErrAbortedByRestore XErrRaftShutdown XErrEnqueueTimeout XErrNothingNewToSnapshot XErrUnsupportedProtocol XErrCantBootstrap XErrLeadershipTransferInProgress XErrIncompatibleLogStore XerrShortBuffer XErrTransportShutdown XErrPipelineShutdown XErrLogNotFound XErrPipelineReplicationNotSupported]
  · simp only [RaftErr.all, g]
    iframe
    iapply BigSepL.bigSepL_nil.2
    iempintro
  have Hinj : Function.Injective
      (fun c => interface.mkOk (go.GoType.PointerType errors.errorString.ty) #(g c)) := by
    intro a b h
    have h1 : g a = g b := by
      simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at h
      exact go.intoVal_inj h.2
    have hall : ∀ c, c ∈ RaftErr.all := by intro c; cases c <;> simp [RaftErr.all]
    exact nodup_map_inj g Hnd (hall a) (hall b) h1
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold pkgGlobals
  isplitr
  · iexists (fun c => interface.mkOk (go.GoType.PointerType errors.errorString.ty) #(g c))
    unfold errVals
    isplitr
    · ipureintro; exact Hinj
    iapply (bigSepL_all _).2
    simp only [g, RaftErr.var, RaftErr.msg]
    iframe #
    isplitr
    · iunfold errors.newVar; iexists _; iframe HErrLeader SErrLeader EErrLeader
    isplitr
    · iunfold errors.newVar; iexists _; iframe HErrNotLeader SErrNotLeader EErrNotLeader
    isplitr
    · iunfold errors.newVar; iexists _; iframe HErrNotVoter SErrNotVoter EErrNotVoter
    isplitr
    · iunfold errors.newVar; iexists _; iframe HErrLeadershipLost SErrLeadershipLost EErrLeadershipLost
    isplitr
    · iunfold errors.newVar; iexists _; iframe HErrAbortedByRestore SErrAbortedByRestore EErrAbortedByRestore
    isplitr
    · iunfold errors.newVar; iexists _; iframe HErrRaftShutdown SErrRaftShutdown EErrRaftShutdown
    isplitr
    · iunfold errors.newVar; iexists _; iframe HErrEnqueueTimeout SErrEnqueueTimeout EErrEnqueueTimeout
    isplitr
    · iunfold errors.newVar; iexists _; iframe HErrNothingNewToSnapshot SErrNothingNewToSnapshot EErrNothingNewToSnapshot
    isplitr
    · iunfold errors.newVar; iexists _; iframe HErrUnsupportedProtocol SErrUnsupportedProtocol EErrUnsupportedProtocol
    isplitr
    · iunfold errors.newVar; iexists _; iframe HErrCantBootstrap SErrCantBootstrap EErrCantBootstrap
    isplitr
    · iunfold errors.newVar; iexists _; iframe HErrLeadershipTransferInProgress SErrLeadershipTransferInProgress EErrLeadershipTransferInProgress
    isplitr
    · iunfold errors.newVar; iexists _; iframe HErrIncompatibleLogStore SErrIncompatibleLogStore EErrIncompatibleLogStore
    isplitr
    · iunfold errors.newVar; iexists _; iframe HerrShortBuffer SerrShortBuffer EerrShortBuffer
    isplitr
    · iunfold errors.newVar; iexists _; iframe HErrTransportShutdown SErrTransportShutdown EErrTransportShutdown
    isplitr
    · iunfold errors.newVar; iexists _; iframe HErrPipelineShutdown SErrPipelineShutdown EErrPipelineShutdown
    isplitr
    · iunfold errors.newVar; iexists _; iframe HErrLogNotFound SErrLogNotFound EErrLogNotFound
    iunfold errors.newVar; iexists _; iframe HErrPipelineReplicationNotSupported SErrPipelineReplicationNotSupported EErrPipelineReplicationNotSupported
  isplitr
  · iexists skeyCurrentTerm; iframe #
  isplitr
  · iexists skeyLastVoteTerm; iframe #
  isplitr
  · iexists skeyLastVoteCand; iframe #
  iexact Hobs

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.hashicorp.raft get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end github_com.hashicorp.raft

end init

end Perennial
