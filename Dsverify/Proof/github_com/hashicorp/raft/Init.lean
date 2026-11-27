/-
Package initialization of `github_com.hashicorp.raft`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`Base.lean`): its error variables (`ErrLeader`, `ErrNotLeader`, `ErrNotVoter`, `ErrLeadershipLost`, `ErrAbortedByRestore`, `ErrRaftShutdown`, `ErrEnqueueTimeout`, `ErrNothingNewToSnapshot`, `ErrUnsupportedProtocol`, `ErrCantBootstrap`, `ErrLeadershipTransferInProgress`, `ErrIncompatibleLogStore`, `ErrTransportShutdown`, `ErrPipelineShutdown`, `ErrLogNotFound`, `ErrPipelineReplicationNotSupported`, `errShortBuffer`, translated
`errors.New` calls) each hold `errors.New` of their message (`errors.newVar`). Its initializer
allocates its variables, initializes its imports and runs their translated initializers.
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
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrLeader ⟨#SErrLeader, #MErrLeader⟩
  -- translated initializer of ErrNotLeader))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrNotLeader ⟨#SErrNotLeader, #MErrNotLeader⟩
  -- translated initializer of ErrNotVoter))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrNotVoter ⟨#SErrNotVoter, #MErrNotVoter⟩
  -- translated initializer of ErrLeadershipLost))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrLeadershipLost ⟨#SErrLeadershipLost, #MErrLeadershipLost⟩
  -- translated initializer of ErrAbortedByRestore))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrAbortedByRestore ⟨#SErrAbortedByRestore, #MErrAbortedByRestore⟩
  -- translated initializer of ErrRaftShutdown))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrRaftShutdown ⟨#SErrRaftShutdown, #MErrRaftShutdown⟩
  -- translated initializer of ErrEnqueueTimeout))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrEnqueueTimeout ⟨#SErrEnqueueTimeout, #MErrEnqueueTimeout⟩
  -- translated initializer of ErrNothingNewToSnapshot))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrNothingNewToSnapshot ⟨#SErrNothingNewToSnapshot, #MErrNothingNewToSnapshot⟩
  -- translated initializer of ErrUnsupportedProtocol))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrUnsupportedProtocol ⟨#SErrUnsupportedProtocol, #MErrUnsupportedProtocol⟩
  -- translated initializer of ErrCantBootstrap))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrCantBootstrap ⟨#SErrCantBootstrap, #MErrCantBootstrap⟩
  -- translated initializer of ErrLeadershipTransferInProgress))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrLeadershipTransferInProgress ⟨#SErrLeadershipTransferInProgress, #MErrLeadershipTransferInProgress⟩
  -- translated initializer of ErrIncompatibleLogStore))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrIncompatibleLogStore ⟨#SErrIncompatibleLogStore, #MErrIncompatibleLogStore⟩
  -- translated initializer of errShortBuffer))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xerrShortBuffer ⟨#SerrShortBuffer, #MerrShortBuffer⟩
  -- translated initializer of ErrTransportShutdown))
  try wp_auto
  wp_alloc_anon
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrTransportShutdown ⟨#SErrTransportShutdown, #MErrTransportShutdown⟩
  -- translated initializer of ErrPipelineShutdown))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrPipelineShutdown ⟨#SErrPipelineShutdown, #MErrPipelineShutdown⟩
  -- translated initializer of keyCurrentTerm))
  try wp_auto
  wp_alloc_anon
  try wp_auto
  wp_apply wp_string_to_bytes go!"CurrentTerm" as %_ ⟨-, -⟩
  try wp_auto
  wp_apply wp_string_to_bytes go!"LastVoteTerm" as %_ ⟨-, -⟩
  try wp_auto
  wp_apply wp_string_to_bytes go!"LastVoteCand" as %_ ⟨-, -⟩
  try wp_auto
  -- translated initializer of keyLastVoteTerm))
  -- translated initializer of keyLastVoteCand))
  -- translated initializer of ErrLogNotFound))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrLogNotFound ⟨#SErrLogNotFound, #MErrLogNotFound⟩
  -- translated initializer of ErrPipelineReplicationNotSupported))
  try wp_auto
  wp_apply _root_.Perennial.errors.wp_New_errorString as %xErrPipelineReplicationNotSupported ⟨#SErrPipelineReplicationNotSupported, #MErrPipelineReplicationNotSupported⟩
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
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold _root_.Perennial.errors.newVar
  isplitr
  · iexists _; iframe HErrLeader SErrLeader MErrLeader
  isplitr
  · iexists _; iframe HErrNotLeader SErrNotLeader MErrNotLeader
  isplitr
  · iexists _; iframe HErrNotVoter SErrNotVoter MErrNotVoter
  isplitr
  · iexists _; iframe HErrLeadershipLost SErrLeadershipLost MErrLeadershipLost
  isplitr
  · iexists _; iframe HErrAbortedByRestore SErrAbortedByRestore MErrAbortedByRestore
  isplitr
  · iexists _; iframe HErrRaftShutdown SErrRaftShutdown MErrRaftShutdown
  isplitr
  · iexists _; iframe HErrEnqueueTimeout SErrEnqueueTimeout MErrEnqueueTimeout
  isplitr
  · iexists _; iframe HErrNothingNewToSnapshot SErrNothingNewToSnapshot MErrNothingNewToSnapshot
  isplitr
  · iexists _; iframe HErrUnsupportedProtocol SErrUnsupportedProtocol MErrUnsupportedProtocol
  isplitr
  · iexists _; iframe HErrCantBootstrap SErrCantBootstrap MErrCantBootstrap
  isplitr
  · iexists _; iframe HErrLeadershipTransferInProgress SErrLeadershipTransferInProgress MErrLeadershipTransferInProgress
  isplitr
  · iexists _; iframe HErrIncompatibleLogStore SErrIncompatibleLogStore MErrIncompatibleLogStore
  isplitr
  · iexists _; iframe HErrTransportShutdown SErrTransportShutdown MErrTransportShutdown
  isplitr
  · iexists _; iframe HErrPipelineShutdown SErrPipelineShutdown MErrPipelineShutdown
  isplitr
  · iexists _; iframe HErrLogNotFound SErrLogNotFound MErrLogNotFound
  isplitr
  · iexists _; iframe HErrPipelineReplicationNotSupported SErrPipelineReplicationNotSupported MErrPipelineReplicationNotSupported
  iexists _; iframe HerrShortBuffer SerrShortBuffer MerrShortBuffer

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
