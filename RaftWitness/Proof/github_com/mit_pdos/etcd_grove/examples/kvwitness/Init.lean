/- Lean-first (no Rocq counterpart).

# The store's package initialization (2026-10-19; ordinary form since 2026-10-22)

`kvwitness.wp_initialize'`: running the package's `initialize'` from `ownInitializing` initializes
its imports (`proto`, `encoding/binary`, `raftpb`, raft, `time`, `sync`, `context`, lintest,
`primitive`, porcupine, in the translation's order) and then the package (no package-level
variable), and gives its `isPkgInit`, at a table of its closure's `isPkgInit`s
(`GetIsPkgInitProp`). `Main.spec` also takes `context`'s `isClosedchanInit`, which the
adequacy proof gets from `context`'s `isPkgInit` (`context.isClosedchanInit_of_init`).

(Until 2026-10-22 this file proved raft's initialization again, at a table whose entry for
`context` carried `isClosedchanInit`, since `context`'s `isPkgInit` did not include it before
Perennial `init-facts`; it is the ordinary form now. The package is in the parallel tree
`RaftWitness/`, which `etc/gen-init.py` does not generate, so the file is hand-written in the
generated files' form, without their `_lb` part: no package imports this one.)

The premises are raft's (`RaftWitness/Proof/go_etcd_io/raft/v3/Init.lean`): the method-set facts
`context.ErrorStringIsError`, `context.DeadlineExceededIsError` and the model of `log.New`,
`log.NewModel`.
-/
module

public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.Base
public import RaftWitness.Proof.go_etcd_io.raft.v3.Init
public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Init
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.kvwitness

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]
variable [log.NewModel]

/-- The store's initialization (see the file header). -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness
      get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvwitness }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply google_golang_org.protobuf.proto.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.1 $$ Hown
    as ⟨Hown, #H10⟩
  wp_apply encoding.binary.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H9⟩
  wp_apply go_etcd_io.raft.v3.raftpb.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1 $$ Hown
    as ⟨Hown, #H8⟩
  wp_apply go_etcd_io.raft.v3.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H7⟩
  wp_apply time.wp_initialize' _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H6⟩
  wp_apply sync.wp_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H5⟩
  wp_apply context.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #H4⟩
  wp_apply github_com.mit_pdos.etcd_grove.examples.lintest.wp_initialize' _ Hinit.2.2.2.1 $$ Hown
    as ⟨Hown, #H3⟩
  wp_apply github_com.goose_lang.primitive.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H2⟩
  wp_apply github_com.anishathalye.porcupine.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #H1⟩
  iframe Hown
  imodintro
  iframe #
  is_pkg_init_finish

end init

end github_com.mit_pdos.etcd_grove.examples.kvwitness

end Perennial
