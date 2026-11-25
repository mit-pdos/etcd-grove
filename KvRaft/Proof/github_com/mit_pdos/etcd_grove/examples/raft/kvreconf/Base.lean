-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvreconf/Base.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Lean-first (no Rocq counterpart).

# The reconfiguring key-value store: package initialization (2026-10-29, track C of
`notes/raft-unified-plan.md`); the pure model is `Pure.lean` (2026-11-21), which this module re-exports

`examples/raft/kvreconf` has no package-level variable (its constants are untyped or typed constants),
so its package fact is `True`; the packages it imports have theirs.

The pure model is `examples/raft/kv`'s (`Proof/github_com/mit_pdos/etcd_grove/examples/raft/kv/Base.lean`),
copied under the namespace `EtcdGrove.kvreconf` (the two examples' proofs are linked in one Lean run
by `etc/tcb-report.py`, so their names must differ) and changed where the Go differs: an
operation's encoding (`encodeOp`: its id, little-endian, the kind, the key's length, the key, the
value; kv's has the proposing replica and its sequence number in place of the id), what `decode`
reads back (`decodeOp`), and the store's state machine (`kvNext`: a `Put` sets its key, anything
else leaves the store; kvreconf has no `Append`).
-/
module

public import KvRaft.Spec.go_etcd_io.raft.v3.Api
public import KvRaft.Proof.go_etcd_io.raft.v3.Base
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Pure
public import KvRaft.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf
public import Perennial.Proof.encoding.binary
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Base
public import Perennial.Proof.github_com.goose_lang.primitive.Base
public import Proof.github_com.mit_pdos.gokv.trusted_proph.Base
public import Perennial.Proof.context.Base
public import Perennial.Proof.time.Base
public import Perennial.Proof.fmt.Base
public import Perennial.Proof.sync.atomic.Base
public import Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.raft.kvreconf

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.raft.kvreconf

namespace EtcdGrove.raft_kvreconf

/-- The store's `quietLogger` type. -/
abbrev qLoggerTy [GooseExts] [GoGlobalContext] : go.GoType :=
  github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.quietLogger.ty

/-- `quietLogger{}`. -/
abbrev qLoggerV [GooseExts] : github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.quietLogger :=
  github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.quietLogger.mk

/-- `quietLogger{}` as a `raft.Logger`. -/
def qLogger [GooseExts] [GoGlobalContext] : GoInterfaceOk := interface.mk qLoggerTy #qLoggerV

end EtcdGrove.raft_kvreconf

end Perennial
