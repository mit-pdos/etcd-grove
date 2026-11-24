/-
# kvnet's package facts for the top-level theorem (2026-11-22)

What the replica's and the checking client's programs read off their packages' initialization
(proved, not trusted), for `RunNode`'s and `Check`'s preconditions:

* `kvnet_pkg_deps`, `kvcheck_pkg_deps`: an initialized `kvnet` (`kvcheck`) has initialized `net` and
  `context` (`iPkgInit`);
* `connGlobals_of_net`: from `net`'s initialization, `io.EOF`'s, `poll.ErrDeadlineExceeded`'s and
  `net.errTimeout`'s values (`connGlobals`), as `Net/`'s `remote` (`Pkg.lean`) does;
* `isClosedchanInit` is Perennial's `context.isClosedchanInit_of_init`.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Client
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Base
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Base
public import KvNet.Proof.net.Base
public import Perennial.Proof.io.Base
public import Perennial.Proof.context.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section pkg
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [Net.NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

/-- `poll`'s package fact, its first two conjuncts (the third, `ErrFileClosing` an `*errorString`, unused). -/
theorem poll_access' :
    isPkgInit (PROP := IProp GF) pkg_id.internal.poll ⊢
      iprop((∃ e : GoInterface, globalAddr internal.poll.ErrNoDeadline ↦□ e) ∗
        (∃ e : GoInterface, globalAddr internal.poll.ErrDeadlineExceeded ↦□ e)) := by
  refine (isPkgInit_access (PROP := IProp GF) pkg_id.internal.poll).trans ?_
  show iprop((∃ e : GoInterface, typedPointsto (globalAddr internal.poll.ErrNoDeadline) e DFrac.discard) ∗
    (∃ x : Loc, typedPointsto (globalAddr internal.poll.ErrDeadlineExceeded)
      (interface.mkOk (go.GoType.PointerType internal.poll.DeadlineExceededError.ty) #x) DFrac.discard) ∗
    (∃ x : Loc, typedPointsto (globalAddr internal.poll.ErrFileClosing)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard)) ⊢ _
  iintro ⟨#Hn, ⟨%xd, #Hd⟩, -⟩
  isplitl [Hn]
  · iexact Hn
  · iexists _
    iexact Hd

/-- **The globals a connection reads**, from `net`'s initialization (which initializes `io` and
`internal/poll`). -/
theorem connGlobals_of_net :
    isPkgInit (PROP := IProp GF) pkg_id.net ⊢ raft_kvcheck.connGlobals := by
  iintro #Hnet
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave #Hpoll : (isPkgInit (PROP := IProp GF) pkg_id.internal.poll) $$ []
  · iPkgInit
  ihave #Hn := io.eof_of_init $$ Hio
  isimp only [_root_.Perennial.errors.newVar] at Hn
  icases Hn with ⟨%eofl, #Heof, -⟩
  ihave #Hp := poll_access' $$ Hpoll
  icases Hp with ⟨-, %ed, #Hed⟩
  ihave #Hi : net.isInit $$ []
  · with_unfolding_all iapply isPkgInit_access (PROP := IProp GF) pkg_id.net $$ Hnet
  icases Hi with ⟨-, -, %p, #Ht⟩
  unfold raft_kvcheck.connGlobals
  iexists _, ed, _
  iframe Heof Hed Ht

/-- An initialized `kvnet` has initialized `net` and `context`. -/
theorem kvnet_pkg_deps :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ⊢
      isPkgInit (PROP := IProp GF) pkg_id.net ∗ isPkgInit (PROP := IProp GF) pkg_id.context := by
  iintro #Hpkg
  isplitr
  · iPkgInit
  · iPkgInit

/-- An initialized `kvcheck` has initialized `net` and `context`. -/
theorem kvcheck_pkg_deps :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck ⊢
      isPkgInit (PROP := IProp GF) pkg_id.net ∗ isPkgInit (PROP := IProp GF) pkg_id.context := by
  iintro #Hpkg
  isplitr
  · iPkgInit
  · iPkgInit

end pkg

end raft_kvnet
end EtcdGrove
end Perennial
