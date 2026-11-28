/-
(hraft_robust R3) Shared definitions of the proofs of `examples/hraftnet/disk` (the kit's durable log, stable
and snapshot stores over the bodied `examples/lib/durable`): its `isPkgInit`. The package fact is proved by
the generated `Init.lean`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.errors.Base
public import Perennial.Proof.errors.NewVar
public import Perennial.Proof.io.Base
public import Perennial.Proof.strconv.Base
public import Perennial.Proof.sync.Base
public import Dsverify.Proof.github_com.hashicorp.raft.iface.Stores
public import Dsverify.Proof.github_com.hashicorp.raft.examples.snapstore.Base
public import Dsverify.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.PkgInit
public import Dsverify.GeneratedProof.github_com.hashicorp.raft.examples.hraftnet.disk

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft.examples.hraftnet.disk

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

/-- The package-initialized state: the five error variables hold `errors.New` errors
(`ErrNotFound`'s message is `"not found"`, the text raft compares `Get`'s error with). -/
abbrev isInit : IProp GF :=
  iprop("#HErrCorrupt" ∷ errors.newVar ErrCorrupt go!"disk: corrupt file" ∗
    "#HErrNotFound" ∷ errors.newVar ErrNotFound go!"not found" ∗
    "#HErrMissing" ∷ errors.newVar ErrMissing go!"disk: missing file" ∗
    "#HErrNoSnapshot" ∷ errors.newVar ErrNoSnapshot go!"disk: no such snapshot" ∗
    "#HErrClosed" ∷ errors.newVar ErrClosed go!"disk: sink closed")

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk :=
  build_get_is_pkg_init_wf

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk ⊢
      isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk

end init

end github_com.hashicorp.raft.examples.hraftnet.disk

end Perennial
