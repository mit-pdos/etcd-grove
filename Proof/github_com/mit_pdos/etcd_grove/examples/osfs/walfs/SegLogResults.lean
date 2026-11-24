/-
The definitions named by the statement of `examples/osfs/walfs`'s `seglog.go` result: the boot
program (`bootLog`, named by `seglog_crash_robust.spec`) and its precondition in a generation
(`bootPreLog`). The result itself, which composes the proofs of `os`'s functions, is in
`SegLogLinked.lean` (CLAUDE.md, "Import tiers").
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.SegLog
public import GooseLang.Ext.Fs.Adequacy

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs DSBase
  github_com.mit_pdos.etcd_grove.examples.osfs.walfs

attribute [local instance] fsExts fsExtsSemantics fsExtsInterp fsExts_hasFs fsExtsCrashInterp

/-- `seglog`'s boot program: initialize the package, then call `Run(dir)`. -/
def bootLog [GoGlobalContext] (dir : GoString) : Expr :=
  Seq (App (Val initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve Run []))) (Val #())) (Val #dir))

section gen
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The precondition of `seglog`'s boot program in the generation `L`, the roots `R`: the shared
view's resources of a well-formed durable tree. -/
def bootPreLog [G : GooseGlobalGS .hasLC GF] (R : Roots) (L : GooseLocalGS GF) : IProp GF :=
  iprop(osInv (L := L) ∗ ownGoState (hG := L.goose_go_stateGS) ∅ ∗
    ∃ m : Tree, osShared (L := L) R (m, []) ∗ ⌜TreeWf R m⌝)

end gen

end osfs_walfs
end EtcdGrove
end Perennial

end
