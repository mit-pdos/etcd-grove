/-
The definitions named by the statement of `examples/osfs/walfs`'s `dirswap.go` result: the boot
program (`bootDS`, named by `dirswap_crash_robust.spec`) and its precondition in a generation
(`bootPreDS`). The result itself, which composes the proofs of `os`'s functions, is in
`DirSwapLinked.lean` (CLAUDE.md, "Import tiers").
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.DirSwap
public import GooseLang.Ext.Fs.Adequacy

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs DSBase DS
  github_com.mit_pdos.etcd_grove.examples.osfs.walfs

attribute [local instance] fsExts fsExtsSemantics fsExtsInterp fsExts_hasFs fsExtsCrashInterp

/-- The boot program: initialize the package, then call `BootDir(dir)`. -/
def bootDS [GoGlobalContext] (dir : GoString) : Expr :=
  Seq (App (Val initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve BootDir []))) (Val #())) (Val #dir))

section gen
variable [GoGlobalContext] {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]

/-- The precondition of the boot program in the generation `L`, the roots `R`, `dir` the root of
`j`. -/
def bootPreDS (R : Roots) (j : Ino) (L : GooseLocalGS GF) : IProp GF :=
  iprop(osInv (L := L) ∗ ownGoState (hG := L.goose_go_stateGS) ∅ ∗
    ∃ (m : Tree) (ko : Option Ino), osShared (L := L) R (m, []) ∗
      ⌜TreeWf R m ∧ SafeT j ko m⌝ ∗ startFile (L := L) ko)

end gen

end osfs_walfs
end EtcdGrove
end Perennial

end
