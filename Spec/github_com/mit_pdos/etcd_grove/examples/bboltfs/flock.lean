/- Lean-first (no Rocq counterpart). `flock(f, exclusive)` (`examples/bboltfs/page.go`, bolt_unix.go's `flock` with no timeout): `syscall.Flock` with `LOCK_NB`, retried (after a `time.Sleep`) while it answers `EWOULDBLOCK`. `Flock` is trivial in the model (`Spec/syscall/Flock.lean`), so the spec only gives back the file and its fd, with any error. -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.Meta
public import Proof.os.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-- See the file header. -/
abbrev flock.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (exclusive : Bool),
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd dq d }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.bboltfs.flock)) (Val #f))
      (Val #exclusive))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d }}

end spec

end bboltfs
end EtcdGrove
end Perennial
