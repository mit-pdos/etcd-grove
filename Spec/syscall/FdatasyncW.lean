/-
`syscall.Fdatasync(fd)` (the byte-less variant) whose error witnesses that **the file system can fail**
(`Fdatasync.specB` with `⌜¬ FsNoErr⌝` in its error arm; session S3f of
`notes/bbolt-integration-plan.md`): under the premises `FsNoErr` names, `specBNoErr`. Proved in
`Proof/syscall/FdatasyncW.lean`, from the two.
-/
module

public import Spec.syscall.Fdatasync
public import GooseLang.Ext.Fs.FsNoErr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [syscall.Assumptions]

/-- See the file header. -/
abbrev syscall.Fdatasync.specBW : Prop :=
  ∀ (fd : w64) (dq : DFrac) (d : OsFd) (m : OsMeta),
  {{ osInv (GF := GF) ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.ino (DFrac.own 1) m }}
    (App (Val (@! syscall.Fdatasync)) (Val #fd))
  {{ (e : w64), RET #(errnoErr e); osFd fd dq d ∗
      ((⌜e = 0⌝ ∗ ∃ c, osMeta d.ino (DFrac.own 1) (m.bsynced c)) ∨
       (⌜e ≠ 0 ∧ e ≠ EINTR ∧ ¬ FsNoErr⌝ ∗ osMeta d.ino (DFrac.own 1) m)) }}

end spec

end EtcdGrove
end Perennial
