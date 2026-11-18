/-
`unix.Madvise` at the base of a mapping, whose error witnesses that **the file system can fail**
(`Madvise.spec` with the mapping's `OsMeta` and `⌜e = 0 ∨ ¬ FsNoErr⌝`; session S3f of
`notes/bbolt-integration-plan.md`): under the premises `FsNoErr` names, `specNoErr`. Proved in
`Proof/golang_org/x/sys/unix/MadviseW.lean`, from the two.
-/
module

public import Spec.golang_org.x.sys.unix.Madvise
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
variable [golang_org.x.sys.unix.Assumptions]

/-- See the file header. -/
abbrev golang_org.x.sys.unix.Madvise.specW : Prop :=
  ∀ (base : Loc) (len cap advice : w64) (p : Ino) (dq : DFrac) (m : OsMeta) (n : Nat),
  advice.toNat ≤ 3 → 0 < base.addr → 0 < len.toInt → m.maps !! base = some n →
  {{ osInv (GF := GF) ∗ osMeta (GF := GF) p dq m }}
    (App (App (Val (@! golang_org.x.sys.unix.Madvise)) (Val #(⟨base, len, cap⟩ : GoSlice)))
      (Val #advice))
  {{ (e : w64), RET #(errnoErr e); osMeta p dq m ∗ ⌜e = 0 ∨ ¬ FsNoErr⌝ }}

end spec

end EtcdGrove
end Perennial
