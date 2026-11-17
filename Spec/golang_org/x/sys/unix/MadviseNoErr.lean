/-
`unix.Madvise(b, advice)` of a mapping with a paging hint, with no error of the environment
(`Madvise.spec` over a semantics whose steps satisfy `NoMapLockErr Sio`, every inode covered;
session S3d, pending the user's review): `nil`. `b` starts at the base of a mapping of the file
`p` (its `OsMeta`, any fraction). Proved in `Proof/golang_org/x/sys/unix/MadviseNoErr.lean`.
Lean-first.
-/
module

public import Spec.golang_org.x.sys.unix.Madvise
public import GooseLang.Ext.Fs.Premises
public import GooseLang.Ext.Fs.FilteredSem

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
abbrev golang_org.x.sys.unix.Madvise.specNoErr : Prop :=
  ∀ (Sio : IoSet) [FsStepSat (NoMapLockErr Sio)], (∀ st i, Sio.ino st i) →
  ∀ (base : Loc) (len cap advice : w64) (p : Ino) (dq : DFrac) (m : OsMeta) (n : Nat),
  advice.toNat ≤ 3 → 0 < base.addr → 0 < len.toInt → m.maps !! base = some n →
  {{ osInv (GF := GF) ∗ osMeta (GF := GF) p dq m }}
    (App (App (Val (@! golang_org.x.sys.unix.Madvise)) (Val #(⟨base, len, cap⟩ : GoSlice)))
      (Val #advice))
  {{ RET #(errnoErr 0); osMeta p dq m }}

end spec

end EtcdGrove
end Perennial
