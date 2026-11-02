/-
`unix.Munmap(b)` of a whole mapping (this repository's `golang.org/x/sys/unix`, project
`bboltfs`): `b` is the slice `unix.Mmap` returned (`Spec/golang_org/x/sys/unix/Mmap.lean`), and
its length positive (as `Mmap` requires), and the client gives back all of its cells' client halves, with the whole of the file's `OsMeta`. The
model (`TrustedCode/golang_org/x/sys/unix.lean`) is the extension's `Munmap` (`wp_osMunmap`). On
success the mapping is gone from the `OsMeta`; on failure it may be gone, or still there with its
cells back. Proved in `Proof/golang_org/x/sys/unix/Munmap.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import GeneratedProof.golang_org.x.sys.unix
public import Proof.syscall.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [golang_org.x.sys.unix.Assumptions]

/-- See the file header. -/
abbrev golang_org.x.sys.unix.Munmap.spec : Prop :=
  ∀ (base : Loc) (len : w64) (p : GoString) (m : OsMeta) (vf : Nat → val),
  0 < len.toInt → m.maps !! base = some len.toNat →
  {{ osInv (GF := GF) ∗ osMeta (GF := GF) p (DFrac.own 1) (some m) ∗
      cellsR (GF := GF) base 0 len.toNat vf }}
    (App (Val (@! golang_org.x.sys.unix.Munmap)) (Val #(⟨base, len, len⟩ : GoSlice)))
  {{ (e : w64), RET #(errnoErr e);
      (⌜e = 0⌝ ∗ osMeta p (DFrac.own 1) (some { m with maps := GMap.delete base m.maps })) ∨
      (⌜e ≠ 0⌝ ∗
        (osMeta p (DFrac.own 1) (some { m with maps := GMap.delete base m.maps }) ∨
         (osMeta p (DFrac.own 1) (some m) ∗ cellsR base 0 len.toNat vf))) }}

end spec

end EtcdGrove
end Perennial
