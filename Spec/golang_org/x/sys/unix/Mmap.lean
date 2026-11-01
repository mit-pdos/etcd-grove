/-
`unix.Mmap(fd, 0, length, PROT_READ, MAP_SHARED[|MAP_POPULATE])` (this repository's
`golang.org/x/sys/unix`, project `bboltfs`): the trusted model (`TrustedCode/golang_org/x/sys/unix.lean`)
is the extension's `Mmap` (`wp_Mmap`), whose base it makes a slice of `length` bytes with
`unsafe.Slice`. With the whole of the file's `OsMeta` (no change in flight on it): on success, a
slice of fresh cells, whose client halves hold the file's bytes, then holes past its end (a
`length` past the file's size is allowed), and the mapping is recorded in the `OsMeta`; on
failure, `nil` and an `Errno`. Proved in `Proof/golang_org/x/sys/unix/Mmap.lean`. Lean-first (no
Rocq counterpart).
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
abbrev golang_org.x.sys.unix.Mmap.spec : Prop :=
  ∀ (fd off len prot fl : w64) (dq : DFrac) (d : OsFd) (m : OsMeta),
  d.readable = true → off = 0 → 0 < len.toInt → prot.toNat = PROT_READ →
  (fl.toNat = MAP_SHARED ∨ fl.toNat = MAP_SHARED + MAP_POPULATE) →
  {{ osInv (GF := GF) ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.path (DFrac.own 1) (some m) }}
    (App (App (App (App (App (Val (@! golang_org.x.sys.unix.Mmap)) (Val #fd)) (Val #off))
      (Val #len)) (Val #prot)) (Val #fl))
  {{ (sl : GoSlice) (e : w64), RET (PairV #sl #(errnoErr e)); osFd fd dq d ∗
      ((∃ base : Loc, ⌜e = 0 ∧ sl = ⟨base, len, len⟩⌝ ∗
          osMeta d.path (DFrac.own 1) (some { m with maps := <[base := len.toNat]> m.maps }) ∗
          ∃ bs : List w8, ⌜bs.length = m.size⌝ ∗
            cellsR base 0 len.toNat (fun i => toCellVal bs[i]?)) ∨
       (⌜e ≠ 0 ∧ sl = slice.nil⌝ ∗ osMeta d.path (DFrac.own 1) (some m))) }}

end spec

end EtcdGrove
end Perennial
