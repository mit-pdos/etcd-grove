/-
`unix.Mmap` whose error witnesses that **the file system can fail** (`Mmap.spec` with `⌜¬ FsNoErr⌝` in
its error arm; session S3f of `notes/bbolt-integration-plan.md`): under the premises `FsNoErr` names,
`specNoErr`. Proved in `Proof/golang_org/x/sys/unix/MmapW.lean`, from the two.
-/
module

public import Spec.golang_org.x.sys.unix.Mmap
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
abbrev golang_org.x.sys.unix.Mmap.specW : Prop :=
  ∀ (fd off len prot fl : w64) (dq : DFrac) (d : OsFd) (m : OsMeta),
  d.readable = true → off = 0 → 0 < len.toInt → prot.toNat = PROT_READ →
  (fl.toNat = MAP_SHARED ∨ fl.toNat = MAP_SHARED + MAP_POPULATE) →
  {{ osInv (GF := GF) ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.ino (DFrac.own 1) m }}
    (App (App (App (App (App (Val (@! golang_org.x.sys.unix.Mmap)) (Val #fd)) (Val #off))
      (Val #len)) (Val #prot)) (Val #fl))
  {{ (sl : GoSlice) (e : w64), RET (PairV #sl #(errnoErr e)); osFd fd dq d ∗
      ((∃ base : Loc, ⌜e = 0 ∧ sl = ⟨base, len, len⟩⌝ ∗
          osMeta d.ino (DFrac.own 1) ({ m with maps := <[base := len.toNat]> m.maps }) ∗
          ∃ bs : List w8, ⌜bs.length = m.size⌝ ∗
            cellsR base 0 len.toNat (fun i => toCellVal bs[i]?)) ∨
       (⌜e ≠ 0 ∧ sl = slice.nil ∧ ¬ FsNoErr⌝ ∗ osMeta d.ino (DFrac.own 1) m)) }}

end spec

end EtcdGrove
end Perennial
