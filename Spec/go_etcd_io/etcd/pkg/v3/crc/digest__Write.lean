/-
`d.Write(p)` on a `*digest` (`pkg/v3/crc`, translated with its body) whose table is the Castagnoli
table: the digest's CRC advanced over `p` (`crc32c`), returning `len(p), nil`; `p` is only read, at
any fraction. Over `crc32.Update`'s spec. Proved in
`Proof/go_etcd_io/etcd/pkg/v3/crc/digest__Write.lean`. Lean-first. (crc32-hooks2, 2026-11-22:
`crc32.Update` reads `hash/crc32`'s package state since its `update` is translated, etcd-grove#14,
hence the premise `isPkgInit hash/crc32`.)
-/
module

public import GeneratedProof.go_etcd_io.etcd.pkg.v3.crc
public import Spec.hash.crc32.Model
public import Spec.hash.crc32.Update

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.pkg.v3.crc.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.pkg.v3.crc.digest.Write.spec : Prop :=
  ∀ (l : Loc) (c : w32) (tab : Loc) (s : GoSlice) (bs : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.hash.crc32 ∗
      (l ↦ go_etcd_io.etcd.pkg.v3.crc.digest.mk c tab : IProp GF) ∗
      tab ↦□ hash.crc32.castagnoliTableArr ∗ s ↦*{dq} bs }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.crc.digest.ty @!! go!"Write")) (Val #s))
  {{ RET (PairV #s.len #interface.nil);
      l ↦ go_etcd_io.etcd.pkg.v3.crc.digest.mk (hash.crc32.crc32c c bs) tab ∗ s ↦*{dq} bs }}

end spec

end EtcdGrove
end Perennial
