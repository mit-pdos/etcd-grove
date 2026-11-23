/-
`crc32.update(crc, tab, p, checkInitIEEE)` with `tab` a Castagnoli table (`crc32.go:202-214`):
`crc32c crc p`, whichever path it takes (`updateCastagnoli` once `haveCastagnoli` is set and `tab` is
`castagnoliTable`; never the IEEE path; else `simpleUpdate`); `p` is only read, at any fraction, and
the table is read-only for good; `checkInitIEEE` changes nothing. Proved in
`Proof/hash/crc32/update.lean` (prove-etcdint3, 2026-11-21: until then the same statement of
`Update`, the trusted function, which now calls this one). Lean-first. (crc32-hooks2, 2026-11-22:
translated with its body, etcd-grove#14, until then trusted; hence the premise `isPkgInit
hash/crc32`, the package state its code reads.)
-/
module

public import Proof.hash.crc32.PkgInit

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
variable [hash.crc32.Assumptions]

/-- See the file header. -/
abbrev hash.crc32.update.spec : Prop :=
  ∀ (c : w32) (tab : Loc) (s : GoSlice) (bs : List w8) (dq : DFrac) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.hash.crc32 ∗ tab ↦□ hash.crc32.castagnoliTableArr ∗
      s ↦*{dq} bs }}
    (App (App (App (App (Val (@! hash.crc32.update)) (Val #c)) (Val #tab)) (Val #s)) (Val #b))
  {{ RET #(hash.crc32.crc32c c bs); s ↦*{dq} bs }}

end spec

end EtcdGrove
end Perennial
