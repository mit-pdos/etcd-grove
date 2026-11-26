/-
`DB.validMetaOverPages` (bbolt, internal; the fork's 2c660ee, W6): whether the meta in page `i` of a
buffer validates and the pages it names lie in the buffer with their flags, `DB.needsInit`'s test that
a file of `init`'s bytes and zeros is a database, not an interrupted `init`. Proof:
`Proof/go_etcd_io/bbolt/DB__validMetaOverPages.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Proof.go_etcd_io.bbolt.Model.Meta

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section defs
variable [GooseExts]

/-- **A valid meta over the pages it names** (4096-byte pages of `B`): the meta in page `i` lies in
`B` and validates; the freelist page it names, if any, lies in `B` with the freelist flag and its own
id; its root page lies in `B` with a leaf or a branch flag. -/
def metaOverPages (B : List w8) (i : Nat) : Prop :=
  i < B.length / 4096 ∧ metaValid (metaOf (bytesAt B (4096 * i) 4096)) ∧
  (∀ f, metaFlpg (metaOf (bytesAt B (4096 * i) 4096)) = some f →
    f < B.length / 4096 ∧ pageFlags (bytesAt B (4096 * f) 4096) = freelistPageFlag ∧
    pageId (bytesAt B (4096 * f) 4096) = f) ∧
  (metaOf (bytesAt B (4096 * i) 4096)).root'.root'.toNat < B.length / 4096 ∧
  (pageFlags (bytesAt B (4096 * (metaOf (bytesAt B (4096 * i) 4096)).root'.root'.toNat) 4096) =
      leafPageFlag ∨
    pageFlags (bytesAt B (4096 * (metaOf (bytesAt B (4096 * i) 4096)).root'.root'.toNat) 4096) =
      branchPageFlag)

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`db.validMetaOverPages(data, i)`**, the buffer `data` holding `B` (persistent: `needsInit`'s,
read whole), the page size `4096` at any fraction (`Open`'s owned phase): `false` only if the meta in
page `i` is not a valid meta over the pages it names (`metaOverPages`). -/
abbrev DB.validMetaOverPages.spec : Prop :=
  ∀ (db : Loc) (sl : GoSlice) (B : List w8) (dqp : DFrac) (i : Nat),
  i < 2 → B.length < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ db.[DB, go!"pageSize"] ↦{dqp} W64 4096 ∗
      sl ↦*□ B }}
    (App (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"validMetaOverPages")) (Val #sl))
      (Val #(W64 (i : Int))))
  {{ (r : Bool), RET #r; db.[DB, go!"pageSize"] ↦{dqp} W64 4096 ∗ ⌜r = false → ¬ metaOverPages B i⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
