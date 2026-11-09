/-
`n.spill()` (`node.go`): children first, then the node split into pages from `tx.allocate`, the parent's keys updated; frees the old page. Users: `Bucket.spill`.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Proof sketch** (verify-round, A11 F9). Children first (recursively); `splitIdx` pieces; per piece
`tx.allocate` (`freshPage` of the run in `C.bufs`, `Tx.allocate.spec`), `wtxCore_buf` lends the
buffer, `node.write` (`nodeWritable` from `freshPage`'s empty header, `wtxCore_keys`, the split's
count and size), `wtxCore_buf` takes it back; the parent's key `node.put` (a branch inode); the
old page `node.free`. The pieces stay cached with their parents' links: the represented data is
unchanged (`repKept`).
**Changes** (verify-round, A11 F9): `repKept` in the post (was: some cache).
-/
module

public import Spec.go_etcd_io.bbolt.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- (internal) the subtree written to fresh pages, or an error (an allocation's). -/
def node.spill.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (C : TxCore) (n : Loc) (N : NodeR),
  {{ wtxCore (GF := GF) tx γ C ∗ ⌜C.nodes n = some N⌝ }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"spill")) (Val #()))
  {{ (err : GoInterface), RET #err; ∃ C' : TxCore, wtxCore tx γ C' ∗ ⌜repKept C C' ∧ (err = GoInterface.nil → ∃ N', C'.nodes n = some N' ∧ N'.spilled = true)⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
