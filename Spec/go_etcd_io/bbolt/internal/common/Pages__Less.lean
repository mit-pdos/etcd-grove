/-
## `Pages.Less(i, j)` (`internal/common/page.go`)

**Users.** tx.go:535 (`Tx.write`'s sort of its dirty pages by id).
**Proof sketch.** two loads of the pointers, two header loads (`Page.Id`'s view).
**Changes.** new.
**Margin.** none: the post is what the code computes.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace BboltCommon

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `s.Less(i, j)` over pages whose bytes are `bss`: whether page `i`'s id is below page `j`'s. -/
def Pages.Less.spec : Prop :=
  ∀ (s : GoSlice) (ps : List Loc) (bss : List (List w8)) (dq dqp : DFrac) (i j : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ s ↦*{dq} ps ∗ ([∗list] p;bs ∈ ps;bss, bytesPointsto p dqp bs) ∗
      ⌜sint.nat i < ps.length ∧ sint.nat j < ps.length ∧ 0 ≤ sint.Z i ∧ 0 ≤ sint.Z j ∧
        ∀ bs ∈ bss, pageHeaderSize ≤ bs.length⌝ }}
    (App (App (Val (s @!! go_etcd_io.bbolt.internal.common.Pages.ty @!! go!"Less")) (Val #i)) (Val #j))
  {{ RET #(decide (uint.Z (hdrOf bss[sint.nat i]!).id' < uint.Z (hdrOf bss[sint.nat j]!).id'));
      s ↦*{dq} ps ∗ ([∗list] p;bs ∈ ps;bss, bytesPointsto p dqp bs) }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
