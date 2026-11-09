/-
`(*keyIndex).findGeneration(rev)` (`key_index.go:300`): a pointer into the key index's generations
(`kiFindGen`), or `nil`. A read; the generation lent back to the key index. Internal (`get`).
**Changes**: the generation's points-to lent (`ownGenAt`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalIdx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc

/-- `ki.findGeneration(rev)`. -/
def keyIndex.findGeneration.spec : Prop :=
  ∀ (p : Loc) (k : GoString) (ki : KeyIndexM) (dq : DFrac) (rev : w64),
  {{ pkgInit ∗ ownKi p k ki dq }}
    (App (Val (p @!! go.GoType.PointerType keyIndex.ty @!! go!"findGeneration")) (Val #rev))
  {{ (g : Loc), RET #g;
      (⌜kiFindGen ki rev = none ∧ g = null⌝ ∗ ownKi p k ki dq) ∨
      (∃ (i : Nat) (gn : Gen), ⌜kiFindGen ki rev = some i ∧ ki.gens[i]? = some gn ∧ g ≠ null⌝ ∗
        ownGenAt g gn dq ∗ (ownGenAt g gn dq -∗ ownKi p k ki dq)) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
