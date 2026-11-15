/-
`(*keyIndex).doCompact(atRev, available)` (`key_index.go:258`): the generation and revision index
compaction keeps from (`kiDoCompact`), the revision it keeps added to `available` (the walk's
closure). A read of the key index. Needs a generation and every generation but the last non-empty
(`kiWf`; index panics otherwise). Internal (`compact`, `keep`). **Changes**: over `availAt`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalIdx

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

/-- `ki.doCompact(atRev, available)`. -/
def keyIndex.doCompact.spec : Prop :=
  ∀ (p m : Loc) (k : GoString) (ki : KeyIndexM) (dq : DFrac) (atRev : w64) (A : Rev → Prop),
  {{ pkgInit ∗ ⌜ki.gens ≠ [] ∧ kiWf ki⌝ ∗ ownKi p k ki dq ∗ availAt m A }}
    (App (App (Val (p @!! go.GoType.PointerType keyIndex.ty @!! go!"doCompact")) (Val #atRev))
      (Val #m))
  {{ RET (PairV #(W64 ((kiDoCompact ki atRev).1 : Int)) #(W64 (kiDoCompact ki atRev).2.1));
      ownKi p k ki dq ∗ availAt m (compactAvail A ki atRev) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
