/- Visit the members of a bucket in the same frozen transaction the snapshot streams. -/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

abbrev backend.snapshot.UnsafeForEach.spec : Prop :=
  ∀ (sp tx : Loc) (γ : GName) (γd : DBNames) (q : Qp) (D : Data) (bk : GoInterface) (bi : BucketInfo)
    (fn : GoFunc) (I : Nat → IProp GF) (E : Nat → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      snapAt sp γ tx γd ∗ txLive tx γd q (bbolt.TxView.ro D) ∗ isBucket bk bi ∗ I 0 ∗
      □ (∀ (i : Nat) (e : Ent) (k v : GoSlice), ⌜(bktEnts (bktOf D bi.name))[i]? = some e⌝ →
          {{ I i ∗ txLive tx γd q (bbolt.TxView.ro D) ∗ ⌜k ≠ slice.nil⌝ ∗ txBytes tx γd k e.1 ∗ txBytes tx γd v e.2 }}
            (App (App (Val #fn) (Val #k)) (Val #v))
          {{ (err : GoInterface), RET #err; txLive tx γd q (bbolt.TxView.ro D) ∗
              ((⌜err = GoInterface.nil⌝ ∗ I (i + 1)) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ E i err)) }}) }}
    (App (App (Val (sp @!! go.GoType.PointerType snapshot.ty @!! go!"UnsafeForEach")) (Val #bk)) (Val #fn))
  {{ (err : GoInterface), RET #err; txLive tx γd q (bbolt.TxView.ro D) ∗
      ((⌜err = GoInterface.nil⌝ ∗ I (bktEnts (bktOf D bi.name)).length) ∨
       (∃ i : Nat, ⌜err ≠ GoInterface.nil ∧ i < (bktEnts (bktOf D bi.name)).length⌝ ∗
          E i err)) }}

end spec
end EtcdGrove
end Perennial
