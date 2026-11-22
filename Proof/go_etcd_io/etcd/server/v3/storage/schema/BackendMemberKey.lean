/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/schema/BackendMemberKey.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.BackendMemberKey
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.BackendMemberKey.wp_proof
    (hS : types.ID.String_ptr.spec (GF := GF) (hG := hG)) :
    schema.BackendMemberKey.spec (GF := GF) (hG := hG) := by
  intro id
  wp_start
  ihave #Htypes : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  wp_auto
  wp_apply hS $$ [$Htypes $id] as %s ⟨-, %Hs⟩
  subst Hs
  (try wp_auto)
  wp_apply wp_string_to_bytes (types.idStr id) as %sl ⟨Hsl, -⟩
  iapply HΦ
  iexact Hsl

end proof

end EtcdGrove
end Perennial
