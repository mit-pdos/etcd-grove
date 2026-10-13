/-
Proof of the spec of the same name (the mvcc store's compaction, unit 5c): the meta key's
`UnsafePut`, the compaction's clause of the batch transaction's contract.
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeSetFinishedCompact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewRevBytes
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.RevToBytes

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.UnsafeSetFinishedCompact.wp_proof
    (h0 : mvcc.NewRevBytes.spec (GF := GF) (hG := hG))
    (h1 : mvcc.RevToBytes.spec (GF := GF) (hG := hG)) :
    mvcc.UnsafeSetFinishedCompact.spec (GF := GF) (hG := hG) := by
  intro bt View Del W Dep Locked P f l value Hv
  wp_start as ⟨#Hbt, Hl⟩
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨%skn, #Hskn, #Hsknv⟩, -⟩
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hsch
  icases Hsi with ⟨⟨%bM, #HMetaG, -⟩, -⟩
  iunfold mvcc.batchTxSpec at Hbt
  iunfold mvcc.batchTxSpecG at Hbt
  icases Hbt with ⟨-, -, -, -, -, -, -, -, #HPut⟩
  ihave #HPut' := HPut $$ []
  · ipureintro; trivial
  (try wp_auto)
  wp_apply h0 as %rb ⟨Hrb, Hrbcap, -⟩
  (try wp_auto)
  wp_apply (h1 _ rb (List.replicate 17 (W8 0)) (Or.inl List.length_replicate)) $$ [$Hrb $Hrbcap]
    as %rb' ⟨Hrb, Hrbcap⟩
  (try wp_auto)
  rw [List.drop_of_length_le (by simp), List.append_nil]
  wp_bind (App (App (App (Val #(methods bt.ty _ bt.v)) (Val #bM)) (Val #skn)) (Val #rb'))
  ihave #HP2 := HPut' $$ %l %bM %skn %rb' %mvcc.finKeyBytes
    %(mvcc.revBytes (mvcc.revOf { Main' := value, Sub' := 0 }) false) %DFrac.discard %(DFrac.own 1) []
  · ipureintro
    exact ⟨Or.inr rfl, value, Hv, rfl⟩
  iapply HP2 $$ [Hl Hrb]
  · iframe HMetaG Hl Hrb
    unfold mvcc.finKeyBytes
    iexact Hsknv
  inext
  iintro ⟨Hl, -, -⟩
  (try wp_auto)
  iapply HΦ
  iexact Hl


end proof

end EtcdGrove
end Perennial
