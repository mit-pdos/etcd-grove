/-
The proof of `Spec/.../mvcc/newKVHasher.lean`: `crc32.New(crc32.MakeTable(crc32.Castagnoli))`, the
`Key` bucket's name written to it (prove-etcdint3, 2026-11-21; until then an axiom).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newKVHasher
public import Spec.hash.crc32.MakeTable
public import Spec.hash.crc32.New
public import Spec.hash.crc32.digest__Write
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__Name

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.newKVHasher.wp_proof (hMT : hash.crc32.MakeTable.spec (GF := GF) (hG := hG))
    (hNew : hash.crc32.New.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hWrite : hash.crc32.digest.Write.spec (GF := GF) (hG := hG)) :
    mvcc.newKVHasher.spec (GF := GF) (hG := hG) := by
  intro prev rev keep
  wp_start
  wp_auto
  rw [show (W32 2197175160) = _root_.Perennial.hash.crc32.castagnoliPoly from rfl]
  ihave #Hc32 : isPkgInit (PROP := IProp GF) pkg_id.hash.crc32 $$ []
  · iPkgInit
  wp_apply hMT as %tab #Htab
  wp_apply hNew $$ [] as %d Hd
  · iframe #
  (try wp_auto)
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hsch
  icases Hsi with ⟨-, -, -, ⟨%b, #HKey, #HbIs⟩, -⟩
  iunfold go_etcd_io.etcd.server.v3.storage.schema.bucketIs at HbIs
  icases HbIs with ⟨%s, %Hb, #Hs⟩
  subst Hb
  wp_auto
  wp_apply hName
  wp_apply hWrite $$ [Hd Hs] as ⟨Hd, -⟩
  · iframe #; iframe
  wp_auto
  iapply HΦ
  isplitl [Hd]
  · iunfold mvcc.kvHasherOk
    iexists d, tab, _
    iframe Hd Htab
    ipureintro; rfl
  ipureintro; exact ⟨rfl, rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
