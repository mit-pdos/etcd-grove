/-
The proof of `Spec/.../mvcc/kvHasher__Hash.lean`: `KeyValueHash{h.hash.Sum32(), ...}`, the digest's
`Sum32` (prove-etcdint3, 2026-11-21; until then an axiom).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.kvHasher__Hash
public import Spec.hash.crc32.digest__Sum32

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

theorem mvcc.kvHasher.Hash.wp_proof (hSum : hash.crc32.digest.Sum32.spec (GF := GF) (hG := hG)) :
    mvcc.kvHasher.Hash.spec (GF := GF) (hG := hG) := by
  intro hp h
  wp_start as ⟨Hh, Hok⟩
  iunfold mvcc.kvHasherOk at Hok
  icases Hok with ⟨%d, %tab, %c, %Hhash, Hd, #Ht⟩
  wp_auto
  rw [Hhash]
  wp_auto
  wp_apply hSum $$ Hd as Hd
  iapply HΦ
  iframe Hh
  iunfold mvcc.kvHasherOk
  iexists d, tab, c
  iframe Hd Ht
  ipureintro; exact Hhash

end proof

end EtcdGrove
end Perennial
