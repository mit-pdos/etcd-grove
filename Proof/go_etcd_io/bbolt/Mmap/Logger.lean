/-
`DB.Logger` and logging (U4, `notes/bbolt-proof-plan.md`): `db.Logger()` returns the database's
logger, which `dbFixed` (batch 15) says is a `boltLogger` (never nil: the option's, or bbolt's
`discardLogger`'s value, which `Open` stores), and `wp_boltLog`, a call of one of its methods
(`lg.Errorf(fmt, args...)`, ...) under `boltLogger`'s contract.
-/
module

public import Spec.go_etcd_io.bbolt.Logger
public import Proof.go_etcd_io.bbolt.PkgInit
public import Spec.fmt.Errorf
public import Proof.go_etcd_io.bbolt.Mmap.LoggerDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section logger
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit hos in
theorem DB.Logger.wp_proof : DB.Logger.spec (GF := GF) (hG := hG) := by
  intro db lg hdb
  wp_start as ⟨#Hl, #Hlg⟩
  cases lg with
  | nil => unfold boltLogger; iexfalso; iexact Hlg
  | ok li =>
    wp_auto
    rw [decide_eq_false hdb]
    wp_auto
    iapply HΦ
    itrivial

end logger

end bbolt
end EtcdGrove
end Perennial
