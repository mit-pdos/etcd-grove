/-
Port of `election_proof/proof_lockedRand__Intn.v`.
-/
module

public import Spec.go_etcd_io.raft.v3.lockedRand__Intn
public import Spec.math.big.NewInt
public import Spec.crypto.rand.Int
public import Spec.math.big.Int__Int64

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Straight-line: lock, build the bound, draw, unlock, read back. The `if err != nil
{ panic }` is folded away by `rand.Int.spec`'s `#interface.nil` return, which is
the point of stating that triple for the package's own `Reader`. The two `Convert`s
(`int` to `int64` and back) are identities on `w64`. -/
theorem lockedRand.Intn.wp_proof
    (wp_big_NewInt : big.NewInt.spec (GF := GF) (hG := hG))
    (wp_rand_Int : rand.Int.spec (GF := GF) (hG := hG))
    (wp_big_Int_Int64 : big.Int.Int64.spec (GF := GF) (hG := hG)) :
    lockedRand.Intn.spec (GF := GF) (hG := hG) := by
  intro lr n Hn
  wp_start as #Hlr
  unfold isLockedRand at *
  iNamed Hlr
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, -⟩
  ihave #Hrand : isPkgInit (PROP := IProp GF) pkg_id.crypto.rand $$ []
  · iPkgInit
  ihave #Hreader := crypto.rand.isInitialized_access $$ Hrand
  unfold crypto.rand.isInitialized
  icases Hreader with ⟨%rdr, #Reader⟩
  wp_auto
  wp_apply wp_big_NewInt as %max Hmax
  wp_apply wp_rand_Int _ _ _ ⟨Hn, by have := word.signed_range n; omega⟩ $$ [$Reader $Hmax] as %v %z ⟨Hmax, Hv, %Hz⟩
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked]
  · itrivial
  wp_apply wp_big_Int_Int64 _ _ (by have := word.signed_range n; omega) $$ [$Hv] as Hv
  iapply HΦ
  ipureintro
  word

end proof

end EtcdGrove
end Perennial
