/-
Port of `election_proof/election.v` (and the `link_*.v` files): every proof
instantiated with its callees' results, and the results of the development.

`#print axioms` on a result is its trust base: `axiom`s are the trust boundary
(`Proof/<fn>.lean` of a function outside the scope), `sorryAx` is unfinished work.
-/
import EtcdGrove.Raft.ElectionProof.Proof.big_NewInt
import EtcdGrove.Raft.ElectionProof.Proof.big_Int__Int64
import EtcdGrove.Raft.ElectionProof.Proof.rand_Int
import EtcdGrove.Raft.ElectionProof.Proof.lockedRand__Intn
import EtcdGrove.Raft.ElectionProof.Proof.voteRespMsgType

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section links
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem big.wp_NewInt : big.NewInt.spec (GF := GF) (hG := hG) := big.NewInt.wp_proof
theorem big.Int.wp_Int64 : big.Int.Int64.spec (GF := GF) (hG := hG) := big.Int.Int64.wp_proof
theorem rand.wp_Int : rand.Int.spec (GF := GF) (hG := hG) := rand.Int.wp_proof
theorem lockedRand.wp_Intn : lockedRand.Intn.spec (GF := GF) (hG := hG) :=
  lockedRand.Intn.wp_proof big.wp_NewInt rand.wp_Int big.Int.wp_Int64
theorem wp_voteRespMsgType : voteRespMsgType.spec (GF := GF) (hG := hG) :=
  voteRespMsgType.wp_proof

end links

end EtcdGrove
end Perennial
