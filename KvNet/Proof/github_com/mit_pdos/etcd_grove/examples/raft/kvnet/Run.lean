/-
The proof of `KvNet/Spec/.../kvnet/Run.lean`: `listen`, `StartNode`, then `Node.accept` (2026-11-24, G5: the accept loop over
`Listener.Accept` (its update from the address's protocols, `accept_au`), each connection served by a
forked `Node.serve`, a failed `Accept` followed by `time.Sleep`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Run
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.StartNode
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.listen
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node__accept

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

theorem Run.wp_proof (F : KvFacts GF) (rep : Loc → w64 → IProp GF)
    (cf : GoInterface → List w8 → IProp GF) (stp : NodeStopper GF)
    (S : w64 → GoString → github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Options → GMap w64 GoString → IProp GF)
    (wp_listen : listen.spec (GF := GF) (hG := hG))
    (wp_StartNode : StartNode.spec (GF := GF) (hG := hG) F rep cf stp S)
    (wp_accept : Node.accept.spec (GF := GF) (hG := hG) F rep stp cf) :
    Run.spec (GF := GF) (hG := hG) F rep cf S := by
  intro cfg M a eof ed Hma
  wp_start as ⟨#HM, #Ha, HS, #Heof, #Hed, #Hcc⟩
  try wp_auto
  wp_apply (wp_map_lookup1 (K := w64) (V := GoString) go.uint64 go.string _ M cfg.ID' DFrac.discard)
    $$ HM as -
  rw [Hma]
  simp only [Option.getD_some]
  try wp_auto
  wp_apply wp_listen a (kvP F cfg.ID') (kvQ F cfg.ID') $$ [$Hpkg $Ha] as %li ⟨%l, #Hli, Hlis, #Hla⟩
  try wp_auto
  wp_apply wp_StartNode cfg M $$ [$Hpkg $HM $HS] as %nd ⟨%γ, %N, #Hnd, #Hcl⟩
  try wp_auto
  wp_apply wp_accept nd γ N cfg.ID' li l a eof ed $$ [$Hpkg $Hnd $Hcl $Ha $Hli $Hlis $Hla $Heof $Hed $Hcc]
  try wp_auto
  iapply HΦ
  itrivial

end proof

end raft_kvnet
end EtcdGrove
end Perennial
