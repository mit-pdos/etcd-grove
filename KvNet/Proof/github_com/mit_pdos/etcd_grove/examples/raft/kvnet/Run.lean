/-
The proof of `KvNet/Spec/.../kvnet/Run.lean`: `listen`, `StartNode`, then the accept loop over
`Listener.Accept` (its update from the address's protocols, `accept_au`), each connection served by a
forked `Node.serve`, a failed `Accept` followed by `time.Sleep`.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Run
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.StartNode
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.listen
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Node__serve
public import KvNet.Spec.net.Listener__Accept
public import Perennial.Proof.time.Link
public import KvNet.Proof.net.AtAddr

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
variable [package_sem' : net.Assumptions]

theorem Run.wp_proof (F : KvFacts GF) (rep : Loc → w64 → IProp GF)
    (cf : GoInterface → List w8 → IProp GF)
    (S : w64 → GoString → github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Options → GMap w64 GoString → IProp GF)
    (wp_listen : listen.spec (GF := GF) (hG := hG))
    (wp_StartNode : StartNode.spec (GF := GF) (hG := hG) F rep cf S)
    (wp_serve : Node.serve.spec (GF := GF) (hG := hG) F rep cf)
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG)) :
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
  wp_apply wp_StartNode cfg M $$ [$Hpkg $HM $HS] as %nd ⟨%γ, %N, %n, #Hnd, #Hcl⟩
  try wp_auto
  unfold net.isListener
  icases Hli with ⟨%t, %xl, %Ht, #Hlt⟩
  subst Ht
  try wp_auto
  ihave HI : ("Hlis" ∷ netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true :
    IProp GF) $$ [Hlis]
  · iexact Hlis
  wp_for HI
  wp_apply (net.Listener.Accept.spec_addrOk wp_Accept) t l xl a
      (fun _ => netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true)
      (fun cn => iprop(netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true ∗
        connEnd cn true (kvQ F cfg.ID') (kvP F cfg.ID') [] [] ∗ connFresh cn true)) $$ [Hlis]
    as %c %err (⟨%Herr, %cn, #Hc, Hlis, Hce, -⟩ | ⟨%k, Hlis, #HE⟩)
  · iframe Hlt Hla
    iapply accept_au a (kvP F cfg.ID') (kvQ F cfg.ID') _ l true $$ Ha Hlis
  · -- a connection: served in a goroutine of its own
    subst Herr
    try wp_auto
    wp_apply wp_fork $$ [Hce]
    · wp_apply wp_serve nd γ N cfg.ID' n c cn a eof ed $$ [$Hpkg $Hnd $Hcl $Hc $Heof $Hed $Hcc $Hce]
      itrivial
    try wp_auto
    wp_for_post
    iframe
  · -- a failure: wait, then go on
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    try wp_auto
    wp_apply time.wp_Sleep
    try wp_auto
    wp_for_post
    iframe

end proof

end raft_kvnet
end EtcdGrove
end Perennial
