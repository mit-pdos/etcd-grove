/-
The proof of `KvRaft/Spec/.../kvraft/Node__accept.lean` (2026-11-24, G5; `Run`'s loop until then):
each connection the listener accepts is served in a goroutine of its own (`Node.serve`); a failed
`Accept` sleeps and retries.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Node__accept
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Node__serve
public import KvRaft.Spec.net.Listener__Accept
public import Perennial.Proof.time.Link
public import KvRaft.Proof.net.AtAddr

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]
theorem Node.accept.wp_proof (F : KvFacts GF) (rep : Loc → w64 → IProp GF) (stp : NodeStopper GF)
    (cf : GoInterface → List w8 → IProp GF)
    (wp_serve : Node.serve.spec (GF := GF) (hG := hG) F rep stp cf)
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG)) :
    Node.accept.spec (GF := GF) (hG := hG) F rep stp cf := by
  intro nd γ N id li l a eof ed
  wp_start as ⟨#Hnd, #Hcl, #Ha, #Hli, Hlis, #Hla, #Heof, #Hed, #Hcc⟩
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
        connEnd cn true (kvQ F id) (kvP F id) [] [] ∗ connFresh cn true)) $$ [Hlis]
    as %c %err (⟨%Herr, %cn, #Hc, Hlis, Hce, -⟩ | ⟨%k, Hlis, #HE⟩)
  · iframe Hlt Hla
    iapply accept_au a (kvP F id) (kvQ F id) _ l true $$ Ha Hlis
  · -- a connection: served in a goroutine of its own
    subst Herr
    try wp_auto
    wp_apply wp_fork $$ [Hce]
    · wp_apply wp_serve nd γ N id c cn a eof ed $$ [$Hpkg $Hnd $Hcl $Hc $Heof $Hed $Hcc $Hce]
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

end kvraft
end EtcdGrove
end Perennial
