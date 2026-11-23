/-
The proof of `Serve` (`Net/Spec/.../lib/remote/Serve.lean`): `listen` (the node's listener at
`a`), then a loop that never exits, its invariant the listener (`netLis`) and `tok sys`: each
`Accept` (its update `accept_au`, from `a`'s protocols `svcAddr`: a failure gives the listener
back, a connection the listener and the acceptor's end's tokens and fresh token), then
`serveConn` on the connection accepted.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.listen
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.serveConn
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Serve
public import Net.Spec.net.Listener__Accept
public import Net.Proof.net.AtAddr

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable {I O : Type} [Pos.Countable I] [Pos.Countable O]

theorem Serve.wp_proof
    (wp_listen : listen.spec (GF := GF) (hG := hG) (I := I) (O := O))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_serveConn : serveConn.spec (GF := GF) (hG := hG) (I := I) (O := O)) :
    Serve.spec (GF := GF) (hG := hG) (I := I) (O := O) := by
  intro S a sys op cd d tok
  wp_start as ⟨#Haddr, #Hcd, #Hop, Htok⟩
  wp_auto
  wp_apply wp_listen S a $$ [] as %li ⟨%l, #Hli, Hlis, #Hla⟩
  · iframe Haddr
  unfold net.isListener
  icases Hli with ⟨%t, %x, %Ht, #Hlt⟩
  subst Ht
  (try wp_auto)
  ihave HI : ("Hlis" ∷ netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true ∗
      "Htok" ∷ tok sys : IProp GF) $$ [Hlis Htok]
  · iframe Hlis Htok
  wp_for HI
  wp_apply (net.Listener.Accept.spec_addrOk wp_Accept) t l x a
      (fun _ => netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true)
      (fun cn => iprop(netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true ∗
        connEnd (Gg := hG.goose_globalGS) cn true (repP (Gg := hG.goose_globalGS) S)
          (reqP (Gg := hG.goose_globalGS) S) [] [] ∗ connFresh (Gg := hG.goose_globalGS) cn true))
      $$ [Hlis]
    as %c %err (⟨%Herr, %cn, #Hc, Hlis, Hend, Hfresh⟩ | ⟨%k, Hlis, #Herr⟩)
  · iframe Hlt Hla
    iunfold svcAddr at Haddr
    iapply accept_au a (reqP S) (repP S) _ l true $$ Haddr Hlis
  · -- a connection: serve it
    subst Herr
    wp_auto
    -- `wp_apply wp_serveConn …` (and `wp_apply_core`) fails here, inside the loop, in its
    -- post-processing (`wp_apply_post`): "unknown free variable" (`tok`), which plain `wp_apply`
    -- turns into a silent `sorry`; `wp_apply_raw` and the steps after it by hand do not.
    ihave #Hsc := wp_serveConn S c cn a sys op cd d tok
    wp_apply_raw Hsc $$ [Hend Hfresh Htok]
    · iframe Hpkg Hc Hend Hfresh Hcd Hop Htok
    inext
    iintro Htok
    wp_auto
    wp_for_post
    iframe
    isplitl [Hlis]
    · iexact Hlis
    · iexact Htok
  · -- a failure, of either kind: go on
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Herr'
    obtain ⟨pe, rfl⟩ := Herr'.2 (by simp)
    wp_auto
    wp_for_post
    iframe
    isplitl [Hlis]
    · iexact Hlis
    · iexact Htok

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
