/- Lean-first (no Rocq counterpart).

# `net/httpdriver`: the top-level robustness result, proved

`httpdriver_robust`, stated in
`Net/Spec/github_com/mit_pdos/etcd_grove/examples/net/httpdriver/TopLevelRobustness.lean`, through the
all-stable bridge with the main thread's token and `Robust`'s thread bound (`robust_of_distBootIT`,
`Net/Statement/DistBridgeExts.lean`, at `netExts`), as rpcdriver's. The start: the net protocol
library's registry (`netProto_alloc`), net/http's registry of connections (`HttpProtoGS`, its invariant
`httpRegInv`), and the server's listener's protocols (`protoLis addrS drvP`, from the address unset:
`lis_set_proto`). Each machine's boot: its command's first initialization (`CmdBootLinked.lean`, under the
environment premise), then its `main` (`cmd/*/Main.lean`) over the linked specs (`Link.lean`).
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.TopLevelRobustness
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.Link
public import Net.Statement.DistBridge

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Robustness EtcdGrove.httpdriver

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  GooseGlobalGS.gooseInvGS

section start
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netGF]

/-- At a valid address, the address unset is the listener at it unset (an exact listener; rpcdriver's). -/
theorem addrUnset_lisUnset (a : GoString) (h : addrOk a = true) :
    addrUnset (GF := netGF) a ⊢ lisUnset a := by
  have hl : PartialMap.get? (addrSpace ()) a = some () := by
    rw [gmap_get?_eq]; exact addrSpace_lookup_ok () h
  unfold addrUnset lisUnset
  have key : ∀ {k : GoString} {v : Unit}, PartialMap.get? (Std.delete (addrSpace ()) a) k = some v →
      (iprop(□ True) : IProp netGF) ⊢
        iprop(⌜lisAccepts a k⌝ → netPend (NG (Gg := G)) k ∅ ∗ netLisTok (NG (Gg := G)) k) := by
    intro k v hk
    iintro - %hacc
    have hk' : a = k := (lisAccepts_addrOk h).mp hacc
    subst hk'
    rw [gmap_get?_eq] at hk
    have : (GMap.delete a (addrSpace ())) !! a = none := GMap.lookup_delete _ _
    rw [show Std.delete (addrSpace ()) a = GMap.delete a (addrSpace ()) from rfl, this] at hk
    cases hk
  refine Entails.trans ?_ (BigSepM.bigSepM_delete hl).2
  iintro ⟨Hp, -, Ht⟩
  isplitl [Hp Ht]
  · iintro %_; iframe Hp Ht
  · iapply (BigSepM.bigSepM_intro key)
    imodintro; itrivial

end start

theorem httpdriver_robust : httpdriver_robust.spec := by
  intro _ lctx sem srv_sem cli_sem field_sem _ σs σc g HEnv
  refine robust_of_distBootIT (GF := netGF) httpAddrs (system σs σc) g httpThreads httpSteps
    (fun hg hl => ⟨extsInitgP_of_init ⟨net_init_compat, trivial⟩ hg,
      fun m hm => extsInitP_of_init ⟨net_init_compat, trivial⟩ (hl m hm)⟩) ?_
  intro G hrb
  iintro Hs
  unfold httpAddrs
  rw [show (go!"127.0.0.1:7401" : GoString) = addrS from rfl]
  icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨Ha, -⟩
  ihave Hla := addrUnset_lisUnset addrS (by decide) $$ Ha
  imod netProto_alloc ⊤ with ⟨%π, #Hreg⟩
  imod ghost_map_alloc_empty (GF := netGF) (K := Nat) (V := GName) with ⟨%γr, Hm⟩
  let hπ : net.http.HttpProtoGS := ⟨γr⟩
  imod inv_alloc net.http.httpRegN ⊤ (net.http.httpRegInv (Gg := G) (hπ := hπ)) $$ [Hm] with #HregH
  · inext
    unfold net.http.httpRegInv
    iexists ∅
    iframe Hm
    iapply BigSepM.bigSepM_empty.2; iempintro
  imod lis_set_proto ⊤ addrS (net.http.httpReqP (Gg := G) (hπ := hπ) drvP)
    (net.http.httpRespP (Gg := G) (hπ := hπ) drvP) (by decide) $$ Hreg Hla with #Hlp
  ihave #Hpl : net.http.protoLis (Gg := G) (hπ := hπ) addrS drvP $$ []
  · unfold net.http.protoLis; iframe Hlp HregH
  imodintro
  iexists fun _ => iprop(net.http.protoLis (Gg := G) (hπ := hπ) addrS drvP)
  isplitr
  · ipureintro
    intro i m hm hG hGG hctx hrb' hT
    obtain ⟨G', L⟩ := hG
    dsimp only at hGG hctx
    subst hGG hctx
    letI hG : HeapGS .hasLC netGF := ⟨G', L⟩
    have hTb : threadBound netGF ≤ 2 ^ 30 := by unfold httpThreads at hT; omega
    match i, hm with
    | 0, hm =>
      cases hm
      iintro #Hpl - Hgs Htok
      imodintro
      unfold boot_server boot
      wp_apply cmd.server.wp_boot HEnv $$ Hgs as ⟨Hown, #Hpkg, #Hres⟩
      try wp_auto
      wp_apply (cmd.server.wp_main (hπ := hπ) wp_Server) $$ []
      · iframe Hres Hpl
        ipureintro; exact hTb
      try wp_auto
      itrivial
    | 1, hm =>
      cases hm
      iintro #Hpl - Hgs Htok
      imodintro
      unfold boot_client boot
      wp_apply cmd.client.wp_boot HEnv $$ Hgs as ⟨Hown, #Hpkg, #Hres⟩
      try wp_auto
      ihave #Hda : drvAddr (GF := netGF) (hπ := hπ) $$ []
      · iunfold drvAddr
        iunfold net.http.protoLis at Hpl
        icases Hpl with ⟨#Hl, #Hr⟩
        iframe Hr
        iapply lisProto_addr addrS addrS _ _ (by decide) ((lisAccepts_addrOk (by decide)).2 rfl) $$ Hl
      wp_apply (cmd.client.wp_main (hπ := hπ) wp_Client) $$ [Htok] as Htok
      · iframe Hres Hda Htok
        ipureintro; exact hTb
      try wp_auto
      itrivial
  · simp only [system]
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iexact Hpl
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iexact Hpl
    iapply BigSepL.bigSepL_nil.2
    iempintro

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial

#print axioms Perennial.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.httpdriver_robust
