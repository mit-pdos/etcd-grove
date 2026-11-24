/- Lean-first (no Rocq counterpart).

# `net/rpcdriver`: the top-level robustness result, proved

`rpcdriver_robust`, stated in
`Net/Spec/github_com/mit_pdos/etcd_grove/examples/net/rpcdriver/TopLevelRobustness.lean`, through the
all-stable bridge with the main thread's token (`robust_of_distBootI`,
`Net/Statement/DistBridgeExts.lean`, at `netExts`). The start: the net protocol library's registry
(`netProto_alloc`), the rpc world's connection registry and the request ids' ghost map (`γid`), and
the server's two listeners' protocols (`rpcLisP_set`, from the addresses unset: an exact listener's
`lisUnset` is its address's, `addrUnset_lisUnset`). Each machine's boot: its command's first
initialization (`CmdBootLinked.lean`), then its `main` (`cmd/*/Main.lean`) over the linked specs.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.TopLevelRobustness
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Link
public import Net.Statement.DistBridge

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Robustness

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  GooseGlobalGS.gooseInvGS

section start
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netGF]

/-- At a valid address, the address unset is the listener at it unset (an exact listener; the
dsverify kits'). -/
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

theorem rpcdriver_robust : rpcdriver_robust.spec := by
  intro _ lctx sem srv_sem cli_sem field_sem _ σs σc g threads
  refine robust_of_distBootI (GF := netGF) rpcAddrs (system σs σc) g threads rpcStepBound
    (fun hg hl => ⟨extsInitgP_of_init ⟨net_init_compat, trivial⟩ hg,
      fun m hm => extsInitP_of_init ⟨net_init_compat, trivial⟩ (hl m hm)⟩) ?_
  intro G hrb
  iintro Hs
  sorry

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
