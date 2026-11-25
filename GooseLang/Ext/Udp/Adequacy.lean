/-
The crash interpretation of the UDP extension, for a program whose closed list of extensions has
`udpExt` (with others: the list and its ghost state are the program's, as kvraft's `NetFs`).

**A crash** keeps the network's ghost state, as the network itself (it is global). A node's local
ghost state after a crash (`udp_crash_interp`) has the same universal camera and a fresh ghost map
of sockets, empty, as the crash leaves the node with no socket (`Impl.lean`'s `crash`, U7);
`crashStart` gives nothing.
-/
module

public import Perennial.GooseLang.DistAdequacy
public import GooseLang.Ext.Udp.Specs

@[expose] public section

noncomputable section

namespace Perennial
namespace Udp

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- A crash: the node's sockets' ghost map made anew (empty). -/
instance udp_crash_interp : ExtCrashInterp udpExt where
  crashStart _ _ := iprop(emp)
  local_crash _ _ hL σ σ' h := by
    obtain rfl := (show σ' = { σ with socks := ∅ } from h)
    letI := hL.allG
    unfold ExtInterp.localCtx udp_interp udpLocalCtx
    simp only
    iintro -
    imod ghost_map_alloc_empty (K := w64) (V := GoString) with ⟨%γ, H⟩
    imodintro
    iexists (⟨hL.allG, γ⟩ : UdpLocalGS _)
    iframe H

end Udp
end Perennial
