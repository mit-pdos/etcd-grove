/-
The closed list of extensions of a networked program over TCP (`[tcpExt]`, `tcpExts`), its
semantics, ghost state and crash interpretation, and ghost state `tcpGF` for it: what a
distributed program's adequacy theorem (`goose_dist_crash_adequacy`, Perennial's
`DistAdequacy.lean`) is instantiated with.

**A crash** keeps the network's ghost state, as the network itself (it is global). A node's
local ghost state after a crash (`tcp_crash_interp`) has the same host and universal camera and
fresh ghost maps of listeners and of their addresses, empty, as the crash leaves the node's listeners
(`Impl.lean`'s `crash`); `crashStart` says the host is kept.

**Start resources**: the network's (`tcpStart`: the plan's persistent entries and every plan
address's pending set, empty), and a node's host and listeners (none, for a node that starts with
none).
-/
module

public import Perennial.GooseLang.DistAdequacy
public import GooseLang.Ext.Tcp.Specs

@[expose] public section

noncomputable section

namespace Perennial
namespace Tcp

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- A crash: the node's listeners' ghost map made anew (empty), the host kept. -/
instance tcp_crash_interp : ExtCrashInterp tcpExt where
  crashStart hL hL' := iprop(⌜hL'.host = hL.host⌝)
  local_crash _ _ hL σ σ' h := by
    obtain rfl := (show σ' = { σ with lis := ∅ } from h)
    letI := hL.allG
    unfold ExtInterp.localCtx tcp_interp tcpLocalCtx
    simp only
    iintro ⟨%Hhost, -⟩
    imod ghost_map_alloc_empty (K := w64) (V := GoString × Bool) with ⟨%γ, H⟩
    imod ghost_map_alloc_empty (K := w64) (V := GoString) with ⟨%γa, Ha⟩
    imodintro
    iexists (⟨hL.allG, hL.host, γ, γa⟩ : TcpLocalGS _)
    have he : lisAddrs (∅ : GMap w64 (GoString × Bool)) = ∅ := by
      apply GMap.ext; intro k; unfold lisAddrs; rw [GMap.lookup_fmap]; rfl
    simp only
    rw [he]
    iframe H Ha
    ipureintro
    exact Hhost

/-- The extensions of a networked program over TCP. -/
@[reducible] def tcpExts : GooseExts := ⟨[tcpExt]⟩

attribute [local instance] tcpExts

@[reducible] def tcpExtsSemantics : GooseSemantics := ⟨(tcp_semantics, ⟨⟩)⟩

@[reducible] def tcpExtsInterp : GooseInterp := ⟨(tcp_interp, ⟨⟩)⟩

attribute [local instance] tcpExtsSemantics tcpExtsInterp

@[reducible] def tcpExtsCrashInterp : GooseCrashInterp := ⟨(tcp_crash_interp, ⟨⟩)⟩

attribute [local instance] tcpExtsCrashInterp

set_option linter.defProp false in
@[reducible] def tcpExts_hasTcp : HasExt tcpExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

attribute [local instance] tcpExts_hasTcp

/-- Ghost state for a networked program over TCP: one slot for each camera that `GooseGpreS`
needs for `[tcpExt]` (the extension needs only the universal camera, `AllG`, at slot 0), so that a
client's adequacy theorem need not assume any. -/
noncomputable def tcpGF : BundledGFunctors := fun
  | 0 => ⟨AllURF, inferInstance⟩
  | 1 => ⟨InvMapF, inferInstance⟩
  | 2 => ⟨constOF CoPsetDisjL, inferInstance⟩
  | 3 => ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  | 4 => ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  | 5 => ⟨constOF (NaHeapUR Loc val), inferInstance⟩
  | 6 => ⟨constOF (HeapView proph_id (Agree (DiscreteO (List val))) (GMap proph_id)), inferInstance⟩
  | 7 => ⟨GhostVarF (GMap GoString Bool), inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

noncomputable instance tcpGpreS : GooseGpreS tcpGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨allGOfSlot 0 rfl⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := allGOfSlot 0 rfl

section start
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The global start resources of `[tcpExt]`: the plan and the pending sets. -/
theorem tcp_globalStart [G : GooseGlobalGS .hasLC GF] (g : ExtsGlobalState exts) :
    extsGlobalStart (GF := GF) g ⊢ tcpStart (extGlobalGS tcpExt) (extGlobal tcpExt g) :=
  sep_elim_left

/-- The local start resources of `[tcpExt]` for a node: its host and its listeners. -/
theorem tcp_localStart [L : GooseLocalGS GF] (σ : ExtsLocalState exts) :
    extsLocalStart (GF := GF) σ ⊢ lisStart (extLocalGS tcpExt (L := L)) (extLocal tcpExt σ) :=
  sep_elim_left

/-- The crash resources of `[tcpExt]`: the new generation's host is the old one's. -/
theorem tcp_crashStart (L L' : GooseLocalGS GF) :
    extsCrashStart (GF := GF) L L' ⊢
      ⌜(extLocalGS tcpExt (L := L')).host = (extLocalGS tcpExt (L := L)).host⌝ :=
  sep_elim_left

end start

end Tcp
end Perennial
