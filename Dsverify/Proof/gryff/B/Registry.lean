/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/B/Registry.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit B3: the registry's facts `connectRes` needs (hub request B3-R1): from the deployment's
invariant (`deployInv`, which holds every registered node's id) and the replica's registration
(`registeredAs`: the registry holds `nodes`, all three), each replica address of `nodes` has its
registration index as port id (`portId`), its protocols, and the replicas below `kr` are dialed
by `kr` (`peerRole`).
-/
module

public import Dsverify.Proof.gryff.Server.SpecsDefs
public import Dsverify.Proof.gryff.WS.Ports
public import Dsverify.Proof.gryff.Replica2.State
public import Dsverify.Proof.gryff.Shares
public import GooseLang.Ext.Net.Decide

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.unitB

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open replica2 (rid32)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]

theorem addrOf_mem (k : Nat) (hk : k < 3) :
    addrOf k ∈ replicaAddrs ∧ addrOf k = portAddr k := by
  rcases k with _ | _ | _ | k
  · exact ⟨by decide, rfl⟩
  · exact ⟨by decide, rfl⟩
  · exact ⟨by decide, rfl⟩
  · omega

/-- Replica port `k` is a valid address its wildcard listener takes. -/
theorem portAddr_lis_ok (k : Nat) (hk : k < 3) :
    addrOk (portAddr k) = true ∧ lisAccepts (lisAddrOf (portAddr k)) (portAddr k) := by
  rcases k with _ | _ | _ | k
  · exact ⟨by decide, lisAcceptsB_iff.1 (by decide)⟩
  · exact ⟨by decide, lisAcceptsB_iff.1 (by decide)⟩
  · exact ⟨by decide, lisAcceptsB_iff.1 (by decide)⟩
  · omega

/-- Replica port `k`'s protocols, from its listener's (`Shares.replicaLis`). -/
theorem replicaLis_addr (γ : GryffNames GF) (k : Nat) (hk : k < 3) :
    replicaLis γ k ⊢ addrProto (portAddr k) (gryffWireP γ (portAddr k)) (gryffWireQ γ (portAddr k)) := by
  obtain ⟨hok, hacc⟩ := portAddr_lis_ok k hk
  unfold replicaLis
  exact lisProto_addr _ _ _ _ hok hacc

/-- See the file header. Port: the protocols come from the replica listeners' `lisProto`
(`Shares.replicaLis`, set by the start), not the lab's per-address `addrProtoG`. -/
theorem registry_ports (γ : GryffNames GF) (k : Nat) (id : w64) (nodes : List GoString)
    (kr : Fin 3) :
    inv deployN (deployInv γ.deploy γ.proto) ∗ registeredAs γ k id nodes ∗
        □ ([∗list] j ∈ [0, 1, 2], replicaLis γ j) ⊢
      |={⊤}=> ([∗list] i ↦ a ∈ nodes, portId γ a (W32 i) ∗
          addrProto a (gryffWireP γ a) (gryffWireQ γ a) ∗ ⌜a ∈ replicaAddrs⌝) ∗
        ([∗list] i ↦ a ∈ nodes, ⌜i < kr.val⌝ -∗ peerRole γ a (rid32 kr)) := by
  iintro ⟨#Hinv, #Hreg, #Hlis⟩
  icases registeredAs_preds γ k id nodes $$ Hreg with ⟨%hk, #Hr, -, -⟩
  iinv Hinv with Hi Hclose
  iunfold regReady at Hr
  icases Hr with ⟨#Hlb, %Hf⟩
  iunfold deployInv at Hi
  icases Hi with ⟨%ks, %M, >Ha, >HM, >%Hks, >Hids, >Hreg2, >Hfree⟩
  ihave #Hids' : [∗list] i ↦ x ∈ ks, nodeIdIs γ.proto x (W64 i) $$ [Hids]
  · iexact Hids
  icases regAuth_lb_prefix γ.deploy (1 : Qp).half (ks.map addrOf) nodes $$ [Ha Hlb] with %Hpre
  · iframe Ha Hlb
  imod Hclose $$ [Ha HM Hreg2 Hfree] with -
  · inext; iunfold deployInv; iexists ks, M; iframe; iframe #; ipureintro; exact Hks
  imodintro
  obtain ⟨ks', hks', rfl⟩ := prefix_map_addrOf Hpre
  have hl3 : ks'.length = 3 := by
    have := Hf.1.length_eq; simpa using this
  have hle := nodup_bound_length Hks.1 Hks.2.1
  have hkseq : ks' = ks := hks'.eq_of_length (by have := hks'.length_le; omega)
  subst hkseq
  rw [BigSepL.bigSepL_map, BigSepL.bigSepL_map]
  ihave #Hports : [∗list] i ↦ x ∈ ks', portId γ (addrOf x) (W32 i) ∗
      addrProto (addrOf x) (gryffWireP γ (addrOf x)) (gryffWireQ γ (addrOf x)) ∗
      ⌜addrOf x ∈ replicaAddrs⌝ $$ []
  · iapply BigSepL.bigSepL_impl $$ Hids'
    imodintro
    iintro %i %x %hx #Hid
    have hx3 : x < 3 := Hks.2.1 x (List.mem_of_getElem? hx)
    obtain ⟨hrep, hport⟩ := addrOf_mem x hx3
    isplitl
    · unfold portId
      iexists x
      have : (W64 (uint.Z (W32 (i : Int)))) = W64 (i : Int) := by
        have hi3 : i < 3 := by have := (List.getElem?_eq_some_iff.mp hx).1; omega
        congr 1; simp only [uint.Z, W32]; rw [BitVec.toNat_ofInt]; omega
      rw [this]
      iframe #
      ipureintro; exact ⟨hx3, hport⟩
    isplitl
    · rw [hport]
      have hmem : x ∈ [0, 1, 2] := by
        rcases x with _ | _ | _ | x <;> simp; omega
      ihave #Hl := BigSepL.bigSepL_mem (Φ := fun j => replicaLis γ j) hmem $$ Hlis
      iapply replicaLis_addr γ x hx3 $$ Hl
    ipureintro; exact hrep
  iframe #
  iapply BigSepL.bigSepL_mono $$ Hports
  intro i x hx
  iintro ⟨#Hp, -⟩ %hik
  have hi3 : i < 3 := by have := kr.isLt; omega
  iapply peerRole_intro γ (addrOf x) (rid32 kr) (W32 i) ?_ $$ Hp
  unfold rid32
  simp only [uint.Z, W32]
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  have := kr.isLt
  omega

end

end Perennial.gryff.unitB
