/-
`(*Replica).alive(q)`: reads `r.Alive[q]` under `r.M` (`fwCore_alive`). Its value is any boolean
for the protocol (the broadcast's ghost step `ep_bcastStep` takes the value read).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.EpBase

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : StateTreemap GF]

theorem wp_alive (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs)
    (Rext : IProp GF) (q : w32) (hq : 0 ≤ sint.Z q ∧ sint.Z q < L.length) :
    {{ pkgInit_epaxos (GF := GF) ∗ efld r go!"Replica" ↦□ rr ∗ isReplicaFw γ rr i L p Rext }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"alive")) (Val #q))
    {{ (a : Bool), RET #a; True }} := by
  wp_start as ⟨#Hrr, #Hfw⟩
  ihave #Hlock := isReplicaFw_lock _ _ _ _ _ _ $$ Hfw
  ihave #Hro := isReplicaFw_ro _ _ _ _ _ _ $$ Hfw
  ihave ⟨-, -, -, -, -, -, -, -, -, -, -, -, #HAl, %HLn⟩ := fwRO_fields _ _ _ _ _ $$ Hro
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HR⟩
  unfold fwLockInv
  icases HR with ⟨Hcore, Hext⟩
  iapply fupd_wp
  imod fwCore_alive γ rr i L p Rext ⊤ CoPset.subseteq_top $$ Hfw Hcore with
    ⟨%als, %Hals, Has, Hclose⟩
  imodintro
  ihave %Hallen := ownSlice_len _ _ _ $$ Has
  have eq : sint.Z (W64 (sint.Z q)) = sint.Z q := by word
  have hb : 0 ≤ sint.Z (W64 (sint.Z q)) ∧ sint.Z (W64 (sint.Z q)) < sint.Z p.alive.len := by
    rw [eq]; have h1 := Hallen.1; have h2 := Hallen.2; rw [Hals] at h1
    constructor
    · omega
    · have : (L.length : Int) = sint.Z p.alive.len := by rw [h1]; exact Int.toNat_of_nonneg h2
      omega
  obtain ⟨a, ha⟩ : ∃ a, als[(sint.Z (W64 (sint.Z q))).toNat]? = some a :=
    ⟨als[(sint.Z (W64 (sint.Z q))).toNat]'(by rw [eq, Hals]; have := hq.2; omega),
      List.getElem?_eq_getElem _⟩
  simp only [hb, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index _ _ als _ a hb.1 $$ [$Has] as Has
  · ipureintro; exact ha
  ihave Hcore := Hclose $$ Has
  wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hcore Hext]
  · iframe Hcore Hext
  iapply HΦ
  itrivial

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
