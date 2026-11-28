/-
The proof of `KvRaft/Spec/.../kvraft/openUDP.lean` (kvraft-udp, phase 2: `notes/kvraft-udp-proof-plan.md`).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.openUDP
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.listenUDP
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.nextBoot
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.udpAddr
public import GooseLang.Ext.Net.Deploy
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net Udp go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [HasExt udpExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [net_sem : net.Assumptions]
variable [go.IntoValInj GoString]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

theorem openUDP.wp_proof
    (wp_udpAddr : udpAddr.spec (GF := GF) (hG := hG))
    (wp_listenUDP : listenUDP.spec (GF := GF) (hG := hG))
    (wp_nextBoot : nextBoot.spec (GF := GF) (hG := hG)) :
    openUDP.spec (GF := GF) (hG := hG) := by
  intro F γu cfg M a Hma Hok
  wp_start as ⟨#HM, Hu⟩
  iapply wp_fupd
  iunfold udpProcStart at Hu
  icases Hu with ⟨#Hai, %bn, %qc, Hbs⟩
  iunfold udpAddrsInv at Hai
  icases Hai with ⟨#Hmi, #Haddr⟩
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %pm Hpm
  try wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (K := w64) (V := GoString) (fun (keys : List w64) (i : Int) =>
      iprop(∃ (x : w64) (y : GoString) (Mp : GMap w64 Loc),
      "%Hi" ∷ ⌜0 ≤ i ∧ ∀ (j : Nat) (k : w64), j < i.toNat → keys[j]? = some k → (Mp !! k).isSome⌝ ∗
      "idv" ∷ id_ptr ↦ x ∗
      "av" ∷ a_ptr ↦ y ∗
      "addrsv" ∷ addrs_ptr ↦ pm ∗
      "Hpm" ∷ pm ↦$ Mp ∗
      "Hps" ∷ ([∗map] _k ↦ p ∈ Mp, isUdpPeerAddr F γu p))) _ go.uint64 go.string _ M DFrac.discard $$ HM
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [id a addrs Hpm]
  · iexists _, _, ∅
    simp only [named]
    iframe
    isplitr
    · ipureintro
      exact ⟨Int.le_refl _, fun j k hj => absurd hj (by simp)⟩
    iapply BigSepM.bigSepM_empty.2; itrivial
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    try wp_auto
    have Hokv := Hok key vv Hvv
    have Hl := addrOk_length Hokv
    wp_apply wp_udpAddr vv (by omega) $$ [$Hpkg] as %p %ok ⟨%Hokeq, Hor⟩
    rw [Hokv] at Hokeq
    subst Hokeq
    icases Hor with (%Hf | ⟨%ip, %port, #Hpa, %Hvd⟩)
    · cases Hf
    try wp_auto
    wp_apply (wp_mapInsert (K := w64) (V := Loc) go.uint64 pm Mp key _) $$ Hpm as Hpm
    try wp_auto
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists key, vv, _
    simp only [named]
    iframe
    isplitr
    · ipureintro
      refine ⟨by omega, ?_⟩
      intro j k hj hk
      by_cases hke : k = key
      · subst hke; rw [GMap.lookup_insert]; rfl
      · rw [GMap.lookup_insert_ne _ _ (fun h => hke h.symm)]
        have hj' : j ≠ i.toNat := by
          intro e; subst e; rw [Hkey] at hk; exact hke (Option.some.inj hk).symm
        exact Hi.2 j k (by omega) hk
    ihave #Hp : isUdpPeerAddr F γu p $$ []
    · unfold isUdpPeerAddr
      iexists ip, port, vv
      iframe Hpa
      isplitr
      · ipureintro; exact Hvd
      iapply Haddr $$ %key %vv
      ipureintro; exact ⟨Hvv, Hokv⟩
    cases h : Mp !! key with
    | none =>
      iapply (BigSepM.bigSepM_insert h).2
      iframe Hp Hps
    | some y =>
      icases (BigSepM.bigSepM_delete h).1 $$ Hps with ⟨-, Hps⟩
      iapply BigSepM.bigSepM_insert_delete.2
      iframe Hp Hps
  iintro HP -
  iNamed HP
  obtain ⟨Hi0, Hall⟩ := Hi
  have Hin : cfg.ID' ∈ keys := (Hkset cfg.ID').2 (by rw [Hma]; rfl)
  obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem Hin
  have hsome := Hall j cfg.ID' (by omega) (by rw [List.getElem?_eq_getElem hj, hjk])
  obtain ⟨self, Hself⟩ := Option.isSome_iff_exists.mp hsome
  imod ownMap_persist pm _ _ $$ Hpm with #Hpm
  try wp_auto
  wp_apply (wp_map_lookup2 (K := w64) (V := Loc) go.uint64 _ pm Mp cfg.ID') $$ [$Hpm] as -
  rw [Hself]
  simp only [Option.getD_some, Option.isSome_some]
  try wp_auto
  icases Hps with #Hps
  icases (BigSepM.bigSepM_delete Hself).1 $$ Hps with ⟨#Hsp, -⟩
  iunfold isUdpPeerAddr at Hsp
  icases Hsp with ⟨%ip, %port, %a', #Hpa, %Hvd, #Hainv⟩
  wp_apply wp_listenUDP self ip port a' $$ [] as %c ⟨%s, #Hc⟩
  · iframe Hpa
    ipureintro; exact Hvd
  try wp_auto
  wp_apply wp_nextBoot γu cfg.ID' cfg.Dir' bn qc $$ [$Hpkg $Hmi $Hbs] as %boot ⟨Hctr, -⟩
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %km Hkm
  try wp_auto
  iStructNamed «$r0»
  imod sync.init_Mutex (udpNetLockInv γu «$r0_ptr» cfg.ID' boot) ⊤ _ $$ mu [seq acks Hkm Hctr]
    with #Hmu
  · inext
    iunfold udpNetLockInv
    iexists _, km, ∅
    iframe seq acks Hkm
    isplitl [Hctr]
    · iapply (show (udpCtr γu cfg.ID' boot (W64 0) : IProp GF) ⊢ udpCtr γu cfg.ID' boot 0 from .rfl)
      iexact Hctr
    iapply BigSepM.bigSepM_empty.2; itrivial
  ipersist id
  ipersist conn
  ipersist addrs
  ipersist boot
  imodintro
  iapply HΦ
  iexists boot
  iunfold isUdpNet
  imodintro
  iexists c, s, a', pm, Mp
  iframe #

end proof

end kvraft
end EtcdGrove
end Perennial
