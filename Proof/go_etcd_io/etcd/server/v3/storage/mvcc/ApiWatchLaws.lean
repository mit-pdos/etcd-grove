/-
**mvcc's candidate API's watch laws** (`Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`),
proved of the watch stream's implementation (`ApiWatchImpl.lean`). Each `<law>_proof` proves
`<law>.law`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The facts of the responses received, after one more. -/
theorem rcvFacts_snoc (γ : WsNames) (γc : WatchChanNames) (ms : List RespM) (r : RespM) :
    □ ([∗list] j ↦ m ∈ ms, rcvFact (GF := GF) γ γc (ms.take j) m) ∗ rcvFact γ γc ms r ⊢
      □ ([∗list] j ↦ m ∈ ms ++ [r], rcvFact γ γc ((ms ++ [r]).take j) m) := by
  iintro ⟨#Hs, #Hr⟩
  imodintro
  iapply (BigSepL.bigSepL_snoc (PROP := IProp GF)).2
  isplitl
  · iapply (BigSepL.bigSepL_mono (PROP := IProp GF) (l := ms)
      (Φ := fun j m => rcvFact (GF := GF) γ γc (ms.take j) m)
      (Ψ := fun j m => rcvFact (GF := GF) γ γc ((ms ++ [r]).take j) m) ?_) $$ Hs
    intro k x hk
    have hlt : k < ms.length := (List.getElem?_eq_some_iff.1 hk).1
    rw [List.take_append_of_le_length (by omega)]
  · rw [List.take_left' rfl]
    iexact Hr

/-- **Receiving on the stream's channel**: the channel's receive (`watch_recv_au`), the received
response's facts kept in the consumer's view. -/
theorem wsChan_recv_proof : wsChan_recv.law (GF := GF) := by
  intro ws γ ι
  iintro #Hst
  iunfold isMvccWatchStream at Hst
  iunfold isMvccWatchStreamI at Hst
  icases Hst with ⟨%Hn, -, -, #Hch, #Hinv, -⟩
  obtain ⟨hmv, -⟩ := Hn
  iexists ι.c.ch
  unfold wsChanOf
  iframe Hch
  iintro !> %rs %Φ Hr HΦ
  iunfold wsRecv at Hr
  iunfold wsRecvI at Hr
  icases Hr with ⟨Htok, %ms, Hcons, %Hrs, #Hfs⟩
  iapply (watch_recv_au γ.ws ι.ch ι.c ms Φ) $$ [] Hcons
  · rw [← hmv]; iexact Hinv
  iintro %v %ok Hres
  iapply HΦ
  iunfold watchRecvResult at Hres
  cases ok with
  | false =>
    isimp only [Bool.false_eq_true, ↓reduceIte] at Hres
    simp only [Bool.false_eq_true, ↓reduceIte]
    iunfold wsRecv
    iunfold wsRecvI
    iframe Htok
    iexists ms
    iframe Hres Hfs
    ipureintro; exact Hrs
  | true =>
    simp only [↓reduceIte]
    icases Hres with ⟨%r, Hcons, #Hv, #Hok, #Hro, #Hreg, #Hprog, #Hcov, #Hrat, #Hsl, %Hidx⟩
    iexists (respView r)
    isplitl [Htok Hcons]
    · iunfold wsRecv
      iunfold wsRecvI
      iframe Htok
      iexists (ms ++ [r])
      iframe Hcons
      isplitr
      · ipureintro; rw [Hrs, List.map_append]; rfl
      iapply rcvFacts_snoc
      iframe Hfs
      iunfold rcvFact
      rw [hmv]
      iframe Hok Hro Hreg Hprog Hcov Hrat Hsl
      ipureintro; exact Hidx
    · iunfold respIs at Hv
      iunfold wrespIs
      icases Hv with ⟨%Hv, %ps, #Hps, %Hlen, #Hevs⟩
      isplitr
      · ipureintro; exact Hv
      iexists ps
      simp only [respView]
      iframe Hps Hevs
      ipureintro; exact Hlen

end laws

end mvcc
end EtcdGrove
end Perennial
