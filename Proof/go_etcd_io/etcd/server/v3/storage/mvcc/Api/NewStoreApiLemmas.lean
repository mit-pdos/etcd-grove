/-
`imageOk_start` and `bkRTx_of_rdToks`, out of `NewStoreApi.lean`'s proof so that `RestoreApi.lean`
imports them without the proof (import tiers, 2026-11-18).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.Retire2
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Image
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.SnapImage
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.RdSupply
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.DeleterApi
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.WriteApi
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.ImageBridge
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-- **The image of the empty history**: an empty `Key` bucket and no compaction record. -/
theorem imageOk_start {D : backend.Data} (h : snap.imageOk D mvccStart.log mvccStart.crev false) :
    (∀ k, backend.dget D keyName k = none) ∧ noCmpData D := by
  obtain ⟨rc, ents, hk, hfin, hsch, -, hpos, hcut, hrc, hu, -⟩ := h
  have he : ents = [] := by
    have hs := hcut.1
    rw [show logEnts mvccStart.log 0 mvccStart.log.length = [] from by decide] at hs
    exact List.sublist_nil.1 hs
  subst he
  have hfr : rc.finRev = -1 := by
    have h1 : mvccStart.crev = -1 := rfl
    unfold CmpRecs.crev at hrc; rw [hu, h1] at hrc; simpa using hrc
  have hf : rc.fin = none := by
    cases hx : rc.fin with
    | none => rfl
    | some x =>
      have := hpos.1 x hx
      unfold CmpRecs.finRev at hfr; rw [hx] at hfr; simp at hfr; omega
  have hs : rc.sched = none := by
    cases hx : rc.sched with
    | none => rfl
    | some x =>
      have h1 := hpos.2 x hx
      have h2 : rc.resumes = true := by
        unfold CmpRecs.resumes CmpRecs.schedRev; rw [hfr, hx]; simp; omega
      rw [h2] at hu; cases hu
  refine ⟨fun k => by rw [hk]; rfl, ?_, ?_⟩
  · rw [hsch, hs]; rfl
  · rw [hfin, hf]; rfl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]
/-- Each reader slot's token with the reader's share of the open token (`bkRTx`). -/
theorem bkRTx_of_rdToks (γ : backend.BNames) (P : backend.BParams) (b : Loc) : ∀ n : Nat,
    ([∗list] _x ∈ List.replicate n (), backend.rdTok (GF := GF) γ P b) ∗
      ([∗list] _x ∈ List.replicate n (), backend.bOpen γ backend.rdOpen) ⊢
      [∗list] _x ∈ List.replicate n (), bkRTx γ P b
  | 0 => by
    simp only [List.replicate]
    iintro -
    iapply BigSepL.bigSepL_nil.2; itrivial
  | n + 1 => by
    simp only [List.replicate]
    iintro ⟨Hr, Ho⟩
    icases BigSepL.bigSepL_cons.1 $$ Hr with ⟨Hr1, Hr⟩
    icases BigSepL.bigSepL_cons.1 $$ Ho with ⟨Ho1, Ho⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hr1 Ho1]
    · unfold bkRTx; iframe Hr1 Ho1
    iapply bkRTx_of_rdToks γ P b n
    iframe Hr Ho

end proof

end api
end mvcc
end EtcdGrove
end Perennial
