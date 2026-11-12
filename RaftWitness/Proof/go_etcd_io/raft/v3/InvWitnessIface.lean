/-
The witness proxy at W2's ghost state, and as a `Witness` (2026-10-20, witness support, W3b,
`notes/raft-witness.md`): `witness.Process`'s spec (`Spec/go_etcd_io/raft/v3/witness__Process.lean`,
for any reading of the storage's states) instantiated at W2's `wGhost` (`InvWitnessGhost.lean`),
and the `Witness` interface's methods on the `*witness` `NewWitness` returns (`ownWitnessI`), the
spec raft and the kv example use.

A request whose protocol reading (`wAbsReq`) is a legitimate message (`isMessage`) is answered,
if at all, with a legitimate message (`wRespOk`), for a storage whose states the protocol's
witness history follows (`isWitnessStorage s N (wGhost γ ·.ws)`); the proxy's cache is a state
of that history (`wSt`).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvWitnessGhost
public import RaftWitness.Spec.go_etcd_io.raft.v3.witness__Close
public import RaftWitness.Spec.go_etcd_io.raft.v3.NewWitness

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section iface
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, so that the heap's invariants are an `InvGS GF` (`raft__Step.lean`)
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `w.Process(m)` at W2's ghost state: the witness `γ.reWit` (not `0`) answers a request to it
(from a node, not `0`) whose reading is legitimate, if at all, legitimately, for a storage in an
invariant of a namespace `N` disjoint from the log invariant's. -/
abbrev witness.Process.ghostSpec : Prop :=
  ∀ (γ : RaftNames) (w : Loc) (s : GoInterface) (cq pv : Bool) (c : WHS) (h : Bool)
    (N : Namespace) (mv : WitnessMessage) (μ : WMsg),
  (↑raftLogN : CoPset) ⊆ ⊤ \ ↑N → γ.reWit ≠ W64 0 → μ.to = γ.reWit → μ.frm ≠ W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      ownWitness w γ.reWit s cq pv c h ∗ isWitnessStorage s N (fun σ => wGhost γ σ.ws) ∗
      ownWMsg mv μ ∗ wSt γ c.ws ∗ raftCommitInv γ ∗ isMessage γ (wAbsReq μ) }}
    (App (Val (w @!! go.GoType.PointerType witness.ty @!! go!"Process")) (Val #mv))
  {{ (ml : Loc) (err : GoError), RET (PairV #ml #err);
      ∃ c' h', ownWitness w γ.reWit s cq pv c' h' ∗ wSt γ c'.ws ∗
      ((⌜err = interface.nil⌝ ∗ ∃ r, respOpt ml r ∗ wRespOk γ r) ∨
       (⌜err ≠ interface.nil⌝ ∗ ⌜ml = null⌝)) }}

theorem witness.Process.ghost (wp_Process : witness.Process.spec (GF := GF) (hG := hG)) :
    witness.Process.ghostSpec (GF := GF) (hG := hG) := by
  intro γ w s cq pv c h N mv μ HN Hwnz Hto Hfr
  iintro %Φ ⟨#Hpkg, Hw, #Hs, #Hm, #Hc, #Hinv, #Hreq⟩ HΦ
  wp_apply wp_Process w γ.reWit s cq pv c h N (fun σ => wGhost γ σ.ws) (fun σ => wSt γ σ.ws)
    (wRespOk γ) mv μ (fun _ => inferInstance) $$ [$Hw] as %ml %err Hpost
  · iframe Hs Hm Hc
    isplitr
    · imodintro
      iintro %σ %hh %r #Hst %Hr
      iapply wInst_cache γ γ.reWit cq pv μ rfl Hwnz Hto σ hh r Hr $$ Hreq Hst
    isplitr
    · imodintro
      iintro %σ %Hty4 Hg
      iapply wInst_read γ N HN cq pv μ Hwnz Hto Hfr Hty4 σ $$ Hinv Hreq Hg
    imodintro
    unfold wRespOk
    itrivial
  iapply HΦ
  iexact Hpost

/-- The `Witness` `NewWitness` returns, of the witness `γ.reWit`: the `*witness`, its storage
following the protocol's witness history, its cache a state of that history. -/
def ownWitnessI (γ : RaftNames) (N : Namespace) (wi : GoInterface) : IProp GF :=
  iprop(∃ (w : Loc) (s : GoInterface) (cq pv : Bool) (c : WHS) (h : Bool),
    ⌜wi = interface.mkOk (go.GoType.PointerType witness.ty) #w⌝ ∗
    ownWitness w γ.reWit s cq pv c h ∗ isWitnessStorage s N (fun σ => wGhost γ σ.ws) ∗
    wSt γ c.ws)

/-- `NewWitness`'s cache, the zero state, is W2's initial one. -/
theorem WHS.zero_ws [GooseExts] : WHS.zero.ws = wInit := rfl

/-- `Witness.Process` (`wi.Process(m)`) on the `Witness` of the witness `γ.reWit`: a
legitimate request answered, if at all, legitimately. -/
abbrev Witness.Process.spec : Prop :=
  ∀ (γ : RaftNames) (N : Namespace) (i : GoInterfaceOk) (mv : WitnessMessage) (μ : WMsg),
  (↑raftLogN : CoPset) ⊆ ⊤ \ ↑N → γ.reWit ≠ W64 0 → μ.to = γ.reWit → μ.frm ≠ W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      ownWitnessI γ N (interface.ok i) ∗ ownWMsg mv μ ∗ raftCommitInv γ ∗
      isMessage γ (wAbsReq μ) }}
    (App (Val #(methods i.ty go!"Process" i.v)) (Val #mv))
  {{ (ml : Loc) (err : GoError), RET (PairV #ml #err);
      ownWitnessI γ N (interface.ok i) ∗
      ((⌜err = interface.nil⌝ ∗ ∃ r, respOpt ml r ∗ wRespOk γ r) ∨
       (⌜err ≠ interface.nil⌝ ∗ ⌜ml = null⌝)) }}

theorem Witness.wp_Process' (wp_Process : witness.Process.spec (GF := GF) (hG := hG)) :
    Witness.Process.spec (GF := GF) (hG := hG) := by
  intro γ N i mv μ HN Hwnz Hto Hfr
  iintro %Φ ⟨#Hpkg, Hw, #Hm, #Hinv, #Hreq⟩ HΦ
  iunfold ownWitnessI at Hw
  icases Hw with ⟨%w, %s, %cq, %pv, %c, %h, %Hwi, Hw, #Hs, #Hc⟩
  rcases i with ⟨ity, iv⟩
  simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at Hwi
  obtain ⟨rfl, rfl⟩ := Hwi
  wp_apply witness.Process.ghost wp_Process γ w s cq pv c h N mv μ HN Hwnz Hto Hfr
    $$ [$Hw] as %ml %err ⟨%c', %h', Hw, #Hc', Hr⟩
  · iframe Hs Hm Hc Hinv Hreq
  iapply HΦ
  iframe Hr
  unfold ownWitnessI
  iexists w, s, cq, pv, c', h'
  iframe Hw Hs Hc'
  ipureintro; rfl

/-- `Witness.Close` on the `Witness` of the witness `γ.reWit`. -/
abbrev Witness.Close.spec : Prop :=
  ∀ (γ : RaftNames) (N : Namespace) (i : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      ownWitnessI γ N (interface.ok i) }}
    (App (Val #(methods i.ty go!"Close" i.v)) (Val #()))
  {{ RET #(); ownWitnessI γ N (interface.ok i) }}

theorem Witness.wp_Close' (wp_Close : witness.Close.spec (GF := GF) (hG := hG)) :
    Witness.Close.spec (GF := GF) (hG := hG) := by
  intro γ N i
  iintro %Φ ⟨#Hpkg, Hw⟩ HΦ
  iunfold ownWitnessI at Hw
  icases Hw with ⟨%w, %s, %cq, %pv, %c, %h, %Hwi, Hw, #Hs, #Hc⟩
  rcases i with ⟨ity, iv⟩
  simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at Hwi
  obtain ⟨rfl, rfl⟩ := Hwi
  wp_apply wp_Close w γ.reWit s cq pv c h N (fun σ => wGhost γ σ.ws) $$ [$Hw $Hs] as Hw
  iapply HΦ
  unfold ownWitnessI
  iexists w, s, cq, pv, c, h
  iframe Hw Hs Hc
  ipureintro; rfl

end iface

end EtcdGrove
end Perennial
