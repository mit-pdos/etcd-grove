/- Lean-first (no Rocq counterpart).

# The examples' closed theorems from the members' start bundles (hub step 7's L4, 2026-11-05)

`etcd_adequate_members` and `etcd_adequate_alloc_members`: `Adequacy.lean`'s `etcd_adequate` and
`etcd_adequate_alloc`, the body proved from the members' start bundles (`etcdstart.memberStartRes`,
`StartRes.lean`) and the other addresses' listen rights, which program start's three lists give up
to order (`etcdstart.memberStartRes_intro`, D2). A module of its own, not `Adequacy.lean`: the start
bundles' module imports the server's (the restart bundle's `srvDiskImage`), which the raft examples
importing `Adequacy.lean` must not (the witness part declares raft's names again).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section adequacy
variable [GooseExts] [GooseInterp]
variable [GooseSemantics] [GoGlobalContext]
variable {GF : BundledGFunctors}

/-- **`progOk` at a body resource that gives the one proved**. -/
theorem progOk_pre [hG : HeapGS .hasLC GF] (R B B' : IProp GF) (init : val) (body : Expr)
    (φ : val → Prop) (hB : B ⊢ B') (h : progOk R B' init body φ) : progOk R B init body φ := by
  obtain ⟨getInit, I, Hinit, Hbody⟩ := h
  refine ⟨getInit, I, Hinit, ?_⟩
  iintro HI Htok HB
  ihave HB' := hB $$ HB
  iapply Hbody $$ HI Htok HB'

/-- **An etcd example's closed theorem, from its members' start bundles** (hub step 7's L4, D2):
`etcd_adequate`, the body proved from the start bundles of the members `ms`
(`etcdstart.memberStartRes`) and the listen rights of the other addresses `Bs`, when the members'
addresses and `Bs` are `As` up to order and the members' WAL directories are `Ds` up to order. -/
theorem etcd_adequate_members [hPre : GooseGpreS GF] [lctx : GoLocalContext]
    (init : val) (body : Expr) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (As : List GoString) (hAs : As.Nodup) (Ds : List GoString) (hDs : Ds.Nodup)
    (ms : List (GoString × etcdstart.MemberAddrs)) (Bs : List GoString)
    (hA : (ms.flatMap (fun m => m.2.addrs) ++ Bs).Perm As)
    (hD : (ms.map (fun m => etcdstart.memberWalDir m.1)).Perm Ds)
    (σ : state) (g : GlobalState) (Hinitg : extsInitgP g.globalWorld)
    (Hinitw : extsInitP σ.world g.globalWorld)
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    (HNs : prometheus.namesUnclaimed (init #() ;; body)
      [read.slowReadIndexName, read.readIndexFailedName])
    (HAs : addrsUnclaimed (init #() ;; body) As) (HDs : walDirsAbsent (init #() ;; body) Ds)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([init #() ;; body], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hprog : ∀ hG : HeapGS .hasLC GF, receiptBound GF = n + 1 → threadBound GF = max (n + 2) 4 →
      progOk (hG := heapWith hG lctx) (read.readRegPerm (GF := GF))
        iprop(([∗list] m ∈ ms, etcdstart.memberStartRes m.1 m.2) ∗ [∗list] b ∈ Bs, netAddrFree b)
        init body φ) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  etcd_adequate init body φ hφ As hAs Ds hDs σ g Hinitg Hinitw Hlctx Hinit Hthreads HNs HAs HDs
    n κs t2 σ2 Hsteps fun hG HN HT =>
      progOk_pre (hG := heapWith hG lctx) _ _ _ init body φ
        (etcdstart.memberStartRes_intro ms Bs As Ds hA hD) (Hprog hG HN HT)

/-- **`etcd_adequate_alloc`, from the members' start bundles** (hub step 7's L4): as
`etcd_adequate_members`, with ghost state allocated first. -/
theorem etcd_adequate_alloc_members [hPre : GooseGpreS GF] [lctx : GoLocalContext]
    (init : val) (body : Expr) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (As : List GoString) (hAs : As.Nodup) (Ds : List GoString) (hDs : Ds.Nodup)
    (ms : List (GoString × etcdstart.MemberAddrs)) (Bs : List GoString)
    (hA : (ms.flatMap (fun m => m.2.addrs) ++ Bs).Perm As)
    (hD : (ms.map (fun m => etcdstart.memberWalDir m.1)).Perm Ds)
    (σ : state) (g : GlobalState) (Hinitg : extsInitgP g.globalWorld)
    (Hinitw : extsInitP σ.world g.globalWorld)
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) (Hthreads : σ.threads = 1)
    (HNs : prometheus.namesUnclaimed (init #() ;; body)
      [read.slowReadIndexName, read.readIndexFailedName])
    (HAs : addrsUnclaimed (init #() ;; body) As) (HDs : walDirsAbsent (init #() ;; body) Ds)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([init #() ;; body], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hprog : ∀ hG : HeapGS .hasLC GF, receiptBound GF = n + 1 → threadBound GF = max (n + 2) 4 →
      ∃ (X : Type) (T : X → IProp GF),
        (⊢ (|==> ∃ x, T x : IProp GF)) ∧
        ∀ x, progOk (hG := heapWith hG lctx) (read.readRegPerm (GF := GF))
          iprop((([∗list] m ∈ ms, etcdstart.memberStartRes m.1 m.2) ∗
            [∗list] b ∈ Bs, netAddrFree b) ∗ T x) init body φ) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  etcd_adequate_alloc init body φ hφ As hAs Ds hDs σ g Hinitg Hinitw Hlctx Hinit Hthreads HNs HAs
    HDs n κs t2 σ2 Hsteps fun hG HN HT => by
      obtain ⟨X, T, Halloc, Hp⟩ := Hprog hG HN HT
      exact ⟨X, T, Halloc, fun x => progOk_pre (hG := heapWith hG lctx) _ _ _ init body φ
        (sep_mono_left (etcdstart.memberStartRes_intro ms Bs As Ds hA hD)) (Hp x)⟩

end adequacy

end EtcdGrove
end Perennial
