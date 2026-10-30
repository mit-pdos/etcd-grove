/-
**The server's view after `applySnapshot`** (D22 receiver epochs, S8d, step 2 of
`srvSnapApplied_of_walk`, `notes/snapshot-s8-plan.md`): `isServer` at the snapshot's names.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyNames

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Step 2: `isServer` at the snapshot's names** `γ' = snapγ γ π0 γB`, `TM' = metaTM γB P`,
`E' = snapE …` (persistent, from the old view and the walk's `HCI'` and hook).

Brief for the prover. Unfold `isServer`; take the old one's parts apart (`⌜ρ.rd = γr⌝`,
`isServerCI`, `∃ v, srvFieldsAt s γ ci TM E ρ v`, `srvAtomics`, `srvGenAt`, `srvRaftNode`).
- `isServerCI s γ' ci`: the hypothesis.
- `srvFieldsAt` at `{ v with hook := #g }`: every field but the hook is the old one's; `waitInv`
  is equal (`waitInv_snapE`, `rfl`); `⌜E'.P = batchLockInv γ' TM' ∧ E'.f = #g⌝` by `rfl`
  (`snapE_P`, `snapE_f`); `hookSpec γ' ci TM' #g` the hypothesis; `srvEnvOk s γ' ci E' v.cluster`:
  `E'.FS = E.FS = srvFS s` (the old `srvEnvOk`'s first conjunct, `snapE_FS`), `E'.ciC = srvCiC γ' ci`
  (`rfl`), and the third part with `γB`, `H := srvObjsOn al ast lp cl d'.be`, `d := d'`
  (`snapE_kb hkb'`, `hγB`), where `cl = v.cluster` from the two persistent points-to of
  `srvClusterAddr s` (the hypothesis's `↦□ cl` and `srvFieldsAt`'s `↦□ v.cluster`: their agreement,
  e.g. `pointsto_agree`/`typed_pointsto_agree` as used elsewhere for `↦□`). Rewrite with that before
  framing `srvEnvOk`'s `cl`.
- `srvAtomics`, `srvGenAt`: equal (`srvAtomics_snapE`, `srvGenAt_snapE`, `rfl`); `srvRaftNode`
  kept. -/
theorem snap_isServer (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (π0 : ApplyPhys) (γB : backend.BNames)
    (P : backend.BParams) (d' : mvcc.KBReal) (p' : mvcc.PhysNames) (g : GoFunc)
    (al ast lp cl : Loc) (hγB : d'.γB = γB) (hkb' : p'.kb = some d') (hcm' : d'.cm = false) :
    isServer s γ ci TM E ρ γr ∗ srvClusterAddr s ↦□ cl ∗
      isServerCI s (snapγ γ π0 γB) ci ∗ hookSpec (snapγ γ π0 γB) ci (metaTM γB P) #g ⊢
    isServer s (snapγ γ π0 γB) ci (metaTM γB P)
      (snapE E (snapγ γ π0 γB) (metaTM γB P) ci p' g γB al ast lp cl d'.be) ρ γr := by
  unfold isServer srvFieldsAt
  iintro ⟨⟨%Hrd, #Hci, Hv, #Hat, #Hgen, #Hrn⟩, #Hcl, #Hci', #Hhook⟩
  icases Hv with ⟨%v, Hf⟩
  icases Hf with ⟨#Hlg, %Hlgn, #Hw, #Hwi, %HP, %Henv, #Hhk, #Hles, #Hlok, #Hfc, #Hal,
    #Hclv, #Hrc, #Hq, #Hlm, #Hmid, #Hli, #He, #Ht, #Hn, #Has⟩
  icombine Hcl Hclv gives %Heq
  subst Heq
  have hok : srvEnvOk s (snapγ γ π0 γB) ci
      (snapE E (snapγ γ π0 γB) (metaTM γB P) ci p' g γB al ast lp v.cluster d'.be) v.cluster :=
    ⟨Henv.1, rfl, γB, _, rfl, rfl, d', al, ast, lp, snapE_kb _ _ _ _ _ _ _ _ _ _ _ _ d' hkb', hγB,
      rfl, hcm'⟩
  rw [srvAtomics_snapE, srvGenAt_snapE]
  isplitr
  · ipureintro; exact Hrd
  isplitr
  · iexact Hci'
  isplitr
  · iexists { v with hook := #g }
    simp only
    rw [waitInv_snapE]
    iframe #
    ipureintro
    exact ⟨Hlgn, ⟨rfl, rfl⟩, hok⟩
  iframe #

end proof
end EtcdGrove
end Perennial
