/- Lean-first (no Rocq counterpart).
# `Close`'s put-back without the update (W4 of `notes/wal-fsext-plan.md`, twenty-fifth session)

`walCloseLawU`: `walCloseLaw` (`CloseLaw.lean`) with no client update to commit: the cleanup's `Close`
(`WAL.Close.specU`, `Create`'s `cleanupWAL`: after the commit `Create` no longer holds `walDiskAt`,
the client does; ledger 2026-11-14). The tail unregistered (`walInvBody_untail`), then
`walInvBody_unpin` with the tail's halves, the directory claim and the pipeline names, and the lock:
the free lock token back.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CloseLaw
import all LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Ghost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **`Close`'s put-back without the update** (see the file header). -/
theorem walCloseLawU (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (w : Loc) (dir : GoString)
    (γ γt : GName) (ino j : Ino) (X : List GoString) (hj : NamesH) (H : List (WalOpG WalEnt))
    (md : List w8) (cuts : List Nat) (wr : Nat) (m : OsMeta) (bs : List ByteG) (b b' : GoString)
    (hTM : TailMetaS m bs) (hwr : wr = (tailStream Mr H md cuts).length) (hb : b ∈ walTmps)
    (hb' : b' ∈ walTmps) :
    ⊢ walInv (L := L) (W := W) walCodec Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walTailKey (W := W) dir γ -∗ tailVar (W := W) γ ((H, md, cuts, wr, ino, none) : TailG) -∗
      osMeta (L := L) ino (DFrac.own (1 : Qp).half) m -∗ osBytes (L := L) ino 0 (DFrac.own (1 : Qp).half) bs -∗
      walDirKey (W := W) dir j X -∗ osNames (L := L) j (.except X) (DFrac.own (1 : Qp).half) hj -∗
      tmpClaim (hG := ⟨G, L⟩) j b -∗ tmpClaim (hG := ⟨G, L⟩) j b' -∗
      walOutFrag (W := W) ⟨[ino], [(j, .except X)], [dir]⟩ -∗
      walTailsFrag (W := W) (<[dir := γt]> (∅ : GMap GoString GName)) -∗ walNamesFrag (W := W) none -∗
      walOpenW (W := W) w dir -∗ walPurgeW (W := W) w dir ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ walUnlockedTok (W := W) := by
  iintro #Hinv Hnc Hk Hv Hm Hbs #Hdk Hn Htb Htb' Ho Htf Hnf Hopen -
  imod walInv_open walCodec Mr R jr r ⊤ CoPset.subseteq_top $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  imod walInvBody_untail Mr R jr r s dir γ γt H md cuts wr ino m bs hTM hwr $$ Hb Htf Hk Hv Hm Hbs with
    ⟨%d, -, Hb, Htf, Hm, Hbs⟩
  unfold walOpenW walLockedTok
  icases Hopen with ⟨-, Hlk⟩
  have hS : ∀ g ∈ [(⟨go!"", ino, m, bs⟩ : SegG)], g.om.size = g.bs.length := by
    intro g hg; simp only [List.mem_singleton] at hg; subst hg; exact hTM.1.1.symm
  have hu := walInvBody_unpin (L := L) (W := W) walCodec Mr R jr r s dir j X hj
    [(⟨go!"", ino, m, bs⟩ : SegG)] true hS
  simp only [List.map_cons, List.map_nil, ↓reduceIte] at hu
  imod hu $$ Hb [Hlk] Htf Hnf Ho [Hm Hbs] Hn [Htb Htb'] Hdk with ⟨Hb, Hu⟩
  · unfold walLockedTok; iexact Hlk
  · iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)).2
    unfold segRes; iframe Hm Hbs
  · iapply tmpClaims_walTmpsRes (L := L) j b b' hb hb'
    iframe Htb Htb'
  imod Hcl $$ [Hb] with -
  · iexists s; iexact Hb
  imodintro
  iframe Hnc Hu

end iris

end WalFs
end EtcdGrove
end Perennial

end
