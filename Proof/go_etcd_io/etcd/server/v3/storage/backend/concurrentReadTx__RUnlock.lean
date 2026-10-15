/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/concurrentReadTx__RUnlock.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.concurrentReadTx__RUnlock
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.wg_wgi_mask_r : (↑(bN.@"wg") : CoPset) ⊆ ⊤ \ ↑(bN.@"wgi") :=
  sync.wg_mask_ndot_ne bN "wg" "wgi" (by decide)

/-- A reader's `txWg.Done()`: its share given back to the interval's protocol, for its budget
token. -/
theorem backend.wp_rdDone (γ : BNames) (rtx wg : Loc) (γw γo γt : GName) (k : Nat) (q : Qp) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ □ wgInv γ rtx wg γw γo γt ∗ rdShare rtx γo k q }}
      (App (Val (wg @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); ownToks γ.rdt 1 }} := by
  iintro %Φ ⟨#Hsync, #Hwgi, Hsh⟩ HΦ
  unfold wgInv
  icases Hwgi with ⟨%γwg, #Hisw, #Hi, #Hauth⟩
  unfold rdShare
  icases Hsh with ⟨Hlive, Hrc⟩
  iapply sync.WaitGroup.wp_Done wg γwg (bN.@"wg") $$ [] [Hlive Hrc HΦ]
  · iframe #
  iinv Hi with Hb Hclose
  iapply fupd_mask_intro wg_wgi_mask_r
  iintro Hmask
  inext
  unfold wgBody
  icases Hb with (⟨%n, %outs, %pool, Hwgo, Hoa, Hpool, Htoks, %Hn, Hw⟩ | ⟨Hoa, -⟩)
  rotate_left
  · icombine Hoa Hrc gives %Hl
    simp at Hl
  icombine Hoa Hrc gives %Hl
  have hsz := GMap.map_size_nonzero_lookup outs k q Hl
  have hn1 : 1 ≤ sint.Z n := by omega
  have hlt : sint.Z n < 2 ^ 31 := by word
  have hnn : sint.nat (n - W32 1) = sint.nat n - 1 := by word
  obtain ⟨j, hj⟩ : ∃ j, sint.nat n = j + 1 := ⟨sint.nat n - 1, by word⟩
  rw [hj]
  icases (ownToks_add 1 j γ.rdt).1 $$ Htoks with ⟨Htoks, Htok⟩
  iexists n
  iframe Hwgo
  isplitr
  · ipureintro; omega
  iintro Hwgo
  imod Hmask with -
  imod ghost_map_delete $$ Hoa Hrc with Hoa
  ihave Hpool := (txLive_fractional rtx).fractional pool q |>.2 $$ [Hpool Hlive]
  · iframe
  imod Hclose $$ [Hwgo Hoa Hpool Htoks Hw] with -
  · inext
    ileft
    iexists n - W32 1, outs.delete k, pool + q
    rw [hnn, hj, show j + 1 - 1 = j by omega]
    iframe
    ipureintro
    have hd := qsum_delete outs k q Hl
    have hs := GMap.map_size_delete_Some outs k q Hl
    constructor
    · rw [hs]; have : sint.Z (n - W32 1) = sint.Z n - 1 := by word
      omega
    · show (pool.val + q.val) + _ = _
      grind
  imodintro
  iapply HΦ
  iexact Htok

theorem backend.concurrentReadTx.RUnlock.wp_proof :
    backend.concurrentReadTx.RUnlock.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b crt rtx rv
  wp_start as H
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold crtSnap
  icases H with ⟨%m, %Pb, %cm, %tm, %wg, %γw, %γo, %γt, %k, %q, %rt, #Hrt, #Htm, -, -, -,
    -, #Hwg, Hown, #Hg, Hsh, #Hsnap, #Hintv, #Hwgi, %Hwf⟩
  wp_auto
  wp_apply wp_rdDone γ rtx wg γw γo γt k q $$ [$Hsync $Hwgi $Hsh] as Htok
  iapply HΦ
  unfold crTok
  iexists rt, tm
  iframe; iframe #


end proof

end EtcdGrove
end Perennial
