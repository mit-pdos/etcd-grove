/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/NewSession.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.NewSession
public import Spec.go_etcd_io.etcd.client.v3.Client__GetLogger
public import Spec.go_etcd_io.etcd.client.v3.Client__Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem NewSession.wp_proof (hGL : Client.GetLogger.spec (GF := GF) (hG := hG))
    (hCtx : Client.Ctx.spec (GF := GF) (hG := hG)) :
    NewSession.spec (GF := GF) (hG := hG) := by
  intro client cctx sl gs pctx pcs
  wp_start as ⟨#Hcl, #Hopts, %Hpc, #Hpctx, #Hpcc⟩
  ihave #Hcl' := Hcl
  iunfold isEtcdSessionClient at Hcl'
  icases Hcl' with ⟨#Hcf, #Hlease, #Hlg⟩
  (try wp_auto)
  wp_apply hGL client $$ [$Hlg] as %lg %Hlg0
  (try wp_auto)
  wp_apply hCtx client cctx $$ [$Hcf]
  (try wp_auto)
  -- the options, in order
  ihave #Hopts' := Hopts
  iunfold sessOptsAt at Hopts'
  icases Hopts' with ⟨%fs, #Hfs, %Hlen, #Hf⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hfs
  ihave IH : iprop(∃ (n : w64) (f0 : GoFunc),
      "i" ∷ i_ptr ↦ n ∗ "Hop" ∷ «$r0_ptr» ↦ (sessOptsFold (gs.take (sint.nat n))
        (SessionOpts.init cctx)).val ∗ "opt" ∷ opt_ptr ↦ f0 ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (fs.length : Int)⌝) $$ [i «$r0» opt]
  · iexists W64 0, _
    simp only [named]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < fs.length := by word
    obtain ⟨f, Hfi⟩ : ∃ f, fs[sint.nat n]? = some f := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨g, Hgi⟩ : ∃ g, gs[sint.nat n]? = some g :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hlt)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) fs DFrac.discard f Hn.1 $$ [Hfs] as -
    · iframe #; ipureintro; exact Hfi
    ihave #Hg := Hf $$ %(sint.nat n) %f %g %Hfi %Hgi
    unfold sessionOptSpec
    wp_apply Hg $$ [$Hop] as Hop
    · ipureintro; exact Hlg0
    wp_for_post
    iframe
    iexists n + W64 1, f
    simp only [named]
    iframe
    isplitl [Hop]
    · rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, sessOptsFold_take_succ gs _ _ g Hgi]
      iexact Hop
    ipureintro; constructor <;> word
  have Hge : sint.nat n = gs.length := by rw [← Hlen]; word
  rw [Hge, List.take_length]
  generalize hO : sessOptsFold gs (SessionOpts.init cctx) = O at Hpc ⊢
  obtain ⟨ottl, olid, octx⟩ := O
  simp only at Hpc
  subst Hpc
  generalize hoptsp : «$r0_ptr» = optsp
  ipersist Hop
  ihave #Hop2 := Hop
  unfold SessionOpts.val
  iStructNamed Hop2
  irename ctx => Hoctxf
  irename ttl => Hottlf
  irename leaseID => Holidf
  ihave #Hl' := Hlease
  iunfold isEtcdLeaseClient at Hl'
  icases Hl' with ⟨%l, #Hlf, #Hl⟩
  ihave #Hl2 := Hl
  iunfold isEtcdLease at Hl2
  icases Hl2 with ⟨#HGrant, #HKA, -⟩
  wp_if_destruct
  · (try wp_auto)
    wp_apply HGrant $$ [$Hpctx] as %resp %err Hres
    icases Hres with (%Herr | ⟨%Herr, %gid, %hdr, %r, #HID, %Hid, #Hhdr, %Hhdrnn, #Hrev, #Hreached⟩)
    · cases err with
      | nil => exact absurd rfl Herr
      | ok e =>
        (try wp_auto)
        iapply HΦ
        ileft; ipureintro; exact ⟨rfl, fun h => by cases h⟩
    · subst Herr
      (try wp_auto)
      wp_apply context.wp_WithCancel iprop(True) pctx pcs $$ [$Hpctx $Hpcc]
          as %ctx' %γ' %cancel ⟨#Hcancel, #Hctx', #Hcc'⟩
      ihave #Hcancel' := context.cancel_spec_forget _ _ _ $$ Hcancel
      (try wp_auto)
      wp_apply HKA $$ [$Hctx'] as %ka %err Hres
      icases Hres with (%Herr | ⟨%Herr, Hka⟩)
      · cases err with
        | nil => exact absurd rfl Herr
        | ok e =>
          (try wp_auto)
          wp_apply Hcancel'
          · imodintro; itrivial
          (try wp_auto)
          iapply HΦ; ileft; ipureintro; exact ⟨rfl, fun h => by cases h⟩
      · subst Herr
        icases Hka with ⟨%γk, #Hka⟩
        ihave #Hka' := Hka
        iunfold isChanAny at Hka'
        icases Hka' with ⟨#Hkach, #Hkainv⟩
        ihave %Hkann := isChan_not_null $$ Hkach
        (try wp_auto)
        have hkn : ka ≠ chan.nil := Hkann
        rw [decide_eq_false hkn]
        (try wp_auto)
        wp_apply chan.wp_make1 (V := Unit) as %dch %γd ⟨#Hdch, %_, Hdoc⟩
        imod alloc_broadcast_chan iprop(True) γd dch $$ Hdch Hdoc with Hpend
        icases ownBroadcastChan_open _ _ _ _ $$ Hpend with ⟨%γch, #Hint, Hown⟩
        ihave #Hdunk : ownBroadcastChan dch γd iprop(True) .Unknown $$ []
        · iapply ownBroadcastChan_close _ _ _ _ γch
          iframe #
        ihave Hpend : ownBroadcastChan dch γd iprop(True) .Pending $$ [Hown]
        · iapply ownBroadcastChan_close _ _ _ _ γch
          iframe #
          iexact Hown
        (try wp_auto)
        irename cancel => Hcanp
        irename donec => Hdonp
        ipersist Hcanp
        ipersist Hdonp
        ipersist keepAlive
        icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨Hr0, %Hsnn⟩
        iStructNamed Hr0
        ipersist client
        ipersist opts
        ipersist id
        ipersist ctx
        ipersist cancel
        ipersist donec
        wp_apply wp_fork $$ [Hpend]
        · (try wp_auto)
          wp_apply wp_with_defer
          iintro %defer Hdefer
          (try wp_auto)
          ihave IH : iprop(True) $$ []
          · itrivial
          wp_for IH
          (try rw [if_pos (decide_eq_true rfl)])
          (try wp_auto)
          wp_bind (App (Val (chan.receive _)) _)
          iapply chan.wp_receive (V := Loc) ka γk $$ Hkach
          iintro ⟨Hlc1, Hlc2, -, -⟩
          iapply chanAny_recv_au γk ka _ $$ [$Hlc1 $Hlc2] Hka
          inext
          iintro %v %ok
          cases ok
          · (try wp_auto)
            wp_for_post
            wp_apply wp_broadcast_chan_close dch γd iprop(True) $$ [$Hpend] as -
            · imodintro; itrivial
            (try wp_auto)
            wp_apply Hcancel'
            · imodintro; itrivial
            (try wp_auto)
            (try itrivial)
          · (try wp_auto)
            wp_for_post
            iframe
        (try wp_auto)
        iapply HΦ
        iright
        isplitr
        · ipureintro; exact ⟨rfl, Hsnn⟩
        iexists ⟨γd⟩, gid
        isplitl
        · unfold isSession
          iexists optsp, { ttl := ottl, leaseID := W64 0, ctx := GoInterface.ok pctx }, pctx, pcs, ctx', _,
            cancel, dch
          unfold SessionOpts.val cancelSpec sessionDoneChan
          iframe #
          ipureintro; exact ⟨rfl, (⟨Hid, fun h => absurd rfl h⟩ : sessionLeaseOk { ttl := ottl, leaseID := W64 0, ctx := GoInterface.ok pctx } gid).1⟩
        · ipureintro; exact (⟨Hid, fun h => absurd rfl h⟩ : sessionLeaseOk { ttl := ottl, leaseID := W64 0, ctx := GoInterface.ok pctx } gid)
  · (try wp_auto)
    wp_apply context.wp_WithCancel iprop(True) pctx pcs $$ [$Hpctx $Hpcc]
        as %ctx' %γ' %cancel ⟨#Hcancel, #Hctx', #Hcc'⟩
    ihave #Hcancel' := context.cancel_spec_forget _ _ _ $$ Hcancel
    (try wp_auto)
    wp_apply HKA $$ [$Hctx'] as %ka %err Hres
    icases Hres with (%Herr | ⟨%Herr, Hka⟩)
    · cases err with
      | nil => exact absurd rfl Herr
      | ok e =>
        (try wp_auto)
        wp_apply Hcancel'
        · imodintro; itrivial
        (try wp_auto)
        iapply HΦ; ileft; ipureintro; exact ⟨rfl, fun h => by cases h⟩
    · subst Herr
      icases Hka with ⟨%γk, #Hka⟩
      ihave #Hka' := Hka
      iunfold isChanAny at Hka'
      icases Hka' with ⟨#Hkach, #Hkainv⟩
      ihave %Hkann := isChan_not_null $$ Hkach
      (try wp_auto)
      have hkn : ka ≠ chan.nil := Hkann
      rw [decide_eq_false hkn]
      (try wp_auto)
      wp_apply chan.wp_make1 (V := Unit) as %dch %γd ⟨#Hdch, %_, Hdoc⟩
      imod alloc_broadcast_chan iprop(True) γd dch $$ Hdch Hdoc with Hpend
      icases ownBroadcastChan_open _ _ _ _ $$ Hpend with ⟨%γch, #Hint, Hown⟩
      ihave #Hdunk : ownBroadcastChan dch γd iprop(True) .Unknown $$ []
      · iapply ownBroadcastChan_close _ _ _ _ γch
        iframe #
      ihave Hpend : ownBroadcastChan dch γd iprop(True) .Pending $$ [Hown]
      · iapply ownBroadcastChan_close _ _ _ _ γch
        iframe #
        iexact Hown
      (try wp_auto)
      irename cancel => Hcanp
      irename donec => Hdonp
      ipersist Hcanp
      ipersist Hdonp
      ipersist keepAlive
      icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨Hr0, %Hsnn⟩
      iStructNamed Hr0
      ipersist client
      ipersist opts
      ipersist id
      ipersist ctx
      ipersist cancel
      ipersist donec
      wp_apply wp_fork $$ [Hpend]
      · (try wp_auto)
        wp_apply wp_with_defer
        iintro %defer Hdefer
        (try wp_auto)
        ihave IH : iprop(True) $$ []
        · itrivial
        wp_for IH
        (try rw [if_pos (decide_eq_true rfl)])
        (try wp_auto)
        wp_bind (App (Val (chan.receive _)) _)
        iapply chan.wp_receive (V := Loc) ka γk $$ Hkach
        iintro ⟨Hlc1, Hlc2, -, -⟩
        iapply chanAny_recv_au γk ka _ $$ [$Hlc1 $Hlc2] Hka
        inext
        iintro %v %ok
        cases ok
        · (try wp_auto)
          wp_for_post
          wp_apply wp_broadcast_chan_close dch γd iprop(True) $$ [$Hpend] as -
          · imodintro; itrivial
          (try wp_auto)
          wp_apply Hcancel'
          · imodintro; itrivial
          (try wp_auto)
          (try itrivial)
        · (try wp_auto)
          wp_for_post
          iframe
      (try wp_auto)
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact ⟨rfl, Hsnn⟩
      iexists ⟨γd⟩, olid
      isplitl
      · unfold isSession
        iexists optsp, { ttl := ottl, leaseID := olid, ctx := GoInterface.ok pctx }, pctx, pcs, ctx', _,
          cancel, dch
        unfold SessionOpts.val cancelSpec sessionDoneChan
        iframe #
        ipureintro; exact ⟨rfl, (⟨‹¬olid = W64 0›, fun _ => rfl⟩ : sessionLeaseOk { ttl := ottl, leaseID := olid, ctx := GoInterface.ok pctx } olid).1⟩
      · ipureintro; exact (⟨‹¬olid = W64 0›, fun _ => rfl⟩ : sessionLeaseOk { ttl := ottl, leaseID := olid, ctx := GoInterface.ok pctx } olid)


end proof

end concurrency
end EtcdGrove
end Perennial
