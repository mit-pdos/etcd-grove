/-
`vsrnet.Op` (notes/dsv-vr.md): client machine `c`'s operation through its go-vsr client, in
remote's form (`opMaybe`, the far side's store `kvR γ.gn`), for one call: from the system's
resource `sysRes γ c sys n` (its request counter `n`, below the ghost layer's budget 2^28) and the
slot's update, it returns the update's output, or the unknown output, and the system's resource
with the counter at most one further.

Ported from dsverify-lab `examples/vr/proof/VsrProof/Top/Op.lean` (`wp_Op_proof`): the operation
registers its request with the update (`ghost_register`, the update made the ghost layer's by
`lin_AUof`), sends it (`Request`), runs the client's loop (`Recv`/`Submit`, `Run`, `CheckResult`,
`OpPolls` rounds), and on a reply retrieves the update's postcondition (`ghost_retrieve`); after the
last round it gives up, the update left registered (helping). Changed: the client's resources are
the system's resource itself (no invariant, `ClientDefs.lean`); an output is a `KOut` (a reply's
value is short: `ghost_reply_short`); the first call's start-up sleep.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.ClientDefs
public import Perennial.Spec.time.Sleep
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.json

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open VsrModel VsrGhost

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

attribute [local instance] GooseGlobalGS.gooseInvGS
attribute [local instance] Perennial.github_com.tangledbytes.go_vsr.examples.vsrnet.jsonCodec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable [bvi : go.BasicIntoValInj]
variable [encoding.json.DecoderRep GF]

local notation "kpkg" => pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet

set_option goose.wp.extras true

/-- The slot's update as the ghost layer's (`lin_AUof`; a read's persistent one, used once). -/
theorem slotUpd_AUof (g : Impl.GN) (i : KIn) (Φ : KOut → IProp GF) :
    slotUpd (Gg := hG.goose_globalGS) (kvR g) i Φ ⊢ Impl.AUof g i.1 (fun _ _ o => Φ (bndO o)) := by
  cases hw : (kvR (GF := GF) (Gg := hG.goose_globalGS) g).B.isWrite i
  · rw [slotUpd_read _ hw]
    iintro #H
    iapply lin_AUof
    iexact H
  · rw [slotUpd_write _ hw]
    iintro H
    iapply lin_AUof
    iexact H

/-- **`Op(sys, in)`, one call** (see the file header). -/
abbrev Op.spec : Prop :=
  ∀ (γ : Names) (c n : Nat) (sys : GoInterface) (i : KIn) (Φ : KOut → IProp GF),
  c < 6 → n < 2 ^ 28 →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ sysRes γ c sys n ∗
      slotUpd (Gg := hG.goose_globalGS) (kvR γ.gn) i Φ }}
    (App (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.Op)) (Val #sys))
      (Val #((kvR (GF := GF) (Gg := hG.goose_globalGS) γ.gn).iv i)))
  {{ (v : GoInterface), RET #v; ∃ n', ⌜n ≤ n' ∧ n' ≤ n + 1⌝ ∗ sysRes γ c sys n' ∗
      ((∃ o, ⌜v = (kvR (GF := GF) (Gg := hG.goose_globalGS) γ.gn).ov o⌝ ∗ Φ o) ∨
        ⌜v = (kvR (GF := GF) (Gg := hG.goose_globalGS) γ.gn).unk i⌝) }}

set_option maxRecDepth 10000 in
theorem Op.wp_proof
    (wp_Request : pkg.client.Client.Request.spec (GF := GF) (hG := hG))
    (wp_Submit : pkg.client.Client.Submit.spec (GF := GF) (hG := hG))
    (wp_Run : pkg.client.Client.Run.spec (GF := GF) (hG := hG)) :
    Op.spec (GF := GF) (hG := hG) := by
  intro γ c n sys i Ψ hc hn
  wp_start as ⟨Hres, HU⟩
  ihave #Hcp : isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.client $$ []
  · iPkgInit
  ihave #Hnp : isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.network $$ []
  · iPkgInit
  unfold sysRes
  icases Hres with ⟨%x, %tcp, %vc, %st, %gu, %cst, %N, %Hsys, Hx, #Htcp, Hcl, Hnext, #HsysI,
    #HregI, #Hsize, %Hinv⟩
  subst Hsys
  ihave HAU := slotUpd_AUof γ.gn i Ψ $$ HU
  wp_auto
  -- the first call's start-up sleep
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
      x ↦ Sys.mk tcp vc (W64 (c : Int)) true gu ∗ x_ptr ↦ x))) $$ [Hx x]
  · cases st
    · wp_auto
      wp_apply time.wp_Sleep
      iframe
      itrivial
    · wp_auto
      iframe
      itrivial
  iintro %v ⟨%Hv, Hx, x⟩
  subst Hv
  wp_auto
  cases gu
  case true =>
    -- the client gave up before: the unknown output, the update unused
    wp_auto
    iapply HΦ
    iexists n
    isplitr
    · ipureintro; omega
    isplitl [Hx Hcl Hnext]
    · iexists x, tcp, vc, true, true, cst, N
      iframe
      iframe #
      ipureintro
      exact ⟨rfl, Hinv.1, fun h => nomatch h⟩
    iright
    ipureintro
    rfl
  obtain ⟨hn1, hpend, hsn⟩ : 1 ≤ n ∧ cst.pend = none ∧ cst.n + 1 = n := ⟨Hinv.1, Hinv.2 rfl⟩
  wp_auto
  -- register the request with the update (before `Request`)
  have hk := i.2
  iapply fupd_wp
  imod ghost_register γ ⊤ CoPset.subseteq_top CoPset.subseteq_top N (c + 1) n i.1 hk.1
    ⟨by omega, by omega⟩ ⟨hn1, hn⟩ hk.2.1 _ $$ Hsize HsysI HregI Hnext HAU
    with ⟨Hnext, #Hfreq, Htk⟩
  have hmb : MsgBound (.request n (c + 1) (encOp i.1)) := ⟨by omega, by omega⟩
  imod (ghost_pure γ ⊤ CoPset.subseteq_top [.msg (.request n (c + 1) (encOp i.1))]
    ((VsrWire.line (.request n (c + 1) (encOp i.1))).length < 2 ^ 60)
    (fun s' hI hf => VsrWire.line_bound s' hI _ (hf _ (List.mem_singleton_self _)) hmb))
    $$ HsysI [] with %hline
  · iapply BigSepL.bigSepL_cons.2
    isplitl []
    · iexact Hfreq
    iapply BigSepL.bigSepL_nil.2; itrivial
  imodintro
  -- the operation string is `encOp i`
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
      kv_ptr ↦ In.mk (inFields i.1).1 (inFields i.1).2.1 (inFields i.1).2.2 ∗
      op_ptr ↦ encOp i.1))) $$ [kv op]
  · rcases i with ⟨ii, hii⟩
    cases ii with
    | get k =>
      simp only [inFields]
      wp_auto
      iframe
      ipureintro; rfl
    | put k v =>
      simp only [inFields]
      wp_auto
      iframe
      simp only [encOp, List.append_assoc]
      iframe
      itrivial
  iintro %v ⟨%Hv, kv, op⟩
  subst Hv
  wp_auto
  obtain ⟨sn, spend⟩ := cst
  simp only at hpend hsn
  subst hpend hsn
  wp_apply (wp_Request vc γ (c + 1) sn (encOp i.1)) $$ [Hcl] as %b0 Hcl
  · iframe
    iframe #
    isplitr
    · ipureintro; omega
    isplitr
    · ipureintro; exact encOp_plain i.1 hk.1
    isplitr
    · ipureintro; exact hmb
    ipureintro; exact hline
  ihave HI : (∃ iv : w64, "i" ∷ i_ptr ↦ iv : IProp GF) $$ [i]
  · iexists _; iexact i
  wp_for HI
  by_cases hlt : uint.Z iv < uint.Z (W64 1600)
  · -- a round: the received events submitted, `Run`, `CheckResult`
    simp only [hlt, _root_.decide_true, ↓reduceIte]
    wp_auto
    wp_for
    dsimp only
    wp_apply (pkg.network.TCP.Recv.wp tcp γ (meC c)) as %ev %okr Hev
    · iframe #
    rcases okr with _ | _
    rotate_left
    · -- an event: submitted
      simp only [↓reduceIte]
      icases Hev with ⟨%m, #Hevm, #Hfm, #Haddr, -⟩
      wp_auto
      wp_apply (wp_Submit vc γ (c + 1) _ tcp ev) $$ [Hcl] as Hcl
      · iframe
        unfold pkg.network.netEvOk
        iexists m
        iframe #
      wp_for_post
      iframe
    wp_auto
    wp_for_post
    wp_apply (wp_Run vc γ (c + 1) _) $$ [Hcl] as Hcl
    · iframe
    wp_apply (lc := 1) (pkg.client.Client.CheckResult.wp vc γ (c + 1) _) $$ [Hcl]
      as %rep %okc Hres
    · iframe
    rcases okc with _ | _
    · -- no reply yet: the next round
      simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      wp_apply time.wp_Sleep
      wp_for_post
      iframe
      iexists _
      iframe
    simp only [↓reduceIte]
    icases Hres with ⟨%Hrep, Hcl, #Hfrep⟩
    -- the reply: retrieve the update's postcondition
    iapply fupd_wp
    imod ghost_retrieve γ ⊤ CoPset.subseteq_top CoPset.subseteq_top (c + 1) (sn + 1)
      (uint.nat rep.ViewNum') i.1 _ rep.Result' $$ Hlc1 HsysI HregI Htk Hfrep
      with ⟨%σ, %σ', HQ, %Hstep⟩
    imod ghost_reply_short γ ⊤ CoPset.subseteq_top _ _ _ _ $$ HsysI Hfrep with %Hshort
    imodintro
    rcases i with ⟨ii, hii⟩
    cases ii with
    | put k v =>
      simp only [inFields]
      wp_auto
      wp_for_post
      iapply HΦ
      iexists (sn + 1 + 1)
      isplitr
      · ipureintro; omega
      isplitl [Hx Hcl Hnext]
      · iexists x, tcp, vc, true, false, ⟨sn + 1, none⟩, N
        iframe
        iframe #
        ipureintro
        exact ⟨rfl, by omega, fun _ => ⟨rfl, rfl⟩⟩
      ileft
      iexists (bndO .done)
      isplitr
      · ipureintro; rw [bndO_of (o := .done) trivial]; rfl
      simp only [outOfReply]
      iexact HQ
    | get k =>
      simp only [inFields]
      wp_auto
      by_cases hres : rep.Result' = []
      · simp only [hres, _root_.decide_true]
        wp_auto
        wp_for_post
        iapply HΦ
        iexists (sn + 1 + 1)
        isplitr
        · ipureintro; omega
        isplitl [Hx Hcl Hnext]
        · iexists x, tcp, vc, true, false, ⟨sn + 1, none⟩, N
          iframe
          iframe #
          ipureintro
          exact ⟨rfl, by omega, fun _ => ⟨rfl, rfl⟩⟩
        ileft
        iexists (bndO (.got none))
        isplitr
        · ipureintro; rw [bndO_of (o := .got none) trivial]; rfl
        simp only [outOfReply, ↓reduceIte]
        iexact HQ
      · simp only [hres, _root_.decide_false]
        wp_auto
        wp_for_post
        iapply HΦ
        iexists (sn + 1 + 1)
        isplitr
        · ipureintro; omega
        isplitl [Hx Hcl Hnext]
        · iexists x, tcp, vc, true, false, ⟨sn + 1, none⟩, N
          iframe
          iframe #
          ipureintro
          exact ⟨rfl, by omega, fun _ => ⟨rfl, rfl⟩⟩
        ileft
        iexists (bndO (.got (some rep.Result')))
        isplitr
        · ipureintro; rw [bndO_of (o := .got (some rep.Result')) Hshort]; rfl
        simp only [outOfReply, hres, ↓reduceIte]
        iexact HQ
  · -- no reply after `OpPolls` rounds: give up, the unknown output, the update left registered
    simp only [hlt, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    iexists (sn + 1 + 1)
    isplitr
    · ipureintro; omega
    isplitl [Hx Hcl Hnext]
    · iexists x, tcp, vc, true, true, ⟨sn + 1, some (encOp i.1)⟩, N
      iframe
      iframe #
      ipureintro
      exact ⟨rfl, by omega, fun h => nomatch h⟩
    iright
    ipureintro
    rfl

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
