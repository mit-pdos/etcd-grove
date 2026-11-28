/-
`hraftnet.admin`'s proof: the servers' connections and the methods, then forever a random sleep, the
server to ask (`adminTarget`), a random request of a random server (`admin_dep`: the deposit from what
the admin knows), its call; the answer is dropped.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.admin
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.adminTarget
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.adminMethods
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.serverConns
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rnd
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.serverID
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.serverAddr
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.apiTimeout
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn__Call
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.CodecApi
public import Perennial.Proof.time.Link

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

open github_com.hashicorp.raft rpctransport service

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : NetProtoGS] [rsem : github_com.hashicorp.raft.Assumptions]

set_option goose.wp.extras true

theorem admin.wp_proof (wp_serverConns : serverConns.spec (GF := GF) (hG := hG))
    (wp_adminMethods : adminMethods.spec (GF := GF))
    (wp_rnd : rnd.spec (GF := GF))
    (wp_adminTarget : adminTarget.spec (GF := GF))
    (wp_serverID : serverID.spec (GF := GF))
    (wp_serverAddr : serverAddr.spec (GF := GF))
    (wp_apiTimeout : apiTimeout.spec (GF := GF))
    (wp_Call : rpctransport.Conn.Call.spec (GF := GF) (hG := hG)) :
    admin.spec (GF := GF) := by
  intro K
  wp_start as ⟨#Hcod, #Hac, %Hrb⟩
  ihave #Hac' := Hac
  iunfold adminCtx at Hac'
  icases Hac' with ⟨%Hss, #Hra, -⟩
  ihave #Hpkr : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply (wp_serverConns K.W) as %csl ⟨%ps, Hcsl, %Hpl, #Hcs⟩
  · iframe #; ipureintro; exact Hrb
  iapply fupd_wp
  imod ownSlice_persist _ _ _ $$ Hcsl with #Hcsl
  imodintro
  (try wp_auto)
  wp_apply wp_adminMethods as %msl ⟨%L, Hms, %HL⟩
  subst HL
  iapply fupd_wp
  imod ownSlice_persist _ _ _ $$ Hms with #Hms
  imodintro
  ihave %Hmlen := ownSlice_len _ _ _ $$ Hms
  ihave %Hclen := ownSlice_len _ _ _ $$ Hcsl
  (try wp_auto)
  wp_for
  wp_apply (wp_rnd (W64 50) (by decide)) as %t0 -
  wp_apply time.wp_Sleep
  (try wp_auto)
  wp_apply (wp_adminTarget K csl ps) as %j %Hj
  · iframe #; ipureintro; exact Hpl
  (try wp_auto)
  have hml : sint.Z msl.len = 6 := by
    have := Hmlen.1; simp only [adminMeths, List.length_cons, List.length_nil] at this; word
  wp_apply (wp_rnd msl.len (by word)) as %k %Hk
  have hk6 : uint.Z k < 6 := by have : uint.Z msl.len = 6 := by word
                                rw [this] at Hk; exact Hk
  wp_apply (wp_rnd (W64 6) (by decide)) as %x %Hx
  have hx : uint.Z x < 6 := Hx
  wp_apply wp_serverID
  wp_apply wp_serverAddr
  have hs1 : 1 ≤ uint.nat (W64 1 + x) ∧ uint.nat (W64 1 + x) ≤ 6 := by constructor <;> word
  have hsx : W64 (((uint.nat (W64 1 + x) : Nat)) : Int) = W64 1 + x := by word
  ipersist «$r0»
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ (ap : Loc) (v' : AdminArgsV) (dq : DFrac),
      args_ptr ↦ ap ∗ ap ↦{dq} AdminArgs.mk v'.id v'.addr ∗
      ⌜adminReq (uint.nat k) (uint.nat (W64 1 + x)) v'⌝)))
    $$ [args] [-]
  · wp_if_destruct
    · wp_apply (wp_rnd (W64 2) (by decide)) as %y -
      wp_if_destruct
      · isplitr; · itrivial
        iexists «$r0_ptr», ⟨[], []⟩, _
        iframe args «$r0»
        ipureintro
        exact ⟨hs1.1, hs1.2, Or.inr ⟨by decide, rfl⟩⟩
      · isplitr; · itrivial
        iexists «$r0_ptr», ⟨sidOf (W64 1 + x), sidOf (W64 1 + x)⟩, _
        iframe args «$r0»
        ipureintro
        exact ⟨hs1.1, hs1.2, Or.inl (by rw [hsx])⟩
    · (try wp_auto)
      isplitr; · itrivial
      iexists «$r0_ptr», ⟨sidOf (W64 1 + x), sidOf (W64 1 + x)⟩, _
      iframe args «$r0»
      ipureintro
      exact ⟨hs1.1, hs1.2, Or.inl (by rw [hsx])⟩
  iintro %v ⟨%hv, %ap, %v', %dq, args, Hap, %Hreq⟩
  subst hv
  ipersist Hap
  (try wp_auto)
  have hks : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z msl.len := by rw [hml]; constructor <;> word
  rw [ite_eq_left hks]
  have hkn : uint.nat k < 6 := by word
  obtain ⟨sm, hsm⟩ : ∃ sm, adminMeths[uint.nat k]? = some sm :=
    ⟨_, List.getElem?_eq_getElem (by simp only [adminMeths, List.length_cons, List.length_nil]; omega)⟩
  have hgd : adminMeths.getD (uint.nat k) go!"" = sm := by
    rw [List.getD_eq_getElem?_getD, hsm]; rfl
  wp_apply wp_load_slice_index msl (sint.Z k) _ DfracDiscarded sm hks.1 $$ [Hms] as -
  · iframe Hms; ipureintro; rw [show (sint.Z k).toNat = uint.nat k by word]; exact hsm
  wp_alloc rp as Hrp
  (try wp_auto)
  wp_apply wp_apiTimeout as %dd -
  have hjn : uint.nat j - 1 < 6 := by word
  obtain ⟨p, hp⟩ : ∃ p, ps[uint.nat j - 1]? = some p :=
    ⟨_, List.getElem?_eq_getElem (by rw [Hpl]; exact hjn)⟩
  have hs : 0 ≤ sint.Z (j - W64 1) ∧ sint.Z (j - W64 1) < sint.Z csl.len := by
    have h1 := Hclen.1; rw [Hpl] at h1; constructor <;> word
  rw [ite_eq_left hs]
  have hidx : (sint.Z (j - W64 1)).toNat = uint.nat j - 1 := by word
  wp_apply wp_load_slice_index csl (sint.Z (j - W64 1)) _ DfracDiscarded p hs.1 $$ [Hcsl] as -
  · iframe Hcsl; ipureintro; rw [hidx]; exact hp
  ihave #Hc := BigSepL.bigSepL_lookup hp $$ Hcs
  ihave ⟨%M, %HM, #Hdep⟩ := admin_dep K (uint.nat k) (uint.nat (W64 1 + x)) hkn v' Hreq $$ Hac
  rw [hgd] at HM
  wp_apply (wp_Call p K.W (serverAddrs.getD (uint.nat j - 1) go!"") sm go!"API" M (apiSvcK K)
      (ptrI AdminArgs.ty ap) (ptrI AdminReply.ty rp) adminAns iprop(True)
      iprop(rp ↦ (Perennial.zero_val AdminReply)) (fun _ _ => iprop(True))
      hraftCodec dd iprop(True))
    $$ [$Hc $Hcod Hrp] as %r -
  · isplitr
    · ipureintro
      refine ⟨HM, ?_, by simp [ptrI, interface.mkOk]⟩
      rw [Hss.1 (uint.nat j) go!"API" (by word) (by word)]
      simp [rpctransport.svcName]
    isplitr
    · ipureintro; exact adminMeths_len sm (List.mem_of_getElem? hsm)
    isplitr
    · itrivial
    isplitr
    · iintro -
      iapply (enc_AdminArgs ap DfracDiscarded (AdminArgs.mk v'.id v'.addr) v')
      iframe Hap
      isplitr
      · unfold adminArgsOwn; ipureintro; exact ⟨rfl, rfl⟩
      iintro - -
      isplitr
      · ipureintro; exact adminReq_length _ _ v' Hreq
      isplitl
      · iexact Hdep
      itrivial
    iframe Hrp
    imodintro
    simp only [adminAns]
    iintro HD %rep %Hrep
    obtain ⟨r, rfl⟩ := Hrep (by simp)
    iapply (dec_AdminReply _ r)
    iframe HD
    iintro %w - -
    itrivial
  (try wp_auto)
  wp_for_post
  iframe

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
