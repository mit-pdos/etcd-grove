-- The copy for the part `KvNet/` of `Net/Proof/net/Conn__Read.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The proof of `Net/Spec/net/Conn__Read.lean`: the interface call resolves to `conn.Read.impl`
(`*TCPConn`'s promoted `Read`), whose extension `Read` takes the caller's update
(`Net.wp_net_Read`); the bytes are then copied into the buffer.
-/
module

public import KvNet.Spec.net.Conn__Read
public import KvNet.Proof.net.OpErrorMsg

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions]
variable [go.BasicIntoValInj]

theorem Conn.Read.wp_proofLc : Conn.Read.specLc (GF := GF) (hG := hG) := by
  intro t cn s a la ra b bs0 eof ed Q
  unfold connAt connFd
  wp_start as ⟨⟨%nw, %Hnw, ⟨%fd, #Ht, #Hfd⟩, #Hla, #Hra, #Hat⟩, Hsl, #Heof, #Hed, HAU⟩
  ihave #HE := _root_.Perennial.io.eof_of_init $$ Hpkg
  unfold _root_.Perennial.errors.newVar
  icases HE with ⟨%xe, #Hxe, -⟩
  icombine Heof Hxe gives %heof
  ihave ⟨%xd, #Hxd⟩ := _root_.Perennial.internal.poll.errDeadlineExceeded_of_pkgInit $$ Hpkg2
  icombine Hed Hxd gives %hed
  subst heof hed
  ihave ⟨%v, %hv, #Hv⟩ := fdAt_elim _ _ _ _ _ $$ Hfd
  obtain ⟨-, rfl, rfl, rfl⟩ := hv
  ihave %Hfdn := typedPointsto_not_null _ _ _ $$ Hv
  ihave #Ht2 := Ht
  iStructNamed Ht2
  iStructNamed Hv
  (try wp_method_call)
  wp_auto
  wp_apply wp_conn_ok _ fd Hfdn $$ conn
  iStructNamed conn
  wp_auto
  wp_apply wp_fd_Read fd cn s a _ _ _ b bs0 _ _ Q $$ Hfd Hat Hsl Heof Hed HAU
    as %r %bs' %k %e HQ Hsl %Hout #He Hlc1 Hlc2
  cases r with
  | bytes bs =>
    unfold fdReadErr; icases He with %he; subst he
    wp_auto
    iapply HΦ
    iexists .bytes bs, bs'
    iframe HQ Hsl Hlc1 Hlc2
    isplitr; · ipureintro; exact Hout
    unfold ReadErr; ipureintro; rfl
  | eof =>
    unfold fdReadErr; icases He with %he; subst he
    wp_auto
    iapply HΦ
    iexists .eof, bs'
    iframe HQ Hsl Hlc1 Hlc2
    isplitr; · ipureintro; exact Hout
    unfold ReadErr; ipureintro; rfl
  | err k =>
    unfold fdReadErr; dsimp only
    ihave %hne := kindErr_ne_nil k _ _ e (fun _ h => by cases h; unfold interface.mkOk; exact fun h' => by cases h') $$ He
    obtain ⟨ie, rfl⟩ : ∃ ie, e = GoInterface.ok ie := by
      cases e with | ok ie => exact ⟨ie, rfl⟩ | nil => exact absurd rfl hne
    ihave %hty : ⌜ie.ty ≠ go.GoType.PointerType _root_.Perennial.errors.errorString.ty⌝ $$ [He]
    · cases k
      · unfold kindErr; dsimp only; icases He with %h; ipureintro
        unfold closedErr interface.mkOk at h; cases h
        exact fun h => by simp only [goose_wp_simp_extra] at h
      · unfold kindErr; dsimp only; icases He with %h; ipureintro
        unfold interface.mkOk at h; cases h
        exact fun h => by simp only [goose_wp_simp_extra] at h
      · unfold kindErr sysErr; dsimp only
        icases He with ⟨%p, %name, %n, %h, -⟩; ipureintro
        unfold interface.mkOk at h; cases h.1
        exact fun h => by simp only [goose_wp_simp_extra] at h
    wp_auto
    rw [ite_cond_eq_false _ _ (eq_false hty)]
    wp_auto
    wp_alloc pe as Hpe
    ipersist Hpe
    wp_auto
    iapply HΦ
    iexists .err k, bs'
    iframe HQ Hsl Hlc1 Hlc2
    isplitr; · ipureintro; exact Hout
    unfold ReadErr; dsimp only
    iapply resErr_intro Hnw
      (by first | exact edTyped_none | (intro x h; cases h; exact ⟨_, rfl⟩)) $$ Hpe He
    all_goals first | iapply addrOrNil_nil | (iapply addrOrNil_addr; iassumption)

/-- `Conn.Read.spec`, from `Conn.Read.specLc`: the count as `ReadOut`'s, the credits dropped. -/
theorem Conn.Read.wp_proof : Conn.Read.spec (GF := GF) (hG := hG) := by
  intro t cn s a la ra b bs0 eof ed Q
  iintro %Φ H HΦ
  iapply Conn.Read.wp_proofLc t cn s a la ra b bs0 eof ed Q $$ H
  inext
  iintro %k %err ⟨%r, %bs', HQ, Hsl, %Hout, He, -, -⟩
  iapply HΦ
  iexists r, bs'
  iframe HQ Hsl He
  ipureintro
  cases r with
  | bytes bs =>
    obtain ⟨h1, h2⟩ := Hout
    refine ⟨?_, h2⟩
    simp only [sint.nat, h1]; omega
  | eof => exact Hout
  | err k => exact Hout

end proof

end net
end Perennial
