/-
**The auth realization's lifecycle** (auth-schema-srv A6, 2026-11-18): the per-backend invariant
(`AuthRealInv.lean`) meets `auth.authBkLife` at the realization's open share `authOpenQ` (`real_life`):
retire (the write token excludes a batch, so the buckets are idle and the lock's share of the history leaves
with the retired token and the succession right), release (the whole currency and the write token refute every
acquiring reader of both pools, `pool_release_later`; the free and held slots' shares and the rest `q0` make
`authOpenQ`), publish (the store's half, the apply thread's quarter and the realization's quarter of the
published index make the whole, raised to the history's last index; the buckets are idle at it). None takes a
later credit: what leaves the invariant is timeless. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthRealRsv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authReal

open Iris Iris.BI Iris.ProofMode backend

section life
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

instance inhGMapNatOQ : Inhabited (GMap Nat (Option Qp)) := ⟨∅⟩
instance inhBktData : Inhabited BktData := ⟨∅⟩
instance inhAuthSess : Inhabited auth.AuthSess := ⟨auth.AuthSess.init⟩

instance bOpen_timeless' (γ : BNames) (q : Qp) : Timeless (bOpen (GF := GF) γ q) := by
  unfold bOpen; infer_instance

instance tokIn_timeless (T : IProp GF) [Timeless T] (a : Nat) : Timeless (tokIn T a) := by
  match a with
  | 0 => unfold tokIn; exact (inferInstance : Timeless (iprop(True) : IProp GF))
  | 1 => unfold tokIn; exact (inferInstance : Timeless T)
  | n + 2 => unfold tokIn; exact (inferInstance : Timeless (iprop(False) : IProp GF))

instance ticketsIn_timeless (γt : GName) (K a : Nat) : Timeless (ticketsIn (GF := GF) γt K a) := by
  unfold ticketsIn; infer_instance

instance depT_timeless (γ : RNames) (o : Option Qp) : Timeless (depT (GF := GF) γ o) := by
  cases o with
  | some q => dsimp only [depT]; unfold auth.authCur; infer_instance
  | none => dsimp only [depT]; unfold auth.authWTok; infer_instance

instance succ_timeless (γa : auth.AuthNames) : Timeless (auth.authSucc (GF := GF) γa) := by
  unfold auth.authSucc; infer_instance

instance retired_timeless (γc : auth.AuthBkNames) : Timeless (auth.authRetired (GF := GF) γc) := by
  unfold auth.authRetired; infer_instance

instance cur_timeless (γc : auth.AuthBkNames) (q : Qp) : Timeless (auth.authCur (GF := GF) γc q) := by
  unfold auth.authCur; infer_instance

instance pubQ_timeless (γa : auth.AuthNames) (q : Qp) (p : Nat) : Timeless (auth.authPubQ (GF := GF) γa q p) := by
  unfold auth.authPubQ; infer_instance

instance pubTok_timeless (γa : auth.AuthNames) : Timeless (auth.authPubTok (GF := GF) γa) := by
  unfold auth.authPubTok; infer_instance

instance liveP_timeless (γ : RNames) (p : Nat) : Timeless (liveP (GF := GF) γ p) := by
  unfold liveP; infer_instance

instance bkTok_timeless (γ : RNames) (q : Qp) (x : BktData × BktData × BktData) :
    Timeless (bkTok (GF := GF) γ q x) := by
  unfold bkTok; infer_instance

instance bkSw_timeless (γ : RNames) (q : Qp) (w : auth.AuthSess) :
    Timeless (bkSw (GF := GF) γ q w) := by
  unfold bkSw; infer_instance

instance batchTok_timeless (γ : RNames) : Timeless (batchTok (GF := GF) γ) := by
  unfold batchTok; infer_instance

instance wTok_timeless (γc : auth.AuthBkNames) : Timeless (auth.authWTok (GF := GF) γc) := by
  unfold auth.authWTok; infer_instance

/-- **Release a pool from inside an invariant** (`pool_release` under a later): the deposits, the counts and
the shares are timeless; the free slots' tokens stay behind. -/
theorem pool_release_later (E : CoPset) (γm γh : GName) (Rs : Nat → IProp GF) (dep : Option Qp → IProp GF)
    (tok sh Z : IProp GF) (N : Nat) (hZ : ∀ d a, dep d ∗ Rs (a + 1) ∗ Z ⊢ False)
    [hRs : ∀ a, Timeless (Rs a)] [hdep : ∀ d, Timeless (dep d)] [hsh : Timeless sh] :
    ▷ poolSt γm γh Rs dep tok sh N ∗ Z ⊢
      |={E}=> poolRel γm γh Rs ∗ Z ∗ ([∗list] _x ∈ List.replicate N (), sh) := by
  iintro ⟨Hp, HZ⟩
  iunfold poolSt at Hp
  icases Hp with ⟨%m, %nx, %kh, >Hm, >Hds, >HRs, >Hh, >Hsh, Hf, >%Hb⟩
  ihave Hf : iprop(▷ [∗list] _x ∈ List.replicate (N - (kh + m.size)) (), sh) $$ [Hf]
  · inext; iapply rep_snd tok sh _ $$ Hf
  icases Hf with >Hf
  by_cases h0 : m.size = 0
  · rw [h0]
    simp only [Nat.add_zero]
    imodintro
    iframe HZ
    isplitl [Hm HRs Hh]
    · iunfold poolRel; iexists m, kh; iframe Hm HRs Hh; ipureintro; exact h0
    ihave H := rep_add sh kh (N - kh) $$ [$Hsh $Hf]
    rw [show kh + (N - kh) = N by omega]
    iexact H
  · obtain ⟨k, v, hk⟩ := (map_size_ne_0_lookup m).mp h0
    icases (BigSepM.bigSepM_delete (Φ := fun (_ : Nat) (d : Option Qp) => dep d) hk).1 $$ Hds with ⟨Hd, -⟩
    iexfalso
    rw [show kh + m.size = (kh + m.size - 1) + 1 by omega]
    iapply hZ v (kh + m.size - 1) $$ [$Hd $HRs $HZ]

theorem authRealN_authRev : (↑authRealN : CoPset) ⊆ ⊤ \ ↑(nroot.@"authRev") := by
  unfold authRealN
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' => ndot_ne_disjoint nroot (by decide : "authReal" ≠ "authRev") p ⟨hp, h'⟩⟩

theorem retired_excl (γc : auth.AuthBkNames) : auth.authRetired (GF := GF) γc ∗ auth.authRetired γc ⊢ False := by
  unfold auth.authRetired
  iintro ⟨H1, H2⟩
  iapply token_exclusive $$ H1 H2

theorem qp_quarters : (1 : Qp).half + ((1 : Qp).half.half + (1 : Qp).half.half) = 1 := by
  rw [Qp.half_add_half, Qp.half_add_half]

theorem pub_join (γ : GName) (n : Nat) :
    monoNatAuthOwn (GF := GF) γ 1 n ⊣⊢ monoNatAuthOwn γ (1 : Qp).half n ∗
      monoNatAuthOwn γ (1 : Qp).half.half n ∗ monoNatAuthOwn γ (1 : Qp).half.half n := by
  have h1 := (monoNatAuthOwn_fractional (GF := GF) γ n).fractional (1 : Qp).half
    ((1 : Qp).half.half + (1 : Qp).half.half)
  have h2 := (monoNatAuthOwn_fractional (GF := GF) γ n).fractional (1 : Qp).half.half (1 : Qp).half.half
  rw [qp_quarters] at h1
  constructor
  · iintro H
    icases h1.1 $$ H with ⟨Ha, Hb⟩
    icases h2.1 $$ Hb with ⟨Hb, Hc⟩
    iframe Ha Hb Hc
  · iintro ⟨Ha, Hb, Hc⟩
    iapply h1.2
    iframe Ha
    iapply h2.2
    iframe Hb Hc

/-- **Retire.** The apply thread's publication quarter (at the live branch's `p`, by agreement) stays with the
retired realization for its views; the realization's own quarter and the live token go back to the store's vault,
which gives the succession right back (V-pub). -/
theorem real_retire (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) :
    realInv (GF := GF) γ d s0 q0 ∗ vaultInv γ.γa γ.γv ⊢ auth.authWTok γ.γc ∗ auth.authPubTok γ.γa ={⊤}=∗
      (∃ st : auth.AuthState, auth.authLockI (.on γ.γa) st) ∗ auth.authRetired γ.γc ∗ auth.authSucc γ.γa := by
  iintro ⟨#Hinv, #Hvi⟩ ⟨HT, Hpt⟩
  iunfold realInv at Hinv
  iinv Hinv with Hi Hclose
  iunfold realSt at Hi
  icases Hi with ⟨%cs, %sa, %su, %sr, %ja, %ju, %jr, %p, Hc, Hl⟩
  icases Hl with (⟨>Hs, >Hr, Hp, Hb⟩ | ⟨Hpt', Hp, Hq, >HT', Hbt⟩ | ⟨Hcur, Hr, Hpr, >HT', Hbt⟩)
  · icases Hb with (Hid | Hbb)
    · iunfold bkIdle at Hid
      icases Hid with ⟨%hs, %rc, %w, >Hlq, -, >Hbt, -, Hq, >%Hid⟩
      ihave Hbt : batchTok γ $$ [Hbt]
      · iunfold batchTok; iexists _; iexact Hbt
      iunfold liveP at Hs
      icases Hs with ⟨Hpq, Hlv⟩
      iunfold auth.authPubTok at Hpt
      icases Hpt with ⟨%p2, Hpt⟩
      iunfold auth.authPubQ at Hpt Hpq
      ihave %Ha := monoNatAuthOwn_agree γ.γa.pub _ _ p p2 $$ Hpq Hpt
      obtain ⟨-, hp⟩ := Ha
      subst hp
      iunfold bkCommon at Hc
      icases Hc with ⟨Ha, Hu, Hr', #Hsa, #Hsu, #Hsr, >%Hv⟩
      imod Hclose $$ [Ha Hu Hr' Hp Hq HT Hpt Hbt]
      · inext
        iunfold realSt
        iexists cs, sa, su, sr, ja, ju, jr, p
        isplitl [Ha Hu Hr']
        · iunfold bkCommon; iframe Ha Hu Hr'; iframe #; ipureintro; exact Hv
        iright; ileft
        isplitl [Hpt]
        · iunfold auth.authPubQ; iexact Hpt
        iframe Hp Hq HT Hbt
      iunfold vaultInv at Hvi
      iinv Hvi with Hv Hvclose
      iunfold pubVault at Hv
      icases Hv with (⟨-, >Hlv'⟩ | >Hsucc)
      · iexfalso; iapply token_exclusive $$ Hlv Hlv'
      imod Hvclose $$ [Hpq Hlv]
      · inext
        iunfold pubVault
        ileft
        iframe Hlv
        iexists p, ja, sa
        iframe Hsa
        isplitl [Hpq]
        · iunfold auth.authPubQ; iexact Hpq
        ipureintro; obtain ⟨-, h1, -, h3, -⟩ := Hv; omega
      imodintro
      iframe Hsucc Hr
      iexists sa
      iunfold auth.authLockI
      iexists hs
      simp only [auth.authLockShare, auth.histLast]
      iframe Hlq
      ipureintro; exact Hid.1
    · iunfold bkBatch at Hbb
      icases Hbb with ⟨>HT', -⟩
      iexfalso; iapply wTok_excl γ.γc $$ [$HT $HT']
  · iexfalso; iapply wTok_excl γ.γc $$ [$HT $HT']
  · iexfalso; iapply wTok_excl γ.γc $$ [$HT $HT']

/-- **Release.** -/
theorem real_release (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (hq : authOpenQ = qpRep q0 s0 authRdN) :
    realInv (GF := GF) γ d s0 q0 ⊢ auth.authRetired γ.γc ∗ auth.authCur γ.γc 1 ={⊤}=∗
      bOpen d.γB authOpenQ ∗ auth.authPubTok γ.γa := by
  iintro #Hinv ⟨HR, Hcur⟩
  iunfold realInv at Hinv
  iinv Hinv with Hi Hclose
  iunfold realSt at Hi
  icases Hi with ⟨%cs, %sa, %su, %sr, %ja, %ju, %jr, %p, Hc, Hl⟩
  icases Hl with (⟨Hs, >Hr, Hp, Hb⟩ | ⟨>Hpt, Hp, >Hq, >HT, Hbt⟩ | ⟨Hcur', >Hr, Hpr, HT', Hbt⟩)
  · iexfalso; iapply retired_excl γ.γc $$ [$HR $Hr]
  · iunfold pools at Hp
    icases Hp with ⟨Hp1, Hp2⟩
    imod pool_release_later _ γ.γm γ.γh (ticketsIn γ.γt ticketN) (depT γ) _ _
      iprop(auth.authCur γ.γc 1 ∗ auth.authWTok γ.γc) ticketN
      (fun o a => by iintro ⟨Hd, -, Hc, HT⟩; iapply depT_released γ o $$ [$Hd $Hc $HT])
      $$ [$Hp1 $Hcur $HT] with ⟨Hr1, ⟨Hcur, HT⟩, Hs1⟩
    imod pool_release_later _ γ.γm' γ.γh' (tokIn (auth.authWTok γ.γc)) (fun _ => iprop(True)) _ _
      iprop(auth.authCur γ.γc 1 ∗ auth.authWTok γ.γc) 1
      (fun o a => by
        iintro ⟨-, HRs, -, HT⟩
        iapply tokIn_T _ (wTok_excl γ.γc) (a + 1) (by omega) $$ [$HRs $HT])
      $$ [$Hp2 $Hcur $HT] with ⟨Hr2, ⟨Hcur, HT⟩, Hs2⟩
    imod Hclose $$ [Hc Hcur HR Hr1 Hr2 HT Hbt]
    · inext
      iunfold realSt
      iexists cs, sa, su, sr, ja, ju, jr, p
      iframe Hc
      iright; iright
      iframe Hcur HR HT Hbt
      iunfold poolsRel
      iframe Hr1 Hr2
    imodintro
    isplitl [Hpt]
    · iunfold auth.authPubTok; iexists p; iexact Hpt
    ihave Hs := rep_add (bOpen d.γB s0) ticketN 1 $$ [$Hs1 $Hs2]
    have hn : ticketN + 1 = authRdN := by unfold ticketN authRdN; omega
    rw [hn]
    rw [hq]
    iapply (bOpen_rep d.γB q0 s0 authRdN).2
    iframe Hq Hs
  · iexfalso; iapply retired_excl γ.γc $$ [$HR $Hr]

/-- **Publish.** -/
theorem real_publish (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) :
    realInv (GF := GF) γ d s0 q0 ⊢ ∀ (hs : List auth.AuthState) (p : Nat), auth.authWTok γ.γc -∗
      auth.authPubTok γ.γa -∗ auth.authHistHalf γ.γa hs -∗ auth.authPubQ γ.γa (1 : Qp).half p -∗
      ⌜p + 1 ≤ hs.length⌝ ={⊤ ∖ ↑(nroot.@"authRev")}=∗
      auth.authWTok γ.γc ∗ auth.authPubTok γ.γa ∗ auth.authHistHalf γ.γa hs ∗
        auth.authPubQ γ.γa (1 : Qp).half (hs.length - 1) := by
  iintro #Hinv %hs %p HT Hpt Hhh Hph %Hle
  iunfold realInv at Hinv
  iinv Hinv with Hi Hclose
  · exact authRealN_authRev
  iunfold realSt at Hi
  icases Hi with ⟨%cs, %sa, %su, %sr, %ja, %ju, %jr, %p', Hc, Hl⟩
  icases Hl with (⟨Hs, Hr, Hp, Hb⟩ | ⟨Hpt', Hp, Hq, >HT', Hbt⟩ | ⟨Hcur, Hr, Hpr, >HT', Hbt⟩)
  · icases Hb with (Hid | Hbb)
    · iunfold bkIdle at Hid
      icases Hid with ⟨%hs', %rc, %w, >Hlq, Hro, Hbt, Hsw, Hq, >%Hid⟩
      ihave %Heq := auth.authHistHalf_lockQ_agree γ.γa hs hs' $$ Hhh Hlq
      subst Heq
      obtain ⟨hl, hu, hr, hja, hju, hjr, hcs⟩ := id Hid
      iunfold bkCommon at Hc
      icases Hc with ⟨Ha, Hu, Hr', Hsa, Hsu, Hsr, >%Hv⟩
      iunfold liveP at Hs
      icases Hs with ⟨>Hpq, Hlv⟩
      iunfold auth.authPubTok at Hpt
      icases Hpt with ⟨%p2, Hpt⟩
      iunfold auth.authPubQ at Hph Hpt Hpq
      ihave %Ha1 := monoNatAuthOwn_agree γ.γa.pub _ _ p p2 $$ Hph Hpt
      ihave %Ha2 := monoNatAuthOwn_agree γ.γa.pub _ _ p p' $$ Hph Hpq
      obtain ⟨-, rfl⟩ := Ha1
      obtain ⟨-, rfl⟩ := Ha2
      ihave Hfull := (pub_join γ.γa.pub p).2 $$ [$Hph $Hpt $Hpq]
      imod mono_nat_own_update (hs.length - 1) (by omega) $$ Hfull with ⟨Hfull, -⟩
      icases (pub_join γ.γa.pub (hs.length - 1)).1 $$ Hfull with ⟨Hph, Hpt, Hpq⟩
      imod Hclose $$ [Ha Hu Hr' Hsa Hsu Hsr Hpq Hlv Hr Hp Hq Hlq Hro Hbt Hsw]
      · inext
        iunfold realSt
        iexists cs, sa, su, sr, ja, ju, jr, hs.length - 1
        isplitl [Ha Hu Hr' Hsa Hsu Hsr]
        · iunfold bkCommon
          iframe Ha Hu Hr' Hsa Hsu Hsr
          ipureintro
          exact ⟨Hv.1, Hv.2.1, Hv.2.2.1, by omega, by omega⟩
        ileft
        isplitl [Hpq Hlv]
        · iunfold liveP; iframe Hlv; iunfold auth.authPubQ; iexact Hpq
        iframe Hr Hp
        ileft
        iunfold bkIdle
        iexists hs, rc, w
        iframe Hlq Hro Hbt Hsw Hq
        ipureintro; exact Hid
      imodintro
      iframe HT Hhh
      isplitl [Hpt]
      · iunfold auth.authPubTok; iexists hs.length - 1; iunfold auth.authPubQ; iexact Hpt
      iunfold auth.authPubQ; iexact Hph
    · iunfold bkBatch at Hbb
      icases Hbb with ⟨>HT', -⟩
      iexfalso; iapply wTok_excl γ.γc $$ [$HT $HT']
  · iexfalso; iapply wTok_excl γ.γc $$ [$HT $HT']
  · iexfalso; iapply wTok_excl γ.γc $$ [$HT $HT']

/-- **The realization meets the lifecycle** at its open share. -/
theorem real_life (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (hq : authOpenQ = qpRep q0 s0 authRdN) :
    realInv (GF := GF) γ d s0 q0 ∗ vaultInv γ.γa γ.γv ⊢ auth.authBkLife γ.γa γ.γc (bOpen d.γB authOpenQ) := by
  iintro ⟨#Hinv, #Hvi⟩
  iunfold auth.authBkLife
  isplitr
  · iintro !> H
    iapply real_retire γ d s0 q0 $$ [$Hinv $Hvi] H
  isplitr
  · iintro !> H
    iapply real_release γ d s0 q0 hq $$ Hinv H
  · iintro !> %hs %p HT Hpt Hhh Hph Hle
    iapply real_publish γ d s0 q0 $$ Hinv %hs %p HT Hpt Hhh Hph Hle

end life

end authReal
end EtcdGrove
end Perennial
