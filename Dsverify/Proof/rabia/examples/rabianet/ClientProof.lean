/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/examples/rabianet/{Op,NewClient}.lean`,
run `rabia-r1wake-1`, onto this kit's Go and `Net/`.)

The kit's client side (`kit.go`): `command`, `op1` (`Op`'s body under `x.mu`: past the sequence
budget, the unknown output; else the request `(c, n)` is registered with the caller's update
(`Ghost.register`) before it is sent; the reply with sequence number `n` (`repOk`) lets the client
collect the update's postcondition (`Ghost.collect`); a get's found-flag from a non-empty value
(`GhostAux.noEmpty_stateOfCmds`); on the timeout, the unknown output), `Op` (`x.mu.Lock`, `op1`,
`Unlock`), `newClient` (wait for the configuration, claim and configure `Conf`, `ClientTcpInit` and
`Connect` to proxy `c mod n`, the mutex over the endpoint state).
-/
module

public import Dsverify.Proof.rabia.examples.rabianet.KitSpecs
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base
public import Perennial.Proof.sync.Link
public import Dsverify.Proof.rabia.examples.rabianet.KitModel
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.rabia.examples.rabianet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.tcp rabia

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.examples.rabianet.Assumptions]
variable [math.rand.Hyps GF]
variable [_root_.Perennial.io.Assumptions] [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj]
variable [sync.Assumptions] [_root_.Perennial.bufio.Assumptions]
variable [tcp_sem : rabia.internal.tcp.Assumptions] [msg_sem : rabia.internal.message.Assumptions]

set_option goose.wp.extras true

theorem command.wp_proof (i : KvInput GoString GoString) :
    {{ (True : IProp GF) }}
      (App (Val (@! rabia.examples.rabianet.command)) (Val #(kvInV i)))
    {{ RET #(cmdOf i); True }} := by
  wp_start
  wp_auto
  cases i with
  | put k v =>
    simp only [kvInV]
    wp_auto
    rw [show ([48#8] ++ k ++ v : GoString) = cmdOf (.put k v) by simp [cmdOf, putCmd]]
    iapply HΦ; itrivial
  | get k =>
    simp only [kvInV]
    wp_auto
    rw [show ([49#8] ++ k : GoString) = cmdOf (.get k) by simp [cmdOf, getCmd]]
    iapply HΦ; itrivial

/-- `op1(x, c, in)`, `Op`'s body, with the endpoint state `clientAt` (held under `x.mu`). -/
theorem op1.wp_proof (γ : Names) (c : Nat) (hc : c < nC) (l t : Loc) (e : ClNames) (cf : RCfg)
    (i : KvInput GoString GoString) (hi : inputOk i) (Q : OpQ GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.examples.rabianet ∗
        structFieldRef Sys go!"t" l ↦□ t ∗ clientChans γ c e t ∗ shared γ ∗ cfgIs γ.rab cf ∗
        clientAt γ c l e ∗ opAU γ.rab i Q }}
      (App (App (App (Val (@! rabia.examples.rabianet.op1)) (Val #l)) (Val #(W64 c)))
        (Val #(kvInV i)))
    {{ (o : Out), RET #o; clientAt γ c l e ∗ (⌜o = unkOutV⌝ ∨
        ∃ σ σ' out, ⌜o = kvOutV out ∧ (kv GoString GoString).step σ i σ' out ∧ outOk out⌝ ∗
          Q σ σ' out) }} := by
  wp_start as ⟨#Ht, #Hch, #Hsh, #Hcfg, Hat, HAU⟩
  have hc6 : c < 6 := hc
  have hcw : uint.nat (W64 (c : Int)) = c := by word
  iunfold clientAt at Hat
  icases Hat with ⟨%n, %sent, %K, %hat, Hnext, Hprod, HK⟩
  obtain ⟨hsent, hnb, hK⟩ := hat
  wp_auto
  wp_if_destruct
  · -- past the budget: unknown, nothing sent
    iapply HΦ
    isplitl [Hnext Hprod HK]
    · iunfold clientAt
      iexists n, sent, K
      iframe
      ipureintro; exact ⟨hsent, hnb, hK⟩
    ileft; ipureintro; rfl
  have hn : n < opBudget := by
    have h32 : n < 2 ^ 32 := by unfold opBudget at hnb; omega
    have : ¬ (W32 (n : Int)).toNat ≥ (W32 (2 ^ 29 : Int)).toNat := by
      intro h; apply Hif; simpa using h
    unfold opBudget; simp at this; omega
  try wp_auto
  unfold clientChans
  icases Hch with ⟨%sc, %rc, #Hsc, #Hrc, #Hspsc, #Hbag⟩
  have hfree : FKey.reg (c, n) ∉ K := fun h => Nat.lt_irrefl _ (hK n h)
  ihave #Hrab : isRabia γ.rab $$ [Hsh]
  · unfold shared; icases Hsh with ⟨#H, -⟩; iexact H
  iapply fupd_wp
  imod register γ.rab ⊤ (by simp) cf c n K hfree i hi Q $$ [Hrab Hcfg HK HAU]
    with ⟨HK, #Hreg, ⟨%γq, #Hq, #HsQ⟩, Hcol⟩
  · iframe Hrab Hcfg HK HAU
  imodintro
  wp_auto
  wp_apply (command.wp_proof i)
  wp_apply wp_slice_literal (V := GoString) (t := go.string) _
  isplitr
  · ipureintro; rfl
  iintro %cs ⟨Hcs, Hcap⟩
  wp_auto
  iapply fupd_wp
  imod ownSlice_persist _ _ _ $$ Hcs with #Hcs
  imodintro
  have hn32 : (W32 (n : Int)).toNat = n := by
    have : n < 2 ^ 32 := by unfold opBudget at hn; omega
    simp only [BitVec.toNat_ofInt]; omega
  wp_apply (wp_spsc_send (t := Command.ty) e.send sc (clSendP γ c)
    (fun _ => iprop(False)) sent _) $$ [$Hspsc $Hprod] as Hprod
  · unfold clSendP
    iexists (CmdV.mk (W32 (uint.Z (W64 (c : Int)))) (W32 (n : Int)) 0 [cmdOf i])
    isplitr
    · ipureintro
      simp only [hn32, hsent]
      exact ⟨by simp, by omega, by omega⟩
    isplitr
    · unfold cmdRep
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl⟩
      iexact Hcs
    · unfold reqOk
      iexists cmdOf i
      isplitr
      · ipureintro
        refine ⟨?_, rfl, rfl, i, rfl, hi⟩
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ofNat, BitVec.toNat_ofInt]
        word
      simp only [hn32]
      iexact Hreg
  -- the endpoint's state at `n + 1`, for `x.mu`'s invariant
  ihave Hat : clientAt γ c l e $$ [Hnext Hprod HK]
  · unfold clientAt
    iexists n + 1, _, _
    rw [show W32 (n : Int) + W32 1 = W32 ((n + 1 : Nat) : Int) by word]
    iframe Hnext Hprod HK
    ipureintro
    refine ⟨by simp [hsent], by omega, ?_⟩
    intro m hm
    rcases List.mem_cons.mp hm with h | h
    · injection h with h; injection h with _ h; omega
    · have := hK m h; omega
  ihave #Htime : (isPkgInit (PROP := IProp GF) pkg_id.time) $$ []
  · iPkgInit
  wp_apply time.After.spec_pkgInit time.wp_After _ $$ [$Htime] as %tch %γt #Htch
  iclear Hcap
  irename «in» => Hin
  wp_for_core
  wp_auto
  cleanup_bool_decide
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Command, inferInstance, inferInstance, inferInstance, inferInstance, rc, e.recv
    isplit
    · ipureintro; rfl
    isplit
    · iapply is_bag_is_chan $$ Hbag
    iapply bag_recv_au _ _ _ _ $$ [$Hlc1 $Hlc2] Hbag
    inext
    iintro %v Hv
    unfold repP cmdRep repOk
    icases Hv with ⟨%q, ⟨%hq, #Hcmds⟩, ⟨%s, %id, %rs, %bc, %j, %res, %cmds, %cmd, %hrep, #Hdec,
      #Hpobj, #Hrf, Hpf⟩⟩
    obtain ⟨hq1, hq2, hq3⟩ := hq
    obtain ⟨hr1, hr2, hrj, hbj, hr3⟩ := hrep
    wp_auto_lc 2
    wp_if_destruct
    rotate_left
    · -- another operation's reply: wait on
      wp_for_post
      iframe
    -- the reply to this operation
    have hseq : q.cliSeq.toNat = n := by
      rw [← hq2, Hif]
      have : n < 2 ^ 32 := by unfold opBudget at hn; omega
      simp only [BitVec.toNat_ofInt]; omega
    ihave %Hclen := ownSlice_len _ _ _ $$ Hcmds
    rw [hr2] at Hclen
    have hl : v.Commands'.len = W64 1 := by
      obtain ⟨h1, h2⟩ := Hclen
      simp only [List.length_singleton] at h1
      word
    simp only [hl, decide_true, Bool.not_true]
    wp_auto
    rw [ite_eq_left (by rw [hl]; decide)]
    wp_apply wp_load_slice_index v.Commands' (sint.Z (W64 0)) q.commands _ res (by decide)
      $$ [$Hcmds] as -
    · ipureintro; rw [hr2]; rfl
    -- the registered command, and `Q` collected
    ihave #Hrf' := Hrf
    iunfold regFacts at Hrf'
    icases Hrf' with ⟨%hlenrb, #Hall⟩
    ihave ⟨%cm, %hcm, #Hreg'⟩ := (BigSepL.bigSepL_lookup hrj) $$ Hall
    rw [hbj] at hcm
    cases hcm
    ihave #Hreg2 : fact γ.rab (.reg (c, q.cliSeq.toNat)) (.cmd (cmdOf i)) $$ [Hreg]
    · rw [hseq]; iexact Hreg
    ihave %hcmd := fact_agree γ.rab (.reg (c, q.cliSeq.toNat)) (.cmd (cmdOf i))
      (.cmd cmd) $$ [Hreg2 Hreg']
    · iframe Hreg2 Hreg'
    injection hcmd with hcmd
    subst hcmd
    have hrj' : rs[j]? = some (c, n) := by rw [← hseq]; exact hrj
    iapply fupd_wp
    imod prefix_inputOk γ.rab ⊤ (by simp) s cmds $$ [Hrab Hpf] with ⟨%hok, Hpf⟩
    · iframe Hrab Hpf
    imod regFacts_inputOk γ.rab ⊤ (by simp) rs bc $$ [Hrab Hrf] with %hokb
    · iframe Hrab Hrf
    imod collect γ.rab ⊤ (by simp) (c, n) s i hi Q γq id rs bc j hrj' cmds
      $$ [Hrab Hlc1 Hcol Hq HsQ Hreg Hdec Hpobj Hrf Hpf] with HQ
    · iframe Hrab Hlc1 Hcol Hq HsQ Hreg Hdec Hpobj Hrf Hpf
    imod lc_fupd_elim_later $$ Hlc2 HQ with ⟨%σ', %o, %hstep, HQ⟩
    imodintro
    have hokL : ∀ x ∈ cmds ++ bc.take j, ∃ i, x = cmdOf i ∧ inputOk i := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hok x hx
      · exact hokb x (List.mem_of_mem_take hx)
    generalize cmds ++ bc.take j = L at hokL hstep hr3 ⊢
    have hne := noEmpty_stateOfCmds L hokL
    cases i with
    | put k v =>
      obtain ⟨hs1, rfl⟩ := hstep
      simp only [kvInV]
      wp_auto
      wp_for_post
      iapply HΦ
      isplitl [Hat]
      · iexact Hat
      iright
      iexists stateOfCmds L, σ', KvOutput.done
      iframe HQ
      ipureintro; exact ⟨rfl, ⟨hs1, rfl⟩, trivial⟩
    | get k =>
      obtain ⟨hs1, rfl⟩ := hstep
      have hk : k.length = 8 := hi
      have hres : res = [49#8] ++ k ++ (stateOfCmds L k).getD [] := by
        rw [hr3]
        simp [execCmd, cmdOf, getCmd, keyLen, List.take_of_length_le (show k.length ≤ 8 by omega)]
      subst hres
      simp only [kvInV]
      wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %hlen8
      have hL : ([49#8] ++ k ++ (stateOfCmds L k).getD []).length =
          9 + ((stateOfCmds L k).getD []).length := by simp [hk]; omega
      rw [hL] at hlen8 ⊢
      rw [decide_eq_false (by word)]
      wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %_
      rw [hL]
      generalize hw : (stateOfCmds L k).getD [] = w at hlen8 ⊢
      have h9 : sint.nat (W64 1 + W64 8) = 9 := by decide
      have hm : sint.nat (W64 ((9 + w.length : Nat) : Int)) = 9 + w.length := by word
      rw [ite_eq_left (by word)]
      have hv : List.take (sint.nat (W64 ((9 + w.length : Nat) : Int)) - sint.nat (W64 1 + W64 8))
          (List.drop (sint.nat (W64 1 + W64 8)) ([49#8] ++ k ++ w)) = w := by
        rw [h9, hm]
        have : List.drop 9 ([49#8] ++ k ++ w) = w := by
          rw [show ([49#8] ++ k ++ w) = ([49#8] ++ k) ++ w by simp]
          exact List.drop_left' (by simp [hk])
        rw [this]; simp
      rw [hv]
      wp_auto
      wp_for_post
      iapply HΦ
      isplitl [Hat]
      · iexact Hat
      iright
      iexists stateOfCmds L, σ', KvOutput.got (stateOfCmds L k)
      iframe HQ
      ipureintro
      have hne' := hne k
      refine ⟨?_, ⟨hs1, rfl⟩, ?_⟩
      · cases hs : stateOfCmds L k with
        | none => rw [hs] at hw; subst hw; rfl
        | some x =>
          rw [hs] at hw hne'; simp only [Option.getD_some] at hw; subst hw
          have : x ≠ [] := fun h => hne' (by rw [h])
          simp [kvOutV, this]
      · cases hs : stateOfCmds L k with
        | none => trivial
        | some x =>
          rw [hs] at hw hne'; simp only [Option.getD_some] at hw; subst hw
          exact ⟨fun h => hne' (by rw [h]), by omega⟩
    done
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
    isplit
    · ipureintro; rfl
    isplit
    · iapply is_bag_is_chan $$ Htch
    iapply bag_recv_au _ _ _ _ $$ [$Hlc1 $Hlc2] Htch
    inext
    iintro %v _
    wp_auto
    wp_for_post
    iapply HΦ
    isplitl [Hat]
    · iexact Hat
    ileft
    ipureintro; rfl
  · iapply BigAndL.bigAndL_nil.2
    itrivial

/-- `Op(x, c, in)` (`Op.spec`): `x.mu.Lock()`, `op1`, `x.mu.Unlock()`. -/
theorem Op.wp_proof : Op.spec (GF := GF) := by
  intro γ c l i Q hc hi
  wp_start as ⟨#Hsys, HAU⟩
  unfold is_sys
  icases Hsys with ⟨%t, %mu, %e, %cf, #Ht, #Hmu, #Hch, #Hsh, #Hcfg, #Hconf, #Hlock⟩
  ihave #Hsync : (isPkgInit (PROP := IProp GF) pkg_id.sync) $$ []
  · iPkgInit
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hsync $Hlock] as ⟨Hlocked, Hat⟩
  wp_apply op1.wp_proof γ c hc l t e cf i hi Q $$ [$Hpkg $Ht $Hch $Hsh $Hcfg $Hat $HAU]
    as %o ⟨Hat, Hres⟩
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock mu (clientAt γ c l e) $$ [$Hsync $Hlocked $Hat]
  · iexact Hlock
  try wp_auto
  iapply HΦ
  icases Hres with (%h | ⟨%σ, %σ', %out, %hp, HQ⟩)
  · ileft; ipureintro; exact h
  · iright; iexists σ, σ', out; iframe HQ; ipureintro; exact hp

/-- `newClient(c)` (`newClient.spec`). -/
theorem newClient.wp_proof (wp_ClientConfAddrs : ClientConfAddrs.spec (GF := GF))
    (wp_waitConf : waitConf.spec (GF := GF)) (wp_NetAddrs : NetAddrs.spec (GF := GF))
    (wp_configure : configure.spec (GF := GF)) (wp_ProxyAddrs : ProxyAddrs.spec (GF := GF))
    (wp_ClientTcpInit : ClientTcpInit.spec (GF := GF))
    (wp_ClientTCP_Connect : ClientTCP.Connect.spec (GF := GF)) :
    newClient.spec (GF := GF) := by
  intro γ c σ hc
  have hc6 : c < 6 := hc
  wp_start as ⟨Hcore, Hσ⟩
  unfold cliCore
  icases Hcore with ⟨#Hsh, HK, Hest, -⟩
  ihave #Hproto := shared_cliCfgProto γ c hc $$ Hsh
  wp_auto
  wp_apply wp_ClientConfAddrs as %sl ⟨%L, Hsl, %HL⟩
  subst HL
  ihave %Hsl0 := ownSlice_len _ _ _ $$ Hsl
  have hcw : sint.Z (W64 (c : Int)) = (c : Int) := by word
  have hsl : sint.Z sl.len = (nC : Int) := by
    obtain ⟨h1, h2⟩ := Hsl0
    rw [List.length_map, List.length_range] at h1
    rw [h1]; exact (Int.toNat_of_nonneg h2).symm
  rw [ite_eq_left (by rw [hcw, hsl]; omega)]
  wp_apply wp_load_slice_index sl _ _ _ (cliCfgAddr c) (by omega) $$ [$Hsl] as -
  · ipureintro; rw [hcw]; simp only [Int.toNat_natCast]; exact range_map_get _ _ _ hc
  wp_apply wp_waitConf γ (cliCfgAddr c) $$ [] as %v ⟨%cf, %Hv, #Hcfg⟩
  · iframe #
  subst Hv
  ihave %Hok := cfgIs_ok' γ.rab cf $$ Hcfg
  have hn5 : cf.n ≤ maxS := by have := Hok; unfold RCfg.Ok at this; unfold maxS; omega
  have hn1 : 1 ≤ cf.n := by have := Hok; unfold RCfg.Ok at this; omega
  wp_apply wp_NetAddrs as %ns ⟨%L, Hns, %HL⟩
  subst HL
  ihave %Hns0 := ownSlice_len _ _ _ $$ Hns
  ihave %Hnwf := ownSlice_wf _ _ _ $$ Hns
  have hnsl : sint.Z ns.len = (maxS : Int) := by
    obtain ⟨h1, h2⟩ := Hns0
    rw [List.length_map, List.length_range] at h1
    rw [h1]; exact (Int.toNat_of_nonneg h2).symm
  have hnz : sint.Z (W64 (cf.n : Int)) = (cf.n : Int) := by unfold maxS at hn5; word
  rw [ite_eq_left (by rw [hnz, show sint.Z (W64 0) = 0 from rfl]; have := Hnwf; omega)]
  ihave ⟨Hps, -⟩ := (ownSlice_split_all (W64 (cf.n : Int)) ns _ _ ⟨by rw [hnz]; omega, by omega⟩).1 $$ Hns
  rw [show sint.nat (W64 (cf.n : Int)) = cf.n by unfold maxS at hn5; word, take_peers cf hn5]
  iapply fupd_wp
  imod ownSlice_persist _ _ _ $$ Hps with #Hps
  imod conf_claim σ ⊤ (by simp) $$ [$Hpkg $Hσ] with HC
  imodintro
  wp_auto
  wp_apply wp_configure _ cf $$ [$Hpkg $HC $Hps] as #Hconf
  · ipureintro; exact Hok
  wp_apply wp_ProxyAddrs as %ps2 ⟨%L, Hps2, %HL⟩
  subst HL
  ihave %Hps20 := ownSlice_len _ _ _ $$ Hps2
  have hps2 : sint.Z ps2.len = (maxS : Int) := by
    obtain ⟨h1, h2⟩ := Hps20
    rw [List.length_map, List.length_range] at h1
    rw [h1]; exact (Int.toNat_of_nonneg h2).symm
  have hm : c % cf.n < cf.n := Nat.mod_lt _ (by omega)
  have hnz' : uint.Z (W64 (cf.n : Int)) = cf.n := by unfold maxS at hn5; word
  rw [ite_eq_right_iff.mpr (fun h => absurd (h.symm.trans hnz') (by omega))]
  wp_auto
  have hmod : sint.Z (W64 (c : Int) % W64 (cf.n : Int)) = ((c % cf.n : Nat) : Int) := by
    unfold maxS at hn5
    have e1 : (W64 (c : Int)).toNat = c := by simp; omega
    have e2 : (W64 (cf.n : Int)).toNat = cf.n := by simp; omega
    have e3 : (W64 (c : Int) % W64 (cf.n : Int)).toNat = c % cf.n := by
      rw [BitVec.toNat_umod, e1, e2]
    have e4 : c % cf.n < 5 := by omega
    word
  rw [ite_eq_left (by rw [hmod, hps2]; unfold maxS at hn5 ⊢; omega)]
  wp_apply wp_load_slice_index ps2 _ _ _ (proxyAddr (c % cf.n)) (by omega) $$ [$Hps2] as -
  · ipureintro; rw [hmod]; simp only [Int.toNat_natCast]
    exact range_map_get _ _ _ (by unfold maxS at hn5 ⊢; omega)
  ihave #Htcp : (isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.tcp) $$ []
  · iPkgInit
  have hc32 : (W32 (uint.Z (W64 (c : Int)))).toNat = c := by word
  wp_apply (wp_ClientTcpInit γ cf (W32 (uint.Z (W64 (c : Int)))) (proxyAddr (c % cf.n))
    (by rw [hc32]; exact hc)) $$ [$Htcp $Hconf] as %t ⟨%γc, #Hchs, Hprod, Hown⟩
  rw [hc32]
  ihave Hest1 := (BigSepL.bigSepL_lookup (i := c % cf.n)
    (by rw [List.getElem?_range (by unfold maxS at hn5 ⊢; omega)])) $$ Hest
  try wp_auto
  try wp_auto
  iapply wp_fupd
  wp_apply (wp_ClientTCP_Connect γ cf c γc t hc) $$ [$Htcp $Hconf $Hsh $Hcfg $Hown $Hest1]
  try wp_auto
  iStructNamed «$r0»
  irename t => Htf
  irename mu => Hmuf
  ipersist Htf
  ipersist Hmuf
  ihave Hat : clientAt γ c «$r0_ptr» γc $$ [next Hprod HK]
  · unfold clientAt
    iexists 0, [], []
    iframe Hprod HK
    isplitr
    · ipureintro; exact ⟨rfl, by unfold opBudget; omega, fun m hm => absurd hm (by simp)⟩
    rw [show (W32 ((0 : Nat) : Int) : w32) = 0 from rfl]
    iexact next
  imod sync.init_Mutex (clientAt γ c «$r0_ptr» γc) ⊤ _ $$ «$v2» [Hat] with #Hlock
  · inext; iexact Hat
  imodintro
  iapply HΦ
  unfold is_sys
  iexists t, «$v2_ptr», γc, cf
  iframe #

theorem outOk_outB (o : KvOutput GoString) (h : outOk o) : outB o := by
  cases o with
  | done => trivial
  | got w =>
    cases w with
    | none => trivial
    | some v => exact h

theorem clampO_val (o : KvOutput GoString) (h : outOk o) : (clampO o).1 = o := by
  rw [clampO_of o (outOk_outB o h)]

theorem kvOutV_outVal (o : KvOutput GoString) : kvOutV o = outVal o := by
  rcases o with _ | _ | v <;> rfl

theorem kvInV_inVal (i : KvInput GoString GoString) : kvInV i = inVal i := by
  cases i <;> rfl

theorem attempt.wp_proof : attempt.spec (GF := GF) := by
  wp_start
  wp_auto
  iapply HΦ
  itrivial

section client
variable [ρ : _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.lib.remote.RemoteGS]

open github_com.mit_pdos.etcd_grove.examples.lib.remote in
theorem Client.wp_proof (wp_Codec : Codec.spec (GF := GF) (hG := hG))
    (wp_ServeClient : github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient.spec
      (GF := GF) (hG := hG) (I := KIn) (O := KOut))
    (wp_newClient : newClient.spec (GF := GF)) (wp_ClientAddrs : ClientAddrs.spec (GF := GF))
    (wp_attempt' : attempt.spec (GF := GF)) :
    Client.spec (GF := GF) (hG := hG) := by
  intro γ c σ hc
  have hc6 : c < 6 := hc
  wp_start as ⟨Hcore, Hσ, #Hra, #Hmap⟩
  ihave #Hrp : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_newClient γ c σ hc $$ [$Hpkg $Hcore $Hσ] as %l #Hsys
  irename sys => Hsysp
  ipersist Hsysp
  irename c => Hcp
  ipersist Hcp
  try wp_auto
  wp_apply wp_ClientAddrs as %sl ⟨%L, Hsl, %HL⟩
  subst HL
  ihave %Hsl0 := ownSlice_len _ _ _ $$ Hsl
  have hcw : sint.Z (W64 (c : Int)) = (c : Int) := by word
  have hsl : sint.Z sl.len = (nC : Int) := by
    obtain ⟨h1, h2⟩ := Hsl0
    rw [List.length_map, List.length_range] at h1
    rw [h1]; exact (Int.toNat_of_nonneg h2).symm
  rw [ite_eq_left (by rw [hcw, hsl]; omega)]
  wp_apply wp_load_slice_index sl _ _ _ (cliAddr c) (by omega) $$ [$Hsl] as -
  · ipureintro; rw [hcw]; simp only [Int.toNat_natCast]; exact range_map_get _ _ _ hc
  try wp_auto
  wp_apply (wp_Codec γ) as %cd #Hcd
  wp_apply wp_attempt' as %d -
  try wp_auto
  wp_apply wp_ServeClient (RBase.svc (Gg := hG.goose_globalGS) (kvR γ)) _ _ _ _ cd d
    (fun sys => iprop(⌜sys = interface.mkOk (go.GoType.PointerType Sys.ty) #l⌝ ∗ is_sys γ c l))
    $$ [] as ⟨⟩
  iframe #
  isplit
  · iapply codecOk_wireOk $$ Hcd
  isplit
  · -- the operation: client `c`'s request
    iapply opMaybe_svcOp
    unfold opMaybe
    iintro %sys %i %Φo
    iintro !> %Φr ⟨⟨%Hsys, #Hs⟩, HL⟩ HΦr
    subst Hsys
    ihave HAU := slotUpd_opAU γ i Φo $$ HL
    simp only [RBase.svc, kvR, inV]
    wp_auto
    rw [← kvInV_inVal]
    wp_apply Op.wp_proof γ c l i.1 (fun _ _ o => Φo (clampO o)) hc i.2.1 $$ [$Hpkg $Hs $HAU]
      as %o Ho
    try wp_auto
    iapply HΦr
    isplitr
    · iframe #
    icases Ho with (%Ho | ⟨%σ, %σ', %out, %Hout, HQ⟩)
    · subst Ho
      iright; ipureintro; rfl
    · obtain ⟨rfl, -, hok⟩ := Hout
      ileft
      iexists clampO out
      iframe HQ
      ipureintro
      rw [clampO_val out hok, kvOutV_outVal]
  · -- the client's system
    iintro !> %Φr - HΦr
    wp_auto
    iapply HΦr
    iframe #
    ipureintro; rfl

end client

end proof

end Perennial.rabia.examples.rabianet
