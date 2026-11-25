/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/client/New.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension.
-/
/-
`client.New`: the members parsed (`FromHostPort`), sorted (`sort.Sort` over `ByLess`), a response
queue, and the client with request number 0, nothing pending.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.client
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.client.Send
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.queue
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.ipv4port
public import Perennial.Proof.sort.Link

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem set_append_rep {α} (ps : List α) (z v : α) (n : Nat) (h : ps.length < n) :
    (ps ++ List.replicate (n - ps.length) z).set ps.length v =
      (ps ++ [v]) ++ List.replicate (n - (ps ++ [v]).length) z := by
  obtain ⟨m, hm⟩ : ∃ m, n - ps.length = m + 1 := ⟨n - ps.length - 1, by omega⟩
  have hm2 : n - (ps.length + 1) = m := by omega
  rw [hm, List.replicate_succ, List.set_append_right _ _ (by simp)]
  simp [hm2]

theorem get_append_rep {α} (ps : List α) (z : α) (n : Nat) (h : ps.length < n) :
    (ps ++ List.replicate (n - ps.length) z)[ps.length]? = some z := by
  rw [List.getElem?_append_right (by simp)]
  simp only [Nat.sub_self]
  rw [List.getElem?_replicate]; simp; omega

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : client.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]
variable [models_lab.jsoncodec.JsonCodec GF]
variable [network.Assumptions] [ipv4port.Assumptions] [queue.Assumptions] [sort.Assumptions]

set_option goose.wp.extras true

theorem client.cfg_addrOk (n : GoInterface) (γ : VsrGhost.Names) :
    ∀ ps : List ipv4port.IPv4Port,
    network.isNet (GF := GF) n γ ∗ ([∗list] v ∈ ps, ∃ a : GoString, ipv4port.ipCfg v a) ⊢
      [∗list] v ∈ ps, network.netAddrOk n v
  | [] => by
    iintro -
    iapply BigSepL.bigSepL_nil.2; itrivial
  | v :: l => by
    iintro ⟨#Hn, Hl⟩
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨⟨%a, #H⟩, Hl⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl []
    · ihave %Hs := ipv4port.ipCfg_str v a $$ H
      iapply network.netAddrOk_cfg n γ v a Hs.1 Hs.2 $$ Hn
    iapply client.cfg_addrOk n γ l
    iframe #
    iexact Hl

theorem client.New.wp_proof
    (wp_FromHostPort : ipv4port.IPv4Port.FromHostPort.spec (GF := GF) (hG := hG))
    (wp_sorter : ipv4port.ByLess.sorter.spec (GF := GF) (hG := hG))
    (wp_QNew : queue.New.spec (GF := GF) (hG := hG)) :
    client.New.spec (GF := GF) (hG := hG) := by
  intro F cfg γ dq ms hms hms62 hcfg ht
  wp_start as ⟨Hms, #Hnet, Hsnd, #Hprotos, #Hlog, #Hcodec, #Hkit⟩
  wp_auto
  ihave %Hmlen := ownSlice_len $$ Hms
  wp_apply (wp_slice_make2 (V := ipv4port.IPv4Port) cfg.Members'.len) as %sl ⟨Hsl, Hcap⟩
  · ipureintro; exact Hmlen.2
  rename_i _ gi_ptr
  irename : (gi_ptr ↦ (_ : w64) : IProp GF) => gi
  rw [← Hmlen.1]
  ihave HI : (∃ (k : w64) (ps : List ipv4port.IPv4Port) (vv : GoString) (ii : w64),
      "ri" ∷ i_ptr ↦ k ∗ "v" ∷ v_ptr ↦ vv ∗ "gi" ∷ gi_ptr ↦ ii ∗
      "Hsl" ∷ sl ↦* (ps ++ List.replicate (ms.length - ps.length) (zero_val ipv4port.IPv4Port)) ∗
      "Hps" ∷ ([∗list] j ↦ p ∈ ps, ∃ a, ⌜ms[j]? = some a⌝ ∗ ipv4port.ipCfg p a) ∗
      "%Hk" ∷ ⌜sint.nat k = ps.length ∧ 0 ≤ sint.Z k ∧ sint.Z k ≤ (ms.length : Int)⌝ :
      IProp GF) $$ [i v gi Hsl]
  · iexists _, [], _, _
    iframe
    simp only [List.length_nil]
    iframe
    isplitr
    · iapply BigSepL.bigSepL_nil.2; itrivial
    ipureintro
    exact ⟨rfl, by word, by word⟩
  wp_for HI
  by_cases hlt : sint.Z k < sint.Z cfg.Members'.len
  · simp only [hlt, _root_.decide_true, ↓reduceIte]
    have Hlt : (sint.Z k).toNat < ms.length := by word
    obtain ⟨a, Ha⟩ : ∃ a, ms[(sint.Z k).toNat]? = some a := ⟨_, List.getElem?_eq_getElem Hlt⟩
    wp_auto
    simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z cfg.Members'.len from ⟨Hk.2.1, hlt⟩,
      _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z k) ms dq a Hk.2.1 $$ [Hms] as Hms
    · iframe; ipureintro; exact Ha
    ihave %Hsllen := ownSlice_len $$ Hsl
    have hpl : ps.length < ms.length := by word
    have hb2 : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len := by
      have := Hsllen.1; simp only [List.length_append, List.length_replicate] at this
      constructor <;> word
    simp only [hb2, _root_.and_self, ↓reduceIte]
    have hkp : (sint.Z k).toNat = ps.length := by word
    icases ownSlice_elem_acc (sint.Z k) (zero_val ipv4port.IPv4Port) sl (DFrac.own 1) _ Hk.2.1
      (by rw [hkp]; exact get_append_rep ps _ _ hpl) $$ Hsl with ⟨Hp, Hsl⟩
    have hma : a ∈ ms := List.mem_of_getElem? Ha
    wp_apply (wp_FromHostPort _ _ a (hcfg a hma)) $$ [Hp] as ⟨%pv, Hp, #Hcfg⟩
    · iexact Hp
    ihave Hsl := Hsl $$ Hp
    rw [hkp, set_append_rep ps _ _ _ hpl]
    wp_for_post
    iframe
    iexists _, ps ++ [pv], _, _
    iframe
    isplitr
    · iapply BigSepL.bigSepL_cons.2
      isplitl
      · iexists a
        iframe #
        ipureintro
        rw [Nat.zero_add, ← hkp]; exact Ha
      iapply BigSepL.bigSepL_nil.2; itrivial
    ipureintro
    simp only [List.length_append, List.length_singleton]
    refine ⟨?_, ?_, ?_⟩ <;> word
  · simp only [hlt, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
    have hpl : ps.length = ms.length := by word
    rw [hpl, Nat.sub_self, List.replicate_zero, List.append_nil]
    wp_auto
    ihave #Hsrt := wp_sorter sl $$ []
    · iPkgInit
    ihave Hown : ipv4port.cfgList sl ps $$ [Hsl Hps]
    · unfold ipv4port.cfgList
      iframe
      iapply (BigSepL.bigSepL_mono_of_forall
        (Ψ := fun _ v => iprop(∃ a : GoString, ipv4port.ipCfg v a)) ?_) $$ Hps
      intro k x
      iintro ⟨%a, -, H⟩
      iexists a
      iexact H
    wp_apply (sort.wp_Sort ⟨ipv4port.ByLess.ty, #sl⟩ (ipv4port.cfgList sl) ipv4port.portLt
      ipv4port.ByLess.swo ps) $$ [Hown] as %ps' ⟨Hown, %Hperm, -⟩
    · iframe; iframe #; ipureintro
      omega
    unfold ipv4port.cfgList
    icases Hown with ⟨Hsl, Hps⟩
    iapply fupd_wp
    imod ownSlice_persist $$ Hsl with #Hsl
    imodintro
    ihave #Hok := client.cfg_addrOk cfg.Network' γ ps' $$ [Hnet Hps]
    · iframe #; iexact Hps
    have hlen' : 0 < ps'.length := by rw [← Hperm.length_eq, hpl]; exact hms
    wp_apply (wp_QNew events.Reply.ty
      (fun rep : events.Reply => VsrGhost.fact γ (.msg (.reply (uint.nat rep.ID')
        (uint.nat rep.ClientID') (uint.nat rep.ViewNum') rep.Result')))) as %q #Hq
    iapply HΦ
    iframe
    unfold client.isClient
    iexists _, ps', F, ‹models_lab.jsoncodec.JsonCodec GF›
    iframe
    iframe #
    dsimp only
    ipureintro
    exact ⟨⟨rfl, rfl, hlen'⟩, ht, rfl, rfl⟩
    done
