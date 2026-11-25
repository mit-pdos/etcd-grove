/- Lean-first (no Rocq counterpart).

# `etcd/dist/putgetk`: member `i`'s machine's boot (`notes/putget-dist-plan.md` §13b, plan item 4)

`member_bootK`: member `i`'s boot program (`putgetk.initialize' #()`, then `putgetk.Member(i, []string{peers…},
[]string{clients…})`) is safe from its share of the start (`⌜cfgOk ∧ i < n⌝ -∗ memberShareK …` at
`Pub = putgetPub`) and its whole start (`DistBootWpSL srvLevelK`), as putget's `member_boot`
(`dist/putget/AdequacyMember.lean`): the file extension's start, the member's WAL area from its machine's
files (`MemberFiles i`), the package's initialization (its registration rights allocated here: putgetk's
`regQs` is putget's list, so `putget_regQsOk` serves), the two slice literals (`wp_strSliceLit`: a list of
`2 ^ 63` strings or more exits angelically), then `Member.wp_proof` at its callees' linked results
(`Valid`, `AddrOK`, `decimal`, `MemberID` over Perennial's `crypto.sha1.wp_Sum`, `Name` over `FormatUint`,
`holdForever` over `time.Sleep`, `zap.NewNop`, the interim axioms `etcd_dist.Serve_dist.wp_proof` and
`bootstrap.wp_proof_dist`) and the
named hypothesis `StartMember_dist` (S5's member side, `HSM`).
-/
module

public import Proof.google_golang_org.protobuf.proto.MarshalBootConfChange
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.bootstrapDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Member
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Valid
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.AddrOK
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.decimal
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.MemberID
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Name
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.holdForever
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.InitLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.PkgTable
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.TopLevelDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.AdequacyMember
public import Perennial.Proof.crypto.sha1.Link

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putgetk_dist

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic go_etcd_io.raft.v3 Net etcd_putget_dist

/-! ## The configuration's slice literals -/

theorem arrayLiteralSize_strKE [GooseExts] [GoGlobalContext] (l : List GoString) :
    go.arrayLiteralSize (l.map (arrayLitKE go.string)) = l.length := by
  have h : ∀ (f : Int × Int → keyed_element → Int × Int),
      (∀ (a b : Int) (y : GoString), f (a, b) (arrayLitKE go.string y) = (a + 1, b)) →
      ∀ (ys : List GoString) (a b : Int),
        List.foldl f (a, b) (ys.map (arrayLitKE go.string)) = (a + ys.length, b) := by
    intro f hf ys
    induction ys with
    | nil => intro a b; simp
    | cons y ys ih =>
      intro a b
      simp only [List.map_cons, List.foldl_cons, hf, List.length_cons]
      rw [ih]; congr 1; push_cast; omega
  unfold go.arrayLiteralSize
  rw [h _ (fun a b y => rfl) l 0 0]
  simp

theorem arrayLiteralSize_strLit [GooseExts] [GoGlobalContext] (l : List GoString) :
    go.arrayLiteralSize (l.map (fun s => KeyedElement none (ElementExpression go.string (Val #s)))) =
      l.length := by
  have h : ∀ (f : Int × Int → keyed_element → Int × Int),
      (∀ (a b : Int) (y : GoString),
        f (a, b) (KeyedElement none (ElementExpression go.string (Val #y))) = (a + 1, b)) →
      ∀ (ys : List GoString) (a b : Int),
        List.foldl f (a, b) (ys.map (fun s => KeyedElement none (ElementExpression go.string (Val #s)))) =
          (a + ys.length, b) := by
    intro f hf ys
    induction ys with
    | nil => intro a b; simp
    | cons y ys ih =>
      intro a b
      simp only [List.map_cons, List.foldl_cons, hf, List.length_cons]
      rw [ih]; congr 1; push_cast; omega
  unfold go.arrayLiteralSize
  rw [h _ (fun a b y => rfl) l 0 0]
  simp

section lit
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

set_option goose.wp.unfoldSliceLiterals true in
/-- **A configuration list's slice literal** (`strSliceLit`): a list of fewer than `2 ^ 63` strings
evaluates to a slice that points to it; a longer one exits angelically (Go cannot build it). -/
theorem wp_strSliceLit (l : List GoString) (Φ : val → IProp GF) :
    (⌜l.length < 2 ^ 63⌝ -∗ ∀ sl : GoSlice, sl ↦* l -∗ Φ #sl) ⊢ WP (strSliceLit l) {{ Φ }} := by
  iintro HΦ
  unfold strSliceLit
  wp_pure
  by_cases hlen : l.length < 2 ^ 63
  · iapply (wp_slice_literal (V := GoString) (l := l)
      (kvs := l.map (fun s => KeyedElement none (ElementExpression go.string (Val #s)))))
    have hp := pure_wp_array_lit_full (hlc := HasLC.hasLC) (GF := GF)
      (go.arrayLiteralSize (l.map (fun s => KeyedElement none (ElementExpression go.string (Val #s)))))
      go.string l _ (by unfold arrayLitKE; rfl)
      (by rw [arrayLiteralSize_strLit]; simp) (by rw [arrayLiteralSize_strLit]; simpa using hlen)
    have hp' : ∀ Ψ : val → IProp GF,
        iprop(▷ (£ 1 -∗ WP (Val #(array.mk (go.arrayLiteralSize
          (l.map (fun s => KeyedElement none (ElementExpression go.string (Val #s))))) l))
          {{ Ψ }})) ⊢
          WP (App (Val (GoInstruction (CompositeLiteral (go.ArrayType
              (go.arrayLiteralSize (l.map (fun s => KeyedElement none (ElementExpression go.string (Val #s)))))
              go.string))))
            (Val (LiteralValueV (l.map (fun s => KeyedElement none (ElementExpression go.string (Val #s))))))) {{ Ψ }} :=
      fun Ψ => hp.pure_wp_wp _ _ Ψ [] trivial
    iapply (hp' _)
    inext
    iintro -
    wp_auto
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    ihave HΦ' := HΦ $$ %hlen
    iapply HΦ'
    iexact Hsl
  · wp_pures
    rw [arrayLiteralSize_strLit]
    rw [ite_eq_right (by omega)]
    iapply wp_AngelicExit

end lit

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem GooseGlobalGS.gooseInvGS

/-- **putgetk's registering packages' IDs can have their rights**: its `regQs` is putget's list. -/
theorem putgetk_regQsOk :
    prometheus.regQsOk github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.regQs :=
  putget_regQsOk

set_option maxHeartbeats 3200000 in
/-- **Member `i`'s machine's boot** (see the file header). -/
theorem member_bootK [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions] [log.NewModel] [net.FieldAssumptions]
    (HEnv : EtcdVerifyOff)
    (HSM : ∀ (hG : HeapGS .hasLC putgetGF) [π : NetProtoGS]
      (S5 : etcd_dist.S5Draft (G := (putgetHeapAt hG lctx).goose_globalGS) putgetGF),
      etcd_dist.StartMember_dist.spec (GF := putgetGF) (hG := putgetHeapAt hG lctx) S5)
    (peers clients : List GoString) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hblf : BootLogFacts (idsOf peers) ps ctxs boot)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit)
    (Hdbo : storage.diskOk)
    (Hbgo : BootGoK peers clients ps ctxs)
    (Hfips : crypto.fips140.GodebugFips140Off)
    (i : Nat) (hi : i < peers.length) (σm : state) (Hm : MemberFiles i σm)
    [G : GooseGlobalGS .hasLC putgetGF] [π : NetProtoGS] (S5 : etcd_dist.S5Draft putgetGF) :
    DistBootWpSL srvLevelK (2 ^ 28 - 1) (bootMember peers clients i) σm
      (iprop(⌜cfgOk peers clients ∧ i < peers.length⌝ -∗ ∃ (c : etcd_dist.ClusterNames) (γE : GName),
        memberShareK S5 c peers clients ps ctxs boot i γE (putgetPub (GF := putgetGF)))) := by
  intro hG hGG hL hlo hrb hT
  obtain ⟨G', ⟨fl, lc, nh, gs, th, cr⟩⟩ := hG
  simp only at hGG hL
  subst hGG hL
  letI hG : HeapGS .hasLC putgetGF := ⟨G', ⟨fl, lc, nh, gs, th, cr⟩⟩
  haveI : ReceiptBoundLe putgetGF (2 ^ 62) := ⟨by omega⟩
  haveI : ReceiptBoundLe putgetGF (2 ^ 28) := ⟨by omega⟩
  haveI : ThreadBoundLe putgetGF (2 ^ 28) := ⟨by rw [hT]; omega⟩
  haveI := etcdFsSemOk
  iintro Hshare Hls Hgs Htok
  -- the machine's registration rights (as `member_boot`)
  imod (prometheus.regKeys_alloc (GF := putgetGF)
    github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.regQs putgetk_regQsOk) with ⟨%γreg, Hregs⟩
  letI : prometheus.PromRegGS putgetGF := ⟨γreg⟩
  ihave Hns := prometheus.idToks_regsFree (GF := putgetGF)
    github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.regQs $$ Hregs
  ihave Hown := ownInitializing_of_empty
    (github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.getIsPkgInit (GF := putgetGF)) $$ Hgs
  ihave #Hvoff : ⌜EtcdVerifyOff⌝ $$ []
  · ipureintro; exact HEnv
  imod etcdNetFs_start σm Hm.1 $$ Hls with ⟨#Hos, -, Htree⟩
  imodintro
  -- the member's WAL area, from its machine's files
  iapply (wp_walAreas ⟨putgetGF_allG⟩ etcdFsExts_sat etcdFsExts_satL (extLocal Fs.fsExt σm.world) Hm.1
    [memberDataDir (nameOf i)] (List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩) Hm.2
    (fun d hd => by
      rw [List.mem_singleton.1 hd]
      exact dirFits_srvWalDirOf_memberDataDir (nameOf i) (nameOf_len i))
    inferInstance (bootMember peers clients i) rfl _) $$ Hos Htree
  iintro Hareas
  icases BigSepL.bigSepL_cons.1 $$ Hareas with ⟨Hwa, -⟩
  -- `putgetk.initialize' #()`
  unfold bootMember
  wp_apply (github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.wp_initialize' _
    github_com.mit_pdos.etcd_grove.examples.etcd.dist.putgetk.getIsPkgInit_wf) $$ [Hown Hns]
    as ⟨-, #Hpkg⟩
  · iframe
  (try wp_auto)
  -- the two slice literals (`clients` first)
  wp_bind (strSliceLit clients)
  iapply wp_strSliceLit clients
  iintro %hcl %csl Hcsl
  (try wp_auto)
  wp_bind (strSliceLit peers)
  iapply wp_strSliceLit peers
  iintro %hpl %psl Hpsl
  (try wp_auto)
  -- `putgetk.Member(i, peers, clients)`
  wp_apply (Member.wp_proof
      (Valid.wp_proof (AddrOK.wp_proof decimal.wp_proof) (MemberID.wp_proof crypto.sha1.wp_Sum))
      (Name.wp_proof etcdstart.strconv.wp_FormatUint) zap.NewNop.wp_proof
      (holdForever.wp_proof time.Sleep.wp_proof) etcd_dist.Serve_dist.wp_proof
      (fun S5' => HSM hG S5') mvcc.api.mvccApi_names_nonempty_law_holds
      _root_.Perennial.EtcdGrove.proto.MarshalBootConfChange.wp_proof
      (fun {_} {_} => _root_.Perennial.EtcdGrove.bootstrap.wp_proof_dist)
      S5 peers clients ps ctxs boot i (putgetPub (GF := putgetGF)) psl csl Hfips Hblf Hbgo
      (by omega) (by unfold srvLevels; rw [hT]; omega) Haf Hbuq Hrf Hdbo inferInstance)
    $$ [Htok Hpsl Hcsl Hwa Hshare]
  · iframe; iframe #
  ipureintro
  rfl

end etcd_putgetk_dist
end EtcdGrove
end Perennial

end
